#include "arena.h"
#include "class_file.h"
#include "str.h"
#include <getopt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static const char *usage =
    // clang-format off
"A small compiler for the Kotlin programming language."
"\n"
"\n  %s [OPTIONS] <path>"
"\n"
"\nEXAMPLES:"
"\n  %s -j /usr/lib/jvm/java-21-openjdk-amd64/ -c /usr/share/java/kotlin-stdlib.jar main.kt"
"\n"
"\nOPTIONS:"
"\n  -v, --verbose                  Verbose."
"\n  -m, --memory-usage             Debug memory usage by printing a heap dump in the pprof format."
"\n  -h, --help                     Print this help message and exit."
"\n  -c, --classpath <classpath>    Load additional classpath entries, which are colon separated."
"\n  -j, --java-home <java_home>    Java home (the root of the Java installation)."
"\n"
    // clang-format on
    ;

static struct option long_cli_options[] = {
    {.name = "java-home", .has_arg = true, .val = 'j'},
    {.name = "memory-usage", .has_arg = false, .val = 'm'},
    {.name = "classpath", .has_arg = true, .val = 'c'},
    {.name = "verbose", .has_arg = false, .val = 'v'},
    {.name = "help", .has_arg = false, .val = 'h'},
};

static void print_usage_and_exit(const char *executable_name) {
  printf(usage, executable_name, executable_name);
  exit(0);
}

int main(int argc, char *argv[]) {
  pg_assert(argc > 0);

  int opt = 0;
  str cli_classpath = str_from_c(".");
  str cli_java_home = {0};
  bool cli_mem_debug = false;

  int options_index = 0;
  while ((opt = getopt_long(argc, argv, "hmvc:j:", long_cli_options,
                            &options_index)) != -1) {
    switch (opt) {
    case 'v':
      cli_log_verbose = true;
      break;

    case 'c':
      cli_classpath = str_from_c(optarg);
      break;

    case 'h':
      print_usage_and_exit(argv[0]);
      break;

    case 'm':
      cli_mem_debug = true;
      break;

    case 'j':
      cli_java_home = str_from_c(optarg);
      break;

    case 0: // Long option
    {
      struct option long_cli_option = long_cli_options[options_index];
      str cli_option_name = str_from_c((char *)long_cli_option.name);
      str cli_arg = str_from_c(optarg);
      if (str_eq_c(cli_option_name, "java-home"))
        cli_java_home = cli_arg;
      if (str_eq_c(cli_option_name, "classpath"))
        cli_classpath = cli_arg;
      else {
        fprintf(stderr,
                "Got argument for long option that did not expect any: %s %s\n",
                long_cli_option.name, optarg);
        print_usage_and_exit(argv[0]);
        exit(EINVAL);
      }

      break;
    }

    default:
      fprintf(stderr, "Unknown option: %c\n", opt);
      print_usage_and_exit(argv[0]);
    }
  }

  if (optind == argc) {
    fprintf(stderr, "Missing source file.\n");
    print_usage_and_exit(argv[0]);
  }
  if (optind != argc - 1) {
    fprintf(stderr, "Multiple source files not yet supported.\n");
    print_usage_and_exit(argv[0]);
  }
  if (str_is_empty(cli_java_home)) {
    fprintf(stderr, "Missing required option -j, --java-home.\n");
    print_usage_and_exit(argv[0]);
  }
  if (str_is_empty(cli_classpath)) {
    fprintf(stderr, "Given empty class path (-c <class_path>).\n");
    print_usage_and_exit(argv[0]);
  }

  mem_profile mem_profile = {
      .arena = arena_new(8 * MiB, NULL),
  };
  arena_t arena =
      arena_new(32 * MiB, cli_mem_debug ? &mem_profile : NULL); // 64 MiB
  LOG("Initial: arena_available=%lu", arena.end - arena.start);

  // This size should be at least the size of the biggest file we read.
  arena_t scratch_arena = arena_new(256 * MiB, NULL);

  str *class_path_entries =
      class_path_string_to_class_path_entries(cli_classpath, &arena);

  {
    // TODO: when parsing multiple files, need to allocate that.
    char *source_file_name_cstr = argv[optind];
    str source_file_name = str_from_c(source_file_name_cstr);
    if (!str_ends_with(source_file_name, str_from_c(".kt"))) {
      fprintf(stderr, "Expected an input file ending with .kt\n");
      exit(EINVAL);
    }

    ut_read_result_t source_file_read_res =
        ut_read_all_from_file_path(source_file_name_cstr, &arena);
    if (source_file_read_res.error) {
      fprintf(stderr, "Failed to read the file %s: %s\n", source_file_name_cstr,
              strerror(source_file_read_res.error));
      exit(source_file_read_res.error);
    }
    if (source_file_read_res.content.len > UINT32_MAX) {
      fprintf(stderr, "The source file %.*s is too big: got %lu, max is %u\n",
              (int)source_file_name.len, source_file_name.data,
              source_file_read_res.content.len, UINT32_MAX);
      return false;
      exit(E2BIG);
    }

    // Lex.
    lex_lexer_t lexer = {
        .file_path = source_file_name,
    };

    str source = source_file_read_res.content;
    pg_array_init_reserve(lexer.tokens, source.len, &arena);
    pg_array_init_reserve(lexer.line_table, source.len, &arena);

    u8 *current = source.data;
    lex_lex(&lexer, source, &current, &arena);

    // Parse.
    parser_t parser = {
        .buf = source,
        .lexer = &lexer,
    };
    const u32 root_i = par_parse(&parser, &arena);

    if (parser.state != PARSER_STATE_OK)
      return 1; // TODO: Should type checking still proceed?

    const str class_file_path =
        cf_make_class_file_path_kt(source_file_name, &arena);

    resolver_t resolver = {0};
    resolver_init(&resolver, &parser, class_path_entries, class_file_path,
                  &arena);

    resolver_load_standard_types(&resolver, cli_java_home, scratch_arena,
                                 &arena);
    LOG("After loading known types: arena_available=%lu",
        arena.end - arena.start);

    resolver_collect_user_defined_function_signatures(&resolver, scratch_arena,
                                                      &arena);
    resolver_resolve_node(&resolver, root_i, scratch_arena, &arena);

    // Debug types.
    {
      LOG("------ After type checking%s", "");
      LOG("After type checking: arena_available=%lu", arena.end - arena.start);

      arena_t tmp_arena = arena;
      resolver_ast_fprint_node(&resolver, root_i, stderr, 0, &tmp_arena);
    }

    if (parser.state != PARSER_STATE_OK)
      return 1;

    // Emit bytecode.
    cf_class_file_t class_file = {
        .class_file_path = class_file_path,
        .minor_version = 0,
        .major_version =
            17, // TODO: Add a CLI option to choose the jdk/jre version
        .access_flags = ACCESS_FLAGS_SUPER | ACCESS_FLAGS_PUBLIC,
    };
    cf_init(&class_file, &arena);
    cg_emit(&resolver, &class_file, root_i, &arena);
    if (parser.state != PARSER_STATE_OK)
      return 1;

    char *class_file_path_c_str =
        str_to_c(class_file.class_file_path, &scratch_arena);
    FILE *file = fopen(class_file_path_c_str, "w");
    if (file == NULL) {
      fprintf(stderr, "Failed to open the file %.*s: %s\n",
              (int)source_file_name.len, (char *)source_file_name.data,
              strerror(errno));
      return errno;
    }
    cf_write(&class_file, file);
    fclose(file);

    LOG("nodes=%lu sizeof(par_ast_node_t)=%lu mem=%lu",
        pg_array_len(parser.nodes), sizeof(par_ast_node_t),
        pg_array_len(parser.nodes) * sizeof(par_ast_node_t));
    LOG("types=%lu sizeof(ty_type_t)=%lu mem=%lu", pg_array_len(resolver.types),
        sizeof(ty_type_t), pg_array_len(resolver.types) * sizeof(ty_type_t));

    LOG("After codegen: arena_available=%lu", arena.end - arena.start);

    {
      LOG("\n----------- Verifiying%s", "");

      ut_read_result_t read_res =
          ut_read_all_from_file_path(class_file_path_c_str, &scratch_arena);
      if (read_res.error) {
        fprintf(stderr, "Failed to read the file %.*s: %s\n",
                (int)class_file_path.len, (char *)class_file_path.data,
                strerror(read_res.error));
        return read_res.error;
      }

      cf_class_file_t class_file_verify = {.class_file_path =
                                               class_file.class_file_path};
      u8 *current = read_res.content.data;
      cf_buf_read_class_file(read_res.content, &current, &class_file_verify,
                             &scratch_arena);
    }
  }
  if (cli_mem_debug) {
    FILE *f = fopen("profile.heap", "w");
    pg_assert(f);
    mem_profile_write(&mem_profile, f);
    fclose(f);
  }
}
