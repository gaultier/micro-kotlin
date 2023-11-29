#include "arena.h"
#include "array.h"
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

Array32_struct(int);

int main(int argc, char *argv[]) {
  pg_assert(argc > 0);

  int opt = 0;
  Str cli_classpath = str_from_c(".");
  Str cli_java_home = {0};
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
      Str cli_option_name = str_from_c((char *)long_cli_option.name);
      Str cli_arg = str_from_c(optarg);
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

  pg_assert(optind <= argc);

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

  Mem_profile mem_profile = {.arena = arena_new(8 * MiB, NULL)};
  Arena arena = arena_new(1024 * MiB, cli_mem_debug ? &mem_profile : NULL);
  LOG("Initial: arena_available=%lu", arena.end - arena.start);

  // This size should be at least the size of the biggest file we read.
  Arena scratch_arena = arena_new(512 * MiB, NULL);

  Array32(Str) class_path_entries =
      class_path_string_to_class_path_entries(cli_classpath, &arena);

  {
    // TODO: when parsing multiple files, need to allocate that.
    char *source_file_name_cstr = argv[optind];
    Str source_file_name = str_from_c(source_file_name_cstr);
    if (!str_ends_with(source_file_name, str_from_c(".kt"))) {
      fprintf(stderr, "Expected an input file ending with .kt\n");
      exit(EINVAL);
    }

    Read_result source_file_read_res =
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
    Lexer lexer = {.file_path = source_file_name};

    Str source = source_file_read_res.content;
    u8 *current = source.data;
    lex_lex(&lexer, source, &current, &arena);

    // Parse.
    Parser parser = {
        .buf = source,
        .lexer = &lexer,
    };
    const Ast_handle root_handle = parser_parse(&parser, &arena);
    parser_ast_fprint(&parser, root_handle, stderr, 0, 0, arena);

    if (parser.state != PARSER_STATE_OK)
      return 1; // TODO: Should type checking still proceed?

    const Str class_file_path =
        jvm_make_class_file_path_kt(source_file_name, &arena);

    Resolver resolver = {0};
    resolver_init(&resolver, &parser, class_path_entries, class_file_path,
                  &arena);

    resolver_load_standard_types(&resolver, cli_java_home, scratch_arena,
                                 &arena);
    LOG("After loading known types: arena_available=%lu",
        arena.end - arena.start);

    resolver_user_defined_function_signatures(&resolver, root_handle,
                                              scratch_arena, &arena);
    resolver_resolve_ast(&resolver, root_handle, scratch_arena, &arena);

    // Debug types.
    {
      LOG("------ After type checking%s", "");
      LOG("After type checking: arena_available=%lu", arena.end - arena.start);

      Arena tmp_arena = arena;
      resolver_ast_fprint(&resolver, root_handle, stderr, 0, 0, &tmp_arena);
    }

    if (parser.state != PARSER_STATE_OK)
      return 1;

    // Emit bytecode.
    Class_file class_file = {
        .class_file_path = class_file_path,
        .minor_version = 0,
        .major_version =
            17, // TODO: Add a CLI option to choose the jdk/jre version
        .access_flags = ACCESS_FLAGS_SUPER | ACCESS_FLAGS_PUBLIC,
    };
    jvm_init(&class_file, &arena);
    codegen_emit(&resolver, &class_file, root_handle, &arena);
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
    jvm_write(&class_file, file);
    fclose(file);

    LOG("After codegen: arena_available=%lu", arena.end - arena.start);

    {
      LOG("\n----------- Verifiying%s", "");

      Read_result read_res =
          ut_read_all_from_file_path(class_file_path_c_str, &scratch_arena);
      if (read_res.error) {
        fprintf(stderr, "Failed to read the file %.*s: %s\n",
                (int)class_file_path.len, (char *)class_file_path.data,
                strerror(read_res.error));
        return read_res.error;
      }

      Class_file class_file_verify = {.class_file_path =
                                          class_file.class_file_path};
      u8 *current = read_res.content.data;
      jvm_buf_read_class_file(read_res.content, &current, &class_file_verify,
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
