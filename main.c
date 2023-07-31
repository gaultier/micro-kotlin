#define _POSIX_C_SOURCE 200809L
#include "class_file.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static const char *usage = "./a.out [-h] (-c classpath) source.kt";

static void print_usage_and_exit() {
  puts(usage);
  exit(0);
}

int main(int argc, char *argv[]) {
  int opt = 0;
  char *classpath = NULL;

  while ((opt = getopt(argc, argv, "c:")) != -1) {
    switch (opt) {
    case 'c':
      classpath = optarg;
      break;
    case 'h':
      print_usage_and_exit();
      break;

    default:
      fprintf(stderr, "Unknown option: %c\n", opt);
      print_usage_and_exit();
    }
  }

  if (optind == argc) {
    fprintf(stderr, "Missing source file.\n");
    print_usage_and_exit();
  }
  if (optind != argc - 1) {
    fprintf(stderr, "Multiple source files not yet supported.\n");
    print_usage_and_exit();
  }
  if (classpath == NULL) {
    classpath = ".";
  }

  arena_t arena = {0};
  arena_init(&arena, 1L << 32);

  // Read class files (stdlib, etc).
  cf_class_file_t *class_files = NULL;
  pg_array_init_reserve(class_files, 1 << 18, &arena);

  string_t *class_path_entries = NULL;
  pg_array_init_reserve(class_path_entries, 16, &arena);
  pg_array_append(class_path_entries, string_make_from_c_no_alloc("."), &arena);

  {
    char *class_path_sep = NULL;
    while ((class_path_sep = strchr(classpath, ':')) != NULL) {
      const string_t class_path_entry = string_make_from_c(classpath, &arena);
      pg_array_append(class_path_entries, class_path_entry, &arena);

      classpath = class_path_sep + 1;
    }
    const string_t class_path_entry = string_make_from_c(classpath, &arena);
    pg_array_append(class_path_entries, class_path_entry, &arena);

    // FIXME: It should be the basename of the source file.
    cf_read_jmod_and_jar_and_class_files_recursively(".", 1, &class_files,
                                                     &arena);
  }
  {
    // TODO: when parsing multiple files, need to allocate that.
    const string_t source_file_name = {
        .value = argv[optind],
        .len = strlen(argv[optind]),
    };
    const int fd = open(source_file_name.value, O_RDONLY);
    if (fd == -1) {
      fprintf(stderr, "Failed to open the file %.*s: %s\n",
              source_file_name.len, source_file_name.value, strerror(errno));
      return errno;
    }

    struct stat st = {0};
    if (stat(source_file_name.value, &st) == -1) {
      fprintf(stderr, "Failed to get the file size %.*s: %s\n",
              source_file_name.len, source_file_name.value, strerror(errno));
      return errno;
    }
    if (st.st_size == 0) {
      return 0;
    }
    if (st.st_size > UINT16_MAX) {
      fprintf(stderr,
              "The file %.*s is too big (limit is %u, got: %ld), stopping.\n",
              source_file_name.len, source_file_name.value, UINT16_MAX,
              st.st_size);
      return E2BIG;
    }

    string_t source = {0};
    int res = ut_read_all_from_fd(fd, st.st_size, &source, &arena);
    if (res != -1) {
      fprintf(stderr, "Failed to read the full file %.*s: %s\n",
              source_file_name.len, source_file_name.value, strerror(res));
      return res;
    }
    close(fd);

    // Lex.
    const u64 estimated_capacity = pg_clamp(64, source.len / 8, UINT16_MAX);
    lex_lexer_t lexer = {
        .file_path = source_file_name,
    };
    pg_array_init_reserve(lexer.tokens, estimated_capacity, &arena);
    pg_array_init_reserve(lexer.line_table, estimated_capacity, &arena);

    const char *current = source.value;
    lex_lex(&lexer, source.value, source.len, &current, &arena);

    // Parse.
    par_parser_t parser = {
        .buf = source.value,
        .buf_len = source.len,
        .lexer = &lexer,
    };
    const u32 root_i = par_parse(&parser, &arena);

    if (parser.state != PARSER_STATE_OK)
      return 1; // TODO: Should type checking still proceed?

    resolver_t resolver = {.parser = &parser, .class_files = class_files};
    pg_array_init_reserve(resolver.variables, 512, &arena);
    pg_array_init_reserve(resolver.types, pg_array_len(parser.nodes) + 32,
                          &arena);
    pg_array_append(resolver.types, (ty_type_t){0}, &arena); // Default value.
    ty_find_known_types(&resolver, &arena);
    ty_resolve_node(&resolver, root_i, &arena);

    // Debug types.
    {
      LOG("------ After type checking%s", "");
      arena_t tmp_arena = arena;
      resolver_ast_fprint_node(&resolver, root_i, stderr, 0, &tmp_arena);
    }

    if (parser.state != PARSER_STATE_OK)
      return 1;

    lo_lower_types(&resolver, &arena);
    // Debug.
    {
      LOG("------ After lowering%s", "");
      arena_t tmp_arena = arena;
      resolver_ast_fprint_node(&resolver, root_i, stderr, 0, &tmp_arena);
    }

    // Emit bytecode.
    cf_class_file_t class_file = {
        .class_file_path = cf_make_class_file_name_kt(source_file_name, &arena),
        .minor_version = 0,
        .major_version = 17,
        .access_flags = ACCESS_FLAGS_SUPER | ACCESS_FLAGS_PUBLIC,
    };
    cf_init(&class_file, &arena);
    cg_emit(&resolver, &class_file, class_files, root_i, &arena);
    if (parser.state != PARSER_STATE_OK)
      return 1;

    FILE *file = fopen(class_file.class_file_path.value, "w");
    if (file == NULL) {
      fprintf(stderr, "Failed to open the file %.*s: %s\n",
              source_file_name.len, source_file_name.value, strerror(errno));
      return errno;
    }
    cf_write(&class_file, file);
    fclose(file);

    LOG("arena=%lu", arena.current_offset);
    {
      arena_t tmp_arena = arena;
      LOG("\n----------- Verifiying%s", "");

      int fd = open(class_file.class_file_path.value, O_RDONLY);
      if (fd == -1) {
        fprintf(stderr, "Failed to open the file %.*s: %s\n",
                source_file_name.len, source_file_name.value, strerror(errno));
        return errno;
      }

      struct stat st = {0};
      if (stat(class_file.class_file_path.value, &st) == -1) {
        fprintf(stderr, "Failed to get the file size %.*s: %s\n",
                source_file_name.len, source_file_name.value, strerror(errno));
        return errno;
      }
      pg_assert(st.st_size > 0);
      pg_assert(st.st_size <= UINT32_MAX);

      const u32 buf_len = st.st_size;
      char *const buf = arena_alloc(&tmp_arena, buf_len, sizeof(u8));

      pg_assert(read(fd, buf, buf_len) == buf_len);
      close(fd);

      cf_class_file_t class_file_verify = {.class_file_path =
                                               class_file.class_file_path};
      char *current = buf;
      cf_buf_read_class_file(buf, buf_len, &current, &class_file_verify,
                             READ_CLASS_FILE_FLAG_ALL, &tmp_arena);
    }
  }
}
