#include "class_file.h"
#include <sys/stat.h>

int main(int argc, char *argv[]) {
  pg_assert(argc == 2);

  arena_t arena = {0};
  arena_init(&arena, 1 << 29);

  {
    // TODO: when parsing multiple files, need to allocate that.
    const string_t source_file_name = {
        .value = argv[1],
        .len = strlen(argv[1]),
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

    // Read class files (stdlib, etc).
    cf_class_file_t *class_files = NULL;
    pg_array_init_reserve(class_files, 32768, &arena);
    {
      LOG("'arena before reading class files'=%lu", arena.current_offset);
      char *const class_path =
          "/home/pg/scratch/java-module/java.base/java"; // FIXME
      cf_read_class_files(class_path, strlen(class_path), &class_files, &arena);
      LOG("class_files_len=%lu arena=%lu", pg_array_len(class_files),
          arena.current_offset);
    }

    // Parse.
    par_parser_t parser = {
        .buf = source.value,
        .buf_len = source.len,
        .lexer = &lexer,
        .class_files = class_files,
    };
    const u32 root_i = par_parse(&parser, &arena);

    // Debug AST.
    {
      arena_t tmp_arena = arena;
      par_ast_fprint_node(&parser, root_i, stderr, 0, &tmp_arena);
    }
    if (parser.state != PARSER_STATE_OK)
      return 1; // TODO: Should type checking still proceed?

    resolver_t resolver = {
        .parser = &parser,
        .class = (u32)-1,
        .constant_pool_class_name_i = (u16)-1,
    };
    ty_resolve_types(&resolver, root_i, &arena);

    // Debug types.
    {
      arena_t tmp_arena = arena;
      par_ast_fprint_node(&parser, root_i, stderr, 0, &tmp_arena);
    }

    if (parser.state != PARSER_STATE_OK)
      return 1;

    // Emit bytecode.
    cf_class_file_t class_file = {
        .file_path = cf_make_class_file_name_kt(source_file_name, &arena),
        .minor_version = 0,
        .major_version = 17,
        .access_flags = CAF_ACC_SUPER | CAF_ACC_PUBLIC,
    };
    cf_init(&class_file, &arena);
    cg_emit(&parser, &class_file, class_files, root_i, &arena);
    if (parser.state != PARSER_STATE_OK)
      return 1;

    FILE *file = fopen(class_file.file_path.value, "w");
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

      int fd = open(class_file.file_path.value, O_RDONLY);
      if (fd == -1) {
        fprintf(stderr, "Failed to open the file %.*s: %s\n",
                source_file_name.len, source_file_name.value, strerror(errno));
        return errno;
      }

      struct stat st = {0};
      if (stat(class_file.file_path.value, &st) == -1) {
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

      cf_class_file_t class_file_verify = {.file_path = class_file.file_path};
      char *current = buf;
      cf_buf_read_class_file(buf, buf_len, &current, &class_file_verify,
                             READ_CLASS_FILE_FLAG_ALL, &tmp_arena);
    }
  }
}
