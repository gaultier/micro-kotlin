#include "class_file.h"
#include <stdint.h>
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
    pg_assert(fd > 0);

    struct stat st = {0};
    pg_assert(stat(source_file_name.value, &st) == 0);
    pg_assert(st.st_size > 0);
    pg_assert(st.st_size <= UINT32_MAX);

    const u32 buf_len = st.st_size;
    char *const buf = arena_alloc(&arena, buf_len, sizeof(u8));

    pg_assert(read(fd, buf, buf_len) == buf_len);
    close(fd);

    const u64 estimated_capacity = pg_clamp(64, buf_len / 8, UINT16_MAX);
    lex_lexer_t lexer = {
        .file_path = source_file_name,
    };
    pg_array_init_reserve(lexer.tokens, estimated_capacity, &arena);
    pg_array_init_reserve(lexer.line_table, estimated_capacity, &arena);

    const char *current = buf;
    lex_lex(&lexer, buf, buf_len, &current);

    par_parser_t parser = {
        .buf = buf,
        .buf_len = buf_len,
        .lexer = &lexer,
    };
    const u32 root_i = par_parse(&parser, &arena);
    {
      const u64 arena_offset_before = arena.current_offset;
      par_ast_fprint_node(&parser, root_i, stderr, 0, &arena);
      arena.current_offset = arena_offset_before;
    }

    cf_class_file_t *class_files = NULL;
    pg_array_init_reserve(class_files, 32768, &arena);
    {
      LOG("'arena before reading class files'=%lu", arena.current_offset);
      char *const class_path = "/home/pg/scratch/java-module"; // FIXME
      cf_read_class_files(class_path, strlen(class_path), &class_files, &arena);
      LOG("class_files_len=%lu arena=%lu", pg_array_len(class_files),
          arena.current_offset);
    }
    ty_resolve_types(&parser, class_files, root_i, &arena);

    {
      const u64 arena_offset_before = arena.current_offset;
      par_ast_fprint_node(&parser, root_i, stderr, 0, &arena);
      arena.current_offset = arena_offset_before;
    }

    if (parser.state != PARSER_STATE_OK)
      return 1;

    cf_class_file_t class_file = {
        .file_path = cf_make_class_file_name_kt(source_file_name, &arena),
        .minor_version = cf_MINOR_VERSION,
        .major_version = cf_MAJOR_VERSION_6,
        .access_flags = CAF_ACC_SUPER | CAF_ACC_PUBLIC,
    };
    cf_init(&class_file, &arena);

    cg_generate(&parser, &class_file, class_files, root_i, &arena);

    FILE *file = fopen(class_file.file_path.value, "w");
    pg_assert(file != NULL);
    cf_write(&class_file, file);
    fclose(file);

    LOG("arena=%lu", arena.current_offset);
    {
      LOG("\n----------- Verifiying%s", "");

      int fd = open(class_file.file_path.value, O_RDONLY);
      pg_assert(fd > 0);

      struct stat st = {0};
      pg_assert(stat(class_file.file_path.value, &st) == 0);
      pg_assert(st.st_size > 0);
      pg_assert(st.st_size <= UINT32_MAX);

      const u32 buf_len = st.st_size;
      char *const buf = arena_alloc(&arena, buf_len, sizeof(u8));

      pg_assert(read(fd, buf, buf_len) == buf_len);
      close(fd);

      cf_class_file_t class_file = {0};
      char *current = buf;
      cf_buf_read_class_file(buf, buf_len, &current, &class_file, &arena);
    }
  }
}
