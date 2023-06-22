#include "class_file.h"
#include <assert.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static cf_constant_array_t constant_pool = {0};

int main(int argc, char *argv[]) {
  pg_assert(argc == 2);

  arena_t arena = {0};
  arena_init(&arena, 1 << 26);
  constant_pool = cf_constant_array_make(1024, &arena);

  int fd = open(argv[1], O_RDONLY);
  pg_assert(fd > 0);

  u8 buf[1 << 14] = {0};
  ssize_t read_bytes = read(fd, buf, sizeof(buf));
  u8 *current = buf;

  cf_buf_read_class_file(buf, read_bytes, &current, &constant_pool);
}
