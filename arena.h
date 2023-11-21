#pragma once

#define _POSIX_C_SOURCE 200809L
#define _XOPEN_SOURCE 500L
#define _GNU_SOURCE
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

typedef uint64_t u64;
typedef int64_t i64;
typedef uint32_t u32;
typedef int32_t i32;
typedef uint16_t u16;
typedef int16_t i16;
typedef uint8_t u8;
typedef int8_t i8;
typedef size_t usize;
typedef ssize_t isize;

#if defined(__linux__) || defined(__FreeBSD__)
#include <elf.h>
#endif

// String builder, like a dynamic array.
typedef struct {
  u8 *data;
  u64 len;
  u64 cap;
} str_builder;

// String view, immutable.
typedef struct {
  u8 *data;
  u64 len;
} str;

static str str_from_c(char *s) {
  return (str){.data = (uint8_t *)s, .len = s == NULL ? 0 : strlen(s)};
}

#define str_from_c_literal(s)                                                  \
  ((str){.data = (uint8_t *)s, .len = sizeof(s) - 1})

// ------------------- Logs

static bool cli_log_verbose = false;
#define LOG(fmt, ...)                                                          \
  if (cli_log_verbose)                                                         \
  fprintf(stderr, fmt "\n", __VA_ARGS__)

// ----------- Utility macros

// Check that __COUNTER__ is defined and that __COUNTER__ increases by 1
// every time it is expanded. X + 1 == X + 0 is used in case X is defined to be
// empty. If X is empty the expression becomes (+1 == +0).
#if defined(__COUNTER__) && (__COUNTER__ + 1 == __COUNTER__ + 0)
#define PG_PRIVATE_UNIQUE_ID __COUNTER__
#else
#define PG_PRIVATE_UNIQUE_ID __LINE__
#endif

// Helpers for generating unique variable names
#define pg_private_name(n) pg_private_concat(n, PG_PRIVATE_UNIQUE_ID)
#define pg_private_concat(a, b) pg_private_concat2(a, b)
#define pg_private_concat2(a, b) a##b
#define pg_pad(n) uint8_t pg_private_name(_padding)[n]

#define pg_unused(x) (void)(x)

#define pg_assert(condition)                                                   \
  do {                                                                         \
    if (!(condition)) {                                                        \
      fflush(stdout);                                                          \
      fflush(stderr);                                                          \
      __builtin_trap();                                                        \
    }                                                                          \
  } while (0)

#define pg_max(a, b) (((a) > (b)) ? (a) : (b))
#define pg_clamp(min, x, max)                                                  \
  (((x) > (max)) ? (max) : ((x) < (min)) ? (min) : (x))

// --------------------------- Arena

extern char _start;

static u64 ut_get_pie_displacement() {
#ifdef __linux__
  FILE *file = fopen("/proc/self/exe", "r");
  if (file == NULL)
    return 0;

  u64 res = 0;
  Elf64_Ehdr header = {0};
  const u64 read = fread(&header, 1, sizeof(header), file);
  if (read != sizeof(header))
    goto end;

  if (memcmp(header.e_ident, ELFMAG, SELFMAG) == 0) {
    const Elf64_Addr entry_point = header.e_entry;
    res = (u64)(&_start - entry_point);
  }

end:
  fclose(file);
  return res;
#endif
  // TODO
  return 0;
}

typedef struct {
  u8 *start;
  u8 *end;
} arena_t;

static arena_t arena_new(u64 cap) {
  void *mem = mmap(NULL, cap, PROT_READ | PROT_WRITE,
                   MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  pg_assert(mem);

  arena_t arena = {
      .start = mem,
      .end = mem + cap,
  };
  return arena;
}

static u64 initial_rbp = 0;
static u64 pie_offset = 0;

// TODO: Maybe use varints to reduce the size.
static u8 ut_record_call_stack(u64 *dst, u64 cap) {
  uintptr_t *rbp = __builtin_frame_address(0);

  u64 len = 0;

  while (rbp != 0 && (u64)rbp != initial_rbp && *rbp != 0) {
    const uintptr_t rip = *(rbp + 1);
    rbp = (uintptr_t *)*rbp;

    if ((u64)rbp == initial_rbp)
      break;

    if (len >= cap)
      break;

    dst[len++] = (rip - pie_offset);
  }
  return len;
}

__attribute((malloc, alloc_size(2, 3), alloc_align(3))) static void *
arena_alloc(arena_t *a, size_t size, size_t align, size_t count) {
  pg_assert(a->start <= a->end);

  size_t available = a->end - a->start;
  size_t padding = -(size_t)a->start & (align - 1);
  // Ignore overflow for now.
  size_t offset = padding + size * count;
  if (available < offset) {
    fprintf(stderr,
            "Out of memory: available=%lu"
            "allocation_size=%lu\n",
            available, offset);
    abort();
  }

  void *res = a->start + padding;

  a->start += offset;

  return res;
}
