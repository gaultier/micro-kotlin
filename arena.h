#pragma once

#define _POSIX_C_SOURCE 200809L
#define _XOPEN_SOURCE 500L
#define _GNU_SOURCE
#include <assert.h>
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

#define KiB 1024UL
#define MiB ((KiB) * 1024UL)

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
#define pg_pad(n) u8 pg_private_name(_padding)[n]

#define pg_unused(x) (void)(x)

#define pg_assert(condition)                                                   \
  do {                                                                         \
    if (!(condition)) {                                                        \
      fflush(stdout);                                                          \
      fflush(stderr);                                                          \
      fprintf(stderr, "Pre-condition failed, aborting.\n");                    \
      abort();                                                                 \
    }                                                                          \
  } while (0)

#define pg_max(a, b) (((a) > (b)) ? (a) : (b))

// --------------------------- Arena

typedef struct mem_profile mem_profile;
typedef struct {
  u8 *start;
  u8 *end;
  mem_profile *profile;
} arena_t;

static arena_t arena_new(u64 cap, mem_profile *profile) {
  u8 *mem = mmap(NULL, cap, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE,
                 -1, 0);
  pg_assert(mem);

  arena_t arena = {
      .profile = profile,
      .start = mem,
      .end = mem + cap,
  };
  return arena;
}

static void mem_profile_record_alloc(mem_profile *profile, u64 objects_count,
                                     u64 bytes_count);

__attribute((malloc, alloc_size(2, 3), alloc_align(3))) static void *
arena_alloc(arena_t *a, size_t size, size_t align, size_t count) {
  pg_assert(a->start <= a->end);
  pg_assert(align == 1 || align == 2 || align == 4 || align == 8);

  size_t available = a->end - a->start;
  size_t padding = -(size_t)a->start & (align - 1);

  // Ignore overflow for now.
  size_t offset = padding + size * count;
  if (available < offset) {
    fprintf(stderr,
            "Out of memory: available=%lu "
            "allocation_size=%lu\n",
            available, offset);
    abort();
  }

  u8 *res = a->start + padding;
  pg_assert(res + count * size <= a->end);

  a->start += offset;
  pg_assert(a->start <= a->end);

  if (a->profile) {
    mem_profile_record_alloc(a->profile, count, offset);
  }

  return (void *)res;
}
