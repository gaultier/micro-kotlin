#pragma once

#define _POSIX_C_SOURCE 200809L
#define _XOPEN_SOURCE 500L
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define u64 uint64_t
#define i64 int64_t
#define u32 uint32_t
#define i32 int32_t
#define u16 uint16_t
#define i16 int16_t
#define u8 uint8_t
#define i8 int8_t

#ifdef __linux__

#ifndef MAP_ANONYMOUS
#define MAP_ANONYMOUS 0x20

#endif

#endif

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

// ------------------- Logs

static bool log_verbose = false;
#define LOG(fmt, ...)                                                          \
  if (log_verbose)                                                             \
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
  str data;
  u64 cap;
} arena_t;

typedef enum __attribute__((packed)) {
  ALLOCATION_TOMBSTONE = 1 << 0,
  ALLOCATION_OBJECT = 1 << 1,
  ALLOCATION_STRING = 1 << 2,
  ALLOCATION_ARRAY = 1 << 3,
  ALLOCATION_CONSTANT_POOL = 1 << 4,
  ALLOCATION_BLOB = 1 << 5,
} allocation_kind_t;

typedef struct {
  allocation_kind_t kind : 8;
  u64 user_allocation_size : 48;
  u8 call_stack_count : 8;
} allocation_metadata_t;

static arena_t arena_new(u64 cap) {
  arena_t arena = {
      .cap = cap,
      .data.data = mmap(NULL, cap, PROT_READ | PROT_WRITE,
                        MAP_ANONYMOUS | MAP_PRIVATE, -1, 0),
  };
  pg_assert(((u64)arena.data.data % 16) == 0);

  return arena;
}

static u64 ut_align_forward_16(u64 n) {
  const u64 modulo = n & (16 - 1);
  if (modulo != 0)
    n += 16 - modulo;

  pg_assert((n % 16) == 0);
  return n;
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

static bool mem_debug = false;
static void *arena_alloc(arena_t *arena, u64 len, u64 element_size,
                         allocation_kind_t kind) {
  // clang-format off
  //                           Metadata to be able to do heap dumps.
  //                           v
  //                           .....................
  // ....|--------------------|allocation_metadata_t|+++++|*************************|
  //     ^                    ^                     ^     ^                         ^
  //   base          old_offset                     ^     new_offset                cap
  //                                                ^
  //                                                res
  // clang-format on

  pg_assert(arena != NULL);
  pg_assert(arena->data.len < arena->cap);
  pg_assert(((u64)((arena->data.data + arena->data.len)) % 16) == 0);
  pg_assert(element_size > 0);

  u64 call_stack[256] = {0};
  const u8 call_stack_count =
      mem_debug ? ut_record_call_stack(call_stack, sizeof(call_stack) /
                                                       sizeof(call_stack[0]))
                : 0;

  const u64 user_allocation_size = len * element_size; // TODO: check overflow.
  pg_assert(user_allocation_size > 0);

  const u64 metadata_size =
      sizeof(allocation_metadata_t) + call_stack_count * sizeof(u64);
  const u64 total_allocation_size = metadata_size + user_allocation_size;

  if (arena->data.len + total_allocation_size > arena->cap) {
    fprintf(stderr,
            "Out of memory: cap=%lu current_offset=%lu "
            "user_allocation_size=%lu total_allocation_size=%lu\n",
            arena->cap, arena->data.len, user_allocation_size,
            total_allocation_size);

    pg_assert(0);
  }

  const u64 new_offset =
      ut_align_forward_16(arena->data.len + total_allocation_size);

  pg_assert((new_offset % 16) == 0);
  pg_assert(arena->data.len + user_allocation_size <= new_offset);

  u8 *const new_allocation = arena->data.data + arena->data.len;
  pg_assert((((u64)new_allocation) % 16) == 0);
  pg_assert((u64)(arena->data.data + arena->data.len) <= (u64)new_allocation);
  pg_assert((u64)(new_allocation) + user_allocation_size <=
            (u64)arena->data.data + new_offset);

  allocation_metadata_t *metadata = (allocation_metadata_t *)new_allocation;
  metadata->kind = kind;
  metadata->user_allocation_size = user_allocation_size;
  metadata->call_stack_count = call_stack_count;
  memcpy(metadata + 1, call_stack, sizeof(call_stack[0]) * call_stack_count);

  arena->data.len = new_offset;
  pg_assert((((u64)arena->data.len) % 16) == 0);

  return new_allocation + metadata_size;
}

static u32
arena_get_user_allocation_offset(arena_t arena,
                                 const allocation_metadata_t *metadata) {
  pg_assert(arena.data.data <= (u8 *)metadata &&
            (u8 *)metadata <= arena.data.data + arena.data.len);

  return (u8 *)metadata - arena.data.data + sizeof(allocation_metadata_t) +
         metadata->call_stack_count * sizeof(u64);
}

static str allocation_kind_to_string(allocation_kind_t kind) {
  const u8 real_kind = kind & (~ALLOCATION_TOMBSTONE);

  switch (real_kind) {
  case ALLOCATION_OBJECT:
    return str_from_c("ALLOCATION_OBJECT");
  case ALLOCATION_STRING:
    return str_from_c("ALLOCATION_STRING");
  case ALLOCATION_ARRAY:
    return str_from_c("ALLOCATION_ARRAY");
  case ALLOCATION_CONSTANT_POOL:
    return str_from_c("ALLOCATION_CONSTANT_POOL");
  case ALLOCATION_BLOB:
    return str_from_c("ALLOCATION_BLOB");
  default:
    pg_assert(0 && "unreachable");
  }
}
