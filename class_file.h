#pragma once

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#ifdef __linux

#ifndef MAP_ANONYMOUS
#define MAP_ANONYMOUS 0x20
#endif

#endif

#define u64 uint64_t
#define i64 int64_t
#define u32 uint32_t
#define i32 int32_t
#define u16 uint16_t
#define i16 int16_t
#define u8 uint8_t
#define i8 int8_t

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
    if (!(condition))                                                          \
      __builtin_trap();                                                        \
  } while (0)

#define pg_max(a, b) (((a) > (b)) ? (a) : (b))
#define pg_clamp(min, x, max)                                                  \
  (((x) > (max)) ? (max) : ((x) < (min)) ? (min) : (x))

// --------------------------- Arena
typedef struct {
  char *base;
  u64 current_offset;
  u64 cap;
} arena_t;

static void arena_init(arena_t *arena, u64 cap) {
  pg_assert(arena != NULL);

  arena->base = mmap(NULL, cap, PROT_READ | PROT_WRITE,
                     MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  pg_assert(arena->base != NULL);
  pg_assert(((u64)arena->base % 16) == 0);
  arena->cap = cap;
  arena->current_offset = 0;
}

static u64 ut_align_forward_16(u64 n) {
  const u64 modulo = n & (16 - 1);
  if (modulo != 0)
    n += 16 - modulo;

  pg_assert((n % 16) == 0);
  return n;
}

static void *arena_alloc(arena_t *arena, u64 len, u64 element_size) {
  // clang-format off
  // 
  // ....|--------------------|++++|
  //     ^                    ^    ^
  //   base          old_offset    new_offset
  //                          ^
  //                        res
  //                           ++++ == physical_size
  // clang-format on

  pg_assert(arena != NULL);
  pg_assert(arena->current_offset < arena->cap);
  pg_assert(arena->current_offset + len < arena->cap);
  pg_assert(((u64)((arena->base + arena->current_offset)) % 16) == 0);
  pg_assert(element_size > 0);
  const u64 physical_size = len * element_size; // TODO: check overflow.

  const u64 new_offset =
      ut_align_forward_16(arena->current_offset + physical_size);
  pg_assert((new_offset % 16) == 0);
  pg_assert(arena->current_offset + physical_size <= new_offset);
  pg_assert(new_offset < arena->current_offset + physical_size + 16);

  void *const res = arena->base + arena->current_offset;
  pg_assert((((u64)res) % 16) == 0);
  pg_assert((u64)(arena->base + arena->current_offset) <= (u64)res);
  pg_assert((u64)(res) + physical_size <= (u64)arena->base + new_offset);

  pg_assert(arena->current_offset < arena->cap);
  arena->current_offset = new_offset;
  pg_assert((((u64)arena->current_offset) % 16) == 0);
  return res;
}

// --------------------------- Array

typedef struct pg_array_header_t {
  u64 len;
  u64 cap;
} pg_array_header_t;

#define pg_array_t(Type) Type *
#define PG_ARRAY_HEADER(x) (((pg_array_header_t *)((void *)x)) - 1)
#define pg_array_len(x) (((x) == NULL) ? 0 : (PG_ARRAY_HEADER(x)->len))
#define pg_array_cap(x) (PG_ARRAY_HEADER(x)->cap)

#define pg_array_init_reserve(x, arg_capacity, arg_arena)                      \
  do {                                                                         \
    u64 capacity = pg_max((u64)(arg_capacity), 8);                             \
    pg_array_header_t *pg__ah = (pg_array_header_t *)arena_alloc(              \
        arg_arena, 1,                                                          \
        sizeof(pg_array_header_t) + sizeof(*(x)) * ((u64)(capacity)));         \
    pg__ah->len = 0;                                                           \
    pg__ah->cap = capacity;                                                    \
    x = (void *)(pg__ah + 1);                                                  \
    pg_assert((u64)x == (u64)pg__ah + 2 * sizeof(u64));                        \
    pg_assert(pg_array_cap(x) == capacity);                                    \
    pg_assert(pg_array_len(x) == 0);                                           \
  } while (0)

#define pg_array_last_index(x) (pg_array_len(x) - 1)
#define pg_array_last(x) (&(x)[pg_array_last_index(x)])
#define pg_array_drop_last(x)                                                  \
  do {                                                                         \
    pg_assert(x != NULL);                                                      \
    pg_assert(pg_array_len(x) > 0);                                            \
    PG_ARRAY_HEADER(x)->len -= 1;                                              \
  } while (0)

#define pg_array_clear(x) PG_ARRAY_HEADER(x)->len = 0

#define pg_array_append(x, item, arena)                                        \
  do {                                                                         \
    pg_assert(pg_array_len(x) <= pg_array_cap(x));                             \
    if (pg_array_len(x) == pg_array_cap(x)) {                                  \
      pg_assert(pg_array_cap(x) >= 8);                                         \
      const u64 new_cap = pg_array_cap(x) * 2;                                 \
      LOG("grow: old_cap=%lu new_cap=%lu len=%lu", pg_array_cap(x), new_cap,   \
          pg_array_len(x));                                                    \
      const u64 old_physical_len =                                             \
          sizeof(pg_array_header_t) + sizeof(*(x)) * pg_array_cap(x);          \
      const u64 new_physical_len =                                             \
          sizeof(pg_array_header_t) + sizeof(*(x)) * new_cap;                  \
      pg_array_header_t *const pg__ah =                                        \
          arena_alloc(arena, 1, new_physical_len);                             \
      LOG("grow: old_physical_len=%lu new_physical_len=%lu old_ptr=%p "        \
          "new_ptr=%p diff=%lu",                                               \
          old_physical_len, new_physical_len, PG_ARRAY_HEADER(x), pg__ah,      \
          (u64)pg__ah - (u64)PG_ARRAY_HEADER(x));                              \
      pg_assert((u64)pg__ah >= (u64)PG_ARRAY_HEADER(x) + old_physical_len);    \
      memcpy(pg__ah, PG_ARRAY_HEADER(x), old_physical_len);                    \
      x = (void *)(pg__ah + 1);                                                \
      PG_ARRAY_HEADER(x)->cap = new_cap;                                       \
    }                                                                          \
    (x)[PG_ARRAY_HEADER(x)->len++] = (item);                                   \
  } while (0)

#define pg_array_drop_last_n(x, n)                                             \
  do {                                                                         \
    for (u64 i = 0; i < n; i++)                                                \
      pg_array_drop_last(x);                                                   \
  } while (0)

// ------------------- Utils

static bool ut_cstring_ends_with(const char *s, u64 s_len, const char *suffix,
                                 u64 suffix_len) {
  pg_assert(s != NULL);
  pg_assert(s_len > 0);
  pg_assert(suffix != NULL);
  pg_assert(suffix_len > 0);

  if (s_len < suffix_len)
    return false;

  return memcmp(s + s_len - suffix_len, suffix, suffix_len) == 0;
}

static char *ut_memrchr(char *s, char c, u64 n) {
  pg_assert(s != NULL);
  pg_assert(n > 0);

  char *res = s + n - 1;
  while (res-- != s) {
    if (*res == c)
      return res;
  }
  return NULL;
}

static bool ut_char_is_alphabetic(u8 c) {
  return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
}

static bool mem_eq_c(const char *a, u32 a_len, char *b) {
  pg_assert(b != NULL);

  const u64 b_len = strlen(b);
  return a_len == b_len && memcmp(a, b, a_len) == 0;
}

// ------------------- String

typedef struct {
  u16 cap;
  u16 len;
  pg_pad(4);
  char *value;
} string_t;

static void string_append_char(string_t *s, char c, arena_t *arena);

static void string_ensure_null_terminated(string_t *s, arena_t *arena) {
  pg_assert(s != NULL);
  pg_assert(s->value != NULL);
  pg_assert(s->len < s->cap);

  if (s->value[s->len] != 0)
    string_append_char(s, 0, arena);
}

static string_t string_reserve(u16 cap, arena_t *arena) {
  pg_assert(arena != NULL);
  cap = pg_max(8, cap + 1);

  return (string_t){
      .cap = cap,
      .value = arena_alloc(arena, cap, sizeof(u8)),
  };
}

static string_t string_make_from_c(char *s, arena_t *arena) {
  pg_assert(s != NULL);
  pg_assert(arena != NULL);

  const u64 len = strlen(s);
  string_t res = string_reserve(len, arena);

  res.len = len;
  memcpy(res.value, s, len);

  pg_assert(res.value != NULL);
  pg_assert(res.len < res.cap);

  string_ensure_null_terminated(&res, arena);
  return res;
}

static string_t string_make_from_c_no_alloc(char *s) {
  pg_assert(s != NULL);

  string_t res = {
      .value = s,
      .len = strlen(s),
      .cap = strlen(s) + 1,
  };
  string_ensure_null_terminated(&res, NULL);

  return res;
}

static string_t string_make(string_t src, arena_t *arena) {
  pg_assert(src.value != NULL);
  string_t result = string_reserve(src.len, arena);
  memcpy(result.value, src.value, src.len);
  result.len = src.len;

  string_ensure_null_terminated(&result, arena);
  return result;
}

static string_t string_find_last_path_component(string_t path) {
  pg_assert(path.value != NULL);
  pg_assert(path.len > 0);

  char *const file = ut_memrchr(path.value, '/', path.len);
  if (file == NULL)
    return path;

  return (string_t){
      .value = file + 1,
      .len = path.value + path.len - (file + 1),
  };
}

static void string_capitalize_first(string_t *s) {
  pg_assert(s->value != NULL);
  pg_assert(s->len > 0);
  pg_assert(ut_char_is_alphabetic(s->value[0]));

  if ('a' <= s->value[0] && s->value[0] <= 'z')
    s->value[0] -= 32;
}

static void string_drop_before_last_incl(string_t *s, char c) {
  pg_assert(s != NULL);
  pg_assert(s->value != NULL);

  char *const last_c = ut_memrchr(s->value, c, s->len);
  if (last_c == NULL)
    return; // Nothing to do.

  char *const new_s_value = last_c + 1;
  s->len -= new_s_value - s->value;
  s->value = new_s_value;
}

static void string_drop_after_last_incl(string_t *s, char c) {
  pg_assert(s != NULL);
  pg_assert(s->value != NULL);

  const char *const last_c = ut_memrchr(s->value, c, s->len);
  if (last_c == NULL)
    return; // Nothing to do.

  s->len = last_c - s->value;
  s->value[s->len] = 0;
}

static bool string_eq(string_t a, string_t b) {
  pg_assert(a.value != NULL);
  pg_assert(b.value != NULL);

  return a.len == b.len && memcmp(a.value, b.value, a.len) == 0;
}

static bool string_eq_c(string_t a, char *b) {
  pg_assert(b != NULL);

  return mem_eq_c(a.value, a.len, b);
}

static void string_append_char(string_t *s, char c, arena_t *arena) {
  pg_assert(s != NULL);
  pg_assert(s->cap != 0);
  pg_assert(s->len <= s->cap);
  pg_assert(arena != NULL);

  if (s->len == s->cap - 1) {
    s->cap *= 2;
    char *const new_s = arena_alloc(arena, s->cap, sizeof(u8));
    s->value = memcpy(new_s, s->value, s->len);
  }

  s->value[s->len] = c;
  s->len += 1;
  s->value[s->len] = 0;

  pg_assert(s->value != NULL);
  pg_assert(s->len <= s->cap);

  string_ensure_null_terminated(s, arena);
}

static void string_append_char_if_not_exists(string_t *s, char c,
                                             arena_t *arena) {
  pg_assert(s != NULL);

  if (s->len > 0 && s->value[s->len - 1] != c) {
    pg_assert(arena != NULL);
    string_append_char(s, c, arena);
  }
}

static void string_append_string_n(string_t *a, string_t b, u64 n,
                                   arena_t *arena) {
  pg_assert(a != NULL);
  pg_assert(a->cap != 0);
  pg_assert(a->len <= a->cap);
  pg_assert(n <= b.len);

  for (u64 i = 0; i < n; i++)
    string_append_char(a, b.value[i], arena);

  pg_assert(a->value != NULL);
  pg_assert(a->len <= a->cap);
}

static void string_append_string(string_t *a, string_t b, arena_t *arena) {
  pg_assert(a != NULL);
  pg_assert(a->cap != 0);
  pg_assert(a->len <= a->cap);

  string_append_string_n(a, b, b.len, arena);

  pg_assert(a->value != NULL);
  pg_assert(a->len <= a->cap);
}

static void string_drop_last_n(string_t *a, u64 n) {
  pg_assert(a != NULL);

  while (a->len > 0 && n > 0) {
    a->value[a->len - 1] = 0;
    a->len -= 1;
    n -= 1;
  }

  pg_assert(a->value != NULL);
}

static void string_clear(string_t *a) {
  pg_assert(a != NULL);
  a->len = 0;
}

static void string_append_cstring(string_t *a, const char *b, arena_t *arena) {
  pg_assert(a != NULL);
  pg_assert(b != NULL);
  pg_assert(a->cap != 0);
  pg_assert(a->len <= a->cap);

  for (u64 i = 0; i < strlen(b); i++)
    string_append_char(a, b[i], arena);

  pg_assert(a->value != NULL);
  pg_assert(a->len <= a->cap);
}

static void string_drop_file_component(string_t *path, arena_t *arena) {
  pg_assert(path != NULL);
  pg_assert(path->value != NULL);
  pg_assert(path->len > 0);

  char *const file = ut_memrchr(path->value, '/', path->len);
  if (file == NULL) {
    string_clear(path);
    string_append_cstring(path, "./", arena);
    return;
  }

  const u64 file_len = path->value + path->len - file;
  string_drop_last_n(path, file_len);

  if (path->len > 0)
    pg_assert(path->value[path->len - 1] != '/');
}

// ------------------- Utils, continued

static int ut_read_all_from_fd(int fd, u64 announced_len, string_t *result,
                               arena_t *arena) {
  pg_assert(fd > 0);
  pg_assert(result != NULL);
  pg_assert(arena != NULL);

  if (announced_len > UINT16_MAX)
    return E2BIG;

  *result = string_reserve(announced_len, arena);
  while (result->len < announced_len) {
    pg_assert(result->len < result->cap);

    const i64 read_bytes = read(fd, result->value + result->len, result->cap);
    if (read_bytes == -1)
      return errno;
    if (read_bytes == 0)
      return EINVAL; // TODO: retry?

    pg_assert((i64)result->len + read_bytes <= UINT16_MAX);
    result->len += read_bytes;
  }
  return -1;
}

// ------------------- Logs

#ifdef PG_WITH_LOG
#define LOG(fmt, ...) fprintf(stderr, fmt "\n", __VA_ARGS__)
#else
#define LOG(fmt, ...)                                                          \
  do {                                                                         \
  } while (0)
#endif

// ------------------------ Class file code

typedef enum __attribute__((packed)) {
  BYTECODE_NOP = 0x00,
  BYTECODE_ALOAD_0 = 0x2a,
  BYTECODE_INVOKE_SPECIAL = 0xb7,
  BYTECODE_RETURN = 0xb1,
  BYTECODE_GET_STATIC = 0xb2,
  BYTECODE_BIPUSH = 0x10,
  BYTECODE_LDC = 0x12,
  BYTECODE_LDC_W = 0x13,
  BYTECODE_LDC2_W = 0x14,
  BYTECODE_ILOAD = 0x15,
  BYTECODE_LLOAD = 0x16,
  BYTECODE_ISTORE = 0x36,
  BYTECODE_LSTORE = 0x37,
  BYTECODE_POP = 0x57,
  BYTECODE_IADD = 0x60,
  BYTECODE_LADD = 0x61,
  BYTECODE_IMUL = 0x68,
  BYTECODE_LMUL = 0x69,
  BYTECODE_IDIV = 0x6c,
  BYTECODE_LDIV = 0x6d,
  BYTECODE_IREM = 0x70,
  BYTECODE_LREM = 0x71,
  BYTECODE_INEG = 0x74,
  BYTECODE_LNEG = 0x75,
  BYTECODE_IAND = 0x7e,
  BYTECODE_LAND = 0x7f,
  BYTECODE_IOR = 0x80,
  BYTECODE_LOR = 0x80,
  BYTECODE_IXOR = 0x82,
  BYTECODE_I2L = 0x85,
  BYTECODE_LCMP = 0x94,
  BYTECODE_IFEQ = 0x99,
  BYTECODE_IFNE = 0x9a,
  BYTECODE_IF_ICMPEQ = 0x9f,
  BYTECODE_IF_ICMPNE = 0xa0,
  BYTECODE_IF_ICMPLT = 0xa1,
  BYTECODE_IF_ICMPGE = 0xa2,
  BYTECODE_IF_ICMPGT = 0xa3,
  BYTECODE_IF_ICMPLE = 0xa4,
  BYTECODE_GOTO = 0xa7,
  BYTECODE_INVOKE_VIRTUAL = 0xb6,
  BYTECODE_IMPDEP1 = 0xfe,
  BYTECODE_IMPDEP2 = 0xff,
} cf_op_kind_t;

static char *const CF_INIT_CONSTRUCTOR_STRING = "<init>";

typedef struct {
  u32 scope_depth;
  u32 var_definition_node_i;
  string_t name;
} par_variable_t;

typedef enum __attribute__((packed)) {
  VERIFICATION_INFO_TOP = 0,
  VERIFICATION_INFO_INT = 1,
  VERIFICATION_INFO_FLOAT = 2,
  VERIFICATION_INFO_DOUBLE = 3,
  VERIFICATION_INFO_LONG = 4,
  VERIFICATION_INFO_NULL = 6,
  VERIFICATION_INFO_OBJECT = 7,
  VERIFICATION_INFO_UNINITIALIZED = 8,
} cf_verification_info_kind_t;

typedef struct {
  cf_verification_info_kind_t kind;
  pg_pad(1);
  u16 extra_data;
} cf_verification_info_t;

typedef struct {
  u32 node_i;
  u32 type_i;
  u32 scope_depth;
  cf_verification_info_t verification_info;
} cf_variable_t;

struct cg_frame_t;
typedef struct cg_frame_t cg_frame_t;
typedef struct {
  u16 pc;
  // TODO: Should we actually memoize this or not?
  u16 offset_delta;
  bool tombstone; // Skip in case of duplicates.
  u8 kind;
  pg_pad(2);
  // Immutable clone of the frame when the stack map
  // frame was created.
  cg_frame_t *frame;
} cf_stack_map_frame_t;

enum __attribute__((packed)) cf_type_kind_t {
  TYPE_ANY,
  TYPE_VOID,
  TYPE_BYTE,
  TYPE_CHAR,
  TYPE_DOUBLE,
  TYPE_FLOAT,
  TYPE_INT,
  TYPE_LONG,
  TYPE_INSTANCE_REFERENCE,
  TYPE_SHORT,
  TYPE_BOOL,
  TYPE_STRING,
  TYPE_ARRAY_REFERENCE,
  TYPE_METHOD,
  TYPE_CONSTRUCTOR,
  TYPE_CLASS_REFERENCE,
};
typedef enum cf_type_kind_t cf_type_kind_t;

struct cg_frame_t {
  cf_variable_t *locals;
  cf_verification_info_t *stack;
  u16 max_stack;
  u16 max_locals;
  u32 scope_depth;
  u16 locals_count;
  u16 stack_count;
  pg_pad(4);
};

struct par_type_t;

typedef struct {
  string_t descriptor;
  u32 return_type_i;
  u32 argument_types_i;
  u8 argument_count;
  pg_pad(7);
} par_type_method_t;

struct par_type_t {
  union {
    string_t class_name;      // TYPE_INSTANCE_REFERENCE
    par_type_method_t method; // TYPE_METHOD, TYPE_CONSTRUCTOR
    u32 array_type_i;         // TYPE_ARRAY_REFERENCE
  } v;
  cf_type_kind_t kind;
  pg_pad(1);
  u16 constant_pool_item_i;
  u32 class_file_i;
  u16 field_i;
  pg_pad(6);
};

typedef struct par_type_t ty_type_t;

typedef struct {
  u16 start_pc;
  u16 end_pc;
  u16 handler_pc;
  u16 catch_type;
} cf_exception_t;

static void stack_map_fill_same_frame(cf_stack_map_frame_t *stack_map_frame,
                                      u16 offset_delta) {

  pg_assert(stack_map_frame != NULL);

  pg_assert(offset_delta <= 63);
  pg_assert(offset_delta <= stack_map_frame->pc);

  stack_map_frame->kind = offset_delta;
  stack_map_frame->offset_delta = offset_delta;
}

static void stack_map_fill_full_frame(cf_stack_map_frame_t *stack_map_frame,
                                      u16 offset_delta) {

  pg_assert(stack_map_frame != NULL);

  stack_map_frame->kind = 255;
  stack_map_frame->offset_delta = offset_delta;
}

// static void stack_map_add_chop_frame(cf_stack_map_frame_t **stack_map_frames,
//                                      u8 chopped_locals_count,
//                                      u16 current_offset, u16 offset_delta,
//                                      arena_t *arena) {
//   pg_assert(stack_map_frames != NULL);
//   pg_assert(*stack_map_frames != NULL);
//
//   pg_assert(offset_delta > 0);
//   pg_assert(offset_delta <= current_offset);
//
//   const cf_stack_map_frame_t stack_map_frame = {
//       .kind = 251 - chopped_locals_count,
//       .offset_delta = offset_delta,
//       .pc = current_offset,
//   };
//   pg_assert(stack_map_frame.kind >= 248);
//   pg_assert(stack_map_frame.kind <= 250);
//   pg_array_append(*stack_map_frames, stack_map_frame, arena);
// }
//
// static void stack_map_add_append_frame(cf_stack_map_frame_t
// **stack_map_frames,
//                                        u8 added_locals_count,
//                                        cf_verification_info_t
//                                        verification_info, u16 current_offset,
//                                        u16 offset_delta, arena_t *arena) {
//   pg_assert(stack_map_frames != NULL);
//   pg_assert(*stack_map_frames != NULL);
//
//   pg_assert(offset_delta > 0);
//   pg_assert(offset_delta <= current_offset);
//
//   cf_stack_map_frame_t stack_map_frame = {
//       .kind = 251 + added_locals_count,
//       .offset_delta = offset_delta,
//       .pc = current_offset,
//   };
//   pg_array_init_reserve(stack_map_frame.locals, 1, arena);
//   pg_array_append(stack_map_frame.locals, verification_info, arena);
//
//   pg_assert(stack_map_frame.kind >= 252);
//   pg_assert(stack_map_frame.kind <= 254);
//   pg_array_append(*stack_map_frames, stack_map_frame, arena);
//
//   LOG("fact=stack_map_add_append_frame pc=%u", current_offset);
// }

static void stack_map_fill_same_locals_1_stack_item_frame(
    cf_stack_map_frame_t *stack_map_frame, u16 offset_delta) {
  pg_assert(stack_map_frame != NULL);

  pg_assert(offset_delta > 0);
  pg_assert(offset_delta <= stack_map_frame->pc);

  stack_map_frame->kind = offset_delta + 64;
  stack_map_frame->offset_delta = offset_delta;

  pg_assert(stack_map_frame->kind >= 64);
  pg_assert(stack_map_frame->kind <= 127);
}

static u16
cf_verification_info_kind_word_count(cf_verification_info_kind_t kind) {
  switch (kind) {
  case VERIFICATION_INFO_TOP:
  case VERIFICATION_INFO_INT:
  case VERIFICATION_INFO_FLOAT:
  case VERIFICATION_INFO_NULL:
  case VERIFICATION_INFO_OBJECT:
  case VERIFICATION_INFO_UNINITIALIZED:
    return 1;
  case VERIFICATION_INFO_DOUBLE:
  case VERIFICATION_INFO_LONG:
    return 2;
  }
  pg_assert(0 && "unreachable");
}

static void cg_frame_stack_push(cg_frame_t *frame,
                                cf_verification_info_t verification_info,
                                arena_t *arena) {
  pg_assert(frame != NULL);
  pg_assert(arena != NULL);

  const u64 word_count =
      cf_verification_info_kind_word_count(verification_info.kind);

  pg_assert(frame->stack_count + word_count < UINT16_MAX);

  if (verification_info.kind == VERIFICATION_INFO_LONG ||
      verification_info.kind == VERIFICATION_INFO_DOUBLE) {
    pg_array_append(frame->stack,
                    (cf_verification_info_t){.kind = VERIFICATION_INFO_TOP},
                    arena);
  }
  pg_array_append(frame->stack, verification_info, arena);

  frame->stack_count += word_count;
  frame->max_stack = pg_max(frame->max_stack, frame->stack_count);
}

static void cg_frame_stack_pop(cg_frame_t *frame) {
  pg_assert(frame != NULL);
  pg_assert(pg_array_len(frame->stack) >= 1);
  pg_assert(frame->stack_count >= 1);
  pg_assert(frame->max_stack >= 1);

  const u64 word_count =
      cf_verification_info_kind_word_count(pg_array_last(frame->stack)->kind);

  pg_assert(pg_array_len(frame->stack) >= word_count);

  pg_array_drop_last_n(frame->stack, word_count);

  frame->stack_count -= word_count;
}

// Probably should not behave like a FIFO and rather like an array.
static u16 cg_frame_locals_push(cg_frame_t *frame,
                                const cf_variable_t *variable, arena_t *arena) {
  pg_assert(frame != NULL);
  pg_assert(arena != NULL);

  const u64 word_count =
      cf_verification_info_kind_word_count(variable->verification_info.kind);
  pg_assert(frame->locals_count + word_count < UINT16_MAX);

  const u16 result_index = pg_array_len(frame->locals);

  if (variable->verification_info.kind == VERIFICATION_INFO_LONG ||
      variable->verification_info.kind == VERIFICATION_INFO_DOUBLE) {
    cf_variable_t top_variable = *variable;
    top_variable.verification_info =
        (cf_verification_info_t){.kind = VERIFICATION_INFO_TOP};

    pg_array_append(frame->locals, top_variable, arena);
  }
  pg_array_append(frame->locals, *variable, arena);

  frame->locals_count += word_count;
  frame->max_locals = pg_max(frame->max_locals, frame->locals_count);

  return result_index;
}

static cg_frame_t *cg_frame_clone(const cg_frame_t *src, arena_t *arena);

static void cf_code_array_push_u8(u8 **array, u8 x, arena_t *arena) {
  pg_array_append(*array, x, arena);
}

static void cf_code_array_push_u16(u8 **array, u16 x, arena_t *arena) {
  cf_code_array_push_u8(array, (u8)(x & 0xff00), arena);
  cf_code_array_push_u8(array, (u8)(x & 0x00ff), arena);
}

typedef enum __attribute__((packed)) {
  ACCESS_FLAGS_PUBLIC = 0x0001,
  ACCESS_FLAGS_STATIC = 0x0008,
  ACCESS_FLAGS_SUPER = 0x0020,
} cf_access_flags_t;

typedef struct {
  union {
    u64 number;        // CONSTANT_POOL_KIND_INT
    string_t s;        // CONSTANT_POOL_KIND_UTF8
    u16 string_utf8_i; // CONSTANT_POOL_KIND_STRING
    struct cf_constant_method_ref_t {
      u16 class;
      u16 name_and_type;
    } method_ref;   // CONSTANT_POOL_KIND_METHOD_REF
    u16 class_name; // CONSTANT_POOL_KIND_CLASS_INFO
    struct cf_constant_name_and_type_t {
      u16 name;
      u16 type_descriptor;
    } name_and_type; // CONSTANT_POOL_KIND_NAME_AND_TYPE
    struct cf_constant_field_ref_t {
      u16 name;
      u16 type_descriptor;
    } field_ref; // CONSTANT_POOL_KIND_FIELD_REF
  } v;
  enum __attribute__((packed)) cp_info_kind_t {
    CONSTANT_POOL_KIND_UTF8 = 1,
    CONSTANT_POOL_KIND_INT = 3,
    CONSTANT_POOL_KIND_FLOAT = 4,
    CONSTANT_POOL_KIND_LONG = 5,
    CONSTANT_POOL_KIND_DOUBLE = 6,
    CONSTANT_POOL_KIND_CLASS_INFO = 7,
    CONSTANT_POOL_KIND_STRING = 8,
    CONSTANT_POOL_KIND_FIELD_REF = 9,
    CONSTANT_POOL_KIND_METHOD_REF = 10,
    CONSTANT_POOL_KIND_INTERFACE_METHOD_REF = 11,
    CONSTANT_POOL_KIND_NAME_AND_TYPE = 12,
    CONSTANT_POOL_KIND_METHOD_HANDLE = 15,
    CONSTANT_POOL_KIND_METHOD_TYPE = 16,
    CONSTANT_POOL_KIND_DYNAMIC = 17,
    CONSTANT_POOL_KIND_INVOKE_DYNAMIC = 18,
    CONSTANT_POOL_KIND_MODULE = 19,
    CONSTANT_POOL_KIND_PACKAGE = 20,
  } kind;
  pg_pad(7);
} cf_constant_t;

typedef struct cf_constant_method_ref_t cf_constant_method_ref_t;

typedef struct cf_constant_name_and_type_t cf_constant_name_and_type_t;

typedef struct cf_constant_field_ref_t cf_constant_field_ref_t;

typedef enum cp_info_kind_t cp_info_kind_t;

typedef struct {
  u64 len;
  u64 cap;
  cf_constant_t *values;
} cf_constant_array_t;

static cf_constant_array_t cf_constant_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_constant_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(cf_constant_t)),
  };
}

static u16 cf_constant_array_push(cf_constant_array_t *array,
                                  const cf_constant_t *x, arena_t *arena) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(((u64)(array->values)) % 16 == 0);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_constant_t *const new_array =
        arena_alloc(arena, new_cap, sizeof(cf_constant_t));
    pg_assert(new_array != NULL);
    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_constant_t));
    pg_assert(array->values != NULL);
    pg_assert(((u64)(array->values)) % 16 == 0);
    array->cap = new_cap;
  }

  array->values[array->len] = *x;
  const u64 index = array->len + 1;
  pg_assert(index > 0);
  pg_assert(index <= array->len + 1);
  array->len += 1;
  return index;
}

static void cg_frame_init(cg_frame_t *frame, arena_t *arena) {
  pg_assert(frame != NULL);
  pg_assert(arena != NULL);

  pg_array_init_reserve(frame->locals, 32, arena);
  pg_array_init_reserve(frame->stack, 256, arena);
}

static cg_frame_t *cg_frame_clone(const cg_frame_t *src, arena_t *arena) {
  pg_assert(src != NULL);
  pg_assert(src->stack != NULL);
  pg_assert(pg_array_len(src->stack) <= UINT16_MAX);
  pg_assert(src->locals != NULL);
  pg_assert(arena != NULL);

  cg_frame_t *dst = arena_alloc(arena, 1, sizeof(cg_frame_t));
  cg_frame_init(dst, arena);

  dst->max_stack = src->max_stack;
  dst->max_locals = src->max_locals;
  dst->scope_depth = src->scope_depth;
  dst->stack_count = src->stack_count;
  dst->locals_count = src->locals_count;

  for (u64 i = 0; i < pg_array_len(src->locals); i++)
    pg_array_append(dst->locals, src->locals[i], arena);

  for (u64 i = 0; i < pg_array_len(src->stack); i++)
    pg_array_append(dst->stack, src->stack[i], arena);

  pg_assert(pg_array_len(dst->locals) == pg_array_len(src->locals));
  pg_assert(pg_array_len(dst->stack) == pg_array_len(src->stack));

  return dst;
}

static const cf_constant_t *
cf_constant_array_get(const cf_constant_array_t *constant_pool, u16 i) {
  pg_assert(constant_pool != NULL);
  pg_assert(i > 0);
  pg_assert(i <= constant_pool->len);
  pg_assert(constant_pool->values != NULL);
  pg_assert(((u64)(constant_pool->values)) % 16 == 0);

  return &constant_pool->values[i - 1];
}

static void cf_fill_type_descriptor_string(const ty_type_t *types, u32 type_i,
                                           string_t *type_descriptor,
                                           arena_t *arena) {
  pg_assert(types != NULL);
  pg_assert(type_i < pg_array_len(types));
  pg_assert(type_descriptor != NULL);

  const ty_type_t *const type = &types[type_i];

  switch (type->kind) {
  case TYPE_ANY:
    pg_assert(0 && "unreachable");
  case TYPE_VOID: {
    string_append_char(type_descriptor, 'V', arena);
    break;
  }
  case TYPE_BYTE: {
    string_append_char(type_descriptor, 'B', arena);
    break;
  }
  case TYPE_CHAR: {
    string_append_char(type_descriptor, 'C', arena);
    break;
  }
  case TYPE_DOUBLE: {
    string_append_char(type_descriptor, 'D', arena);
    break;
  }
  case TYPE_FLOAT: {
    string_append_char(type_descriptor, 'F', arena);
    break;
  }
  case TYPE_INT: {
    string_append_char(type_descriptor, 'I', arena);
    break;
  }
  case TYPE_LONG: {
    string_append_char(type_descriptor, 'J', arena);
    break;
  }
  case TYPE_STRING: {
    string_append_cstring(type_descriptor, "Ljava/lang/String;", arena);
    break;
  }
  case TYPE_INSTANCE_REFERENCE: {
    const string_t class_name = type->v.class_name;

    string_append_char(type_descriptor, 'L', arena);
    string_append_string(type_descriptor, class_name, arena);
    string_append_char(type_descriptor, ';', arena);

    break;
  }
  case TYPE_SHORT: {
    string_append_char(type_descriptor, 'S', arena);
    break;
  }
  case TYPE_BOOL: {
    string_append_char(type_descriptor, 'Z', arena);
    break;
  }
  case TYPE_ARRAY_REFERENCE: {
    string_append_char(type_descriptor, '[', arena);

    cf_fill_type_descriptor_string(types, type->v.array_type_i, type_descriptor,
                                   arena);

    break;
  }
  case TYPE_CONSTRUCTOR:
  case TYPE_METHOD: {
    const par_type_method_t *const method_type = &type->v.method;
    string_append_char(type_descriptor, '(', arena);

    for (u64 i = 0; i < method_type->argument_count; i++) {
      cf_fill_type_descriptor_string(types, method_type->argument_types_i,
                                     type_descriptor, arena);
    }

    string_append_char(type_descriptor, ')', arena);

    cf_fill_type_descriptor_string(types, method_type->return_type_i,
                                   type_descriptor, arena);

    break;
  }
  case TYPE_CLASS_REFERENCE: {
    const string_t class_name = type->v.class_name;
    string_append_string(type_descriptor, class_name, arena);
    break;
  }
  }
}

static void cf_parse_field_type_descriptor(string_t type_descriptor,
                                           ty_type_t *type, ty_type_t **types,
                                           arena_t *arena) {
  pg_assert(type != NULL);
  pg_assert(types != NULL);
  pg_assert(arena != NULL);

  if (type_descriptor.len == 0)
    return;

  switch (type_descriptor.value[0]) {
  case 'B':
    type->kind = TYPE_BYTE;
    return;
  case 'C':
    type->kind = TYPE_CHAR;
    return;
  case 'D':
    type->kind = TYPE_DOUBLE;
    return;
  case 'F':
    type->kind = TYPE_FLOAT;
    return;
  case 'I':
    type->kind = TYPE_INT;
    return;
  case 'J':
    type->kind = TYPE_LONG;
    return;
  case 'Z':
    type->kind = TYPE_BOOL;
    return;
  case 'L':
    type->kind = TYPE_INSTANCE_REFERENCE;
    string_t class_name = {
        .value = type_descriptor.value + 1, // Skip starting `L`.
        .len = type_descriptor.len - 1,
    };
    pg_assert(class_name.len >= 2);
    pg_assert(class_name.value[class_name.len - 1] = ';');
    // `Drop ending `;`.
    class_name.len -= 1;
    type->v.class_name = class_name;
    return;
  case '[':
    type->kind = TYPE_ARRAY_REFERENCE;
    ty_type_t item_type = {0};

    string_t type_descriptor_remaining = {
        .value = type_descriptor.value + 1,
        .len = type_descriptor.len - 1,
    };
    cf_parse_field_type_descriptor(type_descriptor_remaining, &item_type, types,
                                   arena);
    pg_array_append(*types, item_type, arena);
    type->v.array_type_i = pg_array_last_index(*types);
    return;
  default:
    pg_assert(0 && "unreachable");
  }
}

#if 0
static void cg_emit_invoke_special(u8 **code, u16 method_ref_i,
                                  cg_frame_t *frame,
                                  const par_type_method_t *method_type,
                                  arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(*code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(frame != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);
  pg_assert(arena != NULL);

  cf_code_array_push_u8(code, BYTECODE_INVOKE_SPECIAL, arena);
  cf_code_array_push_u16(code, method_ref_i, arena);

  for (u8 i = 0; i < 1 + method_type->argument_count; i++)
    cg_frame_stack_pop(frame);
}

static void cg_emit_call_superclass_constructor(
    u8 **code, u16 super_class_constructor_i, cg_frame_t *frame,
    const par_type_t *constructor_type, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(super_class_constructor_i > 0);
  pg_assert(frame != NULL);
  pg_assert(constructor_type != NULL);
  pg_assert(constructor_type->kind == TYPE_CONSTRUCTOR);

  cf_code_array_push_u8(code, BYTECODE_ALOAD_0,
                        arena); // TODO: move the responsability to the caller?

  const par_type_method_t *const method_type = &constructor_type->v.method;
  pg_assert(method_type != NULL);
  cg_emit_invoke_special(code, super_class_constructor_i, frame, method_type,
                        arena);
}

static void cg_emit_i2l(u8 **code, cg_frame_t *frame, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(frame != NULL);
  pg_assert(arena != NULL);

  cf_code_array_push_u8(code, BYTECODE_I2L, arena);

  cg_frame_stack_pop(frame);

  cg_frame_stack_push(
      frame, (cf_verification_info_t){.kind = VERIFICATION_INFO_TOP}, arena);
  cg_frame_stack_push(
      frame, (cf_verification_info_t){.kind = VERIFICATION_INFO_LONG}, arena);
}
#endif

typedef struct cf_attribute_t cf_attribute_t;

typedef struct {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  pg_pad(2);
  cf_attribute_t *attributes;
} cf_field_t;

typedef struct cf_method_t cf_method_t;

typedef struct cf_interfaces_t cf_interfaces_t;

typedef struct {
  u16 start_pc;
  u16 line_number;
} cf_line_number_table_entry_t;

struct cf_attribute_t {
  union {
    struct cf_attribute_code_t {
      u16 max_stack;
      u16 max_locals;
      pg_pad(4);
      u8 *code;
      cf_exception_t *exceptions;
      cf_attribute_t *attributes;
    } code; // ATTRIBUTE_KIND_CODE

    struct cf_attribute_source_file_t {
      u16 source_file;
    } source_file; // ATTRIBUTE_KIND_SOURCE_FILE

    cf_line_number_table_entry_t
        *line_number_table_entries; // ATTRIBUTE_KIND_LINE_NUMBER_TABLE

    cf_stack_map_frame_t *stack_map_table; // ATTRIBUTE_KIND_STACK_MAP_TABLE
  } v;
  u16 name;
  enum __attribute__((packed)) cf_attribute_kind_t {
    ATTRIBUTE_KIND_SOURCE_FILE,
    ATTRIBUTE_KIND_CODE,
    ATTRIBUTE_KIND_LINE_NUMBER_TABLE,
    ATTRIBUTE_KIND_STACK_MAP_TABLE,
  } kind;
  pg_pad(5);
};

typedef struct cf_attribute_line_number_table_t
    cf_attribute_line_number_table_t;

typedef struct cf_attribute_code_t cf_attribute_code_t;

typedef struct cf_attribute_source_file_t cf_attribute_source_file_t;

struct cf_method_t {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  pg_pad(2);
  cf_attribute_t *attributes;
};

const u32 cf_MAGIC_NUMBER = 0xbebafeca;
const u16 cf_MAJOR_VERSION_6 = 50;
const u16 cf_MAJOR_VERSION_7 = 51;
const u16 cf_MINOR_VERSION = 0;

struct cf_class_file_t {
  string_t file_path;
  u16 minor_version;
  u16 major_version;
  u16 access_flags;
  u16 this_class;
  u16 super_class;
  u16 interfaces_count;
  u16 fields_count;
  pg_pad(2);
  u16 *interfaces;
  cf_field_t *fields;
  cf_method_t *methods;
  cf_attribute_t *attributes;
  cf_constant_array_t constant_pool;
};
typedef struct cf_class_file_t cf_class_file_t;

static void file_write_u8(FILE *file, u8 x) {
  pg_assert(file != NULL);
  fwrite(&x, sizeof(x), 1, file);
}
static void file_write_be_u16(FILE *file, u16 x) {
  pg_assert(file != NULL);

  const u8 x_be[2] = {
      (x & 0xff00) >> 8,
      (x & 0x00ff) >> 0,
  };
  fwrite(x_be, sizeof(x_be), 1, file);
}

static void file_write_be_u32(FILE *file, u32 x) {
  pg_assert(file != NULL);

  const u8 x_be[4] = {
      (x & 0xff000000) >> 24,
      (x & 0x00ff0000) >> 16,
      (x & 0x0000ff00) >> 8,
      (x & 0x000000ff) >> 0,
  };
  fwrite(x_be, sizeof(x_be), 1, file);
}

static void file_write_be_u64(FILE *file, u64 x) {
  pg_assert(file != NULL);

  const u8 x_be[8] = {
      (x & 0xfff0000000000000) >> 56, (x & 0x00ff000000000000) >> 48,
      (x & 0x0000ff0000000000) >> 40, (x & 0x000000ff00000000) >> 32,
      (x & 0x00000000ff000000) >> 24, (x & 0x0000000000ff0000) >> 16,
      (x & 0x000000000000ff00) >> 8,  (x & 0x00000000000000ff) >> 0,
  };
  fwrite(x_be, sizeof(x_be), 1, file);
}

static u16 buf_read_be_u16(char *buf, u64 size, char **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 2 <= buf + size);

  const char *const ptr = *current;
  const u16 x = (((u16)(ptr[0] & 0xff)) << 8) | ((u16)((ptr[1] & 0xff)) << 0);
  *current += 2;
  return x;
}

static u32 buf_read_be_u32(char *buf, u64 size, char **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 4 <= buf + size);

  const char *const ptr = *current;
  const u32 x = ((u32)(ptr[0] & 0xff) << 24) | (((u32)(ptr[1] & 0xff)) << 16) |
                (((u32)(ptr[2] & 0xff)) << 8) | (((u32)(ptr[3] & 0xff)) << 0);
  *current += 4;
  return x;
}

static void buf_read_n_u8(char *buf, u64 size, u8 *dst, u64 dst_len,
                          char **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + dst_len <= buf + size);

  if (dst != NULL)
    memcpy(dst, *current, dst_len);

  *current += dst_len;
}

static u8 buf_read_u8(char *buf, u64 size, char **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 1 <= buf + size);

  const u8 x = (*current)[0];
  *current += 1;
  return x;
}

static string_t
cf_constant_array_get_as_string(const cf_constant_array_t *constant_pool,
                                u16 i) {
  const cf_constant_t *const constant = cf_constant_array_get(constant_pool, i);
  pg_assert(constant->kind == CONSTANT_POOL_KIND_UTF8);
  return constant->v.s;
}

static const u8 READ_CLASS_FILE_FLAG_ALL_CONSTANTS = 0x1;
static const u8 READ_CLASS_FILE_FLAG_ALL_ATTRIBUTES = 0x2;
static const u8 READ_CLASS_FILE_FLAG_ALL = 0xff;

static void cf_buf_read_attributes(char *buf, u64 buf_len, char **current,
                                   cf_class_file_t *class_file,
                                   cf_attribute_t **attributes, u8 flags,
                                   arena_t *arena);

static void cf_buf_read_sourcefile_attribute(char *buf, u64 buf_len,
                                             char **current,
                                             cf_class_file_t *class_file,
                                             cf_attribute_t **attributes,
                                             arena_t *arena) {

  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(*attributes != NULL);

  const char *const current_start = *current;

  cf_attribute_source_file_t source_file = {0};
  source_file.source_file = buf_read_be_u16(buf, buf_len, current);
  pg_assert(source_file.source_file > 0);
  pg_assert(source_file.source_file <= class_file->constant_pool.len);

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == 2);

  cf_attribute_t attribute = {.kind = ATTRIBUTE_KIND_SOURCE_FILE,
                              .v = {.source_file = source_file}};
  pg_array_append(*attributes, attribute, arena);
}

static void cf_buf_read_code_attribute_exceptions(char *buf, u64 buf_len,
                                                  char **current,
                                                  cf_class_file_t *class_file,
                                                  cf_exception_t **exceptions,
                                                  arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(exceptions != NULL);

  const char *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  pg_array_init_reserve(*exceptions, table_len, arena);

  for (u16 i = 0; i < table_len; i++) {
    cf_exception_t exception = {0};

    exception.start_pc = buf_read_be_u16(buf, buf_len, current);
    exception.end_pc = buf_read_be_u16(buf, buf_len, current);
    exception.handler_pc = buf_read_be_u16(buf, buf_len, current);
    exception.catch_type = buf_read_be_u16(buf, buf_len, current);

    pg_array_append(*exceptions, exception, arena);
  }

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == sizeof(u16) + table_len * sizeof(u16) * 4);
}

static void cf_buf_read_code_attribute(char *buf, u64 buf_len, char **current,
                                       cf_class_file_t *class_file,
                                       u32 attribute_len, u16 name_i,
                                       cf_attribute_t **attributes,
                                       arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const char *const current_start = *current;

  cf_attribute_code_t code = {0};
  code.max_stack = buf_read_be_u16(buf, buf_len, current);
  code.max_locals = buf_read_be_u16(buf, buf_len, current);
  const u32 code_len = buf_read_be_u32(buf, buf_len, current);
  pg_assert(*current + code_len <= buf + buf_len);
  pg_assert(code_len <= UINT16_MAX); // Actual limit per spec.

  pg_array_init_reserve(code.code, code_len, arena);
  buf_read_n_u8(buf, buf_len, code.code, code_len, current);
  PG_ARRAY_HEADER(code.code)->len = code_len;

  cf_buf_read_code_attribute_exceptions(buf, buf_len, current, class_file,
                                        &code.exceptions, arena);

  cf_buf_read_attributes(buf, buf_len, current, class_file, &code.attributes, 0,
                         arena);

  cf_attribute_t attribute = {
      .kind = ATTRIBUTE_KIND_CODE, .name = name_i, .v = {.code = code}};
  pg_array_append(*attributes, attribute, arena);

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

static void cf_buf_read_stack_map_table_attribute_verification_infos(
    char *buf, u64 buf_len, char **current, u16 count) {
  pg_assert(buf != NULL);
  pg_assert(current != NULL);

  for (u16 i = 0; i < count; i++) {
    const u8 kind = buf_read_u8(buf, buf_len, current);

    if (kind < 7)
      continue;

    if (kind > 8)
      pg_assert(0 && "invalid");

    buf_read_be_u16(buf, buf_len, current);
  }
}

static void cf_buf_read_stack_map_table_attribute(char *buf, u64 buf_len,
                                                  char **current,
                                                  u32 attribute_len, u16 name_i,
                                                  cf_attribute_t **attributes,
                                                  arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(current != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const char *const current_start = *current;

  const u16 len = buf_read_be_u16(buf, buf_len, current);
  cf_stack_map_frame_t *stack_map_frames = NULL;
  pg_array_init_reserve(stack_map_frames, len, arena);

  for (u16 i = 0; i < len; i++) {
    cf_stack_map_frame_t stack_map_frame = {
        .kind = buf_read_u8(buf, buf_len, current),
    };

    if (stack_map_frame.kind <= 63) // same_frame
    {
      stack_map_frame.offset_delta = stack_map_frame.kind;
    } else if (64 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 127) { // same_locals_1_stack_item_frame
      stack_map_frame.offset_delta = stack_map_frame.kind - 64;
      cf_buf_read_stack_map_table_attribute_verification_infos(buf, buf_len,
                                                               current, 1);

    } else if (128 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 246) { // reserved
      pg_assert(0 && "unreachable");
    } else if (247 <= stack_map_frame.kind &&
               stack_map_frame.kind <=
                   247) { // same_locals_1_stack_item_frame_extended
      stack_map_frame.offset_delta = buf_read_be_u16(buf, buf_len, current);
      cf_buf_read_stack_map_table_attribute_verification_infos(buf, buf_len,
                                                               current, 1);

    } else if (248 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 250) { // chop_frame
      stack_map_frame.offset_delta = buf_read_be_u16(buf, buf_len, current);

    } else if (251 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 251) { // same_frame_extended
      stack_map_frame.offset_delta = buf_read_be_u16(buf, buf_len, current);

    } else if (252 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 254) { // append_frame
      stack_map_frame.offset_delta = buf_read_be_u16(buf, buf_len, current);
      const u16 verification_info_count = stack_map_frame.kind - 251;
      cf_buf_read_stack_map_table_attribute_verification_infos(
          buf, buf_len, current, verification_info_count);

    } else { // full_frame_attribute
      stack_map_frame.offset_delta = buf_read_be_u16(buf, buf_len, current);
      const u16 locals_count = buf_read_be_u16(buf, buf_len, current);
      cf_buf_read_stack_map_table_attribute_verification_infos(
          buf, buf_len, current, locals_count);
      const u16 stack_items_count = buf_read_be_u16(buf, buf_len, current);
      cf_buf_read_stack_map_table_attribute_verification_infos(
          buf, buf_len, current, stack_items_count);
    }
    pg_array_append(stack_map_frames, stack_map_frame, arena);
  }

  cf_attribute_t attribute = {
      .kind = ATTRIBUTE_KIND_STACK_MAP_TABLE,
      .name = name_i,
      .v = {.stack_map_table = stack_map_frames},
  };
  pg_array_append(*attributes, attribute, arena);

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

static void cf_buf_read_line_number_table_attribute(char *buf, u64 buf_len,
                                                    char **current,
                                                    cf_class_file_t *class_file,
                                                    u32 attribute_len,
                                                    arena_t *arena) {
  pg_unused(arena);
  pg_unused(class_file);

  const char *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  pg_assert(sizeof(table_len) + table_len * (sizeof(u16) + sizeof(u16)) ==
            attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 start_pc = buf_read_be_u16(buf, buf_len, current);
    pg_unused(start_pc);
    const u16 line_number = buf_read_be_u16(buf, buf_len, current);
    pg_unused(line_number);

    // TODO store.
  }

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

static void cf_buf_read_local_variable_table_attribute(
    char *buf, u64 buf_len, char **current, cf_class_file_t *class_file,
    u32 attribute_len, arena_t *arena) {
  pg_unused(arena);
  const char *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  const u16 entry_size = sizeof(u16) * 5;
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 start_pc = buf_read_be_u16(buf, buf_len, current);
    pg_unused(start_pc);
    const u16 len = buf_read_be_u16(buf, buf_len, current);
    pg_unused(len);
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= class_file->constant_pool.len);

    const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    pg_unused(descriptor_i);
    const u16 idx = buf_read_be_u16(buf, buf_len, current);
    pg_unused(idx);

    // TODO store.
  }
  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

static void cf_buf_read_local_variable_type_table_attribute(
    char *buf, u64 buf_len, char **current, cf_class_file_t *class_file,
    u32 attribute_len, arena_t *arena) {
  pg_unused(arena);
  const char *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  const u16 entry_size = sizeof(u16) * 5;
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 start_pc = buf_read_be_u16(buf, buf_len, current);
    pg_unused(start_pc);
    const u16 len = buf_read_be_u16(buf, buf_len, current);
    pg_unused(len);
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= class_file->constant_pool.len);

    const u16 signature_i = buf_read_be_u16(buf, buf_len, current);
    pg_unused(signature_i);
    const u16 idx = buf_read_be_u16(buf, buf_len, current);
    pg_unused(idx);

    // TODO store.
  }
  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

static void cf_buf_read_signature_attribute(char *buf, u64 buf_len,
                                            char **current,
                                            cf_class_file_t *class_file,
                                            u32 attribute_len, arena_t *arena) {
  pg_unused(arena);
  pg_unused(class_file);

  const char *const current_start = *current;

  pg_assert(attribute_len == 2);
  const u16 signature_i = buf_read_be_u16(buf, buf_len, current);
  pg_unused(signature_i);
  // TODO store.

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

// TODO: store this data.
static void
cf_buf_read_exceptions_attribute(char *buf, u64 buf_len, char **current,
                                 cf_class_file_t *class_file, u32 attribute_len,
                                 cf_attribute_t **attributes, arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const char *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  const u16 entry_size = sizeof(u16);
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 exception_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(exception_i > 0);
    pg_assert(exception_i <= class_file->constant_pool.len);
  }
  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

static void cf_buf_read_inner_classes_attribute(char *buf, u64 buf_len,
                                                char **current,
                                                cf_class_file_t *class_file,
                                                u32 attribute_len,
                                                arena_t *arena) {
  pg_unused(arena);
  const char *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  const u16 entry_size = sizeof(u16) * 4;
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 inner_class_info_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(inner_class_info_i > 0);
    pg_assert(inner_class_info_i <= class_file->constant_pool.len);

    const u16 outer_class_info_i = buf_read_be_u16(buf, buf_len, current);
    // Could be 0.
    pg_assert(outer_class_info_i <= class_file->constant_pool.len);

    const u16 inner_name_i = buf_read_be_u16(buf, buf_len, current);
    // Could be 0.
    pg_assert(inner_name_i <= class_file->constant_pool.len);

    const u16 inner_class_access_flags = buf_read_be_u16(buf, buf_len, current);
    pg_unused(inner_class_access_flags);

    // TODO store.
  }
  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

static void cf_buf_read_attribute(char *buf, u64 buf_len, char **current,
                                  cf_class_file_t *class_file,
                                  cf_attribute_t **attributes, u8 flags,
                                  arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u16 name_i = buf_read_be_u16(buf, buf_len, current);
  pg_assert(name_i > 0);
  const u32 size = buf_read_be_u32(buf, buf_len, current);
  pg_assert(*current + size <= buf + buf_len);

  if ((flags & READ_CLASS_FILE_FLAG_ALL_ATTRIBUTES) == 0) {
    buf_read_n_u8(buf, buf_len, NULL, size, current);
    return;
  }

  pg_assert(name_i <= class_file->constant_pool.len);
  const string_t attribute_name =
      cf_constant_array_get_as_string(&class_file->constant_pool, name_i);

  if (string_eq_c(attribute_name, "SourceFile")) {
    pg_assert(2 == size);
    cf_buf_read_sourcefile_attribute(buf, buf_len, current, class_file,
                                     attributes, arena);
  } else if (string_eq_c(attribute_name, "Code")) {
    cf_buf_read_code_attribute(buf, buf_len, current, class_file, size, name_i,
                               attributes, arena);
  } else if (string_eq_c(attribute_name, "StackMapTable")) {
    cf_buf_read_stack_map_table_attribute(buf, buf_len, current, size, name_i,
                                          attributes, arena);
  } else if (string_eq_c(attribute_name, "Exceptions")) {
    cf_buf_read_exceptions_attribute(buf, buf_len, current, class_file, size,
                                     attributes, arena);
  } else if (string_eq_c(attribute_name, "InnerClasses")) {
    cf_buf_read_inner_classes_attribute(buf, buf_len, current, class_file, size,
                                        arena);
  } else if (string_eq_c(attribute_name, "EnclosingMethod")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "Synthetic")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "Signature")) {
    cf_buf_read_signature_attribute(buf, buf_len, current, class_file, size,
                                    arena);
  } else if (string_eq_c(attribute_name, "SourceDebugExtension")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "LineNumberTable")) {
    cf_buf_read_line_number_table_attribute(buf, buf_len, current, class_file,
                                            size, arena);
  } else if (string_eq_c(attribute_name, "LocalVariableTable")) {
    cf_buf_read_local_variable_table_attribute(buf, buf_len, current,
                                               class_file, size, arena);
  } else if (string_eq_c(attribute_name, "LocalVariableTypeTable")) {
    cf_buf_read_local_variable_type_table_attribute(buf, buf_len, current,
                                                    class_file, size, arena);
  } else if (string_eq_c(attribute_name, "Deprecated")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "RuntimeVisibleAnnotations")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "RuntimeInvisibleAnnotations")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name,
                         "RuntimeVisibleParameterAnnotations")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name,
                         "RuntimeInvisibleParameterAnnotations")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "RuntimeInvisibleAnnotations")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "AnnotationsDefault")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "BootstrapMethods")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "NestMembers")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "NestHost")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "ConstantValue")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "Module")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "ModulePackages")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "ModuleMainClass")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "Record")) {
    *current += size; // TODO
  } else if (string_eq_c(attribute_name, "PermittedSubclasses")) {
    *current += size; // TODO
  } else {
    *current += size; // TODO
  }
}

static void cf_buf_read_attributes(char *buf, u64 buf_len, char **current,
                                   cf_class_file_t *class_file,
                                   cf_attribute_t **attributes, u8 flags,
                                   arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u16 attribute_count = buf_read_be_u16(buf, buf_len, current);
  pg_array_init_reserve(*attributes, attribute_count, arena);

  for (u64 i = 0; i < attribute_count; i++) {
    cf_buf_read_attribute(buf, buf_len, current, class_file, attributes, flags,
                          arena);
  }
}

// Returns the number of incoming slots to skip:
// - `1` in the case of CONSTANT_POOL_KIND_LONG or CONSTANT_POOL_KIND_DOUBLE
// - `0` otherwise
static u8 cf_buf_read_constant(char *buf, u64 buf_len, char **current,
                               cf_class_file_t *class_file,
                               u16 constant_pool_count, arena_t *arena) {
  u8 kind = buf_read_u8(buf, buf_len, current);

  if (!(kind == CONSTANT_POOL_KIND_UTF8 || kind == CONSTANT_POOL_KIND_INT ||
        kind == CONSTANT_POOL_KIND_FLOAT || kind == CONSTANT_POOL_KIND_LONG ||
        kind == CONSTANT_POOL_KIND_DOUBLE ||
        kind == CONSTANT_POOL_KIND_CLASS_INFO ||
        kind == CONSTANT_POOL_KIND_STRING ||
        kind == CONSTANT_POOL_KIND_FIELD_REF ||
        kind == CONSTANT_POOL_KIND_METHOD_REF ||
        kind == CONSTANT_POOL_KIND_INTERFACE_METHOD_REF ||
        kind == CONSTANT_POOL_KIND_NAME_AND_TYPE ||
        kind == CONSTANT_POOL_KIND_METHOD_HANDLE ||
        kind == CONSTANT_POOL_KIND_METHOD_TYPE ||
        kind == CONSTANT_POOL_KIND_DYNAMIC ||
        kind == CONSTANT_POOL_KIND_INVOKE_DYNAMIC ||
        kind == CONSTANT_POOL_KIND_MODULE ||
        kind == CONSTANT_POOL_KIND_PACKAGE)) {
    fprintf(stderr, "Unknown constant kind found: offset=%lu kind=%u\n",
            *current - buf - 1, kind);
    pg_assert(0);
  }

  switch (kind) {
  case CONSTANT_POOL_KIND_UTF8: { // FIXME: It's actually modified utf8!
    u16 len = buf_read_be_u16(buf, buf_len, current);

    char *const s = *current;
    buf_read_n_u8(buf, buf_len, NULL, len, current);

    cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                              .v = {.s = {.len = len, .value = s}}};
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);

    break;
  }
  case CONSTANT_POOL_KIND_INT: {
    const u32 value = buf_read_be_u32(buf, buf_len, current);
    pg_unused(value);

    const cf_constant_t constant = {.kind = kind, .v = {.number = 0}}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_FLOAT: {
    const u32 value = buf_read_be_u32(buf, buf_len, current);
    pg_unused(value);

    const cf_constant_t constant = {.kind = kind, .v = {.number = 0}}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_DOUBLE:
  case CONSTANT_POOL_KIND_LONG: {
    const u32 high = buf_read_be_u32(buf, buf_len, current);
    pg_unused(high);
    const u32 low = buf_read_be_u32(buf, buf_len, current);
    pg_unused(low);

    const cf_constant_t constant = {.kind = kind, .v = {.number = 0}}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    const cf_constant_t dummy = {0};
    cf_constant_array_push(&class_file->constant_pool, &dummy, arena);
    return 1;
  }
  case CONSTANT_POOL_KIND_CLASS_INFO: {
    const u16 class_name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_name_i > 0);
    pg_assert(class_name_i <= constant_pool_count);

    const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_CLASS_INFO,
                                    .v = {.class_name = class_name_i}};
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_STRING: {
    const u16 utf8_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(utf8_i > 0);
    pg_assert(utf8_i <= constant_pool_count);

    const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_STRING,
                                    .v = {.string_utf8_i = utf8_i}};
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_FIELD_REF: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_count);

    const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_count);

    const cf_constant_t constant = {
        .kind = CONSTANT_POOL_KIND_FIELD_REF,
        .v = {.field_ref = {.name = name_i, .type_descriptor = descriptor_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_REF: {
    const u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_count);

    const u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_count);

    const cf_constant_t constant = {
        .kind = CONSTANT_POOL_KIND_METHOD_REF,
        .v = {.method_ref = {.name_and_type = name_and_type_i,
                             .class = class_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_INTERFACE_METHOD_REF: {
    const u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_count);

    const u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_count);

    const cf_constant_t constant = {
        .kind = CONSTANT_POOL_KIND_INTERFACE_METHOD_REF,
    }; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_NAME_AND_TYPE: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_count);

    const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_count);

    const cf_constant_t constant = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = name_i,
                                .type_descriptor = descriptor_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_HANDLE: {
    const u8 reference_kind = buf_read_u8(buf, buf_len, current);
    pg_unused(reference_kind);
    const u16 reference_i = buf_read_be_u16(buf, buf_len, current);
    pg_unused(reference_i);

    const cf_constant_t constant = {.kind = kind}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_TYPE: {
    const u16 descriptor = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor > 0);
    pg_assert(descriptor <= constant_pool_count);

    const cf_constant_t constant = {.kind = kind}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_DYNAMIC: {
    const u16 bootstrap_method_attr_index =
        buf_read_be_u16(buf, buf_len, current);
    pg_unused(bootstrap_method_attr_index);

    const u16 name_and_type_index = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_index > 0);
    pg_assert(name_and_type_index <= constant_pool_count);

    const cf_constant_t constant = {.kind = kind}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_INVOKE_DYNAMIC: {
    const u16 bootstrap_method_attr_index =
        buf_read_be_u16(buf, buf_len, current);
    pg_unused(bootstrap_method_attr_index);

    const u16 name_and_type_index = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_index > 0);
    pg_assert(name_and_type_index <= constant_pool_count);

    const cf_constant_t constant = {.kind = kind}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_MODULE: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_count);

    const cf_constant_t constant = {.kind = kind}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_PACKAGE: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_count);

    const cf_constant_t constant = {.kind = kind}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
  return 0;
}

static void cf_buf_read_constants(char *buf, u64 buf_len, char **current,
                                  cf_class_file_t *class_file,
                                  u16 constant_pool_count, arena_t *arena) {
  for (u64 i = 0; i < constant_pool_count; i++) {
    pg_assert((u64)(*current - buf) < buf_len);
    i += cf_buf_read_constant(buf, buf_len, current, class_file,
                              constant_pool_count, arena);
    pg_assert((u64)(*current - buf) <= buf_len);
  }
  pg_assert(constant_pool_count <= class_file->constant_pool.len);
}

static void cf_buf_read_method(char *buf, u64 buf_len, char **current,
                               cf_class_file_t *class_file, u8 flags,
                               arena_t *arena) {
  cf_method_t method = {0};
  method.access_flags = buf_read_be_u16(buf, buf_len, current);
  method.name = buf_read_be_u16(buf, buf_len, current);
  pg_assert(method.name > 0);
  pg_assert(method.name <= class_file->constant_pool.len);

  method.descriptor = buf_read_be_u16(buf, buf_len, current);
  pg_assert(method.descriptor > 0);
  pg_assert(method.descriptor <= class_file->constant_pool.len);

  cf_buf_read_attributes(buf, buf_len, current, class_file, &method.attributes,
                         flags, arena);

  pg_array_append(class_file->methods, method, arena);
}

static void cf_buf_read_methods(char *buf, u64 buf_len, char **current,
                                cf_class_file_t *class_file, u8 flags,
                                arena_t *arena) {

  const u16 methods_count = buf_read_be_u16(buf, buf_len, current);
  pg_array_init_reserve(class_file->methods, methods_count, arena);

  for (u64 i = 0; i < methods_count; i++) {
    cf_buf_read_method(buf, buf_len, current, class_file, flags, arena);
  }
}

static void cf_buf_read_interfaces(char *buf, u64 buf_len, char **current,
                                   cf_class_file_t *class_file,
                                   arena_t *arena) {

  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  const char *const current_start = *current;

  const u16 interfaces_count = buf_read_be_u16(buf, buf_len, current);
  pg_array_init_reserve(class_file->interfaces, interfaces_count, arena);

  for (u16 i = 0; i < interfaces_count; i++) {
    const u16 interface_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(interface_i > 0);
    pg_assert(interface_i <= class_file->constant_pool.len);

    pg_array_append(class_file->interfaces, interface_i, arena);
  }

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == sizeof(u16) + interfaces_count * sizeof(u16));
}

static void cf_buf_read_field(char *buf, u64 buf_len, char **current,
                              cf_class_file_t *class_file, arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  cf_field_t field = {0};
  field.access_flags = buf_read_be_u16(buf, buf_len, current);
  field.name = buf_read_be_u16(buf, buf_len, current);
  pg_assert(field.name > 0);
  pg_assert(field.name <= class_file->constant_pool.len);

  field.descriptor = buf_read_be_u16(buf, buf_len, current);
  pg_assert(field.descriptor > 0);
  pg_assert(field.descriptor <= class_file->constant_pool.len);

  cf_buf_read_attributes(buf, buf_len, current, class_file, &field.attributes,
                         0, arena);

  pg_array_append(class_file->fields, field, arena);
}

static void cf_buf_read_fields(char *buf, u64 buf_len, char **current,
                               cf_class_file_t *class_file, arena_t *arena) {

  const u16 fields_count = buf_read_be_u16(buf, buf_len, current);
  pg_array_init_reserve(class_file->fields, fields_count, arena);

  for (u16 i = 0; i < fields_count; i++) {
    cf_buf_read_field(buf, buf_len, current, class_file, arena);
  }
}

static void cf_buf_read_class_file(char *buf, u64 buf_len, char **current,
                                   cf_class_file_t *class_file, u8 flags,
                                   arena_t *arena) {

  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  // Magic.
  pg_assert(buf_read_u8(buf, buf_len, current) == 0xca);
  pg_assert(buf_read_u8(buf, buf_len, current) == 0xfe);
  pg_assert(buf_read_u8(buf, buf_len, current) == 0xba);
  pg_assert(buf_read_u8(buf, buf_len, current) == 0xbe);

  class_file->minor_version = buf_read_be_u16(buf, buf_len, current);
  class_file->major_version = buf_read_be_u16(buf, buf_len, current);

  const u16 constant_pool_count = buf_read_be_u16(buf, buf_len, current) - 1;
  pg_assert(constant_pool_count > 0);
  class_file->constant_pool = cf_constant_array_make(
      constant_pool_count * 2,
      arena); // Worst case: only LONG or DOUBLE entries which take 2 slots.
  pg_assert(class_file->constant_pool.values != NULL);
  pg_assert(((u64)class_file->constant_pool.values) % 16 == 0);

  cf_buf_read_constants(buf, buf_len, current, class_file, constant_pool_count,
                        arena);

  class_file->access_flags = buf_read_be_u16(buf, buf_len, current);

  class_file->this_class = buf_read_be_u16(buf, buf_len, current);
  pg_assert(class_file->this_class > 0);
  pg_assert(class_file->this_class <= constant_pool_count);

  class_file->super_class = buf_read_be_u16(buf, buf_len, current);
  pg_assert(class_file->super_class <= constant_pool_count);

  cf_buf_read_interfaces(buf, buf_len, current, class_file, arena);

  cf_buf_read_fields(buf, buf_len, current, class_file, arena);

  cf_buf_read_methods(buf, buf_len, current, class_file, flags, arena);

  cf_buf_read_attributes(buf, buf_len, current, class_file,
                         &class_file->attributes, flags, arena);

  const u64 remaining = buf + buf_len - *current;
  pg_assert(remaining == 0);
}

// Returns the number of incoming slots to skip:
// - `1` in the case of CONSTANT_POOL_KIND_LONG or CONSTANT_POOL_KIND_DOUBLE
// - `0` otherwise
static u8 cf_write_constant(const cf_class_file_t *class_file, FILE *file,
                            const cf_constant_t *constant) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);
  pg_assert(constant != NULL);

  fwrite(&constant->kind, sizeof(u8), 1, file);
  switch (constant->kind) {
  case CONSTANT_POOL_KIND_UTF8: {
    const string_t *const s = &constant->v.s;
    file_write_be_u16(file, s->len);
    fwrite(s->value, sizeof(u8), s->len, file);
    break;
  }
  case CONSTANT_POOL_KIND_FLOAT:
  case CONSTANT_POOL_KIND_INT:
    file_write_be_u32(file, constant->v.number);
    break;
  case CONSTANT_POOL_KIND_LONG:
  case CONSTANT_POOL_KIND_DOUBLE:
    file_write_be_u64(file, constant->v.number);
    return 1;
  case CONSTANT_POOL_KIND_CLASS_INFO:
    file_write_be_u16(file, constant->v.class_name);
    break;
  case CONSTANT_POOL_KIND_STRING:
    file_write_be_u16(file, constant->v.string_utf8_i);
    break;
  case CONSTANT_POOL_KIND_FIELD_REF: {

    const cf_constant_field_ref_t *const field_ref = &constant->v.field_ref;

    file_write_be_u16(file, field_ref->name);
    file_write_be_u16(file, field_ref->type_descriptor);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_REF: {

    const cf_constant_method_ref_t *const method_ref = &constant->v.method_ref;

    file_write_be_u16(file, method_ref->class);
    file_write_be_u16(file, method_ref->name_and_type);
    break;
  }
  case CONSTANT_POOL_KIND_INTERFACE_METHOD_REF:
    pg_assert(0 && "unimplemented");
    break;
  case CONSTANT_POOL_KIND_NAME_AND_TYPE: {

    const cf_constant_name_and_type_t *const name_and_type =
        &constant->v.name_and_type;

    file_write_be_u16(file, name_and_type->name);
    file_write_be_u16(file, name_and_type->type_descriptor);
    break;
  }
  case CONSTANT_POOL_KIND_INVOKE_DYNAMIC:
    pg_assert(0 && "unimplemented");
    break;
  default:
    pg_assert(0 && "unreachable/unimplemented");
  }
  return 0;
}

static void cf_write_constant_pool(const cf_class_file_t *class_file,
                                   FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);
  file_write_be_u16(file, class_file->constant_pool.len + 1);

  for (u64 i = 0; i < class_file->constant_pool.len; i++) {
    pg_assert(class_file->constant_pool.values != NULL);
    pg_assert(((u64)class_file->constant_pool.values) % 16 == 0);

    const cf_constant_t *const constant = &class_file->constant_pool.values[i];
    i += cf_write_constant(class_file, file, constant);
  }
}
static void cf_write_interfaces(const cf_class_file_t *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  file_write_be_u16(file, class_file->interfaces_count);

  pg_assert(class_file->interfaces_count == 0 && "unimplemented");
}

static void cf_write_fields(const cf_class_file_t *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  file_write_be_u16(file, class_file->fields_count);

  pg_assert(class_file->fields_count == 0 && "unimplemented");
}

static u32
cf_compute_verification_info_size(cf_verification_info_t verification_info) {
  pg_assert(verification_info.kind <= 8);

  return verification_info.kind < 7 ? sizeof(u8) : sizeof(u8) + sizeof(u16);
}

static u32 cf_compute_verification_infos_size(
    const cf_stack_map_frame_t *stack_map_frame) {
  pg_assert(stack_map_frame != NULL);

  if (stack_map_frame->kind <= 63) // same_frame
  {
    return 0;
  } else if (64 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 127) { // same_locals_1_stack_item_frame
    const cf_verification_info_t verification_info =
        *pg_array_last(stack_map_frame->frame->stack);

    return cf_compute_verification_info_size(verification_info);
  } else if (128 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 246) { // reserved
    pg_assert(0 && "unreachable");
  } else if (247 <= stack_map_frame->kind &&
             stack_map_frame->kind <=
                 247) { // same_locals_1_stack_item_frame_extended
    const cf_verification_info_t verification_info =
        *pg_array_last(stack_map_frame->frame->stack);

    return cf_compute_verification_info_size(verification_info);
  } else if (248 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 250) { // chop_frame
    return 0;
  } else if (251 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 251) { // same_frame_extended
    return 0;
  } else if (252 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 254) { // append_frame
    u64 count = 255 - stack_map_frame->kind;

    u32 size = 0;
    for (i64 i = stack_map_frame->frame->locals_count - 1;
         i >= 0 && count > 0;) {
      const cf_verification_info_t verification_info =
          stack_map_frame->frame->locals[i].verification_info;
      const u64 word_count =
          cf_verification_info_kind_word_count(verification_info.kind);
      size += cf_compute_verification_info_size(verification_info);

      i -= word_count;
      count -= 1;
    }

    return size;
  } else { // full_frame
    u32 size = 0;
    for (u64 i = 0; i < pg_array_len(stack_map_frame->frame->locals); i++) {
      const cf_verification_info_t verification_info =
          stack_map_frame->frame->locals[i].verification_info;
      size += cf_compute_verification_info_size(verification_info);
    }

    for (u64 i = 0; i < pg_array_len(stack_map_frame->frame->stack); i++) {
      const cf_verification_info_t verification_info =
          stack_map_frame->frame->stack[i];
      size += cf_compute_verification_info_size(verification_info);
    }

    return size;
  }
  pg_assert(0 && "unreachable");
}

static u32 cf_compute_attribute_size(const cf_attribute_t *attribute) {
  pg_assert(attribute != NULL);

  switch (attribute->kind) {
  case ATTRIBUTE_KIND_SOURCE_FILE:
    return 2;
  case ATTRIBUTE_KIND_CODE: {
    const cf_attribute_code_t *const code = &attribute->v.code;

    u32 size = sizeof(code->max_stack) + sizeof(code->max_locals) +
               sizeof(u32) + pg_array_len(code->code) +
               sizeof(u16) /* exception count */ +
               +pg_array_len(code->exceptions) * sizeof(cf_exception_t) +
               sizeof(u16) // attributes length
        ;

    for (u64 i = 0; i < pg_array_len(code->attributes); i++) {
      const cf_attribute_t *const child_attribute = &code->attributes[i];
      size += sizeof(u16) + sizeof(u32) +
              cf_compute_attribute_size(child_attribute);
    }
    return size;
  }
  case ATTRIBUTE_KIND_LINE_NUMBER_TABLE: {
    return sizeof(u16) /* count */ +
           pg_array_len(attribute->v.line_number_table_entries) *
               sizeof(cf_line_number_table_entry_t);
  }
  case ATTRIBUTE_KIND_STACK_MAP_TABLE: {
    const cf_stack_map_frame_t *const stack_map_frames =
        attribute->v.stack_map_table;
    pg_assert(stack_map_frames != NULL);

    u32 size = sizeof(u16) /* count */;
    for (u16 i = 0; i < pg_array_len(stack_map_frames); i++) {
      const cf_stack_map_frame_t *const stack_map_frame = &stack_map_frames[i];

      if (stack_map_frame->kind <= 63) // same_frame
      {
        size += sizeof(u8);
      } else if (64 <= stack_map_frame->kind &&
                 stack_map_frame->kind <=
                     127) { // same_locals_1_stack_item_frame
        const u32 delta =
            sizeof(u8) + cf_compute_verification_infos_size(stack_map_frame);
        pg_assert(delta >= 2);
        pg_assert(delta <= 4);

        size += delta;
      } else if (128 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 246) { // reserved
        pg_assert(0 && "unreachable");
      } else if (247 <= stack_map_frame->kind &&
                 stack_map_frame->kind <=
                     247) { // same_locals_1_stack_item_frame_extended
        const u32 delta = sizeof(u8) + sizeof(u16) +
                          cf_compute_verification_infos_size(stack_map_frame);
        pg_assert(delta >= 4);
        pg_assert(delta <= 5);

        size += delta;

      } else if (248 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 250) { // chop_frame
        size += sizeof(u8) + sizeof(u16);
      } else if (251 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 251) { // same_frame_extended
        size += sizeof(u8) + sizeof(u16);
      } else if (252 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 254) { // append_frame
        const u32 delta = sizeof(u8) + sizeof(u16) +
                          cf_compute_verification_infos_size(stack_map_frame);

        pg_assert(delta >= 4);
        pg_assert(delta <= 9);

        size += delta;
      } else { // full_frame
        size += sizeof(u8) + 3 * sizeof(u16) +
                cf_compute_verification_infos_size(stack_map_frame);
      }
    }

    return size;
  }
  }
  pg_assert(0 && "unreachable");
}

static void cf_write_attributes(FILE *file, const cf_attribute_t *attributes);

static void
cf_write_verification_info(FILE *file,
                           cf_verification_info_t verification_info) {
  pg_assert(file != NULL);
  pg_assert(verification_info.kind <= 8);

  file_write_u8(file, verification_info.kind);

  if (verification_info.kind >= 7) {
    file_write_be_u16(file, verification_info.extra_data);
  }
}

static void cf_write_stack_map_table_attribute(
    FILE *file, const cf_stack_map_frame_t *stack_map_frame) {
  pg_assert(file != NULL);
  pg_assert(stack_map_frame != NULL);

  if (stack_map_frame->kind <= 63) // same_frame
  {
    file_write_u8(file, stack_map_frame->kind);
  } else if (64 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 127) { // same_locals_1_stack_item_frame
    file_write_u8(file, stack_map_frame->kind);
    cf_write_verification_info(file,
                               *pg_array_last(stack_map_frame->frame->stack));
  } else if (128 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 246) { // reserved
    pg_assert(0 && "unreachable");
  } else if (247 <= stack_map_frame->kind &&
             stack_map_frame->kind <=
                 247) { // same_locals_1_stack_item_frame_extended
    pg_assert(0 && "todo");
  } else if (248 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 250) { // chop_frame
    file_write_u8(file, stack_map_frame->kind);
    file_write_be_u16(file, stack_map_frame->offset_delta);
  } else if (251 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 251) { // same_frame_extended
    pg_assert(0 && "todo");
  } else if (252 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 254) { // append_frame
    file_write_u8(file, stack_map_frame->kind);
    file_write_be_u16(file, stack_map_frame->offset_delta);
    cf_write_verification_info(
        file, pg_array_last(stack_map_frame->frame->locals)->verification_info);
  } else { // full_frame

    file_write_u8(file, stack_map_frame->kind);
    file_write_be_u16(file, stack_map_frame->offset_delta);
    file_write_be_u16(file, pg_array_len(stack_map_frame->frame->locals));

    for (u64 i = 0; i < pg_array_len(stack_map_frame->frame->locals); i++) {
      cf_write_verification_info(
          file, stack_map_frame->frame->locals[i].verification_info);
    }

    file_write_be_u16(file, pg_array_len(stack_map_frame->frame->stack));
    for (u64 i = 0; i < pg_array_len(stack_map_frame->frame->stack); i++) {
      cf_write_verification_info(file, stack_map_frame->frame->stack[i]);
    }
  }
}

static void cf_write_attribute(FILE *file, const cf_attribute_t *attribute) {
  pg_assert(file != NULL);
  pg_assert(attribute != NULL);

  file_write_be_u16(file, attribute->name);

  switch (attribute->kind) {
  case ATTRIBUTE_KIND_SOURCE_FILE: {
    const u32 size = cf_compute_attribute_size(attribute);
    file_write_be_u32(file, size);

    const cf_attribute_source_file_t *const source_file =
        &attribute->v.source_file;
    file_write_be_u16(file, source_file->source_file);

    break;
  }
  case ATTRIBUTE_KIND_CODE: {
    const u32 size = cf_compute_attribute_size(attribute);
    file_write_be_u32(file, size);

    const cf_attribute_code_t *const code = &attribute->v.code;

    file_write_be_u16(file, code->max_stack);

    file_write_be_u16(file, code->max_locals);

    file_write_be_u32(file, pg_array_len(code->code));
    fwrite(code->code, pg_array_len(code->code), sizeof(u8), file);

    file_write_be_u16(file, pg_array_len(code->exceptions));
    pg_assert(pg_array_len(code->exceptions) == 0 && "todo");

    cf_write_attributes(file, code->attributes);

    break;
  }
  case ATTRIBUTE_KIND_LINE_NUMBER_TABLE: {
    const u32 size = cf_compute_attribute_size(attribute);
    file_write_be_u32(file, size);

    for (u16 i = 0; i < pg_array_len(attribute->v.line_number_table_entries);
         i++) {
      cf_line_number_table_entry_t line_number_table =
          attribute->v.line_number_table_entries[i];
      file_write_be_u16(file, line_number_table.start_pc);
      file_write_be_u16(file, line_number_table.line_number);
    }

    break;
  }
  case ATTRIBUTE_KIND_STACK_MAP_TABLE: {
    const u32 size = cf_compute_attribute_size(attribute);
    file_write_be_u32(file, size);

    pg_assert(attribute->v.stack_map_table != NULL);
    const u16 count = pg_array_len(attribute->v.stack_map_table);
    file_write_be_u16(file, count);

    for (u16 i = 0; i < pg_array_len(attribute->v.stack_map_table); i++) {
      const cf_stack_map_frame_t *const stack_map_frame =
          &attribute->v.stack_map_table[i];
      cf_write_stack_map_table_attribute(file, stack_map_frame);
    }
    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
}

static void cf_write_attributes(FILE *file, const cf_attribute_t *attributes) {
  file_write_be_u16(file, pg_array_len(attributes));

  for (u64 i = 0; i < pg_array_len(attributes); i++) {
    const cf_attribute_t *const attribute = &attributes[i];
    cf_write_attribute(file, attribute);
  }
}

static void cf_write_method(FILE *file, const cf_method_t *method) {
  file_write_be_u16(file, method->access_flags);
  file_write_be_u16(file, method->name);
  file_write_be_u16(file, method->descriptor);

  cf_write_attributes(file, method->attributes);
}

static void cf_write_methods(const cf_class_file_t *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  file_write_be_u16(file, pg_array_len(class_file->methods));

  for (u64 i = 0; i < pg_array_len(class_file->methods); i++) {
    const cf_method_t *const method = &class_file->methods[i];
    cf_write_method(file, method);
  }
}

static void cf_write(const cf_class_file_t *class_file, FILE *file) {
  fwrite(&cf_MAGIC_NUMBER, sizeof(cf_MAGIC_NUMBER), 1, file);

  file_write_be_u16(file, class_file->minor_version);
  file_write_be_u16(file, 44 + class_file->major_version);
  cf_write_constant_pool(class_file, file);
  file_write_be_u16(file, class_file->access_flags);
  file_write_be_u16(file, class_file->this_class);
  file_write_be_u16(file, class_file->super_class);

  cf_write_interfaces(class_file, file);
  cf_write_fields(class_file, file);
  cf_write_methods(class_file, file);
  cf_write_attributes(file, class_file->attributes);
  fflush(file);
}

static void cf_init(cf_class_file_t *class_file, arena_t *arena) {
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  class_file->constant_pool = cf_constant_array_make(1024, arena);
  pg_array_init_reserve(class_file->interfaces, 64, arena);

  pg_array_init_reserve(class_file->methods, 64, arena);
  pg_array_init_reserve(class_file->fields, 64, arena);

  pg_array_init_reserve(class_file->attributes, 64, arena);
}

static void cf_attribute_code_init(cf_attribute_code_t *code, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(arena != NULL);

  pg_array_init_reserve(code->code, 512, arena);
  pg_array_init_reserve(code->attributes, 4, arena);
  pg_array_init_reserve(code->exceptions, 0, arena);
}

static u16 cf_add_constant_string(cf_constant_array_t *constant_pool,
                                  string_t s, arena_t *arena) {
  pg_assert(constant_pool != NULL);
  pg_assert(s.value != NULL);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                  .v = {.s = s}};
  return cf_constant_array_push(constant_pool, &constant, arena);
}

static u16 cf_add_constant_cstring(cf_constant_array_t *constant_pool, char *s,
                                   arena_t *arena) {
  pg_assert(constant_pool != NULL);
  pg_assert(s != NULL);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                  .v = {.s = {
                                            .len = strlen(s),
                                            .value = s,
                                        }}};
  return cf_constant_array_push(constant_pool, &constant, arena);
}

static u16 cf_add_constant_jstring(cf_constant_array_t *constant_pool,
                                   u16 constant_utf8_i, arena_t *arena) {
  pg_assert(constant_pool != NULL);
  pg_assert(constant_utf8_i > 0);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_STRING,
                                  .v = {.string_utf8_i = constant_utf8_i}};

  return cf_constant_array_push(constant_pool, &constant, arena);
}

// TODO: sanitize `source_file_name` in case of spaces, etc.
static string_t cf_make_class_file_name_kt(string_t source_file_name,
                                           arena_t *arena) {
  pg_assert(source_file_name.value != NULL);
  pg_assert(source_file_name.len > 0);
  pg_assert(arena != NULL);

  string_t last_path_component =
      string_make(string_find_last_path_component(source_file_name), arena);
  pg_assert(last_path_component.len > 0);
  pg_assert(last_path_component.value[0] != '/');

  string_drop_after_last_incl(&last_path_component, '.');
  string_append_cstring(&last_path_component, "Kt.class", arena);
  string_capitalize_first(&last_path_component);

  return last_path_component;
}

// TODO: one thread that walks the directory recursively and one/many worker
// threads to parse class files?
static void cf_read_class_files(char *path, u64 path_len,
                                cf_class_file_t **class_files, arena_t *arena) {
  pg_assert(path != NULL);
  pg_assert(path_len > 0);
  pg_assert(class_files != NULL);
  pg_assert(arena != NULL);

  struct stat st = {0};
  if (stat(path, &st) == -1) {
    return;
  }

  if (S_ISREG(st.st_mode) &&
      ut_cstring_ends_with(path, path_len, ".class", 6)) {
    const int fd = open(path, O_RDONLY);
    pg_assert(fd > 0);

    const u64 arena_before = arena->current_offset;
    char *buf = arena_alloc(arena, st.st_size, sizeof(u8));
    const ssize_t read_bytes = read(fd, buf, st.st_size);
    pg_assert(read_bytes == st.st_size);
    close(fd);

    char *current = buf;
    cf_class_file_t class_file = {
        .file_path = string_make_from_c(path, arena),
    };
    cf_buf_read_class_file(buf, read_bytes, &current, &class_file, 0, arena);
    pg_array_append(*class_files, class_file, arena);

    const u64 arena_after = arena->current_offset;
    const u64 delta = arena_after - arena_before;
    LOG("cf_read_class_files path=%s count=%lu arena_delta=%lu "
        "delta-file_size=%lu",
        path, pg_array_len(*class_files), delta, delta - st.st_size);
    return;
  }
  if (!S_ISDIR(st.st_mode))
    return;

  pg_assert(S_ISDIR(st.st_mode));

  // Recurse
  DIR *dirp = opendir(path);
  if (dirp == NULL)
    return;

  struct dirent *entry = {0};

#define PATH_MAX 4096
  char pathbuf[PATH_MAX + 1] = {0};
  u64 pathbuf_len = path_len;
  pg_assert(pathbuf_len < PATH_MAX);

  memcpy(pathbuf, path, path_len);
  if (pathbuf[pathbuf_len - 1] != '/') {
    pathbuf[pathbuf_len++] = '/';
  }

  pg_assert(pathbuf_len < PATH_MAX);

  while ((entry = readdir(dirp)) != NULL) {
    pg_assert(entry->d_name != NULL);
    const u64 d_name_len = strlen(entry->d_name);
    pg_assert(d_name_len > 0);

    // Skip over `.` and `..`.
    if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0)
      continue;

    pg_assert(pathbuf_len + d_name_len < PATH_MAX);
    memcpy(pathbuf + pathbuf_len, entry->d_name, d_name_len);
    pathbuf[pathbuf_len + d_name_len] = 0;

    cf_read_class_files(pathbuf, pathbuf_len + d_name_len, class_files, arena);
  }
  closedir(dirp);
#undef PATH_MAX
}

static bool cf_class_files_find_field_exactly(
    const cf_class_file_t *class_files, string_t class_name,
    string_t field_name, u16 access_flags, u32 *class_file_i, u16 *field_i) {
  pg_assert(class_files != NULL);
  pg_assert(field_name.len > 0);
  pg_assert(class_file_i != NULL);
  pg_assert(field_i != NULL);

  // TODO: use the file path <-> class name mapping to search less?

  for (u64 i = 0; i < pg_array_len(class_files); i++) {
    const cf_class_file_t *const class_file = &class_files[i];
    pg_assert(class_file->file_path.cap >= class_file->file_path.len);
    pg_assert(class_file->file_path.len > 0);
    pg_assert(class_file->file_path.value != NULL);

    const cf_constant_t *const this_class = cf_constant_array_get(
        &class_file->constant_pool, class_file->this_class);
    pg_assert(this_class->kind == CONSTANT_POOL_KIND_CLASS_INFO);
    const u16 this_class_i = this_class->v.class_name;
    const string_t this_class_name = cf_constant_array_get_as_string(
        &class_file->constant_pool, this_class_i);

    if (!string_eq(this_class_name, class_name))
      continue;

    for (u64 j = 0; j < pg_array_len(class_file->fields); j++) {
      const cf_field_t *const this_field = &class_file->fields[j];
      if ((this_field->access_flags & access_flags) == 0)
        continue;

      const string_t this_field_name = cf_constant_array_get_as_string(
          &class_file->constant_pool, this_field->name);

      if (!string_eq(this_field_name, field_name))
        continue;

      *class_file_i = i;
      *field_i = j;
      return true;
    }
  }
  return false;
}

static bool cf_class_files_find_class_exactly(
    const cf_class_file_t *class_files, string_t class_name,
    string_t alernate_class_name, u32 *class_file_i,
    u16 *constant_pool_class_name_i) {
  pg_assert(class_files != NULL);
  pg_assert(class_name.len > 0);

  // TODO: use the file path <-> class name mapping to search less?

  for (u64 i = 0; i < pg_array_len(class_files); i++) {
    const cf_class_file_t *const class_file = &class_files[i];
    pg_assert(class_file->file_path.cap >= class_file->file_path.len);
    pg_assert(class_file->file_path.len > 0);
    pg_assert(class_file->file_path.value != NULL);

    const cf_constant_t *const this_class = cf_constant_array_get(
        &class_file->constant_pool, class_file->this_class);
    pg_assert(this_class->kind == CONSTANT_POOL_KIND_CLASS_INFO);
    const u16 this_class_i = this_class->v.class_name;
    const string_t this_class_name = cf_constant_array_get_as_string(
        &class_file->constant_pool, this_class_i);

    if (!string_eq(this_class_name, class_name) &&
        !string_eq(this_class_name, alernate_class_name))
      continue;

    if (class_file_i != NULL)
      *class_file_i = i;
    if (constant_pool_class_name_i != NULL)
      *constant_pool_class_name_i = this_class_i;
    return true;
  }
  return false;
}

static bool
cf_class_files_find_method_exactly(const cf_class_file_t *class_files,
                                   string_t class_name, string_t method_name,
                                   string_t descriptor) {
  pg_assert(class_files != NULL);
  pg_assert(descriptor.len > 0);
  pg_assert(descriptor.value != NULL);
  pg_assert(class_name.len > 0);

  // TODO: use the file path <-> class name mapping to search less?

  for (u64 i = 0; i < pg_array_len(class_files); i++) {
    const cf_class_file_t *const class_file = &class_files[i];
    pg_assert(class_file->file_path.cap >= class_file->file_path.len);
    pg_assert(class_file->file_path.len > 0);
    pg_assert(class_file->file_path.value != NULL);

    const cf_constant_t *const this_class = cf_constant_array_get(
        &class_file->constant_pool, class_file->this_class);
    pg_assert(this_class->kind == CONSTANT_POOL_KIND_CLASS_INFO);
    const u16 this_class_i = this_class->v.class_name;
    const string_t this_class_name = cf_constant_array_get_as_string(
        &class_file->constant_pool, this_class_i);

    if (!string_eq(this_class_name, class_name))
      continue;

    for (u64 j = 0; j < pg_array_len(class_file->methods); j++) {
      const cf_method_t *const this_method = &class_file->methods[j];
      // TODO: check attributes?

      const string_t this_method_name = cf_constant_array_get_as_string(
          &class_file->constant_pool, this_method->name);

      if (!string_eq(this_method_name, method_name))
        continue;

      const string_t this_method_descriptor = cf_constant_array_get_as_string(
          &class_file->constant_pool, this_method->descriptor);

      if (!string_eq(this_method_descriptor, descriptor)) {
        continue;
      }

      return true; // TODO: return `method`?
    }
  }
  return false;
}

// ---------------------------------- Lexer

typedef enum __attribute__((packed)) {
  TOKEN_KIND_NONE,
  TOKEN_KIND_NUMBER,
  TOKEN_KIND_PLUS,
  TOKEN_KIND_MINUS,
  TOKEN_KIND_STAR,
  TOKEN_KIND_SLASH,
  TOKEN_KIND_PERCENT,
  TOKEN_KIND_AMPERSAND,
  TOKEN_KIND_AMPERSAND_AMPERSAND,
  TOKEN_KIND_PIPE,
  TOKEN_KIND_PIPE_PIPE,
  TOKEN_KIND_LEFT_PAREN,
  TOKEN_KIND_RIGHT_PAREN,
  TOKEN_KIND_LEFT_BRACE,
  TOKEN_KIND_RIGHT_BRACE,
  TOKEN_KIND_BUILTIN_PRINTLN,
  TOKEN_KIND_KEYWORD_FUN,
  TOKEN_KIND_KEYWORD_FALSE,
  TOKEN_KIND_KEYWORD_TRUE,
  TOKEN_KIND_KEYWORD_VAR,
  TOKEN_KIND_KEYWORD_IF,
  TOKEN_KIND_KEYWORD_ELSE,
  TOKEN_KIND_KEYWORD_WHILE,
  TOKEN_KIND_IDENTIFIER,
  TOKEN_KIND_EQUAL,
  TOKEN_KIND_COMMA,
  TOKEN_KIND_DOT,
  TOKEN_KIND_COLON,
  TOKEN_KIND_NOT,
  TOKEN_KIND_EQUAL_EQUAL,
  TOKEN_KIND_NOT_EQUAL,
  TOKEN_KIND_LE,
  TOKEN_KIND_LT,
  TOKEN_KIND_GE,
  TOKEN_KIND_GT,
  TOKEN_KIND_STRING_LITERAL,
} lex_token_kind_t;

typedef struct {
  u32 source_offset;
  lex_token_kind_t kind;
  pg_pad(3);
} lex_token_t;

typedef struct {
  string_t file_path;
  lex_token_t *tokens;
  u32 *line_table; // line_table[i] is the start offset of the LOC `i+1`
} lex_lexer_t;

static u32 lex_get_current_offset(const char *buf, u32 buf_len,
                                  const char *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return *current - buf;
}

static bool lex_is_at_end(const char *buf, u32 buf_len,
                          const char *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return lex_get_current_offset(buf, buf_len, current) == buf_len;
}

static char lex_peek(const char *buf, u32 buf_len, const char *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  return lex_is_at_end(buf, buf_len, current) ? 0 : **current;
}

static u8 lex_advance(const char *buf, u32 buf_len, const char **current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  const u8 c = **current;

  *current += 1;

  return lex_is_at_end(buf, buf_len, current) ? 0 : c;
}

static bool lex_match(const char *buf, u32 buf_len, const char **current,
                      u8 c) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  if (lex_peek(buf, buf_len, current) == c) {
    lex_advance(buf, buf_len, current);
    return true;
  }
  return false;
}

static bool lex_is_digit(char c) { return ('0' <= c && c <= '9'); }

static bool lex_is_identifier_char(char c) {
  return ut_char_is_alphabetic(c) || lex_is_digit(c) || c == '_';
}

static u32 lex_number_length(const char *buf, u32 buf_len, u32 current_offset) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current_offset < buf_len);

  const u32 start_offset = current_offset;
  const char *current = &buf[current_offset];
  pg_assert(lex_is_digit(lex_peek(buf, buf_len, &current)));

  lex_advance(buf, buf_len, &current);

  while (!lex_is_at_end(buf, buf_len, &current)) {
    const char c = lex_peek(buf, buf_len, &current);

    if (!(lex_is_digit(c) || c == '_' || c == 'L'))
      break;
    lex_advance(buf, buf_len, &current);
  }

  const u32 end_offset_excl = lex_get_current_offset(buf, buf_len, &current);
  pg_assert(end_offset_excl > start_offset);
  pg_assert(end_offset_excl <= buf_len);

  const u32 len = end_offset_excl - start_offset;
  pg_assert(len >= 1);
  pg_assert(len <= buf_len);
  return len;
}

static u32 lex_string_length(const char *buf, u32 buf_len, u32 current_offset) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current_offset < buf_len);

  const u32 start_offset = current_offset;
  const char *current = &buf[current_offset];
  pg_assert(*(current - 1) == '"');

  char *end_quote = memchr(current, '"', buf_len - start_offset);
  pg_assert(end_quote != NULL);

  return end_quote - current;
}

static u32 lex_identifier_length(const char *buf, u32 buf_len,
                                 u32 current_offset) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current_offset < buf_len);

  const u32 start_offset = current_offset;
  const char *current = &buf[current_offset];
  pg_assert(ut_char_is_alphabetic(*current));

  lex_advance(buf, buf_len, &current);

  while (!lex_is_at_end(buf, buf_len, &current)) {
    const char c = lex_peek(buf, buf_len, &current);

    if (!lex_is_identifier_char(c))
      break;
    lex_advance(buf, buf_len, &current);
  }

  pg_assert(!lex_is_at_end(buf, buf_len, &current));
  pg_assert(!lex_is_identifier_char(lex_peek(buf, buf_len, &current)));

  const u32 end_offset_excl = lex_get_current_offset(buf, buf_len, &current);
  pg_assert(end_offset_excl > start_offset);
  pg_assert(end_offset_excl <= buf_len);

  const u32 len = end_offset_excl - start_offset;
  pg_assert(len >= 1);
  pg_assert(len <= buf_len);
  return len;
}

static void lex_identifier(lex_lexer_t *lexer, const char *buf, u32 buf_len,
                           const char **current, arena_t *arena) {
  pg_assert(lexer != NULL);
  pg_assert(lexer->tokens != NULL);
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);
  pg_assert(ut_char_is_alphabetic(**current));

  const u32 start_offset = lex_get_current_offset(buf, buf_len, current);
  const char *const identifier = *current;
  const u32 identifier_len = lex_identifier_length(buf, buf_len, start_offset);
  *current += identifier_len;
  if (mem_eq_c(identifier, identifier_len, "fun")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_KEYWORD_FUN,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  } else if (mem_eq_c(identifier, identifier_len, "println")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_BUILTIN_PRINTLN,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  } else if (mem_eq_c(identifier, identifier_len, "true")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_KEYWORD_TRUE,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  } else if (mem_eq_c(identifier, identifier_len, "false")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_KEYWORD_FALSE,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  } else if (mem_eq_c(identifier, identifier_len, "var")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_KEYWORD_VAR,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  } else if (mem_eq_c(identifier, identifier_len, "if")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_KEYWORD_IF,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  } else if (mem_eq_c(identifier, identifier_len, "else")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_KEYWORD_ELSE,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  } else if (mem_eq_c(identifier, identifier_len, "while")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_KEYWORD_WHILE,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  } else {
    const lex_token_t token = {
        .kind = TOKEN_KIND_IDENTIFIER,
        .source_offset = start_offset,
    };
    pg_array_append(lexer->tokens, token, arena);
  }
}

static void lex_number(lex_lexer_t *lexer, const char *buf, u32 buf_len,
                       const char **current, arena_t *arena) {
  pg_assert(lexer != NULL);
  pg_assert(lexer->tokens != NULL);
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);
  pg_assert(lex_is_digit(lex_peek(buf, buf_len, current)));

  const u32 start_offset = lex_get_current_offset(buf, buf_len, current);

  lex_advance(buf, buf_len, current);

  while (!lex_is_at_end(buf, buf_len, current)) {
    const char c = lex_peek(buf, buf_len, current);

    if (!(lex_is_digit(c) || c == '_'))
      break;
    lex_advance(buf, buf_len, current);
  }

  if (lex_match(buf, buf_len, current, 'L')) { // Long suffix.
  }

  const lex_token_t token = {
      .kind = TOKEN_KIND_NUMBER,
      .source_offset = start_offset,
  };
  pg_array_append(lexer->tokens, token, arena);
}

static void lex_lex(lex_lexer_t *lexer, const char *buf, u32 buf_len,
                    const char **current, arena_t *arena) {
  pg_assert(lexer != NULL);
  pg_assert(lexer->line_table != NULL);
  pg_assert(pg_array_len(lexer->line_table) == 0);
  pg_assert(lexer->tokens != NULL);
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  // Push first line.
  pg_array_append(lexer->line_table, 0, arena);

  // Push first dummy token.
  const lex_token_t dummy_token = {0};
  pg_array_append(lexer->tokens, dummy_token, arena);

  while (!lex_is_at_end(buf, buf_len, current)) {
    const u8 c = **current;

    switch (c) {
    case '(': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_LEFT_PAREN,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case ')': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_RIGHT_PAREN,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case ',': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_COMMA,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case ':': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_COLON,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '!': {
      lex_advance(buf, buf_len, current);

      if (lex_match(buf, buf_len, current, '=')) {
        const lex_token_t token = {
            .kind = TOKEN_KIND_NOT_EQUAL,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 2,
        };
        pg_array_append(lexer->tokens, token, arena);
      } else {
        const lex_token_t token = {
            .kind = TOKEN_KIND_NOT,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 1,
        };
        pg_array_append(lexer->tokens, token, arena);
      }
      break;
    }
    case '{': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_LEFT_BRACE,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '}': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_RIGHT_BRACE,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '+': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_PLUS,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '-': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_MINUS,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '*': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_STAR,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '/': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_SLASH,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '%': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_PERCENT,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '.': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_DOT,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '&': {
      lex_advance(buf, buf_len, current);

      if (lex_match(buf, buf_len, current, '&')) {
        const lex_token_t token = {
            .kind = TOKEN_KIND_AMPERSAND_AMPERSAND,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 2,
        };
        pg_array_append(lexer->tokens, token, arena);
      } else {
        const lex_token_t token = {
            .kind = TOKEN_KIND_AMPERSAND,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 1,
        };
        pg_array_append(lexer->tokens, token, arena);
      }
      break;
    }
    case '|': {
      lex_advance(buf, buf_len, current);

      if (lex_match(buf, buf_len, current, '|')) {
        const lex_token_t token = {
            .kind = TOKEN_KIND_PIPE_PIPE,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 2,
        };
        pg_array_append(lexer->tokens, token, arena);
      } else {
        const lex_token_t token = {
            .kind = TOKEN_KIND_PIPE,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 1,
        };
        pg_array_append(lexer->tokens, token, arena);
      }
      break;
    }
    case '=': {
      lex_advance(buf, buf_len, current);

      if (lex_match(buf, buf_len, current, '=')) {
        const lex_token_t token = {
            .kind = TOKEN_KIND_EQUAL_EQUAL,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 2,
        };
        pg_array_append(lexer->tokens, token, arena);
      } else {
        const lex_token_t token = {
            .kind = TOKEN_KIND_EQUAL,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 1,
        };
        pg_array_append(lexer->tokens, token, arena);
      }
      break;
    }
    case '<': {
      lex_advance(buf, buf_len, current);

      if (lex_match(buf, buf_len, current, '=')) {
        const lex_token_t token = {
            .kind = TOKEN_KIND_LE,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 2,
        };
        pg_array_append(lexer->tokens, token, arena);
      } else {
        const lex_token_t token = {
            .kind = TOKEN_KIND_LT,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 1,
        };
        pg_array_append(lexer->tokens, token, arena);
      }
      break;
    }
    case '>': {
      lex_advance(buf, buf_len, current);

      if (lex_match(buf, buf_len, current, '=')) {
        const lex_token_t token = {
            .kind = TOKEN_KIND_GE,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 2,
        };
        pg_array_append(lexer->tokens, token, arena);
      } else {
        const lex_token_t token = {
            .kind = TOKEN_KIND_GT,
            .source_offset = lex_get_current_offset(buf, buf_len, current) - 1,
        };
        pg_array_append(lexer->tokens, token, arena);
      }
      break;
    }
    case '"': {
      lex_advance(buf, buf_len, current);

      const lex_token_t token = {
          .kind = TOKEN_KIND_STRING_LITERAL,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_assert(buf[token.source_offset - 1] == '"');

      while (!lex_match(buf, buf_len, current, '"')) {
        lex_advance(buf, buf_len, current);
      }
      pg_array_append(lexer->tokens, token, arena);
      break;
    }
    case '\n': {
      lex_advance(buf, buf_len, current);

      if (!lex_is_at_end(buf, buf_len, current))
        pg_array_append(lexer->line_table,
                        lex_get_current_offset(buf, buf_len, current), arena);

      break;
    }
    case ' ': {
      lex_advance(buf, buf_len, current);
      break;
    }
    default: {
      if (ut_char_is_alphabetic(c)) {
        lex_identifier(lexer, buf, buf_len, current, arena);
      } else if (lex_is_digit(c)) {
        lex_number(lexer, buf, buf_len, current, arena);
      } else {
        pg_assert(0 && "unimplemented");
      }
    }
    }
  }
  // Ensure the line table has at least 2 items: line_table=[0]=0,
  // line_table[last]=buf_len, for easier logic later to find token
  // positions.
  pg_array_append(lexer->line_table, buf_len, arena);
}

static u32 lex_find_token_length(const lex_lexer_t *lexer, const char *buf,
                                 const u32 buf_len, lex_token_t token) {
  pg_assert(lexer != NULL);
  pg_assert(buf != NULL);

  switch (token.kind) {
  case TOKEN_KIND_NONE:
    return 0;
  case TOKEN_KIND_PLUS:
  case TOKEN_KIND_MINUS:
  case TOKEN_KIND_STAR:
  case TOKEN_KIND_SLASH:
  case TOKEN_KIND_PERCENT:
  case TOKEN_KIND_LEFT_PAREN:
  case TOKEN_KIND_RIGHT_PAREN:
  case TOKEN_KIND_LEFT_BRACE:
  case TOKEN_KIND_RIGHT_BRACE:
  case TOKEN_KIND_COMMA:
  case TOKEN_KIND_DOT:
  case TOKEN_KIND_COLON:
  case TOKEN_KIND_NOT:
  case TOKEN_KIND_EQUAL:
  case TOKEN_KIND_LT:
  case TOKEN_KIND_GT:
  case TOKEN_KIND_AMPERSAND:
  case TOKEN_KIND_PIPE:
    return 1;
  case TOKEN_KIND_KEYWORD_IF:
  case TOKEN_KIND_NOT_EQUAL:
  case TOKEN_KIND_LE:
  case TOKEN_KIND_GE:
  case TOKEN_KIND_EQUAL_EQUAL:
  case TOKEN_KIND_AMPERSAND_AMPERSAND:
  case TOKEN_KIND_PIPE_PIPE:
    return 2;
  case TOKEN_KIND_KEYWORD_FUN:
  case TOKEN_KIND_KEYWORD_VAR:
    return 3;
  case TOKEN_KIND_KEYWORD_TRUE:
  case TOKEN_KIND_KEYWORD_ELSE:
    return 4;
  case TOKEN_KIND_KEYWORD_FALSE:
  case TOKEN_KIND_KEYWORD_WHILE:
    return 5;
  case TOKEN_KIND_BUILTIN_PRINTLN:
    return 7;

  case TOKEN_KIND_NUMBER:
    return lex_number_length(buf, buf_len, token.source_offset);

  case TOKEN_KIND_IDENTIFIER:
    return lex_identifier_length(buf, buf_len, token.source_offset);

  case TOKEN_KIND_STRING_LITERAL:
    return lex_string_length(buf, buf_len, token.source_offset);
  }
}

// ------------------------------ Parser

typedef enum __attribute__((packed)) {
  AST_KIND_NONE,
  AST_KIND_NUMBER,
  AST_KIND_BOOL,
  AST_KIND_BUILTIN_PRINTLN,
  AST_KIND_FUNCTION_DEFINITION,
  AST_KIND_BINARY,
  AST_KIND_UNARY,
  AST_KIND_VAR_DEFINITION,
  AST_KIND_VAR_REFERENCE,
  AST_KIND_CLASS_REFERENCE,
  AST_KIND_IF,
  AST_KIND_LIST,
  AST_KIND_WHILE_LOOP,
  AST_KIND_STRING,
  AST_KIND_FIELD_ACCESS,
  AST_KIND_MAX,
} par_ast_node_kind_t;

static const char *par_ast_node_kind_to_string[AST_KIND_MAX] = {
    [AST_KIND_NONE] = "NONE",
    [AST_KIND_NUMBER] = "NUMBER",
    [AST_KIND_BOOL] = "BOOL",
    [AST_KIND_BUILTIN_PRINTLN] = "BUILTIN_PRINTLN",
    [AST_KIND_FUNCTION_DEFINITION] = "FUNCTION_DEFINITION",
    [AST_KIND_BINARY] = "BINARY",
    [AST_KIND_UNARY] = "UNARY",
    [AST_KIND_VAR_DEFINITION] = "VAR_DEFINITION",
    [AST_KIND_VAR_REFERENCE] = "VAR_REFERENCE",
    [AST_KIND_CLASS_REFERENCE] = "CLASS_REFERENCE",
    [AST_KIND_IF] = "IF",
    [AST_KIND_LIST] = "LIST",
    [AST_KIND_WHILE_LOOP] = "WHILE_LOOP",
    [AST_KIND_STRING] = "STRING",
    [AST_KIND_FIELD_ACCESS] = "FIELD_ACCESS",
};

// TODO: compact fields.
typedef struct {
  u32 main_token_i;
  u32 lhs;
  u32 rhs;
  u32 type_i; // TODO: should it be separate?
  // TODO: should it be separate?
  u32 *nodes; // AST_KIND_LIST
  par_ast_node_kind_t kind;
  pg_pad(1);
  u16 constant_pool_class_name_i;
  u32 class_file_i;
} par_ast_node_t;

typedef enum __attribute__((packed)) {
  PARSER_STATE_OK,
  PARSER_STATE_ERROR,
  PARSER_STATE_PANIC,
  PARSER_STATE_SYNCED,
} par_parser_state_t;

typedef struct {
  char *buf;
  lex_lexer_t *lexer;
  par_variable_t *variables;
  par_ast_node_t *nodes;
  ty_type_t *types;
  cf_class_file_t *class_files;
  u32 current_function_i;
  u32 scope_depth;
  u32 buf_len;
  u32 tokens_i;
  par_parser_state_t state;
  pg_pad(7);
} par_parser_t;

static u32 par_add_node(par_parser_t *parser, const par_ast_node_t *node,
                        arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(node != NULL);
  pg_assert(pg_array_len(parser->nodes) < UINT32_MAX);

  pg_array_append(parser->nodes, *node, arena);
  return pg_array_last_index(parser->nodes);
}

static void par_begin_scope(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->scope_depth < UINT32_MAX);

  parser->scope_depth += 1;
}

static void par_end_scope(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->scope_depth > 0);

  parser->scope_depth -= 1;
}

static void ut_fwrite_indent(FILE *file, u16 indent) {
  for (u16 i = 0; i < indent; i++) {
    fputc(' ', file);
  }
}

static void par_find_token_position(const par_parser_t *parser,
                                    lex_token_t token, u32 *line, u32 *column,
                                    string_t *token_string) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));
  pg_assert(line != NULL);
  pg_assert(column != NULL);
  pg_assert(token_string != NULL);
  pg_assert(pg_array_len(parser->lexer->line_table) > 1);

  token_string->value = &parser->buf[token.source_offset];
  token_string->len =
      lex_find_token_length(parser->lexer, parser->buf, parser->buf_len, token);

  for (u32 i = 0; i < pg_array_len(parser->lexer->line_table) - 1; i++) {
    const u32 line_start_offset = parser->lexer->line_table[i];
    const u32 line_end_offset_excl = parser->lexer->line_table[i + 1];
    if (line_start_offset <= token.source_offset &&
        token.source_offset <= line_end_offset_excl) {
      *line = i + 1;
      *column = 1 + token.source_offset - line_start_offset;

      return;
    }
  }
  /* pg_assert(*line > 0); */
  pg_assert(*line <= pg_array_len(parser->lexer->line_table));
  /* pg_assert(*column > 0); */
}

static string_t ty_type_to_human_string(const ty_type_t *types, u32 type_i,
                                        arena_t *arena) {
  const ty_type_t *const type = &types[type_i];

  switch (type->kind) {
  case TYPE_ANY:
    return string_make_from_c("Any", arena);
  case TYPE_INT:
    return string_make_from_c("Int", arena);
  case TYPE_VOID:
    return string_make_from_c("void", arena);
  case TYPE_BOOL:
    return string_make_from_c("Boolean", arena);
  case TYPE_BYTE:
    return string_make_from_c("Byte", arena);
  case TYPE_CHAR:
    return string_make_from_c("Char", arena);
  case TYPE_SHORT:
    return string_make_from_c("Short", arena);
  case TYPE_LONG:
    return string_make_from_c("Long", arena);
  case TYPE_DOUBLE:
    return string_make_from_c("Double", arena);
  case TYPE_STRING:
    return string_make_from_c("String", arena);
  case TYPE_ARRAY_REFERENCE:
    return string_make_from_c("Array<todo>", arena);
  case TYPE_INSTANCE_REFERENCE:
    return string_make_from_c("Instance<todo>", arena);
  case TYPE_METHOD:
    return string_make_from_c("Method<todo>", arena);
  case TYPE_CONSTRUCTOR:
    return string_make_from_c("Constructor<todo>", arena);
  case TYPE_FLOAT:
    return string_make_from_c("Float", arena);
  case TYPE_CLASS_REFERENCE:
    return string_make_from_c("Class<todo>", arena);
  }
}

static void par_ast_fprint_node(const par_parser_t *parser, u32 node_i,
                                FILE *file, u16 indent, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));
  pg_assert(node_i < pg_array_len(parser->nodes));

#ifdef PG_WITH_LOG
  const par_ast_node_t *const node = &parser->nodes[node_i];
  if (node->kind == AST_KIND_NONE)
    return;

  const char *const kind_string = par_ast_node_kind_to_string[node->kind];
  const lex_token_t token = parser->lexer->tokens[node->main_token_i];
  u32 line = 0;
  u32 column = 0;
  string_t token_string = {0};
  par_find_token_position(parser, token, &line, &column, &token_string);

  ut_fwrite_indent(file, indent);

  const string_t human_type =
      ty_type_to_human_string(parser->types, node->type_i, arena);

  pg_assert(indent < UINT16_MAX - 1); // Avoid overflow.
  switch (node->kind) {
  case AST_KIND_BOOL:
    LOG("[%ld] %s %.*s : %.*s (at %.*s:%u:%u:%u)", node - parser->nodes,
        kind_string, token_string.len, token_string.value, human_type.len,
        human_type.value, parser->lexer->file_path.len,
        parser->lexer->file_path.value, line, column, token.source_offset);
    break;
  case AST_KIND_LIST:
    LOG("[%ld] %s %.*s : %.*s (at %.*s:%u:%u:%u)", node - parser->nodes,
        kind_string, token_string.len, token_string.value, human_type.len,
        human_type.value, parser->lexer->file_path.len,
        parser->lexer->file_path.value, line, column, token.source_offset);

    for (u64 i = 0; i < pg_array_len(node->nodes); i++)
      par_ast_fprint_node(parser, node->nodes[i], file, indent + 2, arena);
    break;
  case AST_KIND_FIELD_ACCESS: {
    if (node->rhs == 0) // End of the chain.
    {
      pg_assert(node->main_token_i + 1 < pg_array_len(parser->lexer->tokens));
      const lex_token_t field = parser->lexer->tokens[node->main_token_i + 1];

      LOG("[%ld] %s .%.*s  : %.*s (at %.*s:%u:%u:%u)", node - parser->nodes,
          kind_string,
          lex_find_token_length(parser->lexer, parser->buf, parser->buf_len,
                                field),
          &parser->buf[field.source_offset], human_type.len, human_type.value,
          parser->lexer->file_path.len, parser->lexer->file_path.value, line,
          column, token.source_offset);
    } else {
      LOG("[%ld] %s %.*s : %.*s (at %.*s:%u:%u:%u)", node - parser->nodes,
          kind_string, token_string.len, token_string.value, human_type.len,
          human_type.value, parser->lexer->file_path.len,
          parser->lexer->file_path.value, line, column, token.source_offset);
    }
  }
    par_ast_fprint_node(parser, node->lhs, file, indent + 2, arena);
    par_ast_fprint_node(parser, node->rhs, file, indent + 2, arena);

    break;

  default:
    LOG("[%ld] %s %.*s : %.*s (at %.*s:%u:%u:%u)", node - parser->nodes,
        kind_string, token_string.len, token_string.value, human_type.len,
        human_type.value, parser->lexer->file_path.len,
        parser->lexer->file_path.value, line, column, token.source_offset);
    par_ast_fprint_node(parser, node->lhs, file, indent + 2, arena);
    par_ast_fprint_node(parser, node->rhs, file, indent + 2, arena);
    break;
  }
#endif
}

static bool par_is_at_end(const par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return parser->tokens_i == pg_array_len(parser->lexer->tokens);
}

static u32 par_declare_variable(par_parser_t *parser, string_t name, u32 node_i,
                                arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->scope_depth > 0);
  pg_assert(parser->variables != NULL);

  pg_assert(pg_array_len(parser->variables) < UINT32_MAX);

  const par_variable_t variable = {
      .name = name,
      .scope_depth = parser->scope_depth,
      .var_definition_node_i = node_i,
  };
  pg_array_append(parser->variables, variable, arena);
  return pg_array_last_index(parser->variables);
}

static u32 par_find_variable(const par_parser_t *parser, string_t name) {
  pg_assert(parser != NULL);
  pg_assert(parser->scope_depth > 0);
  pg_assert(parser->variables != NULL);

  for (i64 i = pg_array_len(parser->variables) - 1; i >= 0; i--) {
    const par_variable_t *const variable = &parser->variables[i];
    if (string_eq(name, variable->name))
      return (u32)i;
  }

  return -1;
}

static lex_token_t par_peek_token(const par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return parser->lexer->tokens[parser->tokens_i];
}

static void par_advance_token(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  // TODO: should we clamp it to the length?
  parser->tokens_i++;
}

static bool par_match_token(par_parser_t *parser, lex_token_kind_t kind) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (par_peek_token(parser).kind == kind) {
    par_advance_token(parser);
    return true;
  }
  return false;
}

static void par_error(par_parser_t *parser, lex_token_t token,
                      const char *error) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  switch (parser->state) {
  case PARSER_STATE_OK: {
    u32 line = 0;
    u32 column = 0;
    string_t token_string = {0};
    par_find_token_position(parser, token, &line, &column, &token_string);

    fprintf(stderr, "%.*s:%u:%u: around `%.*s`, %s\n",
            parser->lexer->file_path.len, parser->lexer->file_path.value, line,
            column, token_string.len, token_string.value, error);

    parser->state = PARSER_STATE_ERROR;
    break;
  }
  case PARSER_STATE_ERROR:
    parser->state = PARSER_STATE_PANIC;
    break;
  case PARSER_STATE_PANIC:
  case PARSER_STATE_SYNCED:
    break;
  }
}

static void par_expect_token(par_parser_t *parser, lex_token_kind_t kind,
                             const char *error) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (!par_match_token(parser, kind)) {
    par_error(parser, par_peek_token(parser), error);
  }
}

static const u8 NUMBER_FLAGS_OVERFLOW = 0x1;
static const u8 NUMBER_FLAGS_LONG = 0x2;

static u64 par_number(const par_parser_t *parser, lex_token_t token,
                      u8 *number_flags) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));
  pg_assert(number_flags != NULL);

  pg_assert(token.kind == TOKEN_KIND_NUMBER);

  const u32 start = token.source_offset;
  const u32 length = lex_number_length(parser->buf, parser->buf_len, start);
  pg_assert(length <= 20);

  u64 number = 0;

  u64 ten_unit = 1;
  for (u32 i = 1; i <= length; i++) {
    pg_assert(i < parser->buf_len);

    const u32 position = start + length - i;
    pg_assert(start <= position);

    const u8 c = parser->buf[position];
    pg_assert(lex_is_digit(c) || c == 'L' || c == '_');
    if (c == '_')
      continue;
    if (c == 'L') {
      *number_flags |= NUMBER_FLAGS_LONG;
      continue;
    }

    const u64 delta = ten_unit * (c - '0');
    i64 number_i64 = (i64)number;
    if (__builtin_add_overflow((i64)number_i64, delta, &number_i64)) {
      *number_flags |= NUMBER_FLAGS_OVERFLOW;
      return 0;
    }
    number += delta;
    ten_unit *= 10;
  }

  return number;
}

static string_t par_token_to_string(par_parser_t *parser, u32 token_i) {
  pg_assert(parser != NULL);
  pg_assert(token_i < pg_array_len(parser->lexer->tokens));

  const lex_token_t token = parser->lexer->tokens[token_i];

  return (string_t){
      .value = &parser->buf[token.source_offset],
      .len = lex_find_token_length(parser->lexer, parser->buf, parser->buf_len,
                                   token),
  };
}

static u32 par_parse_expression(par_parser_t *parser, arena_t *arena);
static u32 par_parse_block(par_parser_t *parser, arena_t *arena);
static u32 par_parse_postfix_unary_expression(par_parser_t *parser,
                                              arena_t *arena);
static u32 par_parse_statements(par_parser_t *parser, arena_t *arena);
static u32 par_parse_declaration(par_parser_t *parser, arena_t *arena);
static u32 par_parse_statement(par_parser_t *parser, arena_t *arena);

static u32 par_parse_builtin_println(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  par_expect_token(parser, TOKEN_KIND_LEFT_PAREN, "expected left parenthesis");

  par_ast_node_t node = {
      .kind = AST_KIND_BUILTIN_PRINTLN,
      .main_token_i = parser->tokens_i - 2,
      .lhs = par_parse_expression(parser, arena),
  };
  const u32 node_i = par_add_node(parser, &node, arena);

  par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                   "expected right parenthesis");
  return node_i;
}

// block:
//     '{'
//     {NL}
//     statements
//     {NL}
//     '}'
static u32 par_parse_block(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  par_expect_token(parser, TOKEN_KIND_LEFT_BRACE,
                   "Expected a left curly brace to start a block");
  par_begin_scope(parser);
  const u32 node_i = par_parse_statements(parser, arena);
  par_end_scope(parser);
  par_expect_token(parser, TOKEN_KIND_RIGHT_BRACE,
                   "Expected a right curly brace to end a block");
  return node_i;
}

// controlStructureBody:
//     block
//     | statement
static u32 par_parse_control_structure_body(par_parser_t *parser,
                                            arena_t *arena) {
  pg_assert(parser);
  pg_assert(arena);

  if (par_peek_token(parser).kind == TOKEN_KIND_LEFT_BRACE)
    return par_parse_block(parser, arena);
  else
    return par_parse_statement(parser, arena);
}

//  'if'
//  {NL}
//  '('
//  {NL}
//  expression
//  {NL}
//  ')'
//  {NL}
//  (controlStructureBody | ([controlStructureBody] {NL} [';'] {NL} 'else' {NL}
//  (controlStructureBody | ';')) | ';')
static u32 par_parse_if_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 main_token_i = parser->tokens_i - 1;

  par_expect_token(parser, TOKEN_KIND_LEFT_PAREN,
                   "expected left parenthesis following if");

  const u32 condition_i = par_parse_expression(parser, arena);

  par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                   "expected right parenthesis following if condition");

  // clang-format off
  //
  //               IF 
  //              /  \
  //    condition     BINARY )
  //                 /      \
  //             then        else
  //
  // clang-format on

  const par_ast_node_t binary_node = {
      .kind = AST_KIND_BINARY,
      .main_token_i = parser->tokens_i - 1,
      .lhs = par_parse_control_structure_body(parser, arena), // Then
      .rhs = par_match_token(parser, TOKEN_KIND_KEYWORD_ELSE)
                 ? par_parse_control_structure_body(parser, arena)
                 : 0,
  };
  const u32 binary_node_i = par_add_node(parser, &binary_node, arena);

  const par_ast_node_t if_node = {
      .kind = AST_KIND_IF,
      .main_token_i = main_token_i,
      .lhs = condition_i,
      .rhs = binary_node_i,
  };
  return par_add_node(parser, &if_node, arena);
}

static string_t ty_know_type_aliases(string_t type_literal, arena_t *arena);

// primaryExpression:
//     parenthesizedExpression
//     | simpleIdentifier
//     | literalConstant
//     | stringLiteral
//     | callableReference
//     | functionLiteral
//     | objectLiteral
//     | collectionLiteral
//     | thisExpression
//     | superExpression
//     | ifExpression
//     | whenExpression
//     | tryExpression
//     | jumpExpression
static u32 par_parse_primary_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (par_match_token(parser, TOKEN_KIND_NUMBER)) {

    const par_ast_node_t node = {
        .kind = AST_KIND_NUMBER,
        .main_token_i = parser->tokens_i - 1,
    };
    return par_add_node(parser, &node, arena);
  } else if (par_match_token(parser, TOKEN_KIND_KEYWORD_FALSE) ||
             par_match_token(parser, TOKEN_KIND_KEYWORD_TRUE)) {
    const lex_token_t token = parser->lexer->tokens[parser->tokens_i - 1];
    const bool is_true = parser->buf[token.source_offset] == 't';
    const par_ast_node_t node = {
        .kind = AST_KIND_BOOL,
        .main_token_i = parser->tokens_i - 1,
        .lhs = is_true,
    };
    return par_add_node(parser, &node, arena);
  } else if (par_match_token(parser, TOKEN_KIND_BUILTIN_PRINTLN)) {
    return par_parse_builtin_println(parser, arena);
  } else if (par_match_token(parser, TOKEN_KIND_LEFT_PAREN)) {
    const u32 node_i = par_parse_expression(parser, arena);
    // TODO: Locate left parenthesis for the error message.
    par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                     "Expected matching right parenthesis");
    return node_i;
  } else if (par_match_token(parser, TOKEN_KIND_IDENTIFIER)) {

    const u32 main_token_i = parser->tokens_i - 1;
    const string_t name = par_token_to_string(parser, main_token_i);
    const u32 variable_i = par_find_variable(parser, name);
    if (variable_i == (u32)-1) {

      const string_t alternate_name = ty_know_type_aliases(name, arena);
      u32 class_file_i = 0;
      u16 constant_pool_class_name_i = 0;
      // TODO: Should we move the resolution to the type checking phase?
      if (!cf_class_files_find_class_exactly(parser->class_files, name,
                                             alternate_name, &class_file_i,
                                             &constant_pool_class_name_i)) {
        par_error(parser, parser->lexer->tokens[main_token_i],
                  "unknown reference to variable");
        return 0;
      }

      par_ast_node_t node = {
          .kind = AST_KIND_CLASS_REFERENCE,
          .main_token_i = parser->tokens_i - 1,
          .class_file_i = class_file_i,
          .constant_pool_class_name_i = constant_pool_class_name_i,
      };
      return par_add_node(parser, &node, arena);
    }
    par_ast_node_t node = {
        .kind = AST_KIND_VAR_REFERENCE,
        .main_token_i = parser->tokens_i - 1,
        .lhs = parser->variables[variable_i].var_definition_node_i,
    };
    return par_add_node(parser, &node, arena);
  } else if (par_match_token(parser, TOKEN_KIND_STRING_LITERAL)) {
    const par_ast_node_t node = {.kind = AST_KIND_STRING,
                                 .main_token_i = parser->tokens_i - 1};
    return par_add_node(parser, &node, arena);
  } else if (par_match_token(parser, TOKEN_KIND_KEYWORD_IF)) {
    return par_parse_if_expression(parser, arena);
  }

  return 0;
}

// multiVariableDeclaration:
//     '('
//     {NL}
//     variableDeclaration
//     {{NL} ',' {NL} variableDeclaration}
//     [{NL} ',']
//     {NL}
//     ')'
static u32 par_parse_var_declaration(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  par_expect_token(parser, TOKEN_KIND_IDENTIFIER,
                   "expected variable name (identifier)");
  const u32 name_token_i = parser->tokens_i - 1;

  const u32 previous_var_i =
      par_find_variable(parser, par_token_to_string(parser, name_token_i));
  if (previous_var_i != (u32)-1) {
    pg_assert(previous_var_i < pg_array_len(parser->variables));
    const par_variable_t *const previous_var =
        &parser->variables[previous_var_i];

    pg_assert(previous_var->var_definition_node_i > 0);
    pg_assert(previous_var->var_definition_node_i <
              pg_array_len(parser->nodes));
    const par_ast_node_t *const previous_var_node =
        &parser->nodes[previous_var->var_definition_node_i];

    const lex_token_t previous_var_name_token =
        parser->lexer->tokens[previous_var_node->main_token_i];

    u32 line = 0;
    u32 column = 0;
    string_t token_string = {0};
    par_find_token_position(parser, previous_var_name_token, &line, &column,
                            &token_string);
    char error[256] = {0};
    snprintf(error, 255, "variable shadowing, already declared at %u:%u", line,
             column);
    par_error(parser, parser->lexer->tokens[name_token_i], error);
    return 0;
  }

  par_expect_token(parser, TOKEN_KIND_COLON,
                   "expected colon between variable name and type");

  par_expect_token(parser, TOKEN_KIND_IDENTIFIER, "expected type");

  par_expect_token(parser, TOKEN_KIND_EQUAL, "expected type");

  const par_ast_node_t node = {
      .kind = AST_KIND_VAR_DEFINITION,
      .main_token_i = name_token_i,
      .lhs = par_parse_expression(parser, arena),
  };
  const u32 node_i = par_add_node(parser, &node, arena);

  const string_t variable_name = par_token_to_string(parser, name_token_i);
  par_declare_variable(parser, variable_name, node_i, arena);
  return node_i;
}

static bool par_is_lvalue(const par_parser_t *parser, u32 node_i) {
  pg_assert(parser != NULL);

  const par_ast_node_t *const node = &parser->nodes[node_i];
  switch (node->kind) {
  case AST_KIND_VAR_REFERENCE:
    return true;
    // TODO: more

  default:
    return false;
  }
}

// assignment:
//     ((directlyAssignableExpression '=') | (assignableExpression
//     assignmentAndOperator)) {NL} expression
static u32 par_parse_assignment(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  // We could here try to parse a `directlyAssignableExpression`, and if it
  // fails, or if it succeeds but the next token is *not* `TOKEN_KIND_EQUAL`,
  // backtrack.
  // But that potentially means we are parsing twice every
  // expression and lots of expensive cloning/resetting.
  // Instead, we first parse it as an expression, and if the next
  // token is `TOKEN_KIND_EQUAL`, we check that this expression was indeed a
  // lvalue. Otherwise, we just return this expression, no more work to do.
  u32 lhs_i = par_parse_expression(parser, arena);

  if (par_match_token(parser, TOKEN_KIND_EQUAL)) { // Assignment
    const u32 main_token_i = parser->tokens_i - 1;

    if (!par_is_lvalue(parser, lhs_i)) {
      par_error(
          parser, parser->lexer->tokens[main_token_i],
          "The assignment target is not a lvalue (such as a local variable)");
    }

    const par_ast_node_t node = {
        .kind = AST_KIND_BINARY,
        .lhs = lhs_i,
        .main_token_i = main_token_i,
        .rhs = par_parse_expression(parser, arena),
    };
    return par_add_node(parser, &node, arena);
  }

  return lhs_i;
}

// whileStatement:
//     'while'
//     {NL}
//     '('
//     expression
//     ')'
//     {NL}
//     (controlStructureBody | ';')
static u32 par_parse_while_statement(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  const u32 main_token_i = parser->tokens_i - 1;
  par_expect_token(parser, TOKEN_KIND_LEFT_PAREN,
                   "Expect left parenthesis after the while keyword");

  const u32 condition_i = par_parse_expression(parser, arena);

  par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                   "Expect right parenthesis after the while condition");

  const par_ast_node_t node = {
      .kind = AST_KIND_WHILE_LOOP,
      .main_token_i = main_token_i,
      .lhs = condition_i,
  };
  const u32 node_i = par_add_node(parser, &node, arena);

  parser->nodes[node_i].rhs = par_parse_control_structure_body(parser, arena);

  return node_i;
}

static u32 par_parse_loop_statement(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  if (par_match_token(parser, TOKEN_KIND_KEYWORD_WHILE))
    return par_parse_while_statement(parser, arena);

  return 0;
}

// statement:
//     {label | annotation} (declaration | assignment | loopStatement |
//     expression)
static u32 par_parse_statement(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (parser->current_function_i == 0) {
    par_error(parser, par_peek_token(parser),
              "code outside of a function body");
  }

  u32 node_i = 0;
  if ((node_i = par_parse_loop_statement(parser, arena)) != 0)
    return node_i;

  if ((node_i = par_parse_declaration(parser, arena)) != 0)
    return node_i;

  if ((node_i = par_parse_assignment(parser, arena)) != 0)
    return node_i;

  return par_parse_expression(parser, arena);
}

// navigationSuffix:
//     memberAccessOperator {NL} (simpleIdentifier | parenthesizedExpression |
//     'class')
static u32 par_parse_navigation_suffix(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (par_match_token(parser, TOKEN_KIND_IDENTIFIER)) {
    return 0; // No need to create a new node.
  }

  if (par_match_token(parser, TOKEN_KIND_LEFT_PAREN)) {
    const u32 node_i = par_parse_expression(parser, arena);
    par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                     "Expected matching right parenthesis after expression");
    return node_i;
  }

  pg_assert(0 && "todo"); // TODO: `class`
}

// postfixUnaryExpression:
//     primaryExpression {postfixUnarySuffix}
static u32 par_parse_postfix_unary_expression(par_parser_t *parser,
                                              arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 lhs_i = par_parse_primary_expression(parser, arena);

  if (!par_match_token(parser, TOKEN_KIND_DOT))
    return lhs_i;

  const u32 main_token_i = parser->tokens_i - 1;
  const u32 rhs_i = par_parse_navigation_suffix(parser, arena);

  const par_ast_node_t node = {
      .kind = AST_KIND_FIELD_ACCESS,
      .main_token_i = main_token_i,
      .lhs = lhs_i,
      .rhs = rhs_i,
  };
  return par_add_node(parser, &node, arena);
}

// prefixUnaryExpression:
//     {unaryPrefix} postfixUnaryExpression
static u32 par_parse_prefix_unary_expression(par_parser_t *parser,
                                             arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (par_match_token(parser, TOKEN_KIND_NOT) ||
      par_match_token(parser, TOKEN_KIND_MINUS)) {
    const par_ast_node_t node = {
        .kind = AST_KIND_UNARY,
        // Departure from the official grammer but I believe it must be (!?)
        // to allow for `!!true`
        .lhs = par_parse_prefix_unary_expression(parser, arena),
        .main_token_i = parser->tokens_i - 1,
    };
    return par_add_node(parser, &node, arena);
  }

  return par_parse_postfix_unary_expression(parser, arena);
}

// asExpression:
//     prefixUnaryExpression {{NL} asOperator {NL} type}
static u32 par_parse_as_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_prefix_unary_expression(parser, arena);
}

// multiplicativeExpression:
//     asExpression {multiplicativeOperator {NL} asExpression}
static u32 par_parse_multiplicative_expression(par_parser_t *parser,
                                               arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 node_i = par_parse_as_expression(parser, arena);
  if (!(par_match_token(parser, TOKEN_KIND_STAR) ||
        par_match_token(parser, TOKEN_KIND_SLASH) ||
        par_match_token(parser, TOKEN_KIND_PERCENT)))
    return node_i;

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = node_i,
      .main_token_i = parser->tokens_i - 1,
      .rhs = par_parse_multiplicative_expression(parser, arena),
  };
  return par_add_node(parser, &node, arena);
}

// additiveExpression:
//     multiplicativeExpression {additiveOperator {NL}
//     multiplicativeExpression}
static u32 par_parse_additive_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 node_i = par_parse_multiplicative_expression(parser, arena);
  if (!(par_match_token(parser, TOKEN_KIND_PLUS) ||
        par_match_token(parser, TOKEN_KIND_MINUS)))
    return node_i;

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = node_i,
      .main_token_i = parser->tokens_i - 1,
      .rhs = par_parse_additive_expression(parser, arena),
  };
  return par_add_node(parser, &node, arena);
}

// rangeExpression:
//     additiveExpression {'..' {NL} additiveExpression}
static u32 par_parse_range_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_additive_expression(parser, arena);
}

// infixFunctionCall:
//     rangeExpression {simpleIdentifier {NL} rangeExpression}
static u32 par_parse_infix_function_call(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_range_expression(parser, arena);
}

// elvisExpression:
//     infixFunctionCall {{NL} elvis {NL} infixFunctionCall}
static u32 par_parse_elvis_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_infix_function_call(parser, arena);
}

// infixOperation:
//     elvisExpression {(inOperator {NL} elvisExpression) | (isOperator {NL}
//     type)}
static u32 par_parse_infix_operation(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_elvis_expression(parser, arena);
}

// genericCallLikeComparison:
//     infixOperation {callSuffix}
static u32 par_parse_generic_call_like_comparison(par_parser_t *parser,
                                                  arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_infix_operation(parser, arena);
}

// comparison:
//     genericCallLikeComparison {comparisonOperator {NL}
//     genericCallLikeComparison}
static u32 par_parse_comparison(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 node_i = par_parse_generic_call_like_comparison(parser, arena);
  if (!(par_match_token(parser, TOKEN_KIND_LT) ||
        par_match_token(parser, TOKEN_KIND_GT) ||
        par_match_token(parser, TOKEN_KIND_LE) ||
        par_match_token(parser, TOKEN_KIND_GE)))
    return node_i;

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = node_i,
      .main_token_i = parser->tokens_i - 1,
      .rhs = par_parse_comparison(parser, arena),
  };
  return par_add_node(parser, &node, arena);
}

// equality:
//     comparison {equalityOperator {NL} comparison}
static u32 par_parse_equality(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 node_i = par_parse_comparison(parser, arena);
  if (!(par_match_token(parser, TOKEN_KIND_EQUAL_EQUAL) ||
        par_match_token(parser, TOKEN_KIND_NOT_EQUAL)))
    return node_i;

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = node_i,
      .main_token_i = parser->tokens_i - 1,
      .rhs = par_parse_equality(parser, arena),
  };
  return par_add_node(parser, &node, arena);
}

// conjunction:
//     equality {{NL} '&&' {NL} equality}
static u32 par_parse_conjunction(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 node_i = par_parse_equality(parser, arena);
  if (!par_match_token(parser, TOKEN_KIND_AMPERSAND_AMPERSAND))
    return node_i;

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = node_i,
      .main_token_i = parser->tokens_i - 1,
      .rhs = par_parse_conjunction(parser, arena),
  };
  return par_add_node(parser, &node, arena);
}

// disjunction:
//     conjunction {{NL} '||' {NL} conjunction}
static u32 par_parse_disjunction(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 node_i = par_parse_conjunction(parser, arena);
  if (!par_match_token(parser, TOKEN_KIND_PIPE_PIPE))
    return node_i;

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = node_i,
      .main_token_i = parser->tokens_i - 1,
      .rhs = par_parse_disjunction(parser, arena),
  };
  return par_add_node(parser, &node, arena);
}

// expression:
//     disjunction
static u32 par_parse_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_disjunction(parser, arena);
}

// statements:
//     [statement {semis statement}] [semis]
static u32 par_parse_statements(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (par_peek_token(parser).kind == TOKEN_KIND_RIGHT_BRACE)
    return 0;

  u32 node_i = par_parse_statement(parser, arena);
  if (node_i == 0)
    return node_i;

  par_ast_node_t node = {.kind = AST_KIND_LIST};
  pg_array_init_reserve(node.nodes, 128, arena);
  pg_array_append(node.nodes, node_i, arena);

  while ((node_i = par_parse_statement(parser, arena)) != 0)
    pg_array_append(node.nodes, node_i, arena);

  return par_add_node(parser, &node, arena);
}

static u32 par_parse_function_value_parameters(par_parser_t *parser,
                                               arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  // No arguments.
  if (par_match_token(parser, TOKEN_KIND_RIGHT_PAREN))
    return 0;

  par_ast_node_t node = {.kind = AST_KIND_LIST};
  pg_array_init_reserve(node.nodes, 128, arena);

  const u32 root_i = par_add_node(parser, &node, arena);
  do {
    pg_array_append(node.nodes, par_parse_expression(parser, arena), arena);
  } while (par_match_token(parser, TOKEN_KIND_COMMA));

  par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                   "expected right parenthesis after the arguments");
  return root_i;
}

// functionBody:
//     block
//     | ('=' {NL} expression)
static u32 par_parse_function_body(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  return par_parse_block(parser, arena);
}

// functionDeclaration:
//     [modifiers]
//     'fun'
//     [{NL} typeParameters]
//     [{NL} receiverType {NL} '.']
//     {NL}
//     simpleIdentifier
//     {NL}
//     functionValueParameters
//     [{NL} ':' {NL} type]
//     [{NL} typeConstraints]
//     [{NL} functionBody]
static u32 par_parse_function_declaration(par_parser_t *parser,
                                          arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (!par_match_token(parser, TOKEN_KIND_KEYWORD_FUN))
    return 0;

  par_expect_token(parser, TOKEN_KIND_IDENTIFIER,
                   "expected function name (identifier)");
  const u32 start_token = parser->tokens_i - 1;

  const par_ast_node_t node = {
      .kind = AST_KIND_FUNCTION_DEFINITION,
      .main_token_i = start_token,
  };

  const u32 fn_i = parser->current_function_i =
      par_add_node(parser, &node, arena);

  par_expect_token(parser, TOKEN_KIND_LEFT_PAREN,
                   "expected left parenthesis before the arguments");
  parser->nodes[parser->current_function_i].lhs =
      par_parse_function_value_parameters(parser, arena);

  parser->nodes[parser->current_function_i].rhs =
      par_parse_function_body(parser, arena);
  parser->current_function_i = 0;

  return fn_i;
}

static void par_sync_if_panicked(par_parser_t *parser) {
  pg_assert(parser != NULL);

  if (parser->state != PARSER_STATE_PANIC)
    return; // Nothing to do.

  parser->state = PARSER_STATE_SYNCED;

  while (!par_is_at_end(parser)) {
    // TODO: sync at newlines?

    switch (par_peek_token(parser).kind) {
    case TOKEN_KIND_BUILTIN_PRINTLN:
    case TOKEN_KIND_KEYWORD_FUN:
      return;
    default:; // Do nothing.
    }

    par_advance_token(parser);
  }
}

// propertyDeclaration:
//     [modifiers]
//     ('val' | 'var')
//     [{NL} typeParameters]
//     [{NL} receiverType {NL} '.']
//     ({NL} (multiVariableDeclaration | variableDeclaration))
//     [{NL} typeConstraints]
//     [{NL} (('=' {NL} expression) | propertyDelegate)]
//     [(NL {NL}) ';']
//     {NL}
//     (([getter] [{NL} [semi] setter]) | ([setter] [{NL} [semi] getter]))
static u32 par_parse_property_declaration(par_parser_t *parser,
                                          arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  if (par_match_token(parser, TOKEN_KIND_KEYWORD_VAR))
    return par_parse_var_declaration(parser, arena);

  return 0;
}

// declaration:
//     classDeclaration
//     | objectDeclaration
//     | functionDeclaration
//     | propertyDeclaration
//     | typeAlias
static u32 par_parse_declaration(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  u32 new_node_i = 0;
  if ((new_node_i = par_parse_function_declaration(parser, arena)) != 0)
    return new_node_i;

  if ((new_node_i = par_parse_property_declaration(parser, arena)) != 0)
    return new_node_i;

  par_sync_if_panicked(parser);

  return new_node_i;
}

// topLevelObject: declaration [semis]
static u32 par_parse(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));
  pg_assert(pg_array_len(parser->lexer->tokens) >= 1);

  pg_array_init_reserve(parser->nodes, pg_array_len(parser->lexer->tokens) * 8,
                        arena);
  pg_array_init_reserve(parser->variables, 256, arena);

  parser->tokens_i = 1; // Skip the dummy token.

  const par_ast_node_t dummy_node = {0};
  par_add_node(parser, &dummy_node, arena);

  const u32 root_i = par_parse_declaration(parser, arena);

  pg_array_init_reserve(parser->types, pg_array_len(parser->nodes) + 32, arena);
  pg_array_append(parser->types, (ty_type_t){0}, arena); // Default value.
  return root_i;
}

// --------------------------------- Typing

// TODO: Something smarter.
// TODO: Find a better name.
static bool ty_merge_types(const ty_type_t *types, u32 lhs_i, u32 rhs_i,
                           u32 *result_i) {
  pg_assert(types != NULL);
  pg_assert(lhs_i < pg_array_len(types));
  pg_assert(rhs_i < pg_array_len(types));
  pg_assert(result_i != NULL);

  const ty_type_t *const lhs = &types[lhs_i];
  const ty_type_t *const rhs = &types[rhs_i];
  if (lhs->kind == rhs->kind) {
    *result_i = lhs_i;
    return true;
  }

  // Any is compatible with everything.
  if (lhs->kind == TYPE_ANY) {
    *result_i = rhs_i;
    return true;
  }

  // Any is compatible with everything.
  if (rhs->kind == TYPE_ANY) {
    *result_i = lhs_i;
    return true;
  }

  return false;
}

static u32 ty_add_type(ty_type_t **types, const ty_type_t *type,
                       arena_t *arena) {
  pg_assert(types != NULL);
  pg_assert(type != NULL);

  // TODO: Deduplicate.
  pg_array_append(*types, *type, arena);
  return pg_array_last_index(*types);
}

static string_t ty_know_type_aliases(string_t type_literal, arena_t *arena) {
  if (string_eq_c(type_literal, "Int"))
    return string_make_from_c_no_alloc("java/lang/Integer");
  if (string_eq_c(type_literal, "Short"))
    return string_make_from_c_no_alloc("java/lang/Short");
  if (string_eq_c(type_literal, "Byte"))
    return string_make_from_c_no_alloc("java/lang/Byte");
  if (string_eq_c(type_literal, "Char"))
    return string_make_from_c_no_alloc("java/lang/Char");
  if (string_eq_c(type_literal, "Boolean"))
    return string_make_from_c_no_alloc("java/lang/Boolean");
  if (string_eq_c(type_literal, "Long"))
    return string_make_from_c_no_alloc("java/lang/Long");
  if (string_eq_c(type_literal, "Float"))
    return string_make_from_c_no_alloc("java/lang/Float");
  if (string_eq_c(type_literal, "Double"))
    return string_make_from_c_no_alloc("java/lang/Double");

  string_t res = string_make_from_c("java/lang/", arena);
  string_append_string(&res, type_literal, arena);
  return res;
}

typedef struct {
  par_parser_t *parser;
  u32 class_file_i;
  u16 constant_pool_class_name_i;
  pg_pad(2);
} resolver_t;

static u32 ty_resolve_types(resolver_t *resolver, u32 node_i, arena_t *arena) {
  pg_assert(resolver != NULL);
  pg_assert(resolver->parser != NULL);
  pg_assert(resolver->parser->class_files != NULL);
  pg_assert(node_i < pg_array_len(resolver->parser->nodes));

  par_ast_node_t *const node = &resolver->parser->nodes[node_i];
  const lex_token_t token = resolver->parser->lexer->tokens[node->main_token_i];

  switch (node->kind) {
  case AST_KIND_NONE:
    pg_array_append(resolver->parser->types, (ty_type_t){.kind = TYPE_ANY},
                    arena);

    return node->type_i = pg_array_last_index(resolver->parser->types);
  case AST_KIND_BOOL:
    pg_array_append(resolver->parser->types, (ty_type_t){.kind = TYPE_BOOL},
                    arena);
    return node->type_i = pg_array_last_index(resolver->parser->types);
  case AST_KIND_BUILTIN_PRINTLN: {
    ty_resolve_types(resolver, node->lhs, arena);

    const par_ast_node_t *const lhs = &resolver->parser->nodes[node->lhs];
    const ty_type_t *const lhs_type = &resolver->parser->types[lhs->type_i];

    const ty_type_t void_type = {.kind = TYPE_VOID};
    const u32 return_type_i =
        ty_add_type(&resolver->parser->types, &void_type, arena);
    const ty_type_t println_type = {
        .kind = TYPE_METHOD,
        .v = {.method = {
                  .argument_count = 1,
                  .return_type_i = return_type_i,
                  .argument_types_i =
                      ty_add_type(&resolver->parser->types, lhs_type, arena),
              }}};
    pg_array_append(resolver->parser->types, println_type, arena);
    node->type_i = pg_array_last_index(resolver->parser->types);

    string_t method_descriptor = {0};
    if (lhs_type->kind == TYPE_INSTANCE_REFERENCE) {
      method_descriptor = string_make_from_c_no_alloc("(Ljava/lang/Object;)V");
    } else {
      method_descriptor = string_reserve(64, arena);
      cf_fill_type_descriptor_string(
          resolver->parser->types, pg_array_last_index(resolver->parser->types),
          &method_descriptor, arena);
    }

    pg_array_last(resolver->parser->types)->v.method.descriptor =
        method_descriptor;

    if (!cf_class_files_find_method_exactly(
            resolver->parser->class_files,
            string_make_from_c_no_alloc("java/io/PrintStream"),
            string_make_from_c_no_alloc("println"), method_descriptor)) {
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error, "incompatible types: ", arena);
      string_append_string(
          &error,
          ty_type_to_human_string(resolver->parser->types, node->type_i, arena),
          arena);
      string_append_cstring(&error, " vs ", arena);
      string_append_string(
          &error,
          ty_type_to_human_string(resolver->parser->types, lhs->type_i, arena),
          arena);
      par_error(resolver->parser, token, error.value);
    }

    return return_type_i;
  }
  case AST_KIND_NUMBER: {
    cf_type_kind_t kind = TYPE_INT;

    u8 number_flags = 0;
    // TODO: should we memoize this to avoid parsing it twice?
    const u64 number = par_number(resolver->parser, token, &number_flags);
    if (number_flags & NUMBER_FLAGS_OVERFLOW) {
      par_error(resolver->parser, token,
                "Long literal is too big (> 9223372036854775807)");
      return 0;

    } else if (number_flags & NUMBER_FLAGS_LONG) {
      kind = TYPE_LONG;
    } else {
      if (number > INT32_MAX) {
        par_error(resolver->parser, token,
                  "Integer literal is too big (> 2147483647)");
        return 0;
      }
    }

    pg_array_append(resolver->parser->types, (ty_type_t){.kind = kind},
                    arena); // TODO: something smarter.
    return node->type_i = pg_array_last_index(resolver->parser->types);
  }
  case AST_KIND_UNARY:
    switch (token.kind) {
    case TOKEN_KIND_NOT:
      node->type_i = ty_resolve_types(resolver, node->lhs, arena);
      const ty_type_t *const type = &resolver->parser->types[node->type_i];
      if (type->kind != TYPE_BOOL) {
        string_t error = string_reserve(256, arena);
        string_append_cstring(&error, "incompatible types: got ", arena);
        string_append_string(&error,
                             ty_type_to_human_string(resolver->parser->types,
                                                     node->type_i, arena),
                             arena);
        string_append_cstring(&error, ", expected Boolean ", arena);
        par_error(resolver->parser, token, error.value);
        return 0;
      }

      return node->type_i;

    case TOKEN_KIND_MINUS:
      return node->type_i = ty_resolve_types(resolver, node->lhs, arena);

    default:
      pg_assert(0 && "todo");
    }
  case AST_KIND_BINARY: {
    pg_assert(node->main_token_i > 0);

    const u32 lhs_i = ty_resolve_types(resolver, node->lhs, arena);
    const u32 rhs_i = ty_resolve_types(resolver, node->rhs, arena);

    if (!ty_merge_types(resolver->parser->types, lhs_i, rhs_i, &node->type_i)) {
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error, "incompatible types: ", arena);
      string_append_string(
          &error,
          ty_type_to_human_string(resolver->parser->types, lhs_i, arena),
          arena);
      string_append_cstring(&error, " vs ", arena);
      string_append_string(
          &error,
          ty_type_to_human_string(resolver->parser->types, rhs_i, arena),
          arena);
      par_error(resolver->parser, token, error.value);
    }

    switch (token.kind) {
    case TOKEN_KIND_LT:
    case TOKEN_KIND_LE:
    case TOKEN_KIND_GT:
    case TOKEN_KIND_GE:
    case TOKEN_KIND_NOT_EQUAL:
    case TOKEN_KIND_EQUAL_EQUAL: {
      pg_array_append(resolver->parser->types, (ty_type_t){.kind = TYPE_BOOL},
                      arena);
      return node->type_i = pg_array_last_index(resolver->parser->types);
    }
    case TOKEN_KIND_AMPERSAND_AMPERSAND:
    case TOKEN_KIND_PIPE_PIPE: {
      const cf_type_kind_t type_kind = resolver->parser->types[lhs_i].kind;
      if (type_kind != TYPE_BOOL) {
        string_t error = string_reserve(256, arena);
        string_append_cstring(
            &error, "incompatible types: expected Boolean, got: ", arena);
        string_append_string(
            &error,
            ty_type_to_human_string(resolver->parser->types, lhs_i, arena),
            arena);
        par_error(resolver->parser, token, error.value);
      }
      return 0;
    }
      return node->type_i;
    default:
      return node->type_i;
    }
  }
  case AST_KIND_LIST: {
    for (u64 i = 0; i < pg_array_len(node->nodes); i++)
      ty_resolve_types(resolver, node->nodes[i], arena);

    pg_array_append(resolver->parser->types, (ty_type_t){.kind = TYPE_VOID},
                    arena);

    return node->type_i = pg_array_last_index(resolver->parser->types);
  }
  case AST_KIND_FUNCTION_DEFINITION:
    ty_resolve_types(resolver, node->lhs, arena);
    // Inspect body (rhs).
    ty_resolve_types(resolver, node->rhs, arena);

    pg_array_append(resolver->parser->types, (ty_type_t){.kind = TYPE_VOID},
                    arena);
    return node->type_i = pg_array_last_index(resolver->parser->types);

  case AST_KIND_VAR_DEFINITION: {
    const string_t type_literal_string =
        par_token_to_string(resolver->parser, node->main_token_i + 2);

    const string_t alternate_type_string =
        ty_know_type_aliases(type_literal_string, arena);

    if (!cf_class_files_find_class_exactly(resolver->parser->class_files,
                                           type_literal_string,
                                           alternate_type_string, NULL, NULL)) {
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error, "unknown type: ", arena);
      string_append_string(&error, type_literal_string, arena);

      par_error(resolver->parser, token, error.value);
      return 0;
    }

    const u32 type_lhs_i = ty_resolve_types(resolver, node->lhs, arena);

    const string_t type_inferred_string =
        ty_type_to_human_string(resolver->parser->types, type_lhs_i, arena);

    if (!string_eq(type_literal_string, type_inferred_string)) {
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error, "incompatible types: ", arena);
      string_append_string(&error, type_literal_string, arena);
      string_append_cstring(&error, " vs ", arena);
      string_append_string(&error, type_inferred_string, arena);
      par_error(resolver->parser, token, error.value);
    }

    return node->type_i = type_lhs_i;
  }
  case AST_KIND_VAR_REFERENCE: {
    pg_assert(node->lhs > 0);
    return node->type_i = resolver->parser->nodes[node->lhs].type_i;
  }
  case AST_KIND_IF: {
    pg_assert(node->lhs > 0);
    pg_assert(node->lhs < pg_array_len(resolver->parser->nodes));
    pg_assert(node->rhs > 0);
    pg_assert(node->rhs < pg_array_len(resolver->parser->nodes));

    const u32 type_condition_i = ty_resolve_types(resolver, node->lhs, arena);

    if (resolver->parser->types[type_condition_i].kind != TYPE_BOOL) {
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error,
                            "incompatible types, expect Boolean, got: ", arena);

      const string_t type_inferred_string = ty_type_to_human_string(
          resolver->parser->types, type_condition_i, arena);
      string_append_string(&error, type_inferred_string, arena);
      par_error(resolver->parser, token, error.value);
    }

    const u32 type_then_else_i = ty_resolve_types(resolver, node->rhs, arena);
    pg_assert(type_then_else_i > 0);

    return node->type_i = type_then_else_i;
  }
  case AST_KIND_WHILE_LOOP: {
    pg_assert(node->lhs > 0);
    pg_assert(node->lhs < pg_array_len(resolver->parser->nodes));
    pg_assert(node->rhs > 0);
    pg_assert(node->rhs < pg_array_len(resolver->parser->nodes));

    const u32 type_condition_i = ty_resolve_types(resolver, node->lhs, arena);

    if (resolver->parser->types[type_condition_i].kind != TYPE_BOOL) {
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error,
                            "incompatible types, expect Boolean, got: ", arena);

      const string_t type_inferred_string = ty_type_to_human_string(
          resolver->parser->types, type_condition_i, arena);
      string_append_string(&error, type_inferred_string, arena);
      par_error(resolver->parser, token, error.value);
    }

    ty_resolve_types(resolver, node->rhs, arena);

    pg_array_append(resolver->parser->types, (ty_type_t){.kind = TYPE_VOID},
                    arena);
    const u32 void_type_i = pg_array_last_index(resolver->parser->types);
    return node->type_i = void_type_i;
  }
  case AST_KIND_STRING: {
    pg_array_append(resolver->parser->types, (ty_type_t){.kind = TYPE_STRING},
                    arena);
    const u32 type_i = pg_array_last_index(resolver->parser->types);
    return node->type_i = type_i;
  }

  case AST_KIND_CLASS_REFERENCE: {
    const string_t class_name = cf_constant_array_get_as_string(
        &resolver->parser->class_files[node->class_file_i].constant_pool,
        node->constant_pool_class_name_i);
    const ty_type_t type = {.kind = TYPE_CLASS_REFERENCE,
                            .class_file_i = node->class_file_i,
                            .constant_pool_item_i =
                                node->constant_pool_class_name_i,
                            .v = {.class_name = class_name}};

    pg_array_append(resolver->parser->types, type, arena);
    return node->type_i = pg_array_last_index(resolver->parser->types);
  }

  case AST_KIND_FIELD_ACCESS: {
    const par_ast_node_t *const lhs = &resolver->parser->nodes[node->lhs];
    pg_assert(node->rhs == 0 && "todo");

    /* const par_ast_node_t *const rhs = &resolver->parser->nodes[node->rhs]; */

    // FIXME: For now, this is the only kind of field access that's supported
    // e.g. `System.out`.
    pg_assert(lhs->kind == AST_KIND_CLASS_REFERENCE);

    const u32 lhs_type_i = ty_resolve_types(resolver, node->lhs, arena);
    const ty_type_t *const lhs_type = &resolver->parser->types[lhs_type_i];
    pg_assert(lhs_type->constant_pool_item_i != (u16)-1);
    pg_assert(lhs_type->constant_pool_item_i > 0);

    if (node->rhs ==
        0) { // `node` is the last member of the field access e.g. `a.b.c`: `c`

      const string_t class_name = cf_constant_array_get_as_string(
          &resolver->parser->class_files[lhs_type->class_file_i].constant_pool,
          lhs_type->constant_pool_item_i);

      pg_assert(node->main_token_i + 1 <
                pg_array_len(resolver->parser->lexer->tokens));
      const lex_token_t token_field =
          resolver->parser->lexer->tokens[node->main_token_i + 1];

      const string_t field_name = {
          .value = &resolver->parser->buf[token_field.source_offset],
          .len = lex_identifier_length(resolver->parser->buf,
                                       resolver->parser->buf_len,
                                       token_field.source_offset),
      };

      ty_type_t type = {0};
      if (!cf_class_files_find_field_exactly(
              resolver->parser->class_files, class_name, field_name,
              ACCESS_FLAGS_STATIC | ACCESS_FLAGS_PUBLIC, &type.class_file_i,
              &type.field_i)) {
        string_t error = string_reserve(256, arena);
        string_append_cstring(&error, "unknown field", arena);
        string_append_string(&error, field_name, arena);
        string_append_cstring(&error, "of class ", arena);
        string_append_string(&error, class_name, arena);

        par_error(resolver->parser, token, error.value);
        return 0;
      }

      const cf_class_file_t *class_file =
          &resolver->parser->class_files[type.class_file_i];
      const u16 type_descriptor_i = class_file->fields[type.field_i].descriptor;
      const string_t type_descriptor = cf_constant_array_get_as_string(
          &class_file->constant_pool, type_descriptor_i);
      cf_parse_field_type_descriptor(type_descriptor, &type,
                                     &resolver->parser->types, arena);
      pg_array_append(resolver->parser->types, type, arena);
      return node->type_i = pg_array_last_index(resolver->parser->types);
    }

    if (lhs_type->kind != TYPE_INSTANCE_REFERENCE) {
      string_t error = string_reserve(256, arena);
      string_append_cstring(
          &error, "incompatible types, expected object, got: ", arena);

      const string_t type_inferred_string =
          ty_type_to_human_string(resolver->parser->types, lhs_type_i, arena);
      string_append_string(&error, type_inferred_string, arena);
      par_error(resolver->parser, token, error.value);
    }

    /* const u32 rhs_type_i = ty_resolve_types(resolver, node->rhs, arena); */
    /* const ty_type_t *const rhs_type = &resolver->parser->types[rhs_type_i];
     */
    // TODO: some checks with rhs_type.

    pg_assert(0 && "todo");
    return node->type_i = 0;
  }

  case AST_KIND_MAX:
    pg_assert(0 && "unreachable");
  }
}

// --------------------------------- Code generation

typedef struct {
  cf_attribute_code_t *code;
  cg_frame_t *frame;
  const cf_class_file_t *class_files;
  cf_stack_map_frame_t *stack_map_frames;
  u16 out_field_ref_i;
  u16 out_field_ref_class_i;
  pg_pad(4);
} cg_generator_t;

static u16 cg_emit_jump_conditionally(cg_generator_t *gen, u8 jump_opcode,
                                      arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->locals != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  cf_code_array_push_u8(&gen->code->code, jump_opcode, arena);
  const u16 jump_from_i = pg_array_len(gen->code->code);
  cf_code_array_push_u8(&gen->code->code, BYTECODE_IMPDEP1, arena);
  cf_code_array_push_u8(&gen->code->code, BYTECODE_IMPDEP2, arena);

  switch (jump_opcode) {
  case BYTECODE_IF_ICMPEQ:
  case BYTECODE_IF_ICMPNE:
  case BYTECODE_IF_ICMPLT:
  case BYTECODE_IF_ICMPGE:
  case BYTECODE_IF_ICMPGT:
  case BYTECODE_IF_ICMPLE:
    cg_frame_stack_pop(gen->frame);
    cg_frame_stack_pop(gen->frame);
    break;
  case BYTECODE_IFEQ:
  case BYTECODE_IFNE:
    cg_frame_stack_pop(gen->frame);
    break;
  default:
    pg_assert(0 && "unreachable/unimplemented");
  }

  return jump_from_i;
}

static u16 cg_emit_jump(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->locals != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_GOTO, arena);
  const u16 from_location = pg_array_len(gen->code->code);
  cf_code_array_push_u8(&gen->code->code, BYTECODE_IMPDEP1, arena);
  cf_code_array_push_u8(&gen->code->code, BYTECODE_IMPDEP2, arena);

  return from_location;
}

static void cg_emit_pop(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->locals != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_POP, arena);

  cg_frame_stack_pop(gen->frame);
}

static void cg_emit_store_variable_int(cg_generator_t *gen, u8 var_i,
                                       arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->locals != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) > 0);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  pg_assert(var_i < gen->frame->locals_count);
  pg_assert(gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind ==
            VERIFICATION_INFO_INT);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_ISTORE, arena);
  cf_code_array_push_u8(&gen->code->code, var_i, arena);

  cg_frame_stack_pop(gen->frame);
}

static void cg_emit_store_variable_long(cg_generator_t *gen, u8 var_i,
                                        arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->locals != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) > 0);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  pg_assert(var_i < gen->frame->locals_count);
  pg_assert(gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind ==
            VERIFICATION_INFO_LONG);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_LSTORE, arena);
  cf_code_array_push_u8(&gen->code->code, var_i, arena);

  cg_frame_stack_pop(gen->frame);
}

static void cg_emit_load_variable_int(cg_generator_t *gen, u8 var_i,
                                      arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->locals != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) < UINT16_MAX);
  pg_assert(var_i < gen->frame->locals_count);
  pg_assert(pg_array_len(gen->frame->locals) > 0);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_ILOAD, arena);
  cf_code_array_push_u8(&gen->code->code, var_i, arena);

  cg_frame_stack_push(gen->frame,
                      (cf_verification_info_t){.kind = VERIFICATION_INFO_INT},
                      arena);
}

static void cg_emit_load_variable_long(cg_generator_t *gen, u8 var_i,
                                       arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->locals != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) < UINT16_MAX);
  pg_assert(var_i < gen->frame->locals_count);
  pg_assert(pg_array_len(gen->frame->locals) > 0);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_LLOAD, arena);
  cf_code_array_push_u8(&gen->code->code, var_i, arena);

  cg_frame_stack_push(gen->frame,
                      (cf_verification_info_t){.kind = VERIFICATION_INFO_LONG},
                      arena);
}

static void cg_emit_add(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);
  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_IADD, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_LADD, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  cg_frame_stack_pop(gen->frame);
}

static void cg_emit_neg(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 1);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);
  const cf_verification_info_kind_t kind =
      pg_array_last(gen->frame->stack)->kind;

  switch (kind) {
  case VERIFICATION_INFO_INT:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_INEG, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_LNEG, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void cg_emit_lcmp(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(arena != NULL);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_LCMP, arena);

  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_pop(gen->frame);

  cg_frame_stack_push(gen->frame,
                      (cf_verification_info_t){.kind = VERIFICATION_INFO_INT},
                      arena);
}

static void cg_emit_bipush(cg_generator_t *gen, u8 value, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(arena != NULL);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_BIPUSH, arena);
  cf_code_array_push_u8(&gen->code->code, value, arena);

  cg_frame_stack_push(gen->frame,
                      (cf_verification_info_t){.kind = VERIFICATION_INFO_INT},
                      arena);
}

static void cg_emit_ixor(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);
  pg_assert(gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind ==
            VERIFICATION_INFO_INT);
  pg_assert(gen->frame->stack[pg_array_len(gen->frame->stack) - 2].kind ==
            VERIFICATION_INFO_INT);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_IXOR, arena);

  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_push(gen->frame,
                      (cf_verification_info_t){.kind = VERIFICATION_INFO_INT},
                      arena);
}

static void cg_emit_mul(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_IMUL, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_LMUL, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_push(gen->frame, (cf_verification_info_t){.kind = kind_a},
                      arena);
}

static void cg_emit_div(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_IDIV, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_LDIV, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_push(gen->frame, (cf_verification_info_t){.kind = kind_a},
                      arena);
}

static void cg_emit_rem(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_IREM, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_LREM, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_push(gen->frame, (cf_verification_info_t){.kind = kind_a},
                      arena);
}

#if 0
static void cg_emit_bitwise_and(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_IAND, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_LAND, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_push(gen->frame, (cf_verification_info_t){.kind = kind_a},
                      arena);
}

static void cg_emit_bitwise_or(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_IOR, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cf_code_array_push_u8(&gen->code->code, BYTECODE_LOR, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_pop(gen->frame);
  cg_frame_stack_push(gen->frame, (cf_verification_info_t){.kind = kind_a},
                      arena);
}
#endif

static void
cg_emit_load_constant_single_word(cg_generator_t *gen, u16 constant_i,
                                  cf_verification_info_t verification_info,
                                  arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(constant_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) < UINT16_MAX);
  pg_assert(cf_verification_info_kind_word_count(verification_info.kind) == 1);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_LDC_W, arena);
  cf_code_array_push_u16(&gen->code->code, constant_i, arena);

  pg_assert(pg_array_len(gen->frame->stack) < UINT16_MAX);

  cg_frame_stack_push(gen->frame, verification_info, arena);
}

static void
cg_emit_load_constant_double_word(cg_generator_t *gen, u16 constant_i,
                                  cf_verification_info_t verification_info,
                                  arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(constant_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) < UINT16_MAX);
  pg_assert(cf_verification_info_kind_word_count(verification_info.kind) == 2);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_LDC2_W, arena);
  cf_code_array_push_u16(&gen->code->code, constant_i, arena);

  pg_assert(pg_array_len(gen->frame->stack) < UINT16_MAX);

  cg_frame_stack_push(gen->frame, verification_info, arena);
}

static void cg_emit_invoke_virtual(cg_generator_t *gen, u16 method_ref_i,
                                   const par_type_method_t *method_type,
                                   arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_INVOKE_VIRTUAL, arena);
  cf_code_array_push_u16(&gen->code->code, method_ref_i, arena);

  for (u8 i = 0; i < 1 + method_type->argument_count; i++)
    cg_frame_stack_pop(gen->frame);
}

static void cg_emit_get_static(cg_generator_t *gen, u16 field_i, u16 class_i,
                               arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(field_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);
  pg_assert(arena != NULL);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_GET_STATIC, arena);
  cf_code_array_push_u16(&gen->code->code, field_i, arena);

  pg_assert(pg_array_len(gen->frame->stack) < UINT16_MAX);
  const cf_verification_info_t verification_info = {
      .kind = VERIFICATION_INFO_OBJECT,
      .extra_data = class_i,
  };
  cg_frame_stack_push(gen->frame, verification_info, arena);
}

static void cg_emit_return(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(arena != NULL);

  cf_code_array_push_u8(&gen->code->code, BYTECODE_RETURN, arena);
}

static void cg_begin_scope(cg_generator_t *gen) {
  pg_assert(gen->frame);
  pg_assert(gen->frame->scope_depth < UINT32_MAX);

  gen->frame->scope_depth += 1;
}

static void
stack_map_record_frame_at_pc(const cg_frame_t *frame,
                             cf_stack_map_frame_t **stack_map_frames, u16 pc,
                             arena_t *arena) {
  pg_assert(frame != NULL);
  pg_assert(arena != NULL);

  const cf_stack_map_frame_t stack_map_frame = {
      .frame = cg_frame_clone(frame, arena),
      .pc = pc,
  };
  pg_array_append(*stack_map_frames, stack_map_frame, arena);
}

static void cg_frame_drop_current_scope_variables(cg_frame_t *frame) {
  pg_assert(frame != NULL);

  u64 to_drop = 0;
  for (i64 i = pg_array_len(frame->locals) - 1; i >= 0; i--) {
    const cf_variable_t *const variable = &frame->locals[i];
    if (variable->scope_depth < frame->scope_depth)
      break;

    pg_assert(variable->scope_depth == frame->scope_depth);

    to_drop += 1;
  }

  pg_array_drop_last_n(frame->locals, to_drop);
}

static void cg_end_scope(cg_generator_t *gen) {
  pg_assert(gen);
  pg_assert(gen->frame);
  pg_assert(gen->frame->scope_depth > 0);

  cg_frame_drop_current_scope_variables(gen->frame);

  gen->frame->scope_depth -= 1;
}

// TODO: Should the AST_KIND_VAR_DEFINITION node simply store the variable
// slot number? Or use a lookup table?
static u32 cf_find_variable(const cg_frame_t *frame, u32 node_i) {
  pg_assert(frame != NULL);
  pg_assert(frame->locals != NULL);

  for (i64 i = pg_array_len(frame->locals) - 1; i >= 0; i--) {
    const cf_variable_t *const variable = &frame->locals[i];
    if (variable->node_i != node_i)
      continue;

    if (variable->verification_info.kind == VERIFICATION_INFO_INT)
      return (u32)i;
    // Long/Double takes up 2 slots: [Top, Long|Double], and we need to return
    // the first slot.
    else if (variable->verification_info.kind == VERIFICATION_INFO_LONG ||
             variable->verification_info.kind == VERIFICATION_INFO_DOUBLE)
      return (u32)i - 1;
    else
      pg_assert(0 && "todo");
  }

  return (u32)-1;
}

static void cg_emit_node(cg_generator_t *gen, par_parser_t *parser,
                         cf_class_file_t *class_file, u32 node_i,
                         arena_t *arena);

static void cg_patch_jump_at(cg_generator_t *gen, u16 at, u16 target) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->code->code != NULL);
  pg_assert(at > 0);
  pg_assert(target > 0);

  const i16 jump_offset = target - (at - 1);
  gen->code->code[at + 0] = (u8)(((u16)(jump_offset & 0xff00)) >> 8);
  gen->code->code[at + 1] = (u8)(((u16)(jump_offset & 0x00ff)) >> 0);
}

// TODO: Make a primitive emerge to use here and in cg_emit_if_then_else.
static void cg_emit_synthetic_if_then_else(cg_generator_t *gen,
                                           u8 conditional_jump_opcode,
                                           arena_t *arena) {
  // Assume the condition is already on the stack

  cf_code_array_push_u8(&gen->code->code, conditional_jump_opcode, arena);
  cf_code_array_push_u8(&gen->code->code, 0, arena);
  cf_code_array_push_u8(&gen->code->code, 3 + 2 + 3, arena);

  switch (conditional_jump_opcode) {
  case BYTECODE_IF_ICMPEQ:
  case BYTECODE_IF_ICMPNE:
  case BYTECODE_IF_ICMPLT:
  case BYTECODE_IF_ICMPGE:
  case BYTECODE_IF_ICMPGT:
  case BYTECODE_IF_ICMPLE:
    cg_frame_stack_pop(gen->frame);
    cg_frame_stack_pop(gen->frame);
    break;
  case BYTECODE_IFEQ:
  case BYTECODE_IFNE:
    cg_frame_stack_pop(gen->frame);
    break;
  default:
    pg_assert(0 && "unreachable/unimplemented");
  }

  const cg_frame_t *const frame_before_then_else =
      cg_frame_clone(gen->frame, arena);

  cg_emit_bipush(gen, true, arena); // Then.
  cf_code_array_push_u8(&gen->code->code, BYTECODE_GOTO, arena);
  cf_code_array_push_u8(&gen->code->code, 0, arena);
  cf_code_array_push_u8(&gen->code->code, 3 + 2, arena);

  const cg_frame_t *const frame_after_then = cg_frame_clone(gen->frame, arena);

  gen->frame = cg_frame_clone(frame_before_then_else, arena);

  const u16 conditional_jump_target_absolute = pg_array_len(gen->code->code);
  cg_emit_bipush(gen, false, arena); // Else.

  const u16 unconditional_jump_target_absolute = pg_array_len(gen->code->code);

  stack_map_record_frame_at_pc(frame_before_then_else, &gen->stack_map_frames,
                               conditional_jump_target_absolute, arena);
  stack_map_record_frame_at_pc(frame_after_then, &gen->stack_map_frames,
                               unconditional_jump_target_absolute, arena);
}

static void cg_emit_gt(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPLE, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cg_emit_lcmp(gen, arena);
    cg_emit_bipush(gen, 1, arena);
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPNE, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void cg_emit_ne(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPEQ, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cg_emit_lcmp(gen, arena);
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IFEQ, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void cg_emit_eq(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPNE, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cg_emit_lcmp(gen, arena);
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IFNE, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void cg_emit_ge(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPLT, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cg_emit_lcmp(gen, arena);
    cg_emit_bipush(gen, -1, arena);
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPEQ, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void cg_emit_le(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPGT, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cg_emit_lcmp(gen, arena);
    cg_emit_bipush(gen, 1, arena);
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPEQ, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void cg_emit_lt(cg_generator_t *gen, arena_t *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(pg_array_len(gen->frame->stack) >= 2);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const cf_verification_info_kind_t kind_a =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1].kind;
  const u8 word_count = cf_verification_info_kind_word_count(kind_a);
  pg_assert(pg_array_len(gen->frame->stack) >= 2 * word_count);

  const cf_verification_info_kind_t kind_b =
      gen->frame->stack[pg_array_len(gen->frame->stack) - 1 - word_count].kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPGE, arena);
    break;
  case VERIFICATION_INFO_LONG:
    cg_emit_lcmp(gen, arena);
    cg_emit_bipush(gen, -1, arena);
    cg_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPNE, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void cg_emit_if_then_else(cg_generator_t *gen, par_parser_t *parser,
                                 cf_class_file_t *class_file, u32 node_i,
                                 arena_t *arena) {
  // clang-format off
  //
  //               IF 
  //              /  \
  //    condition     BINARY
  //                 /      \
  //             then        else
  //
  //                 <condition expression>
  //      x     ---- jump_conditionally (IFEQ,  etc)
  //      x     |    jump_conditionally_offset1
  //      x     |    jump_conditionally_offset2
  //      x     |    <then branch>
  //  +   x  ...|... jump
  //  +   x  .  |    jump_offset1 
  //  +   x  .  |    jump_offset2
  //  +   x  .  |--> <else branch> 
  //  +      ......> ...          
  //
  // clang-format on

  pg_assert(gen != NULL);
  pg_assert(parser != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);
  pg_assert(node_i < pg_array_len(parser->nodes));
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->locals != NULL);
  pg_assert(gen->frame->stack != NULL);
  pg_assert(gen->stack_map_frames != NULL);

  const par_ast_node_t *const node = &parser->nodes[node_i];
  pg_assert(node->type_i > 0);
  pg_assert(node->lhs > 0);
  pg_assert(node->lhs < pg_array_len(parser->nodes));
  pg_assert(node->rhs > 0);
  pg_assert(node->rhs < pg_array_len(parser->nodes));

  // Emit condition.
  cg_emit_node(gen, parser, class_file, node->lhs, arena);

  const u16 jump_conditionally_from_i =
      cg_emit_jump_conditionally(gen, BYTECODE_IFEQ, arena);

  pg_assert(node->rhs > 0);
  const par_ast_node_t *const rhs = &parser->nodes[node->rhs];
  pg_assert(rhs->kind == AST_KIND_BINARY);

  // Emit `then` branch.
  // Save a clone of the frame before the `then` branch since we need it
  // later.
  const cg_frame_t *const frame_before_then_else =
      cg_frame_clone(gen->frame, arena);

  cg_emit_node(gen, parser, class_file, rhs->lhs, arena);
  const u16 jump_from_i = cg_emit_jump(gen, arena);
  const u16 conditional_jump_target_absolute = pg_array_len(gen->code->code);

  // Save a clone of the frame after the `then` branch executed so that we can
  // generate a stack map frame later.
  const cg_frame_t *const frame_after_then = cg_frame_clone(gen->frame, arena);

  // Emit `else` branch.
  // Restore the frame as if the `then` branch never executed.
  gen->frame = cg_frame_clone(frame_before_then_else, arena);

  cg_emit_node(gen, parser, class_file, rhs->rhs, arena);
  const u16 unconditional_jump_target_absolute = pg_array_len(gen->code->code);

  gen->frame->max_stack =
      pg_max(frame_after_then->max_stack, gen->frame->max_stack);
  gen->frame->max_locals =
      pg_max(frame_after_then->max_locals, gen->frame->max_locals);
  // TODO: assert that the stack/locals count is the same?

  // Patch first, conditional, jump.
  {
    cg_patch_jump_at(gen, jump_conditionally_from_i,
                     conditional_jump_target_absolute);
    stack_map_record_frame_at_pc(frame_before_then_else, &gen->stack_map_frames,
                                 conditional_jump_target_absolute, arena);
  }
  // Patch second, unconditional, jump.
  {
    cg_patch_jump_at(gen, jump_from_i, unconditional_jump_target_absolute);
    stack_map_record_frame_at_pc(frame_after_then, &gen->stack_map_frames,
                                 unconditional_jump_target_absolute, arena);
  }
}

static int stack_map_frame_sort(const void *a, const void *b) {
  pg_assert(a != NULL);
  pg_assert(b != NULL);

  const cf_stack_map_frame_t *const smp_a = a;
  const cf_stack_map_frame_t *const smp_b = b;

  return (int)smp_a->pc - (int)smp_b->pc;
}

static void stack_map_resolve_frames(const cg_frame_t *first_method_frame,
                                     cf_stack_map_frame_t *stack_map_frames,
                                     arena_t *arena) {
  pg_assert(first_method_frame != NULL);
  pg_assert(stack_map_frames != NULL);
  pg_assert(arena != NULL);

  if (pg_array_len(stack_map_frames) == 0)
    return;

  // TODO: Better sort.
  qsort(stack_map_frames, pg_array_len(stack_map_frames),
        sizeof(cf_stack_map_frame_t), stack_map_frame_sort);

  for (u64 i = 0; i < pg_array_len(stack_map_frames); i++) {
    cf_stack_map_frame_t *const stack_map_frame = &stack_map_frames[i];
    cg_frame_t *const frame = stack_map_frame->frame;

    const cg_frame_t *const previous_frame =
        i > 0 ? stack_map_frames[i - 1].frame : first_method_frame;

    i16 locals_delta =
        pg_array_len(frame->locals) - pg_array_len(previous_frame->locals);

    i32 offset_delta =
        i == 0 ? stack_map_frame->pc
               : (stack_map_frame->pc - stack_map_frames[i - 1].pc - 1);

    if (offset_delta == -1) // Duplicate jump target, already has a valid
                            // stack map frame, skip.
    {
      stack_map_frame->tombstone = true;
      continue;
    }

    pg_assert(offset_delta >= 0);
    pg_assert(offset_delta <= UINT16_MAX);

    if (frame->stack_count == 0 && locals_delta == 0 && offset_delta <= 63) {
      stack_map_fill_same_frame(stack_map_frame, offset_delta);
    } else if (frame->stack_count == 0 && locals_delta == 0 &&
               offset_delta > 63) {
      pg_assert(0 && "todo"); // same_frame_extended
    } else if (frame->stack_count == 1 && locals_delta == 0 &&
               offset_delta <= 63) {
      stack_map_fill_same_locals_1_stack_item_frame(stack_map_frame,
                                                    offset_delta);
    } else if (frame->stack_count == 1 && locals_delta == 0 &&
               offset_delta <= 63) {
      pg_assert(0 && "todo"); // same_locals_1_stack_item_frame_extended
    } else if (frame->stack_count == 0 && locals_delta == 1 &&
               offset_delta <= 3) {
      pg_assert(0 && "todo"); // append_frame
    } else if (frame->stack_count == 0 &&
               (locals_delta == -1 || locals_delta == -2 ||
                locals_delta == -3) &&
               offset_delta <= 3) {
      pg_assert(0 && "todo"); // chop_frame
    } else {
      stack_map_fill_full_frame(stack_map_frame, offset_delta);
    }
  }
}

static u16 cg_add_class_name_in_constant_pool(cf_class_file_t *class_file,
                                              string_t class_name,
                                              arena_t *arena) {
  const u16 class_name_i =
      cf_add_constant_string(&class_file->constant_pool, class_name, arena);
  const cf_constant_t out_class = {.kind = CONSTANT_POOL_KIND_CLASS_INFO,
                                   .v = {.class_name = class_name_i}};
  const u16 class_i =
      cf_constant_array_push(&class_file->constant_pool, &out_class, arena);

  return class_i;
}

static void cg_emit_node(cg_generator_t *gen, par_parser_t *parser,
                         cf_class_file_t *class_file, u32 node_i,
                         arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));
  pg_assert(pg_array_len(parser->nodes) > 0);
  pg_assert(class_file != NULL);
  pg_assert(node_i < pg_array_len(parser->nodes));

  const par_ast_node_t *const node = &parser->nodes[node_i];
  const lex_token_t token = parser->lexer->tokens[node->main_token_i];
  const ty_type_t *const type = &parser->types[node->type_i];

  switch (node->kind) {
  case AST_KIND_NONE:
    return;
  case AST_KIND_BOOL: {
    pg_assert(node->main_token_i < pg_array_len(parser->lexer->tokens));
    const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_INT,
                                    .v = {.number = node->lhs}};
    const u16 number_i =
        cf_constant_array_push(&class_file->constant_pool, &constant, arena);

    pg_assert(gen->code != NULL);
    pg_assert(gen->code->code != NULL);
    pg_assert(gen->frame != NULL);

    const cf_verification_info_t verification_info = {
        .kind = VERIFICATION_INFO_INT};
    cg_emit_load_constant_single_word(gen, number_i, verification_info, arena);
    break;
  }
  case AST_KIND_NUMBER: {
    pg_assert(node->main_token_i < pg_array_len(parser->lexer->tokens));

    u8 number_flags = 0;
    const u64 number = par_number(parser, token, &number_flags);
    cp_info_kind_t pool_kind = CONSTANT_POOL_KIND_INT;
    cf_verification_info_kind_t verification_info_kind = VERIFICATION_INFO_INT;
    if (number_flags & NUMBER_FLAGS_LONG) {
      pool_kind = CONSTANT_POOL_KIND_LONG;
      verification_info_kind = VERIFICATION_INFO_LONG;
    }
    // TODO: Float, Double, etc.

    const cf_constant_t constant = {.kind = pool_kind, .v = {.number = number}};
    const u16 number_i =
        cf_constant_array_push(&class_file->constant_pool, &constant, arena);
    if (pool_kind == CONSTANT_POOL_KIND_LONG ||
        pool_kind == CONSTANT_POOL_KIND_DOUBLE) {
      const cf_constant_t dummy = {0};
      cf_constant_array_push(&class_file->constant_pool, &dummy, arena);

      cg_emit_load_constant_double_word(
          gen, number_i,
          (cf_verification_info_t){.kind = verification_info_kind}, arena);
    } else {
      cg_emit_load_constant_single_word(
          gen, number_i,
          (cf_verification_info_t){.kind = verification_info_kind}, arena);
    }
    break;
  }
  case AST_KIND_BUILTIN_PRINTLN: {
    pg_assert(gen->out_field_ref_i > 0);
    pg_assert(gen->out_field_ref_class_i > 0);
    pg_assert(pg_array_len(gen->frame->stack) == 0);

    cg_emit_get_static(gen, gen->out_field_ref_i, gen->out_field_ref_class_i,
                       arena);

    cg_emit_node(gen, parser, class_file, node->lhs, arena);

    pg_assert(type->kind == TYPE_METHOD);

    const par_type_method_t *const method = &type->v.method;

    pg_assert(method->descriptor.value != NULL);
    pg_assert(method->descriptor.len > 0);
    const u16 descriptor_i = cf_add_constant_string(&class_file->constant_pool,
                                                    method->descriptor, arena);
    const u16 name_i =
        cf_add_constant_cstring(&class_file->constant_pool, "println", arena);

    const cf_constant_t name_and_type = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = name_i,
                                .type_descriptor = descriptor_i}}};
    const u16 name_and_type_i = cf_constant_array_push(
        &class_file->constant_pool, &name_and_type, arena);

    const u16 printstream_name_i = cf_add_constant_cstring(
        &class_file->constant_pool, "java/io/PrintStream", arena);

    const cf_constant_t printstream_class = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {.class_name = printstream_name_i}};
    const u16 printstream_class_i = cf_constant_array_push(
        &class_file->constant_pool, &printstream_class, arena);
    const cf_constant_t method_ref = {
        .kind = CONSTANT_POOL_KIND_METHOD_REF,
        .v = {.method_ref = {.class = printstream_class_i,
                             .name_and_type = name_and_type_i}}};
    const u16 method_ref_i =
        cf_constant_array_push(&class_file->constant_pool, &method_ref, arena);

    cg_emit_invoke_virtual(gen, method_ref_i, method, arena);
    pg_assert(pg_array_len(gen->frame->stack) == 0);
    break;
  }
  case AST_KIND_FUNCTION_DEFINITION: {
    const u32 token_name_i = node->main_token_i;
    pg_assert(token_name_i < pg_array_len(parser->lexer->tokens));
    const lex_token_t token_name = parser->lexer->tokens[token_name_i];
    pg_assert(token_name.kind == TOKEN_KIND_IDENTIFIER);

    string_t method_name = {
        .len = lex_identifier_length(parser->buf, parser->buf_len,
                                     token_name.source_offset),
        .value = &parser->buf[token_name.source_offset],
    };
    const u16 method_name_i =
        cf_add_constant_string(&class_file->constant_pool, method_name, arena);

    // FIXME: hardcoded type.

    pg_array_append(parser->types, (ty_type_t){.kind = TYPE_VOID}, arena);
    const u32 void_type_i = pg_array_last_index(parser->types);

    const string_t string_class_name =
        string_make_from_c("java/lang/String", arena);
    const ty_type_t string_type = {
        .kind = TYPE_INSTANCE_REFERENCE,
        .v = {.class_name = string_class_name},
    };
    pg_array_append(parser->types, string_type, arena);
    const u32 string_type_i = pg_array_last_index(parser->types);

    const ty_type_t main_argument_types = {
        .kind = TYPE_ARRAY_REFERENCE,
        .v = {.array_type_i = string_type_i},
    };
    pg_array_append(parser->types, main_argument_types, arena);
    const u32 main_argument_types_i = pg_array_last_index(parser->types);

    const ty_type_t main_type = {
        .kind = TYPE_METHOD,
        .v =
            {
                .method =
                    {
                        .argument_count = 1,
                        .return_type_i = void_type_i,
                        .argument_types_i = main_argument_types_i,
                    },
            },
    };
    pg_array_append(parser->types, main_type, arena);
    const u32 main_type_i = pg_array_last_index(parser->types);

    string_t type_descriptor = string_reserve(64, arena);
    cf_fill_type_descriptor_string(parser->types, main_type_i, &type_descriptor,
                                   arena);
    const u16 descriptor_i = cf_add_constant_string(&class_file->constant_pool,
                                                    type_descriptor, arena);

    cf_method_t method = {
        .access_flags = ACCESS_FLAGS_STATIC | ACCESS_FLAGS_PUBLIC /* FIXME */,
        .name = method_name_i,
        .descriptor = descriptor_i,
    };
    pg_array_init_reserve(method.attributes, 1, arena);

    cf_attribute_code_t code = {0};
    cf_attribute_code_init(&code, arena);
    gen->code = &code;
    gen->frame = arena_alloc(arena, 1, sizeof(cg_frame_t));
    cg_frame_init(gen->frame, arena);

    const u16 function_args_string = cf_add_constant_cstring(
        &class_file->constant_pool, "[Ljava/lang/String;", arena);

    const cf_constant_t functions_args_class = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {
            .class_name = function_args_string,
        }};
    const u16 functions_args_class_i = cf_constant_array_push(
        &class_file->constant_pool, &functions_args_class, arena);

    const cf_variable_t arg0 = {
        .type_i = main_argument_types_i,
        .scope_depth = gen->frame->scope_depth,
        .verification_info =
            {
                .kind = VERIFICATION_INFO_OBJECT,
                .extra_data = functions_args_class_i,
            },
    };
    cg_frame_locals_push(gen->frame, &arg0, arena);

    cg_frame_t *const first_method_frame = cg_frame_clone(gen->frame, arena);

    // `lhs` is the arguments, `rhs` is the body.
    // TODO: Handle `lhs`.
    if (node->lhs > 0)
      pg_assert(0 && "todo");

    cg_emit_node(gen, parser, class_file, node->rhs, arena);

    cg_emit_return(gen, arena);

    gen->code->max_stack = gen->frame->max_stack;
    gen->code->max_locals = gen->frame->max_locals;

    stack_map_resolve_frames(first_method_frame, gen->stack_map_frames, arena);

    cf_attribute_t attribute_stack_map_frames = {
        .kind = ATTRIBUTE_KIND_STACK_MAP_TABLE,
        .name = cf_add_constant_cstring(&class_file->constant_pool,
                                        "StackMapTable", arena),
        .v = {.stack_map_table = NULL}};
    pg_array_init_reserve(attribute_stack_map_frames.v.stack_map_table,
                          pg_array_len(gen->stack_map_frames), arena);

    for (u64 i = 0; i < pg_array_len(gen->stack_map_frames); i++) {
      if (!gen->stack_map_frames[i].tombstone)
        pg_array_append(attribute_stack_map_frames.v.stack_map_table,
                        gen->stack_map_frames[i], arena);
    }

    pg_array_append(code.attributes, attribute_stack_map_frames, arena);

    const cf_attribute_t attribute_code = {
        .kind = ATTRIBUTE_KIND_CODE,
        .name =
            cf_add_constant_cstring(&class_file->constant_pool, "Code", arena),
        .v = {.code = code}};
    pg_array_append(method.attributes, attribute_code, arena);

    pg_array_append(class_file->methods, method, arena);

    gen->code = NULL;
    gen->frame = NULL;
    pg_array_clear(gen->stack_map_frames);
    break;
  }
  case AST_KIND_UNARY: {

    switch (token.kind) {
    case TOKEN_KIND_NOT:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_bipush(gen, 1, arena);
      cg_emit_ixor(gen, arena);
      break;

    case TOKEN_KIND_MINUS:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_neg(gen, arena);
      break;

    default:
      pg_assert(0 && "unimplemented");
    }
    break;
  }
  case AST_KIND_BINARY: {
    pg_assert(gen->frame != NULL);
    pg_assert(gen->frame->locals != NULL);

    pg_assert(node->lhs < pg_array_len(parser->nodes));
    pg_assert(node->rhs < pg_array_len(parser->nodes));

    switch (token.kind) {
    case TOKEN_KIND_NONE:
      break; // Nothing to do.

    case TOKEN_KIND_PLUS:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_add(gen, arena);
      break;

    case TOKEN_KIND_MINUS:
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_neg(gen, arena);
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_add(gen, arena);
      break;

    case TOKEN_KIND_STAR:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_mul(gen, arena);
      break;

    case TOKEN_KIND_SLASH:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_div(gen, arena);
      break;

    case TOKEN_KIND_PERCENT:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_rem(gen, arena);
      break;

    case TOKEN_KIND_AMPERSAND_AMPERSAND: {
      // Since the if_xxx opcodes always pop the condition off the stack,
      // there is no simple way to push 0 on the stack if `lhs` is falsey.
      // We have to use this contrived way, short of advanced CFG analysis. :(
      //
      // clang-format off
      //
      // a && b
      // 
      // <=>
      // 
      // if (a) {
      //   if (b) {
      //     push 1 
      //     goto end
      //   }  
      // } else {
      //   push 0
      // }
      // end:
      //
      //                 lhs
      //      x     ---- jump_conditionally (IFEQ,  etc)
      //      x     |    jump_conditionally_offset1 
      //      x     |    jump_conditionally_offset2
      //      x     |    rhs
      //  +   x  ...|... jump
      //  +   x  .  |    jump_offset1 
      //  +   x  .  |    jump_offset2
      //  +   x  .  |--> bipush 0
      //  +      ......> ...           
      //
      // clang-format on
      cg_emit_node(gen, parser, class_file, node->lhs, arena);

      cf_code_array_push_u8(&gen->code->code, BYTECODE_IFEQ, arena);
      const u16 conditional_jump_location = pg_array_len(gen->code->code);
      cf_code_array_push_u16(&gen->code->code, 0, arena);
      cg_frame_stack_pop(gen->frame);

      const cg_frame_t *const frame_before_rhs =
          cg_frame_clone(gen->frame, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);

      const cg_frame_t *const frame_after_rhs =
          cg_frame_clone(gen->frame, arena);
      const u16 unconditional_jump_location = cg_emit_jump(gen, arena);

      {
        const u16 pc_end = pg_array_len(gen->code->code);
        cg_patch_jump_at(gen, conditional_jump_location, pc_end);
        stack_map_record_frame_at_pc(frame_before_rhs, &gen->stack_map_frames,
                                     pc_end, arena);
      }

      // Restore the frame as if the `rhs` branch never executed.
      gen->frame = cg_frame_clone(frame_before_rhs, arena);
      cg_emit_bipush(gen, false, arena);

      {
        const u16 pc_end = pg_array_len(gen->code->code);
        cg_patch_jump_at(gen, unconditional_jump_location, pc_end);
        stack_map_record_frame_at_pc(frame_after_rhs, &gen->stack_map_frames,
                                     pc_end, arena);
      }

      break;
    }

    case TOKEN_KIND_PIPE_PIPE: {
      // Since the if_xxx opcodes always pop the condition off the stack,
      // there is no simple way to push 0 on the stack if `lhs` is falsey.
      // We have to use this contrived way, short of advanced CFG analysis. :(
      //
      // clang-format off
      //
      // a || b
      // 
      // <=>
      // 
      // if (a) {
      //   push 1
      // } else {
      //   if (b) {
      //     push 1 
      //     goto end
      //   }
      //   push 0
      // }
      // end:
      //
      //                 lhs
      //      x     ---- jump_conditionally (IFNE)
      //      x     |    jump_conditionally_offset1 
      //      x     |    jump_conditionally_offset2
      //      x     |    rhs
      //  +   x  ...|... jump
      //  +   x  .  |    jump_offset1 
      //  +   x  .  |    jump_offset2
      //  +   x  .  |--> bipush 1
      //  +      ......> ...           
      //
      // clang-format on
      cg_emit_node(gen, parser, class_file, node->lhs, arena);

      cf_code_array_push_u8(&gen->code->code, BYTECODE_IFNE, arena);
      const u16 conditional_jump_location = pg_array_len(gen->code->code);
      cf_code_array_push_u16(&gen->code->code, 0, arena);
      cg_frame_stack_pop(gen->frame);

      const cg_frame_t *const frame_before_rhs =
          cg_frame_clone(gen->frame, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);

      const cg_frame_t *const frame_after_rhs =
          cg_frame_clone(gen->frame, arena);
      const u16 unconditional_jump_location = cg_emit_jump(gen, arena);

      {
        const u16 pc_end = pg_array_len(gen->code->code);
        cg_patch_jump_at(gen, conditional_jump_location, pc_end);
        stack_map_record_frame_at_pc(frame_before_rhs, &gen->stack_map_frames,
                                     pc_end, arena);
      }

      // Restore the frame as if the `rhs` branch never executed.
      gen->frame = cg_frame_clone(frame_before_rhs, arena);
      cg_emit_bipush(gen, true, arena);

      {
        const u16 pc_end = pg_array_len(gen->code->code);
        cg_patch_jump_at(gen, unconditional_jump_location, pc_end);
        stack_map_record_frame_at_pc(frame_after_rhs, &gen->stack_map_frames,
                                     pc_end, arena);
      }

      break;
    }

    case TOKEN_KIND_EQUAL_EQUAL:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_eq(gen, arena);
      break;

    case TOKEN_KIND_LE:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_le(gen, arena);
      break;

    case TOKEN_KIND_LT:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_lt(gen, arena);
      break;

    case TOKEN_KIND_GT:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_gt(gen, arena);
      break;

    case TOKEN_KIND_GE:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_ge(gen, arena);
      break;

    case TOKEN_KIND_NOT_EQUAL:
      cg_emit_node(gen, parser, class_file, node->lhs, arena);
      cg_emit_node(gen, parser, class_file, node->rhs, arena);
      cg_emit_ne(gen, arena);
      break;

    case TOKEN_KIND_EQUAL:
      pg_assert(node->lhs > 0);
      const par_ast_node_t *const lhs = &parser->nodes[node->lhs];
      pg_assert(lhs->kind == AST_KIND_VAR_REFERENCE);

      cg_emit_node(gen, parser, class_file, node->rhs, arena);

      const u32 var_i = cf_find_variable(gen->frame, lhs->lhs);
      pg_assert(var_i != (u32)-1);

      switch (type->kind) {
      case TYPE_INT:
        cg_emit_store_variable_int(gen, var_i, arena);
        break;
      case TYPE_LONG:
        pg_assert(0 && "todo");
        break;
      default:
        pg_assert(0 && "todo");
      }
      break;

    default:
      pg_assert(0 && "todo");
    }
    break;
  }
  case AST_KIND_LIST: {
    if (gen->code != NULL) {
      pg_assert(gen->frame != NULL);
      pg_assert(gen->frame->locals != NULL);
    }

    cg_begin_scope(gen);

    for (u64 i = 0; i < pg_array_len(node->nodes); i++) {
      pg_assert(pg_array_len(gen->frame->stack) == 0);
      cg_emit_node(gen, parser, class_file, node->nodes[i], arena);

      // If the 'statement' was in fact an expression, we need to pop it out.
      while (gen->frame->stack_count > 0)
        cg_emit_pop(gen, arena);
    }

    cg_end_scope(gen);
    break;
  }
  case AST_KIND_VAR_DEFINITION: {
    pg_assert(gen->frame != NULL);
    pg_assert(gen->frame->locals != NULL);
    pg_assert(node->type_i > 0);

    cg_emit_node(gen, parser, class_file, node->lhs, arena);

    cf_verification_info_t verification_info = {.kind = VERIFICATION_INFO_INT};
    if (type->kind == TYPE_LONG) {
      verification_info.kind = VERIFICATION_INFO_LONG;
    } else if (type->kind == TYPE_DOUBLE) {
      verification_info.kind = VERIFICATION_INFO_DOUBLE;
    } else if (type->kind == TYPE_FLOAT) {
      verification_info.kind = VERIFICATION_INFO_FLOAT;
    } else if (type->kind == TYPE_ARRAY_REFERENCE ||
               type->kind == TYPE_INSTANCE_REFERENCE) {
      verification_info.kind = VERIFICATION_INFO_OBJECT;
    }
    const cf_variable_t variable = {
        .node_i = node_i,
        .type_i = node->type_i,
        .scope_depth = gen->frame->scope_depth,
        .verification_info = verification_info,
    };
    const u16 local_i = cg_frame_locals_push(gen->frame, &variable, arena);

    if (verification_info.kind == VERIFICATION_INFO_INT) {
      cg_emit_store_variable_int(gen, local_i, arena);
    } else if (verification_info.kind == VERIFICATION_INFO_LONG) {
      cg_emit_store_variable_long(gen, local_i, arena);
    } else {
      pg_assert(0 && "todo");
    }
    break;
  }
  case AST_KIND_VAR_REFERENCE: {
    pg_assert(gen->frame != NULL);
    pg_assert(gen->frame->locals != NULL);
    pg_assert(node->type_i > 0);

    pg_assert(node->lhs > 0);
    pg_assert(parser->nodes[node->lhs].kind == AST_KIND_VAR_DEFINITION);
    const u32 var_i = cf_find_variable(gen->frame, node->lhs);
    pg_assert(var_i != (u32)-1);

    if (gen->frame->locals[var_i].verification_info.kind ==
        VERIFICATION_INFO_INT)
      cg_emit_load_variable_int(gen, var_i, arena);
    else if (gen->frame->locals[var_i].verification_info.kind ==
                 VERIFICATION_INFO_TOP &&
             gen->frame->locals[var_i + 1].verification_info.kind ==
                 VERIFICATION_INFO_LONG)
      cg_emit_load_variable_long(gen, var_i, arena);
    else
      pg_assert(0 && "todo");

    break;
  }
  case AST_KIND_IF: {
    cg_emit_if_then_else(gen, parser, class_file, node_i, arena);
    break;
  }
  case AST_KIND_WHILE_LOOP: {
    const u16 pc_start = pg_array_len(gen->code->code);
    const cg_frame_t *const frame_before_loop =
        cg_frame_clone(gen->frame, arena);

    cg_emit_node(gen, parser, class_file, node->lhs, arena); // Condition.
    const u16 conditional_jump =
        cg_emit_jump_conditionally(gen, BYTECODE_IFEQ, arena);
    cg_emit_node(gen, parser, class_file, node->rhs, arena); // Body.
    const u16 unconditional_jump = cg_emit_jump(gen, arena);

    const i16 unconditional_jump_delta = -(unconditional_jump - 1 - pc_start);
    gen->code->code[unconditional_jump + 0] =
        (u8)(((u16)(unconditional_jump_delta & 0xff00)) >> 8);
    gen->code->code[unconditional_jump + 1] =
        (u8)(((u16)(unconditional_jump_delta & 0x00ff)) >> 0);

    const u16 pc_end = pg_array_len(gen->code->code);

    // This stack map frame covers the unconditional jump.
    stack_map_record_frame_at_pc(cg_frame_clone(gen->frame, arena),
                                 &gen->stack_map_frames, pc_start, arena);

    // Patch first, conditional, jump.
    {
      cg_patch_jump_at(gen, conditional_jump, pc_end);
      stack_map_record_frame_at_pc(frame_before_loop, &gen->stack_map_frames,
                                   pc_end, arena);
    }

    break;
  }
  case AST_KIND_STRING: {
    const u32 length =
        lex_string_length(parser->buf, parser->buf_len, token.source_offset);
    const string_t s = {
        .value = parser->buf + token.source_offset,
        .len = length,
    };
    const u16 string_i =
        cf_add_constant_string(&class_file->constant_pool, s, arena);
    const u16 jstring_i =
        cf_add_constant_jstring(&class_file->constant_pool, string_i, arena);
    const cf_verification_info_t verification_info = {
        .kind = VERIFICATION_INFO_OBJECT,
        .extra_data = jstring_i,
    };
    cg_emit_load_constant_single_word(gen, jstring_i, verification_info, arena);

    break;
  }
  case AST_KIND_CLASS_REFERENCE: {
    pg_assert(0 && "todo");
    break;
  }
  case AST_KIND_FIELD_ACCESS: {
    const par_ast_node_t *const lhs = &parser->nodes[node->lhs];
    pg_assert(node->rhs == 0 && "todo");

    // FIXME: For now, this is the only kind of field access that's supported
    // e.g. `System.out`.

    const cf_class_file_t *field_class_file =
        &parser->class_files[type->class_file_i];
    const cf_field_t external_field_ref =
        field_class_file->fields[type->field_i];
    const string_t external_field_descriptor = cf_constant_array_get_as_string(
        &field_class_file->constant_pool, external_field_ref.descriptor);
    const string_t field_name_string = cf_constant_array_get_as_string(
        &field_class_file->constant_pool, external_field_ref.name);

    const cf_constant_t field_name = {.kind = CONSTANT_POOL_KIND_UTF8,
                                      .v = {.s = field_name_string}};
    const u16 field_name_i =
        cf_constant_array_push(&class_file->constant_pool, &field_name, arena);

    const cf_constant_t field_descriptor = {
        .kind = CONSTANT_POOL_KIND_UTF8, .v = {.s = external_field_descriptor}};
    const u16 field_descriptor_i = cf_constant_array_push(
        &class_file->constant_pool, &field_descriptor, arena);

    const cf_constant_t field_name_and_type = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {
                  .name = field_name_i,
                  .type_descriptor = field_descriptor_i,
              }}};
    const u16 field_name_and_type_i = cf_constant_array_push(
        &class_file->constant_pool, &field_name_and_type, arena);

    pg_assert(lhs->kind == AST_KIND_CLASS_REFERENCE);
    const ty_type_t *const lhs_type = &parser->types[lhs->type_i];
    pg_assert(lhs_type->class_file_i != (u32)-1);
    pg_assert(lhs_type->constant_pool_item_i != (u16)-1);
    pg_assert(lhs_type->constant_pool_item_i > 0);

    const cf_class_file_t *lhs_class_file =
        &parser->class_files[lhs_type->class_file_i];
    const string_t lhs_class_name = cf_constant_array_get_as_string(
        &lhs_class_file->constant_pool, lhs_type->constant_pool_item_i);
    const u16 lhs_class_name_i =
        cg_add_class_name_in_constant_pool(class_file, lhs_class_name, arena);

    const cf_constant_t field_ref = {
        .kind = CONSTANT_POOL_KIND_FIELD_REF,
        .v = {.field_ref = {
                  .name = lhs_class_name_i,
                  .type_descriptor = field_name_and_type_i,
              }}};
    const u16 field_ref_i =
        cf_constant_array_push(&class_file->constant_pool, &field_ref, arena);

    cg_emit_get_static(gen, field_ref_i, lhs_class_name_i, arena);

    break;
  }
  case AST_KIND_MAX:
    pg_assert(0 && "unreachable");
  }
}

static string_t cg_make_class_name_from_path(string_t path, arena_t *arena) {
  pg_assert(path.value != NULL);
  pg_assert(path.len > 0);
  string_t class_name = string_make(path, arena);

  string_drop_before_last_incl(&class_name, '/');
  pg_assert(class_name.len > 0);
  pg_assert(class_name.value[0] != '/');
  string_drop_after_last_incl(&class_name, '.');
  pg_assert(class_name.len > 0);

  string_capitalize_first(&class_name);

  return class_name;
}

static void cg_emit_synthetic_class(cg_generator_t *gen, par_parser_t *parser,
                                    cf_class_file_t *class_file,
                                    arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));
  pg_assert(pg_array_len(parser->nodes) > 0);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  // FIXME: System.out for println.
  {
    const u16 out_name_i =
        cf_add_constant_cstring(&class_file->constant_pool, "out", arena);
    const u16 out_descriptor_i = cf_add_constant_cstring(
        &class_file->constant_pool, "Ljava/io/PrintStream;", arena);

    const cf_constant_t out_name_and_type = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = out_name_i,
                                .type_descriptor = out_descriptor_i}}};
    const u16 out_name_and_type_i = cf_constant_array_push(
        &class_file->constant_pool, &out_name_and_type, arena);

    const u16 system_name_i = cf_add_constant_cstring(
        &class_file->constant_pool, "java/lang/System", arena);
    const cf_constant_t system_class = {.kind = CONSTANT_POOL_KIND_CLASS_INFO,
                                        .v = {.class_name = system_name_i}};
    const u16 system_class_i = cf_constant_array_push(
        &class_file->constant_pool, &system_class, arena);

    const cf_constant_t out_field_ref = {
        .kind = CONSTANT_POOL_KIND_FIELD_REF,
        .v = {.field_ref = {.name = system_class_i,
                            .type_descriptor = out_name_and_type_i}}};
    const u16 out_field_ref_i = cf_constant_array_push(
        &class_file->constant_pool, &out_field_ref, arena);

    gen->out_field_ref_i = out_field_ref_i;

    const u16 out_class_name_i = cf_add_constant_cstring(
        &class_file->constant_pool, "java/io/PrintStream", arena);
    const cf_constant_t out_class = {.kind = CONSTANT_POOL_KIND_CLASS_INFO,
                                     .v = {.class_name = out_class_name_i}};
    const u16 out_class_i =
        cf_constant_array_push(&class_file->constant_pool, &out_class, arena);
    gen->out_field_ref_class_i = out_class_i;
  }

  { // This class
    const string_t class_name =
        cg_make_class_name_from_path(class_file->file_path, arena);
    const u16 this_class_name_i =
        cf_add_constant_string(&class_file->constant_pool, class_name, arena);

    const cf_constant_t this_class_info = {.kind =
                                               CONSTANT_POOL_KIND_CLASS_INFO,
                                           .v = {
                                               .class_name = this_class_name_i,
                                           }};
    class_file->this_class = cf_constant_array_push(&class_file->constant_pool,
                                                    &this_class_info, arena);
  }

  { // Super class
    const u16 constant_java_lang_object_string_i = cf_add_constant_cstring(
        &class_file->constant_pool, "java/lang/Object", arena);

    const cf_constant_t super_class_info = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {
            .class_name = constant_java_lang_object_string_i,
        }};

    class_file->super_class = cf_constant_array_push(&class_file->constant_pool,
                                                     &super_class_info, arena);
  }
}

static void cg_emit(par_parser_t *parser, cf_class_file_t *class_file,
                    const cf_class_file_t *class_files, u32 root_i,
                    arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));
  pg_assert(pg_array_len(parser->nodes) > 0);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  cg_generator_t gen = {.class_files = class_files};
  pg_array_init_reserve(gen.stack_map_frames, 64, arena);

  cg_emit_synthetic_class(&gen, parser, class_file, arena);

  if (pg_array_len(parser->nodes) == 1)
    return;

  cg_emit_node(&gen, parser, class_file, root_i, arena);
}
