#pragma once

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
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

static u64 align_forward_16(u64 n) {
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
      align_forward_16(arena->current_offset + physical_size);
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

// FIXME
#define pg_array_append(x, item, arena)                                        \
  do {                                                                         \
    pg_assert(pg_array_len(x) <= -pg_array_cap(x));                            \
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

typedef struct {
  u16 cap;
  u16 len;
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

static bool mem_eq_c(const char *a, u32 a_len, char *b) {
  pg_assert(b != NULL);

  const u64 b_len = strlen(b);
  return a_len == b_len && memcmp(a, b, a_len) == 0;
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

  if (s->len > 0 && s->value[0] != c) {
    pg_assert(arena != NULL);
    string_append_char(s, c, arena);
  }
}

static void string_append_string(string_t *a, string_t b, arena_t *arena) {
  pg_assert(a != NULL);
  pg_assert(a->cap != 0);
  pg_assert(a->len <= a->cap);

  for (u64 i = 0; i < b.len; i++)
    string_append_char(a, b.value[i], arena);

  pg_assert(a->value != NULL);
  pg_assert(a->len <= a->cap);
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

static bool cstring_ends_with(const char *s, u64 s_len, const char *suffix,
                              u64 suffix_len) {
  pg_assert(s != NULL);
  pg_assert(s_len > 0);
  pg_assert(suffix != NULL);
  pg_assert(suffix_len > 0);

  if (s_len < suffix_len)
    return false;

  return memcmp(s + s_len - suffix_len, suffix, suffix_len) == 0;
}

#ifdef PG_WITH_LOG
#define LOG(fmt, ...) fprintf(stderr, fmt "\n", __VA_ARGS__)
#else
#define LOG(fmt, ...)                                                          \
  do {                                                                         \
  } while (0)
#endif

// ------------------------ Class file code

typedef enum {
  BYTECODE_NOP = 0x00,
  BYTECODE_ALOAD_0 = 0x2a,
  BYTECODE_INVOKE_SPECIAL = 0xb7,
  BYTECODE_RETURN = 0xb1,
  BYTECODE_GET_STATIC = 0xb2,
  BYTECODE_BIPUSH = 0x10,
  BYTECODE_LDC = 0x12,
  BYTECODE_LDC_W = 0x13,
  BYTECODE_ILOAD = 0x15,
  BYTECODE_ISTORE = 0x36,
  BYTECODE_IADD = 0x60,
  BYTECODE_IMUL = 0x68,
  BYTECODE_IXOR = 0x82,
  BYTECODE_IFEQ = 0x99,
  BYTECODE_IFNE = 0x9a,
  BYTECODE_GOTO = 0xa7,
  BYTECODE_INVOKE_VIRTUAL = 0xb6,
  BYTECODE_IMPDEP1 = 0xfe,
  BYTECODE_IMPDEP2 = 0xff,
} cf_op_kind_t;

static char *const CF_INIT_CONSTRUCTOR_STRING = "<init>";

typedef struct {
  u32 scope_depth;
  string_t name;
  u32 var_definition_node_i;
} par_variable_t;

typedef struct {
  u32 node_i;
  u32 type_i;
} cf_variable_t;

typedef enum {
  VERIFICATION_INFO_TOP = 0,
  VERIFICATION_INFO_INT = 1,
  VERIFICATION_INFO_FLOAT = 2,
  VERIFICATION_INFO_DOUBLE = 3,
  VERIFICATION_INFO_LONG = 4,
  VERIFICATION_INFO_NULL = 6,
  VERIFICATION_INFO_OBJECT = 7,
  VERIFICATION_INFO_UNINITIALIZED = 8,
} cf_verification_info_t;

typedef struct {
  u8 kind;
  u8 offset_delta;
  u16 offset_absolute;
  cf_verification_info_t
      verification_info; // TODO: it's actually: `cf_verification_info_t[]`.
} cf_stack_map_frame_t;

enum cf_type_kind_t {
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
  TYPE_ARRAY_REFERENCE,
  TYPE_METHOD,
  TYPE_CONSTRUCTOR,
} kind;
typedef enum cf_type_kind_t cf_type_kind_t;

typedef struct {
  u16 max_stack;
  u16 max_locals;
  cf_variable_t *locals;
  cf_type_kind_t *stack;
  cf_stack_map_frame_t *stack_map_frames;
} cg_frame_t;

struct par_type_t;

typedef struct {
  u32 return_type_i;
  u8 argument_count;
  u32 argument_types_i;
  string_t descriptor;
} par_type_method_t;

struct par_type_t {
  cf_type_kind_t kind;
  union {
    string_t class_name;      // TYPE_INSTANCE_REFERENCE
    par_type_method_t method; // TYPE_METHOD, TYPE_CONSTRUCTOR
    u32 array_type_i;         // TYPE_ARRAY_REFERENCE
  } v;
};
typedef struct par_type_t par_type_t;

typedef struct {
  u16 start_pc;
  u16 end_pc;
  u16 handler_pc;
  u16 catch_type;
} cf_exception_t;

static u16
stack_map_offset_delta_from_last(const cf_stack_map_frame_t *stack_map_frames,
                                 u16 current_offset) {
  pg_assert(stack_map_frames != NULL);
  if (pg_array_len(stack_map_frames) == 0)
    return current_offset;

  const u16 last_offset = pg_array_last(stack_map_frames)->offset_absolute;
  pg_assert(last_offset < current_offset);
  return current_offset - last_offset - 1;
}

static void stack_map_add_same_frame(cg_frame_t *frame, u16 current_offset,
                                     arena_t *arena) {

  pg_assert(frame != NULL);
  pg_assert(frame->stack_map_frames != NULL);

  const u16 offset_delta =
      stack_map_offset_delta_from_last(frame->stack_map_frames, current_offset);
  pg_assert(offset_delta <= 63);
  pg_assert(offset_delta >= 0);
  pg_assert(offset_delta <= current_offset);

  const cf_stack_map_frame_t stack_map_frame = {
      .kind = offset_delta,
      .offset_absolute = current_offset,
      .offset_delta = offset_delta,
  };
  pg_array_append(frame->stack_map_frames, stack_map_frame, arena);
  LOG("fact='add same frame' current_offset=%hu offset_delta=%hu kind=%hu "
      "offset_absolute=%u len=%lu",
      current_offset, offset_delta, stack_map_frame.kind,
      stack_map_frame.offset_absolute, pg_array_len(frame->stack_map_frames));
}

static void stack_map_add_chop_frame(cg_frame_t *frame, u8 chopped_locals_count,
                                     cf_verification_info_t verification_info,
                                     u16 current_offset, arena_t *arena) {
  pg_assert(frame != NULL);
  pg_assert(frame->stack_map_frames != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(chopped_locals_count > 0);
  pg_assert(chopped_locals_count <= 3);
  pg_assert(pg_array_len(frame->stack) == 0);

  const u16 offset_delta =
      stack_map_offset_delta_from_last(frame->stack_map_frames, current_offset);
  pg_assert(offset_delta > 0);
  pg_assert(offset_delta <= current_offset);

  const cf_stack_map_frame_t stack_map_frame = {
      .kind = 251 - chopped_locals_count,
      .verification_info = verification_info,
      .offset_delta = offset_delta,
      .offset_absolute = current_offset,
  };
  pg_assert(stack_map_frame.kind >= 248);
  pg_assert(stack_map_frame.kind <= 250);
  pg_array_append(frame->stack_map_frames, stack_map_frame, arena);
}

static void stack_map_add_append_frame(cg_frame_t *frame, u8 added_locals_count,
                                       cf_verification_info_t verification_info,
                                       u16 current_offset, arena_t *arena) {
  pg_assert(frame != NULL);
  pg_assert(frame->stack_map_frames != NULL);
  pg_assert(added_locals_count > 0);
  pg_assert(added_locals_count <= 3);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) == 0);

  const u16 offset_delta =
      stack_map_offset_delta_from_last(frame->stack_map_frames, current_offset);
  pg_assert(offset_delta > 0);
  pg_assert(offset_delta <= current_offset);

  const cf_stack_map_frame_t stack_map_frame = {
      .kind = 251 + added_locals_count,
      .verification_info = verification_info,
      .offset_delta = offset_delta,
      .offset_absolute = current_offset,
  };
  pg_assert(stack_map_frame.kind >= 252);
  pg_assert(stack_map_frame.kind <= 254);
  pg_array_append(frame->stack_map_frames, stack_map_frame, arena);
}

static void stack_map_add_same_locals_1_stack_item_frame(
    cg_frame_t *frame, cf_verification_info_t verification_info,
    u16 current_offset, arena_t *arena) {
  pg_assert(frame != NULL);
  pg_assert(frame->stack_map_frames != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) == 1);

  const u16 offset_delta =
      stack_map_offset_delta_from_last(frame->stack_map_frames, current_offset);
  pg_assert(offset_delta > 0);
  pg_assert(offset_delta <= current_offset);

  const cf_stack_map_frame_t stack_map_frame = {
      .kind = offset_delta + 64,
      .verification_info = verification_info,
      .offset_delta = offset_delta,
      .offset_absolute = current_offset,
  };
  pg_assert(stack_map_frame.kind >= 64);
  pg_assert(stack_map_frame.kind <= 127);
  pg_array_append(frame->stack_map_frames, stack_map_frame, arena);
}

static u16 cf_verification_info_size(cf_verification_info_t verification_info) {
  switch (verification_info) {
  case VERIFICATION_INFO_TOP:
  case VERIFICATION_INFO_INT:
  case VERIFICATION_INFO_FLOAT:
  case VERIFICATION_INFO_NULL:
  case VERIFICATION_INFO_DOUBLE:
  case VERIFICATION_INFO_LONG:
    return 1;
  case VERIFICATION_INFO_OBJECT:
  case VERIFICATION_INFO_UNINITIALIZED:
    return 2;
  }
}

static u16 cf_type_kind_stack_size(cf_type_kind_t kind) {
  switch (kind) {
  case TYPE_ANY:
  case TYPE_METHOD:
  case TYPE_CONSTRUCTOR:
  case TYPE_VOID:
    pg_assert(0 && "unreachable");
  case TYPE_BYTE:
  case TYPE_CHAR:
  case TYPE_FLOAT:
  case TYPE_SHORT:
  case TYPE_BOOL:
  case TYPE_INT:
  case TYPE_INSTANCE_REFERENCE:
  case TYPE_ARRAY_REFERENCE:
    return 1;
  case TYPE_LONG:
  case TYPE_DOUBLE:
    return 2;
  }
}

static u16 cf_stack_type_dumbbed_down_for_jvm(cf_type_kind_t kind) {
  switch (kind) {
  case TYPE_ANY:
  case TYPE_METHOD:
  case TYPE_CONSTRUCTOR:
  case TYPE_VOID:
    pg_assert(0 && "unreachable");
  case TYPE_BYTE:
  case TYPE_CHAR:
  case TYPE_FLOAT:
  case TYPE_SHORT:
  case TYPE_BOOL:
  case TYPE_INT:
    return TYPE_INT;
  case TYPE_ARRAY_REFERENCE:
  case TYPE_INSTANCE_REFERENCE:
    return kind;
  default:
    return kind;
  }
}

static u16 cg_compute_stack_size(const cf_type_kind_t *stack) {
  pg_assert(stack != NULL);
  pg_assert(pg_array_len(stack) <= UINT16_MAX);

  u16 size = 0;
  for (u16 i = 0; i < pg_array_len(stack); i++) {
    size += cf_type_kind_stack_size(stack[i]);
  }
  pg_assert(size >= pg_array_len(stack));
  return size;
}

static cf_verification_info_t
cf_type_kind_to_verification_info(cf_type_kind_t kind) {
  switch (kind) {
  case TYPE_BYTE:
  case TYPE_BOOL:
  case TYPE_CHAR:
  case TYPE_SHORT:
  case TYPE_INT:
    return VERIFICATION_INFO_INT;
  case TYPE_FLOAT:
    return VERIFICATION_INFO_FLOAT;
  case TYPE_DOUBLE:
    return VERIFICATION_INFO_DOUBLE;
  case TYPE_LONG:
    return VERIFICATION_INFO_LONG;
  case TYPE_INSTANCE_REFERENCE:
  case TYPE_ARRAY_REFERENCE:
    return VERIFICATION_INFO_OBJECT;
  case TYPE_CONSTRUCTOR:
  case TYPE_ANY:
  case TYPE_METHOD:
  case TYPE_VOID:
    pg_assert(0 && "unreachable");
  }
}

static void stack_map_add_frame(cg_frame_t *frame, u16 current_offset,
                                const cg_frame_t *before,
                                const cg_frame_t *after, arena_t *arena) {
  pg_assert(frame != NULL);
  pg_assert(frame->stack_map_frames != NULL);
  pg_assert(before != NULL);
  pg_assert(after != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(after->stack) >= pg_array_len(before->stack));
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);

  const u16 diff_stack =
      pg_array_len(after->stack) - pg_array_len(before->stack);

  if (diff_stack == 0) {
    stack_map_add_same_frame(frame, current_offset, arena);
  } else if (diff_stack == 1) {
    stack_map_add_same_locals_1_stack_item_frame(
        frame, VERIFICATION_INFO_INT /* FIXME */, current_offset, arena);

  } else {
    pg_assert(0 && "todo");
  }
}

static void cf_code_array_push_u8(u8 **array, u8 x, arena_t *arena) {
  pg_array_append(*array, x, arena);
}

static void cf_code_array_push_u16(u8 **array, u16 x, arena_t *arena) {
  cf_code_array_push_u8(array, (u8)(x & 0xff00), arena);
  cf_code_array_push_u8(array, (u8)(x & 0x00ff), arena);
}

typedef enum {
  CAF_ACC_PUBLIC = 0x0001,
  CAF_ACC_STATIC = 0x0008,
  CAF_ACC_SUPER = 0x0020,
} cf_access_flags_t;

typedef struct {
  enum cp_info_kind_t {
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
} cf_constant_t;

typedef struct cf_constant_method_ref_t cf_constant_method_ref_t;

typedef struct cf_constant_name_and_type_t cf_constant_name_and_type_t;

typedef struct cf_constant_field_ref_t cf_constant_field_ref_t;

typedef struct {
  u64 len;
  u64 cap;
  cf_constant_t *values;
  arena_t *arena;
} cf_constant_array_t;

static cf_constant_array_t cf_constant_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_constant_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(cf_constant_t)),
      .arena = arena,
  };
}

static u16 cf_constant_array_push(cf_constant_array_t *array,
                                  const cf_constant_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(((u64)(array->values)) % 16 == 0);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_constant_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(cf_constant_t));
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
  pg_array_init_reserve(frame->stack_map_frames, 64, arena);
}

static void cg_frame_clone(cg_frame_t *dst, const cg_frame_t *src,
                           arena_t *arena) {
  pg_assert(src != NULL);
  pg_assert(src->stack != NULL);
  pg_assert(pg_array_len(src->stack) <= UINT16_MAX);
  pg_assert(src->locals != NULL);
  pg_assert(src->stack_map_frames != NULL);
  pg_assert(dst != NULL);
  pg_assert(arena != NULL);

  dst->max_stack = src->max_stack;
  dst->max_locals = src->max_locals;

  pg_array_init_reserve(dst->locals, pg_array_len(src->locals), arena);
  memcpy(dst->locals, src->locals,
         sizeof(cf_variable_t) * pg_array_len(src->locals));
  PG_ARRAY_HEADER(dst->locals)->len = pg_array_len(src->locals);

  pg_array_init_reserve(dst->stack, pg_array_len(src->stack), arena);
  memcpy(dst->stack, src->stack,
         sizeof(cf_type_kind_t) * pg_array_len(src->stack));
  PG_ARRAY_HEADER(dst->stack)->len = pg_array_len(src->stack);

  pg_array_init_reserve(dst->stack_map_frames,
                        pg_array_len(src->stack_map_frames), arena);
  memcpy(dst->stack_map_frames, src->stack_map_frames,
         sizeof(cf_stack_map_frame_t) * pg_array_len(src->stack_map_frames));
  PG_ARRAY_HEADER(dst->stack_map_frames)->len =
      pg_array_len(src->stack_map_frames);

  pg_assert(dst->stack != NULL);
  pg_assert(dst->locals != NULL);
  pg_assert(dst->stack_map_frames != NULL);
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

static void cf_fill_type_descriptor_string(const par_type_t *types, u32 type_i,
                                           string_t *type_descriptor,
                                           arena_t *arena) {
  pg_assert(types != NULL);
  pg_assert(type_i < pg_array_len(types));
  pg_assert(type_descriptor != NULL);

  const par_type_t *const type = &types[type_i];

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
  }
}

static u16 cf_asm_jump_conditionally(u8 **code, cg_frame_t *frame,
                                     u8 jump_opcode, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(frame != NULL);
  pg_assert(frame->locals != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) > 0);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);
  pg_assert(*pg_array_last(frame->stack) == TYPE_BOOL);

  cf_code_array_push_u8(code, jump_opcode, arena);
  const u16 jump_from_i = pg_array_len(*code);
  cf_code_array_push_u8(code, BYTECODE_IMPDEP1, arena);
  cf_code_array_push_u8(code, BYTECODE_IMPDEP2, arena);

  pg_array_drop_last(frame->stack);

  return jump_from_i;
}

static u16 cf_asm_jump(u8 **code, cg_frame_t *frame, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(frame != NULL);
  pg_assert(frame->locals != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);

  cf_code_array_push_u8(code, BYTECODE_GOTO, arena);
  const u16 from_location = pg_array_len(*code);
  cf_code_array_push_u8(code, BYTECODE_IMPDEP1, arena);
  cf_code_array_push_u8(code, BYTECODE_IMPDEP2, arena);

  return from_location;
}

static void cf_asm_store_variable_int(u8 **code, cg_frame_t *frame, u8 var_i,
                                      arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(frame != NULL);
  pg_assert(frame->locals != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) > 0);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);

  pg_assert(pg_array_len(frame->locals) >
            var_i); // FIXME: variable size. Also do we need to expand the
                    // local variable array automatically?

  pg_assert(cf_stack_type_dumbbed_down_for_jvm(
                frame->stack[pg_array_len(frame->stack) - 1]) == TYPE_INT);

  cf_code_array_push_u8(code, BYTECODE_ISTORE, arena);
  cf_code_array_push_u8(code, var_i, arena);

  pg_array_drop_last(frame->stack);
}

static void cf_asm_load_variable_int(u8 **code, cg_frame_t *frame, u8 var_i,
                                     arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(frame != NULL);
  pg_assert(frame->locals != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) < UINT16_MAX);
  pg_assert(var_i < pg_array_len(frame->locals)); // FIXME: local variable size
  pg_assert(pg_array_len(frame->locals) > 0);

  cf_code_array_push_u8(code, BYTECODE_ILOAD, arena);
  cf_code_array_push_u8(code, var_i, arena);

  pg_array_append(frame->stack, TYPE_INT, arena);
  frame->max_stack =
      pg_max(frame->max_stack, cg_compute_stack_size(frame->stack));
}

static void cf_asm_nop(u8 **code, arena_t *arena) {
  pg_assert(code != NULL);

  cf_code_array_push_u8(code, BYTECODE_NOP, arena);
}

static void cf_asm_iadd(u8 **code, cg_frame_t *frame, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(frame != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) >= 2);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);
  pg_assert(frame->stack[pg_array_len(frame->stack) - 1] == TYPE_INT);
  pg_assert(frame->stack[pg_array_len(frame->stack) - 2] == TYPE_INT);

  cf_code_array_push_u8(code, BYTECODE_IADD, arena);

  pg_array_drop_last(frame->stack);
}

static void cf_asm_ixor(u8 **code, cg_frame_t *frame, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(frame != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) >= 2);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);
  pg_assert(frame->stack[pg_array_len(frame->stack) - 1] == TYPE_INT);
  pg_assert(frame->stack[pg_array_len(frame->stack) - 2] == TYPE_INT);

  cf_code_array_push_u8(code, BYTECODE_IXOR, arena);

  pg_array_drop_last(frame->stack);
}

static void cf_asm_imul(u8 **code, cg_frame_t *frame, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(frame != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) >= 2);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);
  pg_assert(frame->stack[pg_array_len(frame->stack) - 1] == TYPE_INT);
  pg_assert(frame->stack[pg_array_len(frame->stack) - 2] == TYPE_INT);

  cf_code_array_push_u8(code, BYTECODE_IMUL, arena);

  pg_array_drop_last(frame->stack);
}

static void cf_asm_load_constant(u8 **code, u16 constant_i, cg_frame_t *frame,
                                 cf_type_kind_t type_kind, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(constant_i > 0);
  pg_assert(frame != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) < UINT16_MAX);

  cf_code_array_push_u8(code, BYTECODE_LDC_W, arena);
  cf_code_array_push_u16(code, constant_i, arena);

  pg_assert(pg_array_len(frame->stack) < UINT16_MAX);
  pg_array_append(frame->stack, type_kind, arena);
  frame->max_stack =
      pg_max(frame->max_stack, cg_compute_stack_size(frame->stack));
}

static void cf_asm_invoke_virtual(u8 **code, u16 method_ref_i,
                                  cg_frame_t *frame,
                                  const par_type_method_t *method_type,
                                  arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(frame != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);

  cf_code_array_push_u8(code, BYTECODE_INVOKE_VIRTUAL, arena);
  cf_code_array_push_u16(code, method_ref_i, arena);

  // FIXME: long, double takes 2 spots on the stack!
  const u16 pop_size = 1 /* objectref */ + method_type->argument_count;
  pg_assert(pg_array_len(frame->stack) >= pop_size);

  pg_array_drop_last_n(frame->stack, pop_size);
}

static void cf_asm_get_static(u8 **code, u16 field_i, cg_frame_t *frame,
                              arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(field_i > 0);
  pg_assert(frame != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);

  cf_code_array_push_u8(code, BYTECODE_GET_STATIC, arena);
  cf_code_array_push_u16(code, field_i, arena);

  pg_assert(pg_array_len(frame->stack) < UINT16_MAX);
  pg_array_append(frame->stack, TYPE_INSTANCE_REFERENCE, arena);
  frame->max_stack =
      pg_max(frame->max_stack, cg_compute_stack_size(frame->stack));
}

static void cf_asm_return(u8 **code, arena_t *arena) {
  cf_code_array_push_u8(code, BYTECODE_RETURN, arena);

  // TODO: pop the current frame.
}

static void cf_asm_invoke_special(u8 **code, u16 method_ref_i,
                                  cg_frame_t *frame,
                                  const par_type_method_t *method_type,
                                  arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(frame != NULL);
  pg_assert(frame->stack != NULL);
  pg_assert(pg_array_len(frame->stack) <= UINT16_MAX);

  cf_code_array_push_u8(code, BYTECODE_INVOKE_SPECIAL, arena);
  cf_code_array_push_u16(code, method_ref_i, arena);

  // FIXME: long, double takes 2 spots on the stack!
  pg_assert(pg_array_len(frame->stack) >= method_type->argument_count);
  pg_array_drop_last_n(frame->stack, method_type->argument_count);
}

static void cf_asm_call_superclass_constructor(
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
  cf_asm_invoke_special(code, super_class_constructor_i, frame, method_type,
                        arena);
}

typedef struct cf_attribute_t cf_attribute_t;

typedef struct {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  cf_attribute_t *attributes;
} cf_field_t;

typedef struct cf_method_t cf_method_t;

typedef struct cf_interfaces_t cf_interfaces_t;

typedef struct {
  u16 start_pc;
  u16 line_number;
} cf_line_number_table_entry_t;

struct cf_attribute_t {
  enum cf_attribute_kind_t {
    ATTRIBUTE_KIND_SOURCE_FILE,
    ATTRIBUTE_KIND_CODE,
    ATTRIBUTE_KIND_LINE_NUMBER_TABLE,
    ATTRIBUTE_KIND_STACK_MAP_TABLE,
  } kind;

  u16 name;

  union {
    struct cf_attribute_code_t {
      u16 max_stack;
      u16 max_locals;
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
};

typedef struct cf_attribute_line_number_table_t
    cf_attribute_line_number_table_t;

typedef struct cf_attribute_code_t cf_attribute_code_t;

typedef struct cf_attribute_source_file_t cf_attribute_source_file_t;

struct cf_method_t {
  u16 access_flags;
  u16 name;
  u16 descriptor;
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
  cf_constant_array_t constant_pool;
  u16 access_flags;
  u16 this_class;
  u16 super_class;
  u16 interfaces_count;
  u16 *interfaces;
  u16 fields_count;
  cf_field_t *fields;
  cf_method_t *methods;
  cf_attribute_t *attributes;
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

static void cf_buf_read_attributes(char *buf, u64 buf_len, char **current,
                                   cf_class_file_t *class_file,
                                   cf_attribute_t **attributes, arena_t *arena);

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

  cf_buf_read_attributes(buf, buf_len, current, class_file, &code.attributes,
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
                                                  cf_class_file_t *class_file,
                                                  u32 attribute_len, u16 name_i,
                                                  cf_attribute_t **attributes,
                                                  arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  pg_unused(class_file);

  const char *const current_start = *current;

  const u16 len = buf_read_be_u16(buf, buf_len, current);
  cf_stack_map_frame_t *stack_map_frames = NULL;
  pg_array_init_reserve(stack_map_frames, len, arena);

  for (u16 i = 0; i < len; i++) {
    cf_stack_map_frame_t stack_map_frame = {
        .kind = buf_read_u8(buf, buf_len, current),
    };

    if (0 <= stack_map_frame.kind && stack_map_frame.kind <= 63) // same_frame
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
    } else if (255 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 255) { // full_frame_attribute
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

// FIXME: each function call here should take the `attributes` argument and
// push to it!
static void cf_buf_read_attribute(char *buf, u64 buf_len, char **current,
                                  cf_class_file_t *class_file,
                                  cf_attribute_t **attributes, arena_t *arena) {
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
    cf_buf_read_stack_map_table_attribute(buf, buf_len, current, class_file,
                                          size, name_i, attributes, arena);
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
                                   cf_attribute_t **attributes,
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
    cf_buf_read_attribute(buf, buf_len, current, class_file, attributes, arena);
  }
}

static void cf_buf_read_constant(char *buf, u64 buf_len, char **current,
                                 cf_class_file_t *class_file, u64 *i,
                                 u16 constant_pool_len) {
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
    cf_constant_array_push(&class_file->constant_pool, &constant);

    break;
  }
  case CONSTANT_POOL_KIND_INT: {
    const u32 value = buf_read_be_u32(buf, buf_len, current);
    pg_unused(value);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_FLOAT: {
    const u32 value = buf_read_be_u32(buf, buf_len, current);
    pg_unused(value);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_LONG: {
    const u32 high = buf_read_be_u32(buf, buf_len, current);
    pg_unused(high);
    const u32 low = buf_read_be_u32(buf, buf_len, current);
    pg_unused(low);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    cf_constant_array_push(&class_file->constant_pool, &constant);
    *i += 1;
    break;
  }
  case CONSTANT_POOL_KIND_DOUBLE: {
    const u32 high = buf_read_be_u32(buf, buf_len, current);
    pg_unused(high);
    const u32 low = buf_read_be_u32(buf, buf_len, current);
    pg_unused(low);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    cf_constant_array_push(&class_file->constant_pool, &constant);
    *i += 1;

    break;
  }
  case CONSTANT_POOL_KIND_CLASS_INFO: {
    const u16 class_name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_name_i > 0);
    pg_assert(class_name_i <= constant_pool_len);

    const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_CLASS_INFO,
                                    .v = {.class_name = class_name_i}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_STRING: {
    const u16 utf8_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(utf8_i > 0);
    pg_assert(utf8_i <= constant_pool_len);

    const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_STRING,
                                    .v = {.string_utf8_i = utf8_i}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_FIELD_REF: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_len);

    const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_len);

    const cf_constant_t constant = {
        .kind = CONSTANT_POOL_KIND_FIELD_REF,
        .v = {.field_ref = {.name = name_i, .type_descriptor = descriptor_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_REF: {
    const u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_len);

    const u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_len);

    const cf_constant_t constant = {
        .kind = CONSTANT_POOL_KIND_METHOD_REF,
        .v = {.method_ref = {.name_and_type = name_and_type_i,
                             .class = class_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_INTERFACE_METHOD_REF: {
    const u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_len);

    const u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_len);

    const cf_constant_t constant = {
        .kind = CONSTANT_POOL_KIND_INTERFACE_METHOD_REF,
    }; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_NAME_AND_TYPE: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_len);

    const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_len);

    const cf_constant_t constant = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = name_i,
                                .type_descriptor = descriptor_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_HANDLE: {
    const u8 reference_kind = buf_read_u8(buf, buf_len, current);
    pg_unused(reference_kind);
    const u16 reference_i = buf_read_be_u16(buf, buf_len, current);
    pg_unused(reference_i);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_TYPE: {
    const u16 descriptor = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor > 0);
    pg_assert(descriptor <= constant_pool_len);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_DYNAMIC: {
    const u16 bootstrap_method_attr_index =
        buf_read_be_u16(buf, buf_len, current);
    pg_unused(bootstrap_method_attr_index);

    const u16 name_and_type_index = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_index > 0);
    pg_assert(name_and_type_index <= constant_pool_len);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_INVOKE_DYNAMIC: {
    const u16 bootstrap_method_attr_index =
        buf_read_be_u16(buf, buf_len, current);
    pg_unused(bootstrap_method_attr_index);

    const u16 name_and_type_index = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_index > 0);
    pg_assert(name_and_type_index <= constant_pool_len);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_MODULE: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_len);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CONSTANT_POOL_KIND_PACKAGE: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_len);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
}

static void cf_buf_read_constants(char *buf, u64 buf_len, char **current,
                                  cf_class_file_t *class_file,
                                  u16 constant_pool_len) {
  for (u64 i = 1; i <= constant_pool_len; i++) {
    cf_buf_read_constant(buf, buf_len, current, class_file, &i,
                         constant_pool_len);
  }
}

static void cf_buf_read_method(char *buf, u64 buf_len, char **current,
                               cf_class_file_t *class_file, arena_t *arena) {
  cf_method_t method = {0};
  method.access_flags = buf_read_be_u16(buf, buf_len, current);
  method.name = buf_read_be_u16(buf, buf_len, current);
  pg_assert(method.name > 0);
  pg_assert(method.name <= class_file->constant_pool.len);

  method.descriptor = buf_read_be_u16(buf, buf_len, current);
  pg_assert(method.descriptor > 0);
  pg_assert(method.descriptor <= class_file->constant_pool.len);

  cf_buf_read_attributes(buf, buf_len, current, class_file, &method.attributes,
                         arena);

  pg_array_append(class_file->methods, method, arena);
}

static void cf_buf_read_methods(char *buf, u64 buf_len, char **current,
                                cf_class_file_t *class_file, arena_t *arena) {

  const u16 methods_count = buf_read_be_u16(buf, buf_len, current);
  pg_array_init_reserve(class_file->methods, methods_count, arena);

  for (u64 i = 0; i < methods_count; i++) {
    cf_buf_read_method(buf, buf_len, current, class_file, arena);
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
                         arena);

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
                                   cf_class_file_t *class_file,
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

  const u16 constant_pool_size = buf_read_be_u16(buf, buf_len, current) - 1;
  pg_assert(constant_pool_size > 0);
  class_file->constant_pool = cf_constant_array_make(constant_pool_size, arena);
  pg_assert(class_file->constant_pool.values != NULL);
  pg_assert(((u64)class_file->constant_pool.values) % 16 == 0);

  cf_buf_read_constants(buf, buf_len, current, class_file, constant_pool_size);

  class_file->access_flags = buf_read_be_u16(buf, buf_len, current);

  class_file->this_class = buf_read_be_u16(buf, buf_len, current);
  pg_assert(class_file->this_class > 0);
  pg_assert(class_file->this_class <= constant_pool_size);

  class_file->super_class = buf_read_be_u16(buf, buf_len, current);
  pg_assert(class_file->super_class <= constant_pool_size);

  cf_buf_read_interfaces(buf, buf_len, current, class_file, arena);

  cf_buf_read_fields(buf, buf_len, current, class_file, arena);

  cf_buf_read_methods(buf, buf_len, current, class_file, arena);

  cf_buf_read_attributes(buf, buf_len, current, class_file,
                         &class_file->attributes, arena);

  const u64 remaining = buf + buf_len - *current;
  pg_assert(remaining == 0);
}

static void cf_write_constant(const cf_class_file_t *class_file, FILE *file,
                              const cf_constant_t *constant) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);
  pg_assert(constant != NULL);

  switch (constant->kind) {
  case CONSTANT_POOL_KIND_UTF8: {
    fwrite(&constant->kind, sizeof(u8), 1, file);
    const string_t *const s = &constant->v.s;
    file_write_be_u16(file, s->len);
    fwrite(s->value, sizeof(u8), s->len, file);
    break;
  }
  case CONSTANT_POOL_KIND_INT:
    fwrite(&constant->kind, sizeof(u8), 1, file);
    file_write_be_u32(file, constant->v.number);
    break;
  case CONSTANT_POOL_KIND_FLOAT:
    pg_assert(0 && "unimplemented");
    break;
  case CONSTANT_POOL_KIND_LONG:
    pg_assert(0 && "unimplemented");
    break;
  case CONSTANT_POOL_KIND_DOUBLE:
    pg_assert(0 && "unimplemented");
    break;
  case CONSTANT_POOL_KIND_CLASS_INFO:
    fwrite(&constant->kind, sizeof(u8), 1, file);
    file_write_be_u16(file, constant->v.class_name);
    break;
  case CONSTANT_POOL_KIND_STRING:
    fwrite(&constant->kind, sizeof(u8), 1, file);
    file_write_be_u16(file, constant->v.string_utf8_i);
    break;
  case CONSTANT_POOL_KIND_FIELD_REF: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const cf_constant_field_ref_t *const field_ref = &constant->v.field_ref;

    file_write_be_u16(file, field_ref->name);
    file_write_be_u16(file, field_ref->type_descriptor);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_REF: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const cf_constant_method_ref_t *const method_ref = &constant->v.method_ref;

    file_write_be_u16(file, method_ref->class);
    file_write_be_u16(file, method_ref->name_and_type);
    break;
  }
  case CONSTANT_POOL_KIND_INTERFACE_METHOD_REF:
    pg_assert(0 && "unimplemented");
    break;
  case CONSTANT_POOL_KIND_NAME_AND_TYPE: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

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
}

static void cf_write_constant_pool(const cf_class_file_t *class_file,
                                   FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  const u16 len = class_file->constant_pool.len + 1;
  file_write_be_u16(file, len);

  for (u64 i = 0; i < class_file->constant_pool.len; i++) {
    pg_assert(class_file->constant_pool.values != NULL);
    pg_assert(((u64)class_file->constant_pool.values) % 16 == 0);

    const cf_constant_t *const constant = &class_file->constant_pool.values[i];
    cf_write_constant(class_file, file, constant);
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

static u32 cf_compute_verification_infos_size(
    const cf_stack_map_frame_t *stack_map_frame) {
  pg_assert(stack_map_frame != NULL);

  if (0 <= stack_map_frame->kind && stack_map_frame->kind <= 63) // same_frame
  {
    return 0;
  } else if (64 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 127) { // same_locals_1_stack_item_frame
    u32 size = sizeof(u8);
    if (stack_map_frame->verification_info < 7)
      return size;
    else if (stack_map_frame->verification_info <= 8)
      return size + sizeof(u16);
    else
      pg_assert(0 && "unreachable");
  } else if (128 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 246) { // reserved
    pg_assert(0 && "unreachable");
  } else if (247 <= stack_map_frame->kind &&
             stack_map_frame->kind <=
                 247) { // same_locals_1_stack_item_frame_extended
    pg_assert(0 && "todo");
  } else if (248 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 250) { // chop_frame
    pg_assert(0 && "todo");
  } else if (251 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 251) { // same_frame_extended
    pg_assert(0 && "todo");
  } else if (252 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 254) { // append_frame
    pg_assert(stack_map_frame->kind == 252 && "todo");
  } else if (255 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 255) { // full_frame
    pg_assert(0 && "todo");
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

      if (0 <= stack_map_frame->kind &&
          stack_map_frame->kind <= 63) // same_frame
      {
        size += sizeof(u8);
      } else if (64 <= stack_map_frame->kind &&
                 stack_map_frame->kind <=
                     127) { // same_locals_1_stack_item_frame
        size +=
            sizeof(u8) + cf_compute_verification_infos_size(stack_map_frame);

      } else if (128 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 246) { // reserved
        pg_assert(0 && "unreachable");
      } else if (247 <= stack_map_frame->kind &&
                 stack_map_frame->kind <=
                     247) { // same_locals_1_stack_item_frame_extended
        pg_assert(0 && "todo");
      } else if (248 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 250) { // chop_frame
        size += sizeof(u8) + sizeof(u16);
      } else if (251 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 251) { // same_frame_extended
        pg_assert(0 && "todo");
      } else if (252 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 254) { // append_frame
        pg_assert(stack_map_frame->kind == 252 && "todo");
        size += sizeof(u8) + sizeof(u16) + sizeof(u8);
      } else if (255 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 255) { // full_frame
        pg_assert(0 && "todo");
      }
    }

    return size;
  }
  }
  pg_assert(0 && "unreachable");
}

static void cf_write_attributes(FILE *file, const cf_attribute_t *attributes);

static void cf_write_stack_map_table_attribute(
    FILE *file, const cf_stack_map_frame_t *stack_map_frame) {
  pg_assert(file != NULL);
  pg_assert(stack_map_frame != NULL);

  if (0 <= stack_map_frame->kind && stack_map_frame->kind <= 63) // same_frame
  {
    file_write_u8(file, stack_map_frame->kind);
  } else if (64 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 127) { // same_locals_1_stack_item_frame
    file_write_u8(file, stack_map_frame->kind);
    file_write_u8(file, stack_map_frame->verification_info);
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
    file_write_u8(file, stack_map_frame->verification_info);
  } else if (255 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 255) { // full_frame
    pg_assert(0 && "todo");
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

  pg_array_init_reserve(code->code, 64, arena);
  pg_array_init_reserve(code->attributes, 4, arena);
  pg_array_init_reserve(code->exceptions, 0, arena);
}

static void cf_method_init(cf_method_t *method, arena_t *arena) {
  pg_assert(method != NULL);
  pg_assert(arena != NULL);

  pg_array_init_reserve(method->attributes, 1024, arena);
}

static u16 cf_add_constant_string(cf_constant_array_t *constant_pool,
                                  string_t s) {
  pg_assert(constant_pool != NULL);
  pg_assert(s.value != NULL);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                  .v = {.s = s}};
  return cf_constant_array_push(constant_pool, &constant);
}

static u16 cf_add_constant_cstring(cf_constant_array_t *constant_pool,
                                   char *s) {
  pg_assert(constant_pool != NULL);
  pg_assert(s != NULL);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                  .v = {.s = {
                                            .len = strlen(s),
                                            .value = s,
                                        }}};
  return cf_constant_array_push(constant_pool, &constant);
}

static u16 cf_add_constant_jstring(cf_constant_array_t *constant_pool,
                                   u16 constant_utf8_i) {
  pg_assert(constant_pool != NULL);
  pg_assert(constant_utf8_i > 0);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_STRING,
                                  .v = {.string_utf8_i = constant_utf8_i}};

  return cf_constant_array_push(constant_pool, &constant);
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

  string_t result = string_make(source_file_name, arena);
  string_drop_after_last_incl(&result, '/');
  string_append_char_if_not_exists(&result, '/', arena);
  string_append_string(&result, last_path_component, arena);
  return result;
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

  if (S_ISREG(st.st_mode) && cstring_ends_with(path, path_len, ".class", 6)) {
    const int fd = open(path, O_RDONLY);
    pg_assert(fd > 0);

    char *buf = arena_alloc(arena, st.st_size, sizeof(u8));
    const ssize_t read_bytes = read(fd, buf, st.st_size);
    pg_assert(read_bytes == st.st_size);
    close(fd);

    char *current = buf;
    cf_class_file_t class_file = {
        .file_path = string_make_from_c(path, arena),
    };
    cf_buf_read_class_file(buf, read_bytes, &current, &class_file, arena);
    pg_array_append(*class_files, class_file, arena);
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

static bool
cf_class_files_find_method_exactly(const cf_class_file_t *class_files,
                                   string_t class_name, string_t method_name,
                                   string_t descriptor) {
  pg_assert(class_files != NULL);
  pg_assert(descriptor.len > 0);
  pg_assert(descriptor.value != NULL);

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

typedef enum {
  TOKEN_KIND_NONE,
  TOKEN_KIND_NUMBER,
  TOKEN_KIND_PLUS,
  TOKEN_KIND_STAR,
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
} lex_token_kind_t;

typedef struct {
  lex_token_kind_t kind;
  u32 source_offset;
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

static u8 lex_peek(const char *buf, u32 buf_len, const char *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  return lex_is_at_end(buf, buf_len, current) ? 0 : **current;
}

static u8 lex_peek_next(const char *buf, u32 buf_len,
                        const char *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  const char *const next = *current + 1;
  return lex_is_at_end(buf, buf_len, &next) ? 0 : *next;
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

static bool lex_is_digit(const char *buf, u32 buf_len,
                         const char *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return ('0' <= **current && **current <= '9');
}

static bool lex_is_identifier_char(const char *buf, u32 buf_len,
                                   const char *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return ut_char_is_alphabetic(**current) ||
         lex_is_digit(buf, buf_len, current) ||
         lex_peek(buf, buf_len, current) == '_';
}

static u32 lex_number_length(const char *buf, u32 buf_len, u32 current_offset) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current_offset < buf_len);

  const u32 start_offset = current_offset;
  const char *current = &buf[current_offset];
  pg_assert(lex_is_digit(buf, buf_len, &current));

  lex_advance(buf, buf_len, &current);

  while (!lex_is_at_end(buf, buf_len, &current)) {
    lex_peek(buf, buf_len, &current);

    if (!lex_is_digit(buf, buf_len, &current))
      break;
    lex_advance(buf, buf_len, &current);
  }

  pg_assert(!lex_is_at_end(buf, buf_len, &current));
  pg_assert(!lex_is_digit(buf, buf_len, &current));

  const u32 end_offset_excl = lex_get_current_offset(buf, buf_len, &current);
  pg_assert(end_offset_excl > start_offset);
  pg_assert(end_offset_excl <= buf_len);

  const u32 len = end_offset_excl - start_offset;
  pg_assert(len >= 1);
  pg_assert(len <= buf_len);
  return len;
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
    lex_peek(buf, buf_len, &current);

    if (!lex_is_identifier_char(buf, buf_len, &current))
      break;
    lex_advance(buf, buf_len, &current);
  }

  pg_assert(!lex_is_at_end(buf, buf_len, &current));
  pg_assert(!lex_is_identifier_char(buf, buf_len, &current));

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
  pg_assert(lex_is_digit(buf, buf_len, current));

  const u32 start_offset = lex_get_current_offset(buf, buf_len, current);

  lex_advance(buf, buf_len, current);

  while (!lex_is_at_end(buf, buf_len, current)) {
    lex_peek(buf, buf_len, current);

    if (!lex_is_digit(buf, buf_len, current))
      break;
    lex_advance(buf, buf_len, current);
  }

  pg_assert(!lex_is_at_end(buf, buf_len, current));
  pg_assert(!lex_is_digit(buf, buf_len, current));

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
      if (lex_peek_next(buf, buf_len, current) == '=') {
        const lex_token_t token = {
            .kind = TOKEN_KIND_NOT_EQUAL,
            .source_offset = lex_get_current_offset(buf, buf_len, current),
        };
        pg_array_append(lexer->tokens, token, arena);
        lex_advance(buf, buf_len, current);
        lex_advance(buf, buf_len, current);
      } else {
        const lex_token_t token = {
            .kind = TOKEN_KIND_NOT,
            .source_offset = lex_get_current_offset(buf, buf_len, current),
        };
        pg_array_append(lexer->tokens, token, arena);
        lex_advance(buf, buf_len, current);
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
    case '*': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_STAR,
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
    case '=': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_EQUAL,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      pg_array_append(lexer->tokens, token, arena);
      lex_advance(buf, buf_len, current);
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
      if (ut_char_is_alphabetic(**current)) {
        lex_identifier(lexer, buf, buf_len, current, arena);
      } else if (lex_is_digit(buf, buf_len, current)) {
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
  case TOKEN_KIND_STAR:
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
    return 1;
  case TOKEN_KIND_KEYWORD_IF:
  case TOKEN_KIND_NOT_EQUAL:
  case TOKEN_KIND_LE:
  case TOKEN_KIND_GE:
  case TOKEN_KIND_EQUAL_EQUAL:
    return 2;
  case TOKEN_KIND_KEYWORD_FUN:
  case TOKEN_KIND_KEYWORD_VAR:
    return 3;
  case TOKEN_KIND_KEYWORD_TRUE:
  case TOKEN_KIND_KEYWORD_ELSE:
    return 4;
  case TOKEN_KIND_KEYWORD_FALSE:
    return 5;
  case TOKEN_KIND_BUILTIN_PRINTLN:
    return 7;

  case TOKEN_KIND_NUMBER:
    return lex_number_length(buf, buf_len, token.source_offset);

  case TOKEN_KIND_IDENTIFIER:
    return lex_identifier_length(buf, buf_len, token.source_offset);
  }
}

// ------------------------------ Parser

typedef enum {
  AST_KIND_NONE,
  AST_KIND_NUM,
  AST_KIND_BOOL,
  AST_KIND_BUILTIN_PRINTLN,
  AST_KIND_FUNCTION_DEFINITION,
  AST_KIND_BINARY,
  AST_KIND_UNARY,
  AST_KIND_VAR_DEFINITION,
  AST_KIND_VAR_REFERENCE,
  AST_KIND_IF,
  AST_KIND_LIST,
  AST_KIND_MAX,
} par_ast_node_kind_t;

static const char *par_ast_node_kind_to_string[AST_KIND_MAX] = {
    [AST_KIND_NONE] = "NONE",
    [AST_KIND_NUM] = "NUM",
    [AST_KIND_BOOL] = "BOOL",
    [AST_KIND_BUILTIN_PRINTLN] = "BUILTIN_PRINTLN",
    [AST_KIND_FUNCTION_DEFINITION] = "FUNCTION_DEFINITION",
    [AST_KIND_VAR_DEFINITION] = "VAR_DEFINITION",
    [AST_KIND_VAR_REFERENCE] = "VAR_REFERENCE",
    [AST_KIND_IF] = "IF",
    [AST_KIND_BINARY] = "BINARY",
    [AST_KIND_UNARY] = "UNARY",
    [AST_KIND_LIST] = "LIST",
};

typedef struct {
  par_ast_node_kind_t kind;
  u32 main_token;
  u32 lhs;
  u32 rhs;
  u32 type_i; // TODO: should it be separate?
} par_ast_node_t;

typedef enum {
  PARSER_STATE_OK,
  PARSER_STATE_ERROR,
  PARSER_STATE_PANIC,
  PARSER_STATE_SYNCED,
} par_parser_state_t;

typedef struct {
  char *buf;
  u32 buf_len;
  u32 tokens_i;
  lex_lexer_t *lexer;
  par_ast_node_t *nodes;
  par_parser_state_t state;
  par_type_t *types;
  u32 current_function_i;
  par_variable_t *variables;
  u32 scope_depth;
} par_parser_t;

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

static string_t ty_type_to_human_string(const par_type_t *types, u32 type_i,
                                        arena_t *arena) {
  const par_type_t *const type = &types[type_i];

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

  const par_ast_node_t *const node = &parser->nodes[node_i];
  if (node->kind == AST_KIND_NONE)
    return;

  const char *const kind_string = par_ast_node_kind_to_string[node->kind];
  const lex_token_t token = parser->lexer->tokens[node->main_token];
  u32 line = 0;
  u32 column = 0;
  string_t token_string = {0};
  par_find_token_position(parser, token, &line, &column, &token_string);

#ifdef PG_WITH_LOG
  ut_fwrite_indent(file, indent);
#endif

  const string_t human_type =
      ty_type_to_human_string(parser->types, node->type_i, arena);
  LOG("[%ld] %s %.*s : %.*s (at %.*s:%u:%u:%u)", node - parser->nodes,
      kind_string, token_string.len, token_string.value, human_type.len,
      human_type.value, parser->lexer->file_path.len,
      parser->lexer->file_path.value, line, column, token.source_offset);

  pg_assert(indent < UINT16_MAX - 1); // Avoid overflow.
  if (node->kind != AST_KIND_BOOL) {
    par_ast_fprint_node(parser, node->lhs, file, indent + 2, arena);
    par_ast_fprint_node(parser, node->rhs, file, indent + 2, arena);
  }
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

static lex_token_t par_advance_token(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return parser->lexer->tokens[parser->tokens_i++];
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

static u64 par_number(const par_parser_t *parser, lex_token_t token) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

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
    pg_assert('0' <= c && c <= '9');
    number += ten_unit * (c - '0');
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

static u32 par_parse_builtin_println(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  par_expect_token(parser, TOKEN_KIND_LEFT_PAREN, "expected left parenthesis");

  par_ast_node_t node = {
      .kind = AST_KIND_BUILTIN_PRINTLN,
      .main_token = parser->tokens_i - 2,
      .lhs = par_parse_expression(parser, arena),
  };
  pg_array_append(parser->nodes, node, arena);
  const u32 node_i = pg_array_last_index(parser->nodes);

  par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                   "expected right parenthesis");
  return node_i;
}

static u32 par_parse_block_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (par_match_token(parser, TOKEN_KIND_LEFT_BRACE)) {
    return par_parse_block(parser, arena);
  } else {
    return par_parse_expression(parser, arena);
  }
}

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
  //    condition     BINARY
  //                 /      \
  //             then        else
  //
  // clang-format on

  const par_ast_node_t binary_node = {
      .kind = AST_KIND_BINARY,
      .main_token = parser->tokens_i - 1,
      .lhs = par_parse_block_expression(parser, arena), // Then
      .rhs = par_match_token(parser, TOKEN_KIND_KEYWORD_ELSE)
                 ? par_parse_block_expression(parser, arena)
                 : 0,
  };
  pg_array_append(parser->nodes, binary_node, arena);

  const par_ast_node_t if_node = {
      .kind = AST_KIND_IF,
      .main_token = main_token_i,
      .lhs = condition_i,
      .rhs = pg_array_last_index(parser->nodes),
  };
  pg_array_append(parser->nodes, if_node, arena);
  return pg_array_last_index(parser->nodes);
}

static u32 par_parse_primary_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (par_match_token(parser, TOKEN_KIND_NUMBER)) {

    const par_ast_node_t node = {
        .kind = AST_KIND_NUM,
        .main_token = parser->tokens_i - 1,
    };
    pg_array_append(parser->nodes, node, arena);
    return pg_array_last_index(parser->nodes);
  } else if (par_match_token(parser, TOKEN_KIND_KEYWORD_FALSE) ||
             par_match_token(parser, TOKEN_KIND_KEYWORD_TRUE)) {
    const lex_token_t token = parser->lexer->tokens[parser->tokens_i - 1];
    const bool is_true = parser->buf[token.source_offset] == 't';
    const par_ast_node_t node = {
        .kind = AST_KIND_BOOL,
        .main_token = parser->tokens_i - 1,
        .lhs = is_true,
    };
    pg_array_append(parser->nodes, node, arena);
    return pg_array_last_index(parser->nodes);
  } else if (par_match_token(parser, TOKEN_KIND_BUILTIN_PRINTLN)) {
    return par_parse_builtin_println(parser, arena);
  } else if (par_match_token(parser, TOKEN_KIND_IDENTIFIER)) {
    par_ast_node_t node = {
        .kind = AST_KIND_VAR_REFERENCE,
        .main_token = parser->tokens_i - 1,
    };
    pg_array_append(parser->nodes, node, arena);

    const string_t variable_name = par_token_to_string(parser, node.main_token);
    const u32 variable_i = par_find_variable(parser, variable_name);
    if (variable_i == (u32)-1) {
      par_error(parser, parser->lexer->tokens[node.main_token],
                "unknown reference to variable");
    } else {
      pg_array_last(parser->nodes)->lhs =
          parser->variables[variable_i].var_definition_node_i;
    }
    return pg_array_last_index(parser->nodes);
  } else if (par_match_token(parser, TOKEN_KIND_KEYWORD_IF)) {
    return par_parse_if_expression(parser, arena);
  }

  par_advance_token(parser);
  return 0;
}

static u32 par_parse_var_definition(par_parser_t *parser, arena_t *arena) {
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
        parser->lexer->tokens[previous_var_node->main_token];

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
      .main_token = name_token_i,
      .lhs = par_parse_expression(parser, arena),
  };
  pg_array_append(parser->nodes, node, arena);

  const string_t variable_name = par_token_to_string(parser, name_token_i);
  par_declare_variable(parser, variable_name,
                       pg_array_last_index(parser->nodes), arena);
  return pg_array_last_index(parser->nodes);
}

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

  if (par_match_token(parser, TOKEN_KIND_KEYWORD_VAR))
    return par_parse_var_definition(parser, arena);
  else
    return par_parse_expression(parser, arena);
}

static u32 par_parse_postfix_unary_expression(par_parser_t *parser,
                                              arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_primary_expression(
      parser, arena); // TODO: parse {0,n} postfix unary suffix.
}

static u32 par_parse_prefix_unary_expression(par_parser_t *parser,
                                             arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  if (par_match_token(parser, TOKEN_KIND_NOT)) {
    const par_ast_node_t node = {
        .kind = AST_KIND_UNARY,
        .lhs = par_parse_postfix_unary_expression(parser, arena),
        .main_token = parser->tokens_i - 1,
    };
    pg_array_append(parser->nodes, node, arena);
    return pg_array_last_index(parser->nodes);
  }

  return par_parse_postfix_unary_expression(parser, arena);
}

static u32 par_parse_multiplicative_expression(par_parser_t *parser,
                                               arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 expression_node = par_parse_prefix_unary_expression(parser, arena);
  if (!par_match_token(parser, TOKEN_KIND_STAR))
    return expression_node;

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = expression_node,
      .main_token = parser->tokens_i - 1,
      .rhs = par_parse_multiplicative_expression(parser, arena),
  };
  pg_array_append(parser->nodes, node, arena);
  return pg_array_last_index(parser->nodes);
}

static u32 par_parse_additive_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  const u32 expression_node =
      par_parse_multiplicative_expression(parser, arena);
  if (!par_match_token(parser, TOKEN_KIND_PLUS))
    return expression_node;

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = expression_node,
      .main_token = parser->tokens_i - 1,
      .rhs = par_parse_additive_expression(parser, arena),
  };
  pg_array_append(parser->nodes, node, arena);
  return pg_array_last_index(parser->nodes);
}

static u32 par_parse_expression(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  return par_parse_additive_expression(parser, arena);
}

static u32 par_parse_block(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  // Empty block.
  if (par_match_token(parser, TOKEN_KIND_RIGHT_BRACE))
    return 0;

  if (par_is_at_end(parser)) {
    par_expect_token(parser, TOKEN_KIND_RIGHT_BRACE,
                     "expected right curly brace after the arguments");
    return 0;
  }

  par_begin_scope(parser);

  const par_ast_node_t root = {
      .kind = AST_KIND_LIST,
      .lhs = par_parse_statement(parser, arena),
      .rhs = par_parse_block(parser, arena),
  };
  pg_array_append(parser->nodes, root, arena);

  par_end_scope(parser);
  return pg_array_last_index(parser->nodes);
}

static u32 par_parse_function_arguments(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  // No arguments.
  if (par_match_token(parser, TOKEN_KIND_RIGHT_PAREN))
    return 0;

  const par_ast_node_t node = {
      .kind = AST_KIND_LIST,
  };
  pg_array_append(parser->nodes, node, arena);
  u32 last_node_i = pg_array_last_index(parser->nodes);
  const u32 root_i = last_node_i;

  do {
    const par_ast_node_t node = {
        .kind = AST_KIND_LIST,
        .lhs = par_parse_expression(parser, arena),
    };
    pg_array_append(parser->nodes, node, arena);
    last_node_i = parser->nodes[last_node_i].rhs =
        pg_array_last_index(parser->nodes);
  } while (par_match_token(parser, TOKEN_KIND_COMMA));

  par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                   "expected right parenthesis after the arguments");
  return root_i;
}

static u32 par_parse_function_definition(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  par_expect_token(parser, TOKEN_KIND_IDENTIFIER,
                   "expected function name (identifier)");
  const u32 start_token = parser->tokens_i - 1;

  const par_ast_node_t node = {
      .kind = AST_KIND_FUNCTION_DEFINITION,
      .main_token = start_token,
  };
  pg_array_append(parser->nodes, node, arena);
  const u32 fn_i = parser->current_function_i =
      pg_array_last_index(parser->nodes);

  par_expect_token(parser, TOKEN_KIND_LEFT_PAREN,
                   "expected left parenthesis before the arguments");
  parser->nodes[parser->current_function_i].lhs =
      par_parse_function_arguments(parser, arena);

  par_expect_token(parser, TOKEN_KIND_LEFT_BRACE,
                   "expected left curly brace before the arguments");
  parser->nodes[parser->current_function_i].rhs =
      par_parse_block(parser, arena);
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

static u32 par_parse_declaration(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->nodes != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));

  u32 new_node_i = 0;
  if (par_match_token(parser, TOKEN_KIND_KEYWORD_FUN))
    new_node_i = par_parse_function_definition(parser, arena);
  else
    new_node_i = par_parse_statement(parser, arena);

  par_sync_if_panicked(parser);

  return new_node_i;
}

static u32 par_parse_declarations(par_parser_t *parser, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens != NULL);
  pg_assert(parser->tokens_i <= pg_array_len(parser->lexer->tokens));
  pg_assert(pg_array_len(parser->lexer->tokens) >= 1);

  const par_ast_node_t node = {
      .kind = AST_KIND_LIST,
      .lhs = par_parse_declaration(parser, arena),
      .rhs = par_is_at_end(parser) ? 0 : par_parse_declarations(parser, arena),
  };
  pg_array_append(parser->nodes, node, arena);
  return pg_array_last_index(parser->nodes);
}

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
  pg_array_append(parser->nodes, dummy_node, arena);

  const u32 root_i = par_parse_declarations(parser, arena);

  pg_array_init_reserve(parser->types, pg_array_len(parser->nodes) + 32, arena);
  pg_array_append(parser->types, (par_type_t){0}, arena); // Default value.
  return root_i;
}

// --------------------------------- Typing

// TODO: Something smarter.
// TODO: Find a better name.
static bool ty_type_eq(const par_type_t *types, u32 lhs_i, u32 rhs_i,
                       u32 *result_i) {
  pg_assert(types != NULL);
  pg_assert(lhs_i < pg_array_len(types));
  pg_assert(rhs_i < pg_array_len(types));
  pg_assert(result_i != NULL);

  const par_type_t *const lhs = &types[lhs_i];
  const par_type_t *const rhs = &types[rhs_i];
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

static u32 ty_add_type(par_type_t **types, const par_type_t *type,
                       arena_t *arena) {
  pg_assert(types != NULL);
  pg_assert(type != NULL);

  // TODO: Deduplicate.
  pg_array_append(*types, *type, arena);
  return pg_array_last_index(*types);
}

static u32 ty_resolve_types(par_parser_t *parser,
                            const cf_class_file_t *class_files, u32 node_i,
                            arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(class_files != NULL);
  pg_assert(node_i < pg_array_len(parser->nodes));

  par_ast_node_t *const node = &parser->nodes[node_i];
  switch (node->kind) {
  case AST_KIND_NONE:
    pg_array_append(parser->types, (par_type_t){.kind = TYPE_ANY}, arena);

    return node->type_i = pg_array_last_index(parser->types);
  case AST_KIND_BOOL:
    pg_array_append(parser->types, (par_type_t){.kind = TYPE_BOOL}, arena);
    return node->type_i = pg_array_last_index(parser->types);
  case AST_KIND_BUILTIN_PRINTLN: {
    ty_resolve_types(parser, class_files, node->lhs, arena);

    const par_ast_node_t *const lhs = &parser->nodes[node->lhs];
    const par_type_t *const lhs_type = &parser->types[lhs->type_i];

    const par_type_t void_type = {.kind = TYPE_VOID};
    const u32 return_type_i = ty_add_type(&parser->types, &void_type, arena);
    const par_type_t println_type = {
        .kind = TYPE_METHOD,
        .v = {.method = {
                  .argument_count = 1,
                  .return_type_i = return_type_i,
                  .argument_types_i =
                      ty_add_type(&parser->types, lhs_type, arena),
              }}};
    pg_array_append(parser->types, println_type, arena);
    node->type_i = pg_array_last_index(parser->types);

    string_t descriptor = string_reserve(64, arena);
    cf_fill_type_descriptor_string(
        parser->types, pg_array_last_index(parser->types), &descriptor, arena);

    pg_array_last(parser->types)->v.method.descriptor = descriptor;

    if (!cf_class_files_find_method_exactly(
            class_files, string_make_from_c_no_alloc("java/io/PrintStream"),
            string_make_from_c_no_alloc("println"), descriptor)) {
      const lex_token_t token = parser->lexer->tokens[node->main_token];
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error, "incompatible types: ", arena);
      string_append_string(
          &error, ty_type_to_human_string(parser->types, node->type_i, arena),
          arena);
      string_append_cstring(&error, " vs ", arena);
      string_append_string(
          &error, ty_type_to_human_string(parser->types, lhs->type_i, arena),
          arena);
      par_error(parser, token, error.value);
    }

    return return_type_i;
  }
  case AST_KIND_NUM:
    pg_array_append(parser->types, (par_type_t){.kind = TYPE_INT},
                    arena); // TODO: something smarter.
    return node->type_i = pg_array_last_index(parser->types);
  case AST_KIND_UNARY:
    return node->type_i =
               ty_resolve_types(parser, class_files, node->lhs, arena);
  case AST_KIND_BINARY: {
    pg_assert(node->main_token > 0);

    const u32 lhs_i = ty_resolve_types(parser, class_files, node->lhs, arena);
    const u32 rhs_i = ty_resolve_types(parser, class_files, node->rhs, arena);

    if (!ty_type_eq(parser->types, lhs_i, rhs_i, &node->type_i)) {
      const lex_token_t token = parser->lexer->tokens[node->main_token];
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error, "incompatible types: ", arena);
      string_append_string(
          &error, ty_type_to_human_string(parser->types, lhs_i, arena), arena);
      string_append_cstring(&error, " vs ", arena);
      string_append_string(
          &error, ty_type_to_human_string(parser->types, rhs_i, arena), arena);
      par_error(parser, token, error.value);
    }

    return node->type_i;
  }
  case AST_KIND_LIST: {
    ty_resolve_types(parser, class_files, node->lhs, arena);
    ty_resolve_types(parser, class_files, node->rhs, arena);

    pg_array_append(parser->types, (par_type_t){.kind = TYPE_VOID}, arena);

    return node->type_i = pg_array_last_index(parser->types);
  }
  case AST_KIND_FUNCTION_DEFINITION:
    ty_resolve_types(parser, class_files, node->lhs, arena);
    // Inspect body (rhs).
    ty_resolve_types(parser, class_files, node->rhs, arena);

    pg_array_append(parser->types, (par_type_t){.kind = TYPE_VOID}, arena);
    return node->type_i = pg_array_last_index(parser->types);

  case AST_KIND_VAR_DEFINITION: {
    const u32 type_lhs_i =
        ty_resolve_types(parser, class_files, node->lhs, arena);

    const string_t type_literal_string =
        par_token_to_string(parser, node->main_token + 2);
    const string_t type_inferred_string =
        ty_type_to_human_string(parser->types, type_lhs_i, arena);

    if (!string_eq(type_literal_string, type_inferred_string)) {
      const lex_token_t token = parser->lexer->tokens[node->main_token];
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error, "incompatible types: ", arena);
      string_append_string(&error, type_literal_string, arena);
      string_append_cstring(&error, " vs ", arena);
      string_append_string(&error, type_inferred_string, arena);
      par_error(parser, token, error.value);
    }

    return node->type_i = type_lhs_i;
  }
  case AST_KIND_VAR_REFERENCE: {
    pg_assert(node->lhs > 0);
    return node->type_i = parser->nodes[node->lhs].type_i;
  }
  case AST_KIND_IF: {
    pg_assert(node->lhs > 0);
    pg_assert(node->lhs < pg_array_len(parser->nodes));
    pg_assert(node->rhs > 0);
    pg_assert(node->rhs < pg_array_len(parser->nodes));

    const u32 type_condition_i =
        ty_resolve_types(parser, class_files, node->lhs, arena);

    if (parser->types[type_condition_i].kind != TYPE_BOOL) {
      const lex_token_t token = parser->lexer->tokens[node->main_token];
      string_t error = string_reserve(256, arena);
      string_append_cstring(&error,
                            "incompatible types, expect Boolean, got: ", arena);

      const string_t type_inferred_string =
          ty_type_to_human_string(parser->types, type_condition_i, arena);
      string_append_string(&error, type_inferred_string, arena);
      par_error(parser, token, error.value);
    }

    const u32 type_then_else_i =
        ty_resolve_types(parser, class_files, node->rhs, arena);
    pg_assert(type_then_else_i > 0);

    return node->type_i = type_then_else_i;
  }

  case AST_KIND_MAX:
    pg_assert(0 && "unreachable");
  }
}
// --------------------------------- Code generation

typedef struct {
  cf_attribute_code_t *code;
  cg_frame_t *frame;
  u16 out_field_ref_i;
  const cf_class_file_t *class_files;
} cg_generator_t;

static u32 cf_find_variable(const cg_frame_t *frame, u32 node_i) {
  pg_assert(frame != NULL);
  pg_assert(frame->locals != NULL);

  for (i64 i = pg_array_len(frame->locals) - 1; i >= 0; i--) {
    const cf_variable_t *const variable = &frame->locals[i];
    if (variable->node_i == node_i)
      return (u32)i;
  }

  return 0;
}

static void cg_emit_node(cg_generator_t *gen, par_parser_t *parser,
                         cf_class_file_t *class_file, u32 node_i,
                         arena_t *arena);

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
  //      x     |    jump_conditionally_offset1 <----- jump_conditionally_from_i
  //      x     |    jump_conditionally_offset2
  //      x     |    <then branch>
  //  +   x  ...|... jump
  //  +   x  .  |    jump_offset1 <------------------- jump_from_i
  //  +   x  .  |    jump_offset2
  //  +   x  .  |--> <else branch> <--- stack map frame same for this location
  //  +      ......> ...           <--- stack map frame same for this location
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
  pg_assert(gen->frame->stack_map_frames != NULL);
  pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

  const par_ast_node_t *const node = &parser->nodes[node_i];
  pg_assert(node->type_i > 0);
  pg_assert(node->lhs > 0);
  pg_assert(node->lhs < pg_array_len(parser->nodes));
  pg_assert(node->rhs > 0);
  pg_assert(node->rhs < pg_array_len(parser->nodes));

  // Emit condition.
  cg_emit_node(gen, parser, class_file, node->lhs, arena);

  const u16 jump_conditionally_from_i = cf_asm_jump_conditionally(
      &gen->code->code, gen->frame, BYTECODE_IFEQ, arena);

  pg_assert(node->rhs > 0);
  const par_ast_node_t *const rhs = &parser->nodes[node->rhs];
  pg_assert(rhs->kind == AST_KIND_BINARY);

  // Emit `then` branch.
  // Save a clone of the frame before the `then` branch since we need it
  // later.
  cg_frame_t frame_before_then_else = {0};
  cg_frame_clone(&frame_before_then_else, gen->frame, arena);

  cg_emit_node(gen, parser, class_file, rhs->lhs, arena);
  const u16 jump_from_i = cf_asm_jump(&gen->code->code, gen->frame, arena);

  // Save a clone of the frame after the `then` branch executed so that we can
  // generate a stack map frame later.
  cg_frame_t frame_after_then = {0};
  cg_frame_clone(&frame_after_then, gen->frame, arena);

  // Emit `else` branch.
  // Restore the frame as if the `then` branch never executed.
  gen->frame = arena_alloc(arena, 1, sizeof(cg_frame_t));
  cg_frame_clone(gen->frame, &frame_before_then_else, arena);
  cg_emit_node(gen, parser, class_file, rhs->rhs, arena);
  // Add a nop to ensure the `<else branch>` has at least one instruction, so
  // that the corresponding, second, stack map frame can be unconditionally
  // emitted with an offset delta >= 1.
  cf_asm_nop(&gen->code->code, arena);
  pg_assert(pg_array_len(frame_after_then.stack) ==
            pg_array_len(gen->frame->stack));
  gen->frame->max_stack =
      pg_max(frame_after_then.max_stack, gen->frame->max_stack);
  gen->frame->max_locals =
      pg_max(frame_after_then.max_locals, gen->frame->max_locals);

  const u16 jump_to_i = pg_array_len(gen->code->code);

  // Patch first, conditional, jump.
  {
    const u16 jump_offset = (jump_from_i + 2) - (jump_conditionally_from_i - 1);
    gen->code->code[jump_conditionally_from_i + 0] =
        (u8)((u16)jump_offset & 0xff00) >> 8;
    gen->code->code[jump_conditionally_from_i + 1] =
        (u8)((u16)jump_offset & 0x00ff) >> 0;

    // This stack map frame covers the conditional jump as if we took it, so
    // the `then` branch never executed. Hence, it seems it should always be
    // `same_frame`?
    stack_map_add_same_frame(gen->frame, jump_from_i + 2, arena);
  }
  // Patch second, unconditional, jump.
  {
    const u16 jump_offset = (jump_to_i) - (jump_from_i - 1);
    gen->code->code[jump_from_i + 0] = (u8)((u16)jump_offset & 0xff00) >> 8;
    gen->code->code[jump_from_i + 1] = (u8)((u16)jump_offset & 0x00ff) >> 0;

    // This stack map frame covers the unconditional jump, i.e. the `then`
    // branch.
    stack_map_add_frame(gen->frame, jump_to_i, &frame_before_then_else,
                        &frame_after_then, arena);
  }
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

  if (node_i == 0)
    return;

  const par_ast_node_t *const node = &parser->nodes[node_i];

  switch (node->kind) {
  case AST_KIND_NONE:
    return;
  case AST_KIND_BOOL: {
    pg_assert(node->main_token < pg_array_len(parser->lexer->tokens));
    const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_INT,
                                    .v = {.number = node->lhs}};
    const u16 number_i =
        cf_constant_array_push(&class_file->constant_pool, &constant);

    pg_assert(gen->code != NULL);
    pg_assert(gen->code->code != NULL);
    pg_assert(gen->frame != NULL);

    const par_type_t *const type = &parser->types[node->type_i];
    cf_asm_load_constant(&gen->code->code, number_i, gen->frame, type->kind,
                         arena);
    break;
  }
  case AST_KIND_NUM: {
    pg_assert(node->main_token < pg_array_len(parser->lexer->tokens));
    const lex_token_t token = parser->lexer->tokens[node->main_token];

    const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_INT,
                                    .v = {.number = par_number(parser, token)}};
    const u16 number_i =
        cf_constant_array_push(&class_file->constant_pool, &constant);

    pg_assert(gen->code != NULL);
    pg_assert(gen->code->code != NULL);
    pg_assert(gen->frame != NULL);

    const par_type_t *const type = &parser->types[node->type_i];
    cf_asm_load_constant(&gen->code->code, number_i, gen->frame, type->kind,
                         arena);
    break;
  }
  case AST_KIND_BUILTIN_PRINTLN: {
    pg_assert(gen->out_field_ref_i > 0);

    cf_asm_get_static(&gen->code->code, gen->out_field_ref_i, gen->frame,
                      arena);

    cg_emit_node(gen, parser, class_file, node->lhs, arena);

    const par_type_t *const type = &parser->types[node->type_i];
    pg_assert(type->kind == TYPE_METHOD);

    const par_type_method_t *const method = &type->v.method;

    pg_assert(method->descriptor.value != NULL);
    pg_assert(method->descriptor.len > 0);
    const u16 descriptor_i =
        cf_add_constant_string(&class_file->constant_pool, method->descriptor);
    const u16 name_i =
        cf_add_constant_cstring(&class_file->constant_pool, "println");

    const cf_constant_t name_and_type = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = name_i,
                                .type_descriptor = descriptor_i}}};
    const u16 name_and_type_i =
        cf_constant_array_push(&class_file->constant_pool, &name_and_type);

    const u16 printstream_name_i = cf_add_constant_cstring(
        &class_file->constant_pool, "java/io/PrintStream");

    const cf_constant_t printstream_class = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {.class_name = printstream_name_i}};
    const u16 printstream_class_i =
        cf_constant_array_push(&class_file->constant_pool, &printstream_class);
    const cf_constant_t method_ref = {
        .kind = CONSTANT_POOL_KIND_METHOD_REF,
        .v = {.method_ref = {.class = printstream_class_i,
                             .name_and_type = name_and_type_i}}};
    const u16 method_ref_i =
        cf_constant_array_push(&class_file->constant_pool, &method_ref);

    cf_asm_invoke_virtual(&gen->code->code, method_ref_i, gen->frame, method,
                          arena);
    break;
  }
  case AST_KIND_FUNCTION_DEFINITION: {
    const u32 token_name_i = node->main_token;
    pg_assert(token_name_i < pg_array_len(parser->lexer->tokens));
    const lex_token_t token_name = parser->lexer->tokens[token_name_i];
    pg_assert(token_name.kind == TOKEN_KIND_IDENTIFIER);

    string_t method_name = {
        .len = lex_identifier_length(parser->buf, parser->buf_len,
                                     token_name.source_offset),
        .value = &parser->buf[token_name.source_offset],
    };
    const u16 method_name_i =
        cf_add_constant_string(&class_file->constant_pool, method_name);

    // FIXME: hardcoded type.

    pg_array_append(parser->types, (par_type_t){.kind = TYPE_VOID}, arena);
    const u32 void_type_i = pg_array_last_index(parser->types);

    const string_t string_class_name =
        string_make_from_c("java/lang/String", arena);
    const par_type_t string_type = {
        .kind = TYPE_INSTANCE_REFERENCE,
        .v = {.class_name = string_class_name},
    };
    pg_array_append(parser->types, string_type, arena);
    const u32 string_type_i = pg_array_last_index(parser->types);

    const par_type_t main_argument_types = {
        .kind = TYPE_ARRAY_REFERENCE,
        .v = {.array_type_i = string_type_i},
    };
    pg_array_append(parser->types, main_argument_types, arena);
    const u32 main_argument_types_i = pg_array_last_index(parser->types);

    const par_type_t main_type = {
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
    const u16 descriptor_i =
        cf_add_constant_string(&class_file->constant_pool, type_descriptor);

    cf_method_t method = {
        .access_flags = CAF_ACC_STATIC | CAF_ACC_PUBLIC /* FIXME */,
        .name = method_name_i,
        .descriptor = descriptor_i,
    };
    pg_array_init_reserve(method.attributes, 8, arena);

    cf_attribute_code_t code = {0};
    cf_attribute_code_init(&code, arena);
    gen->code = &code;
    cg_frame_t frame = {0};
    cg_frame_init(&frame, arena);
    const cf_variable_t arg0 = {.type_i = main_argument_types_i};
    pg_array_append(frame.locals, arg0, arena);
    frame.max_locals = pg_array_len(frame.locals);
    gen->frame = &frame;

    // `lhs` is the arguments, `rhs` is the body.
    // TODO: Handle `lhs`.
    if (node->lhs > 0)
      pg_assert(0 && "todo");

    cg_emit_node(gen, parser, class_file, node->rhs, arena);

    cf_asm_return(&code.code, arena);

    gen->code->max_stack = gen->frame->max_stack;
    gen->code->max_locals = gen->frame->max_locals;

    const cf_attribute_t attribute_stack_map_frames = {
        .kind = ATTRIBUTE_KIND_STACK_MAP_TABLE,
        .name = cf_add_constant_cstring(&class_file->constant_pool,
                                        "StackMapTable"),
        .v = {.stack_map_table = gen->frame->stack_map_frames}};
    pg_array_append(code.attributes, attribute_stack_map_frames, arena);

    const cf_attribute_t attribute_code = {
        .kind = ATTRIBUTE_KIND_CODE,
        .name = cf_add_constant_cstring(&class_file->constant_pool, "Code"),
        .v = {.code = code}};
    pg_array_append(method.attributes, attribute_code, arena);

    pg_array_append(class_file->methods, method, arena);

    // In the current implementation, 2 stack map frames are emitted per
    // if-then-else.
    pg_assert(pg_array_len(gen->frame->stack_map_frames) % 2 == 0);

    gen->code = NULL;
    gen->frame = NULL;
    break;
  }
  case AST_KIND_UNARY: {
    pg_assert(gen->frame != NULL);
    pg_assert(gen->frame->locals != NULL);
    pg_assert(gen->frame->stack != NULL);
    pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

    pg_assert(node->lhs < pg_array_len(parser->nodes));

    const u16 stack_before = pg_array_len(gen->frame->stack);

    const par_ast_node_t true_node = {
        .kind = AST_KIND_BOOL,
        .lhs = true,
    };
    pg_array_append(parser->nodes, true_node, arena);
    const u32 true_node_i = pg_array_last_index(parser->nodes);

    const par_ast_node_t false_node = {
        .kind = AST_KIND_BOOL,
        .lhs = false,
    };
    pg_array_append(parser->nodes, false_node, arena);
    const u32 false_node_i = pg_array_last_index(parser->nodes);

    const par_ast_node_t binary_node = {
        .kind = AST_KIND_BINARY,
        .rhs = true_node_i,
        .lhs = false_node_i,
        .main_token = node->main_token,
    };
    const lex_token_t token = parser->lexer->tokens[node->main_token];
    const bool is_not = token.kind == TOKEN_KIND_NOT;
    if (!is_not)
      pg_assert(0 && "todo");

    pg_array_append(parser->nodes, binary_node, arena);

    const par_ast_node_t if_node = {
        .kind = AST_KIND_IF,
        .lhs = node->lhs,
        .rhs = pg_array_last_index(parser->nodes),
    };
    pg_array_append(parser->nodes, if_node, arena);
    ty_resolve_types(parser, class_file, pg_array_last_index(parser->nodes),
                     arena);

    cg_emit_node(gen, parser, class_file, pg_array_last_index(parser->nodes),
                 arena);

    pg_assert(gen->frame != NULL);
    pg_assert(gen->frame->locals != NULL);
    pg_assert(gen->frame->stack != NULL);
    pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

    const u16 stack_after = pg_array_len(gen->frame->stack);
    pg_assert(stack_after == stack_before + 1); // TODO: Is it always +1?
    break;
  }
  case AST_KIND_BINARY: {
    pg_assert(gen->frame != NULL);
    pg_assert(gen->frame->locals != NULL);
    pg_assert(gen->frame->stack != NULL);
    pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

    pg_assert(node->lhs < pg_array_len(parser->nodes));
    pg_assert(node->rhs < pg_array_len(parser->nodes));

    cg_emit_node(gen, parser, class_file, node->lhs, arena);
    cg_emit_node(gen, parser, class_file, node->rhs, arena);

    const lex_token_t token = parser->lexer->tokens[node->main_token];
    switch (token.kind) {
    case TOKEN_KIND_NONE:
      break; // Nothing to do.
    case TOKEN_KIND_PLUS:
      cf_asm_iadd(&gen->code->code, gen->frame, arena);
      break;
    case TOKEN_KIND_STAR:
      cf_asm_imul(&gen->code->code, gen->frame, arena);
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
      pg_assert(gen->frame->stack != NULL);
      pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);
    }

    cg_emit_node(gen, parser, class_file, node->lhs, arena);
    cg_emit_node(gen, parser, class_file, node->rhs, arena);
    break;
  }
  case AST_KIND_VAR_DEFINITION: {
    pg_assert(gen->frame != NULL);
    pg_assert(gen->frame->locals != NULL);
    pg_assert(gen->frame->stack != NULL);
    pg_assert(pg_array_len(gen->frame->stack) < UINT16_MAX);
    pg_assert(node->type_i > 0);

    cg_emit_node(gen, parser, class_file, node->lhs, arena);
    pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

    const cf_variable_t variable = {
        .node_i = node_i,
        .type_i = node->type_i,
    };
    pg_array_append(gen->frame->locals, variable, arena);
    pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);
    gen->frame->max_locals =
        pg_max(gen->frame->max_locals, pg_array_len(gen->frame->locals));
    pg_assert(pg_array_len(gen->frame->stack) <= UINT16_MAX);

    cf_asm_store_variable_int(&gen->code->code, gen->frame,
                              pg_array_last_index(gen->frame->locals), arena);
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

    cf_asm_load_variable_int(&gen->code->code, gen->frame, var_i, arena);
    break;
  }
  case AST_KIND_IF: {
    cg_emit_if_then_else(gen, parser, class_file, node_i, arena);
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

// static void ty_add_method_type(par_type_t ** types, )

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
        cf_add_constant_cstring(&class_file->constant_pool, "out");
    const u16 out_descriptor_i = cf_add_constant_cstring(
        &class_file->constant_pool, "Ljava/io/PrintStream;");

    const cf_constant_t out_name_and_type = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = out_name_i,
                                .type_descriptor = out_descriptor_i}}};
    const u16 out_name_and_type_i =
        cf_constant_array_push(&class_file->constant_pool, &out_name_and_type);

    const u16 system_name_i =
        cf_add_constant_cstring(&class_file->constant_pool, "java/lang/System");
    const cf_constant_t system_class = {.kind = CONSTANT_POOL_KIND_CLASS_INFO,
                                        .v = {.class_name = system_name_i}};
    const u16 system_class_i =
        cf_constant_array_push(&class_file->constant_pool, &system_class);

    const cf_constant_t out_field_ref = {
        .kind = CONSTANT_POOL_KIND_FIELD_REF,
        .v = {.field_ref = {.name = system_class_i,
                            .type_descriptor = out_name_and_type_i}}};
    const u16 out_field_ref_i =
        cf_constant_array_push(&class_file->constant_pool, &out_field_ref);

    gen->out_field_ref_i = out_field_ref_i;
  }

  { // This class
    const string_t class_name =
        cg_make_class_name_from_path(class_file->file_path, arena);
    const u16 this_class_name_i =
        cf_add_constant_string(&class_file->constant_pool, class_name);

    const cf_constant_t this_class_info = {.kind =
                                               CONSTANT_POOL_KIND_CLASS_INFO,
                                           .v = {
                                               .class_name = this_class_name_i,
                                           }};
    class_file->this_class =
        cf_constant_array_push(&class_file->constant_pool, &this_class_info);
  }

  { // Super class
    const u16 constant_java_lang_object_string_i =
        cf_add_constant_cstring(&class_file->constant_pool, "java/lang/Object");

    const cf_constant_t super_class_info = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {
            .class_name = constant_java_lang_object_string_i,
        }};

    class_file->super_class =
        cf_constant_array_push(&class_file->constant_pool, &super_class_info);
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
  cg_emit_synthetic_class(&gen, parser, class_file, arena);

  if (pg_array_len(parser->nodes) == 1)
    return;

  cg_emit_node(&gen, parser, class_file, root_i, arena);
}
