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

#define pg_unused(x) (void)(x)

#define pg_assert(condition)                                                   \
  do {                                                                         \
    if (!(condition))                                                          \
      __builtin_trap();                                                        \
  } while (0)

#define pg_max(a, b) ((a) > (b) ? (a) : (b))
#define pg_clamp(min, x, max)                                                  \
  ((x) > (max)) ? (max) : ((x) < (min)) ? (min) : (x)

// ------------------- Utils

typedef struct {
  char *base;
  u64 current_offset;
  u64 capacity;
} arena_t;

static void arena_init(arena_t *arena, u64 capacity) {
  pg_assert(arena != NULL);

  arena->base = mmap(NULL, capacity, PROT_READ | PROT_WRITE,
                     MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  pg_assert(arena->base != NULL);
  pg_assert(((u64)arena->base % 16) == 0);
  arena->capacity = capacity;
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
  pg_assert(arena != NULL);
  pg_assert(arena->current_offset < arena->capacity);
  pg_assert(arena->current_offset + len < arena->capacity);
  pg_assert(((u64)((arena->base + arena->current_offset)) % 16) == 0);
  pg_assert(element_size > 0);
  const u64 actual_len = len * element_size; // TODO: check overflow.

  const u64 new_offset = align_forward_16(arena->current_offset + actual_len);
  pg_assert((new_offset % 16) == 0);

  void *res = arena->base + arena->current_offset;
  pg_assert((((u64)res) % 16) == 0);
  arena->current_offset = new_offset;
  pg_assert((((u64)arena->current_offset) % 16) == 0);
  return res;
}

typedef struct {
  u16 cap;
  u16 len;
  char *value;
  arena_t *arena;
} string_t;

static string_t string_reserve(u16 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (string_t){
      .cap = cap,
      .value = arena_alloc(arena, cap, sizeof(u8)),
      .arena = arena,
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
  pg_assert(res.len <= res.cap);
  pg_assert(res.arena != NULL);

  return res;
}

static string_t string_make(string_t src, arena_t *arena) {
  pg_assert(src.value != NULL);
  string_t result = string_reserve(src.len, arena);
  memcpy(result.value, src.value, src.len);
  result.len = src.len;

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
}

bool string_eq(string_t a, string_t b) {
  pg_assert(a.value != NULL);
  pg_assert(b.value != NULL);

  return a.len == b.len && memcmp(a.value, b.value, a.len) == 0;
}

bool mem_eq_c(const char *a, u32 a_len, char *b) {
  pg_assert(b != NULL);

  const u64 b_len = strlen(b);
  return a_len == b_len && memcmp(a, b, a_len) == 0;
}

bool string_eq_c(string_t a, char *b) {
  pg_assert(b != NULL);

  return mem_eq_c(a.value, a.len, b);
}

void string_append_char(string_t *s, char c) {
  pg_assert(s != NULL);
  pg_assert(s->cap != 0);
  pg_assert(s->len <= s->cap);
  pg_assert(s->arena != NULL);

  if (s->len == s->cap - 1) {
    s->cap *= 2;
    char *const new_s = arena_alloc(s->arena, s->cap, sizeof(u8));
    s->value = memcpy(new_s, s->value, s->len);
  }

  s->value[s->len] = c;
  s->len += 1;

  pg_assert(s->value != NULL);
  pg_assert(s->len <= s->cap);
  pg_assert(s->arena != NULL);
}

void string_append_char_if_not_exists(string_t *s, char c) {
  pg_assert(s != NULL);

  if (s->len > 0 && s->value[0] != c)
    string_append_char(s, c);
}

void string_append_string(string_t *a, const string_t *b) {
  pg_assert(a != NULL);
  pg_assert(b != NULL);
  pg_assert(a->cap != 0);
  pg_assert(a->len <= a->cap);
  pg_assert(a->arena != NULL);
  pg_assert(b->cap != 0);
  pg_assert(b->len <= b->cap);
  pg_assert(b->arena != NULL);

  for (u64 i = 0; i < b->len; i++)
    string_append_char(a, b->value[i]);

  pg_assert(a->value != NULL);
  pg_assert(a->len <= a->cap);
  pg_assert(a->arena != NULL);
}

void string_append_cstring(string_t *a, const char *b) {
  pg_assert(a != NULL);
  pg_assert(b != NULL);
  pg_assert(a->cap != 0);
  pg_assert(a->len <= a->cap);
  pg_assert(a->arena != NULL);

  for (u64 i = 0; i < strlen(b); i++)
    string_append_char(a, b[i]);

  pg_assert(a->value != NULL);
  pg_assert(a->len <= a->cap);
  pg_assert(a->arena != NULL);
}

bool cstring_ends_with(const char *s, u64 s_len, const char *suffix,
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
  BYTECODE_ALOAD_0 = 0x2a,
  BYTECODE_INVOKE_SPECIAL = 0xb7,
  BYTECODE_RETURN = 0xb1,
  BYTECODE_GET_STATIC = 0xb2,
  BYTECODE_BIPUSH = 0x10,
  BYTECODE_LDC = 0x12,
  BYTECODE_LDC_W = 0x13,
  BYTECODE_INVOKE_VIRTUAL = 0xb6,
} cf_op_kind_t;

static char *const CF_INIT_CONSTRUCTOR_STRING = "<init>";

typedef struct {
  u16 current_stack;
  u16 max_stack;
  u16 max_locals;
} cf_frame_t;

struct cf_type_t;

typedef struct {
  struct cf_type_t *return_type;
  u8 argument_count;
  struct cf_type_t *argument_types;
} cf_type_method_t;

struct cf_type_t {
  enum cf_type_kind_t {
    TYPE_VOID,
    TYPE_BYTE,
    TYPE_CHAR,
    TYPE_DOUBLE,
    TYPE_FLOAT,
    TYPE_INT,
    TYPE_LONG,
    TYPE_INSTANCE_REFERENCE,
    TYPE_SHORT,
    TYPE_BOOLEAN,
    TYPE_ARRAY_REFERENCE,
    TYPE_METHOD,
    TYPE_CONSTRUCTOR,
  } kind;
  union {
    string_t class_name;          // TYPE_INSTANCE_REFERENCE
    cf_type_method_t method;      // TYPE_METHOD, TYPE_CONSTRUCTOR
    struct cf_type_t *array_type; // TYPE_ARRAY_REFERENCE
  } v;
};
typedef struct cf_type_t cf_type_t;

typedef struct {
  u16 start_pc;
  u16 end_pc;
  u16 handler_pc;
  u16 catch_type;
} cf_exception_t;

typedef struct {
  u64 len;
  u64 cap;
  cf_exception_t *values;
  arena_t *arena;
} cf_exception_array_t;

cf_exception_array_t cf_exception_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_exception_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(cf_exception_t)),
      .arena = arena,
  };
}

void cf_exception_array_push(cf_exception_array_t *array,
                             const cf_exception_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_exception_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(cf_exception_t));
    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_exception_t));
    pg_assert(array->values != NULL);
    pg_assert(((u64)(array->values)) % 16 == 0);
    array->cap = new_cap;
  }

  array->values[array->len++] = *x;
}

typedef struct {
  u64 len;
  u64 cap;
  char *values;
  arena_t *arena;
} cf_code_array_t;

cf_code_array_t cf_code_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_code_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(u8)),
      .arena = arena,
  };
}

void cf_code_array_push_u8(cf_code_array_t *array, u8 x) {
  pg_assert(array != NULL);
  pg_assert(array->len < UINT32_MAX);
  pg_assert(array->values != NULL);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    char *const new_array = arena_alloc(array->arena, new_cap, sizeof(u8));
    array->values = memcpy(new_array, array->values, array->len * sizeof(u8));
    array->cap = new_cap;
  }

  array->values[array->len++] = x;
}
void cf_code_array_push_u16(cf_code_array_t *array, u16 x) {
  cf_code_array_push_u8(array, (u8)(x & 0xff00));
  cf_code_array_push_u8(array, (u8)(x & 0x00ff));
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

cf_constant_array_t cf_constant_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_constant_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(cf_constant_t)),
      .arena = arena,
  };
}

u16 cf_constant_array_push(cf_constant_array_t *array, const cf_constant_t *x) {
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

const cf_constant_t *
cf_constant_array_get(const cf_constant_array_t *constant_pool, u16 i) {
  pg_assert(constant_pool != NULL);
  pg_assert(i > 0);
  pg_assert(i <= constant_pool->len);
  pg_assert(constant_pool->values != NULL);
  pg_assert(((u64)(constant_pool->values)) % 16 == 0);

  return &constant_pool->values[i - 1];
}

void cf_fill_type_descriptor_string(const cf_type_t *type,
                                    string_t *type_descriptor) {
  pg_assert(type != NULL);
  pg_assert(type_descriptor != NULL);

  switch (type->kind) {
  case TYPE_VOID: {
    string_append_char(type_descriptor, 'V');
    break;
  }
  case TYPE_BYTE: {
    string_append_char(type_descriptor, 'B');
    break;
  }
  case TYPE_CHAR: {
    string_append_char(type_descriptor, 'C');
    break;
  }
  case TYPE_DOUBLE: {
    string_append_char(type_descriptor, 'D');
    break;
  }
  case TYPE_FLOAT: {
    string_append_char(type_descriptor, 'F');
    break;
  }
  case TYPE_INT: {
    string_append_char(type_descriptor, 'I');
    break;
  }
  case TYPE_LONG: {
    string_append_char(type_descriptor, 'J');
    break;
  }
  case TYPE_INSTANCE_REFERENCE: {
    const string_t class_name = type->v.class_name;

    string_append_char(type_descriptor, 'L');
    string_append_string(type_descriptor, &class_name);
    string_append_char(type_descriptor, ';');

    break;
  }
  case TYPE_SHORT: {
    string_append_char(type_descriptor, 'S');
    break;
  }
  case TYPE_BOOLEAN: {
    string_append_char(type_descriptor, 'Z');
    break;
  }
  case TYPE_ARRAY_REFERENCE: {
    string_append_char(type_descriptor, '[');

    const cf_type_t *const array_type = type->v.array_type;
    pg_assert(array_type != NULL);
    cf_fill_type_descriptor_string(array_type, type_descriptor);

    break;
  }
  case TYPE_CONSTRUCTOR:
  case TYPE_METHOD: {
    const cf_type_method_t *const method_type = &type->v.method;
    string_append_char(type_descriptor, '(');

    for (u64 i = 0; i < method_type->argument_count; i++) {
      pg_assert(method_type->argument_types != NULL);

      const cf_type_t *const argument_type = &method_type->argument_types[i];
      cf_fill_type_descriptor_string(argument_type, type_descriptor);
    }

    string_append_char(type_descriptor, ')');

    cf_fill_type_descriptor_string(method_type->return_type, type_descriptor);

    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
}

void cf_asm_load_constant(cf_code_array_t *code, u16 constant_i,
                          cf_frame_t *frame) {
  pg_assert(code != NULL);
  pg_assert(constant_i > 0);
  pg_assert(frame != NULL);

  cf_code_array_push_u8(code, BYTECODE_LDC_W);
  cf_code_array_push_u16(code, constant_i);

  frame->current_stack += 1;
  pg_assert(frame->current_stack < UINT16_MAX);
  frame->max_stack = pg_max(frame->max_stack, frame->current_stack);
}

void cf_asm_invoke_virtual(cf_code_array_t *code, u16 method_ref_i,
                           cf_frame_t *frame,
                           const cf_type_method_t *method_type) {
  pg_assert(code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(frame != NULL);

  cf_code_array_push_u8(code, BYTECODE_INVOKE_VIRTUAL);
  cf_code_array_push_u16(code, method_ref_i);

  // FIXME: long, double takes 2 spots on the stack!
  pg_assert(frame->current_stack >= method_type->argument_count);
  frame->current_stack -= method_type->argument_count;
}

void cf_asm_get_static(cf_code_array_t *code, u16 field_i, cf_frame_t *frame) {
  pg_assert(code != NULL);
  pg_assert(field_i > 0);
  pg_assert(frame != NULL);

  cf_code_array_push_u8(code, BYTECODE_GET_STATIC);
  cf_code_array_push_u16(code, field_i);

  frame->current_stack += 1;
  pg_assert(frame->current_stack < UINT16_MAX);
  frame->max_stack = pg_max(frame->max_stack, frame->current_stack);
}

void cf_asm_return(cf_code_array_t *code) {
  cf_code_array_push_u8(code, BYTECODE_RETURN);

  // TODO
}

void cf_asm_push_number(cf_code_array_t *code, u64 number, cf_frame_t *frame) {
  pg_assert(code != NULL);
  pg_assert(number <= UINT8_MAX && "unimplemented");
  pg_assert(frame != NULL);

  cf_code_array_push_u8(code, BYTECODE_BIPUSH);
  cf_code_array_push_u8(code, number & 0xff);

  frame->current_stack += 1;
  frame->max_stack = pg_max(frame->max_stack, frame->current_stack);
}

void cf_asm_invoke_special(cf_code_array_t *code, u16 method_ref_i,
                           cf_frame_t *frame,
                           const cf_type_method_t *method_type) {
  pg_assert(code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(frame != NULL);

  cf_code_array_push_u8(code, BYTECODE_INVOKE_SPECIAL);
  cf_code_array_push_u16(code, method_ref_i);

  // FIXME: long, double takes 2 spots on the stack!
  pg_assert(frame->current_stack >= method_type->argument_count);
  frame->current_stack -= method_type->argument_count;
}

void cf_asm_call_superclass_constructor(cf_code_array_t *code,
                                        u16 super_class_constructor_i,
                                        cf_frame_t *frame,
                                        const cf_type_t *constructor_type) {
  pg_assert(code != NULL);
  pg_assert(super_class_constructor_i > 0);
  pg_assert(frame != NULL);
  pg_assert(constructor_type != NULL);
  pg_assert(constructor_type->kind == TYPE_CONSTRUCTOR);

  cf_code_array_push_u8(
      code, BYTECODE_ALOAD_0); // TODO: move the responsability to the caller?

  const cf_type_method_t *const method_type = &constructor_type->v.method;
  pg_assert(method_type != NULL);
  cf_asm_invoke_special(code, super_class_constructor_i, frame, method_type);
}

typedef struct cf_attribute_t cf_attribute_t;
typedef struct {
  u64 len;
  u64 cap;
  cf_attribute_t *values;
  arena_t *arena;
} cf_attribute_array_t;

typedef struct {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  cf_attribute_array_t attributes;
} cf_field_t;

typedef struct cf_method_t cf_method_t;
typedef struct {
  u64 len;
  u64 cap;
  cf_method_t *values;
  arena_t *arena;
} cf_method_array_t;

typedef struct {
  u64 len;
  u64 cap;
  cf_field_t *values;
  arena_t *arena;
} cf_field_array_t;

cf_field_array_t cf_field_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_field_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(cf_field_t)),
      .arena = arena,
  };
}

void cf_field_array_push(cf_field_array_t *array, const cf_field_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_field_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(cf_field_t));
    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_field_t));
    array->cap = new_cap;
  }

  array->values[array->len++] = *x;
}

typedef struct cf_interfaces_t cf_interfaces_t;
typedef struct {
  u64 len;
  u64 cap;
  u16 *values;
  arena_t *arena;
} cf_interface_array_t;

cf_interface_array_t cf_interface_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_interface_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(u16)),
      .arena = arena,
  };
}

void cf_interface_array_push(cf_interface_array_t *array, u16 x) {
  pg_assert(array != NULL);
  pg_assert(x > 0);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_interfaces_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(u16));
    array->values = memcpy(new_array, array->values, array->len * sizeof(u16));
    array->cap = new_cap;
  }

  array->values[array->len++] = x;
}

typedef struct {
  u16 start_pc;
  u16 line_number;
} cf_line_number_table_t;

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
      cf_code_array_t code;
      cf_exception_array_t exceptions;
      cf_attribute_array_t attributes;
    } code; // ATTRIBUTE_KIND_CODE

    struct cf_attribute_source_file_t {
      u16 source_file;
    } source_file; // ATTRIBUTE_KIND_SOURCE_FILE

    struct cf_attribute_line_number_table_t {
      u16 line_number_table_count;
      cf_line_number_table_t *line_number_tables;
    } line_number_table; // ATTRIBUTE_KIND_LINE_NUMBER_TABLE
  } v;
};

typedef struct cf_attribute_line_number_table_t
    cf_attribute_line_number_table_t;

typedef struct cf_attribute_code_t cf_attribute_code_t;

typedef struct cf_attribute_source_file_t cf_attribute_source_file_t;

cf_attribute_array_t cf_attribute_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_attribute_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(cf_attribute_t)),
      .arena = arena,
  };
}

void cf_attribute_array_push(cf_attribute_array_t *array,
                             const cf_attribute_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_attribute_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(cf_attribute_t));
    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_attribute_t));
    array->cap = new_cap;
  }

  array->values[array->len++] = *x;
}

struct cf_method_t {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  cf_attribute_array_t attributes;
};

cf_method_array_t cf_method_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_method_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(cf_method_t)),
      .arena = arena,
  };
}

void cf_method_array_push(cf_method_array_t *array, const cf_method_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_method_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(cf_method_t));
    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_method_t));
    array->cap = new_cap;
  }

  array->values[array->len++] = *x;
}

const u32 cf_MAGIC_NUMBER = 0xbebafeca;
const u16 cf_MAJOR_VERSION_6 = 50;
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
  cf_interface_array_t interfaces;
  u16 fields_count;
  cf_field_array_t fields;
  cf_method_array_t methods;
  cf_attribute_array_t attributes;
};
typedef struct cf_class_file_t cf_class_file_t;

void file_write_be_16(FILE *file, u16 x) {
  pg_assert(file != NULL);

  const u8 x_be[2] = {
      (x & 0xff00) >> 8,
      (x & 0x00ff) >> 0,
  };
  fwrite(x_be, sizeof(x_be), 1, file);
}

void file_write_be_32(FILE *file, u32 x) {
  pg_assert(file != NULL);

  const u8 x_be[4] = {
      (x & 0xff000000) >> 24,
      (x & 0x00ff0000) >> 16,
      (x & 0x0000ff00) >> 8,
      (x & 0x000000ff) >> 0,
  };
  fwrite(x_be, sizeof(x_be), 1, file);
}

u16 buf_read_be_u16(char *buf, u64 size, char **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 2 <= buf + size);

  const char *const ptr = *current;
  const u16 x = (((u16)(ptr[0] & 0xff)) << 8) | ((u16)((ptr[1] & 0xff)) << 0);
  *current += 2;
  return x;
}

u32 buf_read_be_u32(char *buf, u64 size, char **current) {
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

void buf_read_n_u8(char *buf, u64 size, char *dst, u64 dst_len,
                   char **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + dst_len <= buf + size);

  if (dst != NULL)
    memcpy(dst, *current, dst_len);

  *current += dst_len;
}

u8 buf_read_u8(char *buf, u64 size, char **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 1 <= buf + size);

  const u8 x = (*current)[0];
  *current += 1;
  return x;
}

string_t
cf_constant_array_get_as_string(const cf_constant_array_t *constant_pool,
                                u16 i) {
  const cf_constant_t *const constant = cf_constant_array_get(constant_pool, i);
  pg_assert(constant->kind == CONSTANT_POOL_KIND_UTF8);
  return constant->v.s;
}

void cf_buf_read_attributes(char *buf, u64 buf_len, char **current,
                            cf_class_file_t *class_file,
                            cf_attribute_array_t *attributes, arena_t *arena);

void cf_buf_read_sourcefile_attribute(char *buf, u64 buf_len, char **current,
                                      cf_class_file_t *class_file,
                                      cf_attribute_array_t *attributes) {

  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);

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
  cf_attribute_array_push(attributes, &attribute);
}

void cf_buf_read_code_attribute_exceptions(char *buf, u64 buf_len,
                                           char **current,
                                           cf_class_file_t *class_file,
                                           cf_exception_array_t *exceptions,
                                           arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(exceptions != NULL);

  const char *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  *exceptions = cf_exception_array_make(table_len, arena);

  for (u16 i = 0; i < table_len; i++) {
    cf_exception_t exception = {0};

    exception.start_pc = buf_read_be_u16(buf, buf_len, current);
    exception.end_pc = buf_read_be_u16(buf, buf_len, current);
    exception.handler_pc = buf_read_be_u16(buf, buf_len, current);
    exception.catch_type = buf_read_be_u16(buf, buf_len, current);

    cf_exception_array_push(exceptions, &exception);
  }

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == sizeof(u16) + table_len * sizeof(u16) * 4);
}

void cf_buf_read_code_attribute(char *buf, u64 buf_len, char **current,
                                cf_class_file_t *class_file, u32 attribute_len,
                                u16 name, cf_attribute_array_t *attributes,
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

  code.code = cf_code_array_make(code_len, arena);
  buf_read_n_u8(buf, buf_len, code.code.values, code_len, current);
  code.code.len = code_len;

  cf_buf_read_code_attribute_exceptions(buf, buf_len, current, class_file,
                                        &code.exceptions, arena);

  cf_buf_read_attributes(buf, buf_len, current, class_file, &code.attributes,
                         arena);

  cf_attribute_t attribute = {
      .kind = ATTRIBUTE_KIND_CODE, .name = name, .v = {.code = code}};
  cf_attribute_array_push(attributes, &attribute);

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_stack_map_table_attribute(char *buf, u64 buf_len,
                                           char **current,
                                           cf_class_file_t *class_file,
                                           u32 attribute_len, arena_t *arena) {
  pg_unused(arena);
  pg_unused(class_file);
  const char *const current_start = *current;

  buf_read_n_u8(buf, buf_len, NULL, attribute_len, current);

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_line_number_table_attribute(char *buf, u64 buf_len,
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

void cf_buf_read_local_variable_table_attribute(char *buf, u64 buf_len,
                                                char **current,
                                                cf_class_file_t *class_file,
                                                u32 attribute_len,
                                                arena_t *arena) {
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

void cf_buf_read_local_variable_type_table_attribute(
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

void cf_buf_read_signature_attribute(char *buf, u64 buf_len, char **current,
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
void cf_buf_read_exceptions_attribute(char *buf, u64 buf_len, char **current,
                                      cf_class_file_t *class_file,
                                      u32 attribute_len,
                                      cf_attribute_array_t *attributes,
                                      arena_t *arena) {
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

void cf_buf_read_inner_classes_attribute(char *buf, u64 buf_len, char **current,
                                         cf_class_file_t *class_file,
                                         u32 attribute_len, arena_t *arena) {
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

// FIXME: each function call here should take the `attributes` argument and push
// to it!
void cf_buf_read_attribute(char *buf, u64 buf_len, char **current,
                           cf_class_file_t *class_file,
                           cf_attribute_array_t *attributes, arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(attributes->cap > 0);
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
                                     attributes);
  } else if (string_eq_c(attribute_name, "Code")) {
    cf_buf_read_code_attribute(buf, buf_len, current, class_file, size, name_i,
                               attributes, arena);
  } else if (string_eq_c(attribute_name, "StackMapTable")) {
    cf_buf_read_stack_map_table_attribute(buf, buf_len, current, class_file,
                                          size, arena);
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

void cf_buf_read_attributes(char *buf, u64 buf_len, char **current,
                            cf_class_file_t *class_file,
                            cf_attribute_array_t *attributes, arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u16 attribute_count = buf_read_be_u16(buf, buf_len, current);
  *attributes = cf_attribute_array_make(attribute_count, arena);

  for (u64 i = 0; i < attribute_count; i++) {
    cf_buf_read_attribute(buf, buf_len, current, class_file, attributes, arena);
  }
}

void cf_buf_read_constant(char *buf, u64 buf_len, char **current,
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

void cf_buf_read_constants(char *buf, u64 buf_len, char **current,
                           cf_class_file_t *class_file, u16 constant_pool_len) {
  for (u64 i = 1; i <= constant_pool_len; i++) {
    cf_buf_read_constant(buf, buf_len, current, class_file, &i,
                         constant_pool_len);
  }
}

void cf_buf_read_method(char *buf, u64 buf_len, char **current,
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

  cf_method_array_push(&class_file->methods, &method);
}

void cf_buf_read_methods(char *buf, u64 buf_len, char **current,
                         cf_class_file_t *class_file, arena_t *arena) {

  const u16 methods_count = buf_read_be_u16(buf, buf_len, current);
  class_file->methods = cf_method_array_make(methods_count, arena);

  for (u64 i = 0; i < methods_count; i++) {
    cf_buf_read_method(buf, buf_len, current, class_file, arena);
  }
}

void cf_buf_read_interfaces(char *buf, u64 buf_len, char **current,
                            cf_class_file_t *class_file, arena_t *arena) {

  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  const char *const current_start = *current;

  const u16 interfaces_count = buf_read_be_u16(buf, buf_len, current);
  class_file->interfaces = cf_interface_array_make(interfaces_count, arena);

  for (u16 i = 0; i < interfaces_count; i++) {
    const u16 interface_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(interface_i > 0);
    pg_assert(interface_i <= class_file->constant_pool.len);

    cf_interface_array_push(&class_file->interfaces, interface_i);
  }

  const char *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == sizeof(u16) + interfaces_count * sizeof(u16));
}

void cf_buf_read_field(char *buf, u64 buf_len, char **current,
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

  cf_field_array_push(&class_file->fields, &field);
}

void cf_buf_read_fields(char *buf, u64 buf_len, char **current,
                        cf_class_file_t *class_file, arena_t *arena) {

  const u16 fields_count = buf_read_be_u16(buf, buf_len, current);
  class_file->fields = cf_field_array_make(fields_count, arena);

  for (u16 i = 0; i < fields_count; i++) {
    cf_buf_read_field(buf, buf_len, current, class_file, arena);
  }
}

void cf_buf_read_class_file(char *buf, u64 buf_len, char **current,
                            cf_class_file_t *class_file, arena_t *arena) {

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

void cf_write_constant(const cf_class_file_t *class_file, FILE *file,
                       const cf_constant_t *constant) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);
  pg_assert(constant != NULL);

  switch (constant->kind) {
  case CONSTANT_POOL_KIND_UTF8: {
    fwrite(&constant->kind, sizeof(u8), 1, file);
    const string_t *const s = &constant->v.s;
    file_write_be_16(file, s->len);
    fwrite(s->value, sizeof(u8), s->len, file);
    break;
  }
  case CONSTANT_POOL_KIND_INT:
    fwrite(&constant->kind, sizeof(u8), 1, file);
    file_write_be_32(file, constant->v.number);
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
    file_write_be_16(file, constant->v.class_name);
    break;
  case CONSTANT_POOL_KIND_STRING:
    fwrite(&constant->kind, sizeof(u8), 1, file);
    file_write_be_16(file, constant->v.string_utf8_i);
    break;
  case CONSTANT_POOL_KIND_FIELD_REF: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const cf_constant_field_ref_t *const field_ref = &constant->v.field_ref;

    file_write_be_16(file, field_ref->name);
    file_write_be_16(file, field_ref->type_descriptor);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_REF: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const cf_constant_method_ref_t *const method_ref = &constant->v.method_ref;

    file_write_be_16(file, method_ref->class);
    file_write_be_16(file, method_ref->name_and_type);
    break;
  }
  case CONSTANT_POOL_KIND_INTERFACE_METHOD_REF:
    pg_assert(0 && "unimplemented");
    break;
  case CONSTANT_POOL_KIND_NAME_AND_TYPE: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const cf_constant_name_and_type_t *const name_and_type =
        &constant->v.name_and_type;

    file_write_be_16(file, name_and_type->name);
    file_write_be_16(file, name_and_type->type_descriptor);
    break;
  }
  case CONSTANT_POOL_KIND_INVOKE_DYNAMIC:
    pg_assert(0 && "unimplemented");
    break;
  default:
    pg_assert(0 && "unreachable/unimplemented");
  }
}

void cf_write_constant_pool(const cf_class_file_t *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  const u16 len = class_file->constant_pool.len + 1;
  file_write_be_16(file, len);

  for (u64 i = 0; i < class_file->constant_pool.len; i++) {
    pg_assert(class_file->constant_pool.values != NULL);
    pg_assert(((u64)class_file->constant_pool.values) % 16 == 0);

    const cf_constant_t *const constant = &class_file->constant_pool.values[i];
    cf_write_constant(class_file, file, constant);
  }
}
void cf_write_interfaces(const cf_class_file_t *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  file_write_be_16(file, class_file->interfaces_count);

  pg_assert(class_file->interfaces_count == 0 && "unimplemented");
}

void cf_write_fields(const cf_class_file_t *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  file_write_be_16(file, class_file->fields_count);

  pg_assert(class_file->fields_count == 0 && "unimplemented");
}

u32 cf_compute_attribute_size(const cf_attribute_t *attribute) {
  pg_assert(attribute != NULL);

  switch (attribute->kind) {
  case ATTRIBUTE_KIND_SOURCE_FILE:
    return 2;
  case ATTRIBUTE_KIND_CODE: {
    const cf_attribute_code_t *const code = &attribute->v.code;

    u32 size = sizeof(code->max_stack) + sizeof(code->max_locals) +
               sizeof(u32) + code->code.len +
               sizeof(u16) /* exception count */ +
               +code->exceptions.len * sizeof(cf_exception_t) +
               sizeof(u16) // attributes length
        ;

    for (uint64_t i = 0; i < code->attributes.len; i++) {
      const cf_attribute_t *const child_attribute = &code->attributes.values[i];
      size += cf_compute_attribute_size(child_attribute);
    }
    return size;
  }
  case ATTRIBUTE_KIND_LINE_NUMBER_TABLE: {
    const cf_attribute_line_number_table_t *const attribute_line_number_table =
        &attribute->v.line_number_table;
    return sizeof(attribute_line_number_table->line_number_table_count) +
           attribute_line_number_table->line_number_table_count *
               sizeof(cf_line_number_table_t);
  }
  case ATTRIBUTE_KIND_STACK_MAP_TABLE:
    pg_assert(0 && "unimplemented");
  }
  pg_assert(0 && "unreachable");
}

void cf_write_attributes(FILE *file, const cf_attribute_array_t *attributes);
void cf_write_attribute(FILE *file, const cf_attribute_t *attribute) {
  pg_assert(file != NULL);
  pg_assert(attribute != NULL);

  file_write_be_16(file, attribute->name);

  switch (attribute->kind) {
  case ATTRIBUTE_KIND_SOURCE_FILE: {
    const u32 size = cf_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const cf_attribute_source_file_t *const source_file =
        &attribute->v.source_file;
    file_write_be_16(file, source_file->source_file);

    break;
  }
  case ATTRIBUTE_KIND_CODE: {
    const u32 size = cf_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const cf_attribute_code_t *const code = &attribute->v.code;

    file_write_be_16(file, code->max_stack);

    file_write_be_16(file, code->max_locals);

    file_write_be_32(file, code->code.len);
    fwrite(code->code.values, code->code.len, sizeof(u8), file);

    file_write_be_16(file, code->exceptions.len);

    cf_write_attributes(file, &code->attributes);

    break;
  }
  case ATTRIBUTE_KIND_LINE_NUMBER_TABLE: {
    const u32 size = cf_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const cf_attribute_line_number_table_t *const attribute_line_number_table =
        &attribute->v.line_number_table;

    for (u64 i = 0; i < attribute_line_number_table->line_number_table_count;
         i++) {
      cf_line_number_table_t line_number_table =
          attribute_line_number_table->line_number_tables[i];
      file_write_be_16(file, line_number_table.start_pc);
      file_write_be_16(file, line_number_table.line_number);
    }

    break;
  }
  case ATTRIBUTE_KIND_STACK_MAP_TABLE: {
    pg_assert(0 && "unimplemented");
    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
}

void cf_write_attributes(FILE *file, const cf_attribute_array_t *attributes) {
  file_write_be_16(file, attributes->len);

  for (uint64_t i = 0; i < attributes->len; i++) {
    const cf_attribute_t *const attribute = &attributes->values[i];
    cf_write_attribute(file, attribute);
  }
}

void cf_write_method(FILE *file, const cf_method_t *method) {
  file_write_be_16(file, method->access_flags);
  file_write_be_16(file, method->name);
  file_write_be_16(file, method->descriptor);

  cf_write_attributes(file, &method->attributes);
}

void cf_write_methods(const cf_class_file_t *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  file_write_be_16(file, class_file->methods.len);

  for (uint64_t i = 0; i < class_file->methods.len; i++) {
    const cf_method_t *const method = &class_file->methods.values[i];
    cf_write_method(file, method);
  }
}

void cf_write(const cf_class_file_t *class_file, FILE *file) {
  fwrite(&cf_MAGIC_NUMBER, sizeof(cf_MAGIC_NUMBER), 1, file);

  file_write_be_16(file, class_file->minor_version);
  file_write_be_16(file, class_file->major_version);
  cf_write_constant_pool(class_file, file);
  file_write_be_16(file, class_file->access_flags);
  file_write_be_16(file, class_file->this_class);
  file_write_be_16(file, class_file->super_class);

  cf_write_interfaces(class_file, file);
  cf_write_fields(class_file, file);
  cf_write_methods(class_file, file);
  cf_write_attributes(file, &class_file->attributes);
  fflush(file);
}

void cf_init(cf_class_file_t *class_file, arena_t *arena) {
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  class_file->constant_pool = cf_constant_array_make(1024, arena);
  class_file->interfaces = cf_interface_array_make(1024, arena);

  class_file->methods = cf_method_array_make(1024, arena);
  class_file->fields = cf_field_array_make(1024, arena);

  class_file->attributes = cf_attribute_array_make(1024, arena);
}

void cf_attribute_code_init(cf_attribute_code_t *code, arena_t *arena) {
  pg_assert(code != NULL);
  pg_assert(arena != NULL);

  code->code = cf_code_array_make(32, arena);
  code->attributes = cf_attribute_array_make(1024, arena);
}

void cf_method_init(cf_method_t *method, arena_t *arena) {
  pg_assert(method != NULL);
  pg_assert(arena != NULL);

  method->attributes = cf_attribute_array_make(1024, arena);
}

u16 cf_add_constant_string(cf_constant_array_t *constant_pool, string_t s) {
  pg_assert(constant_pool != NULL);
  pg_assert(s.value != NULL);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                  .v = {.s = s}};
  return cf_constant_array_push(constant_pool, &constant);
}

u16 cf_add_constant_cstring(cf_constant_array_t *constant_pool, char *s) {
  pg_assert(constant_pool != NULL);
  pg_assert(s != NULL);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                  .v = {.s = {
                                            .len = strlen(s),
                                            .value = s,
                                        }}};
  return cf_constant_array_push(constant_pool, &constant);
}

u16 cf_add_constant_jstring(cf_constant_array_t *constant_pool,
                            u16 constant_utf8_i) {
  pg_assert(constant_pool != NULL);
  pg_assert(constant_utf8_i > 0);

  const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_STRING,
                                  .v = {.string_utf8_i = constant_utf8_i}};

  return cf_constant_array_push(constant_pool, &constant);
}

// TODO: sanitize `source_file_name` in case of spaces, etc.
string_t cf_make_class_file_name_kt(string_t source_file_name, arena_t *arena) {
  pg_assert(source_file_name.value != NULL);
  pg_assert(source_file_name.len > 0);
  pg_assert(arena != NULL);

  string_t last_path_component =
      string_make(string_find_last_path_component(source_file_name), arena);
  pg_assert(last_path_component.len > 0);
  pg_assert(last_path_component.value[0] != '/');

  string_drop_after_last_incl(&last_path_component, '.');
  string_append_cstring(&last_path_component, "Kt.class");
  string_capitalize_first(&last_path_component);

  string_t result = string_make(source_file_name, arena);
  string_drop_after_last_incl(&result, '/');
  string_append_char_if_not_exists(&result, '/');
  string_append_string(&result, &last_path_component);
  return result;
}

typedef struct {
  u64 len;
  u64 cap;
  cf_class_file_t *values;
  arena_t *arena;
} cf_class_file_array_t;

cf_class_file_array_t cf_class_file_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (cf_class_file_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(cf_class_file_t)),
      .arena = arena,
  };
}

u16 cf_class_file_array_push(cf_class_file_array_t *array,
                             const cf_class_file_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(((u64)array->values) % 16 == 0);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_class_file_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(cf_class_file_t));
    pg_assert(new_array != NULL);
    pg_assert(((u64)new_array) % 16 == 0);

    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_class_file_t));
    pg_assert(array->values != NULL);
    pg_assert(((u64)array->values) % 16 == 0);
    array->cap = new_cap;
  }

  array->values[array->len] = *x;
  const u64 index = array->len + 1;
  pg_assert(index > 0);
  pg_assert(index <= array->len + 1);
  array->len += 1;
  return index;
}

// TODO: one thread that walks the directory recursively and one/many worker
// threads to parse class files?
void cf_read_class_files(char *path, u64 path_len,
                         cf_class_file_array_t *class_files, arena_t *arena) {
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
    cf_class_file_array_push(class_files, &class_file);
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

bool cf_class_files_find_method_exactly(
    const cf_class_file_array_t *class_files, string_t class_name,
    string_t method_name, string_t descriptor) {
  pg_assert(class_files != NULL);
  pg_assert(descriptor.len > 0);
  pg_assert(descriptor.value != NULL);
  pg_assert(class_files->values != NULL);
  pg_assert(class_files->len <= class_files->cap);

  for (u64 i = 0; i < class_files->len; i++) {
    const cf_class_file_t *const class_file = &class_files->values[i];
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

    for (u64 j = 0; j < class_file->methods.len; j++) {
      const cf_method_t *const this_method = &class_file->methods.values[j];
      // TODO: check attributes?

      const string_t this_method_name = cf_constant_array_get_as_string(
          &class_file->constant_pool, this_method->name);

      if (!string_eq(this_method_name, method_name))
        continue;

      const string_t this_method_descriptor = cf_constant_array_get_as_string(
          &class_file->constant_pool, this_method->descriptor);

      if (!string_eq(this_method_descriptor, descriptor))
        continue;

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
  TOKEN_KIND_LEFT_PAREN,
  TOKEN_KIND_RIGHT_PAREN,
  TOKEN_KIND_LEFT_BRACE,
  TOKEN_KIND_RIGHT_BRACE,
  TOKEN_KIND_BUILTIN_PRINTLN,
  TOKEN_KIND_KEYWORD_FUN,
  TOKEN_KIND_IDENTIFIER,
  TOKEN_KIND_COMMA,
  TOKEN_KIND_DOT,
  TOKEN_KIND_COLON,
  TOKEN_KIND_NOT,
} lex_token_kind_t;

typedef struct {
  lex_token_kind_t kind;
  u32 source_offset;
} lex_token_t;

typedef struct {
  u64 len;
  u64 cap;
  lex_token_t *values;
  arena_t *arena;
} lex_token_array_t;

lex_token_array_t lex_token_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (lex_token_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(lex_token_t)),
      .arena = arena,
  };
}

u16 lex_token_array_push(lex_token_array_t *array, const lex_token_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT32_MAX);
  pg_assert(array->values != NULL);
  pg_assert(((u64)array->values) % 16 == 0);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    lex_token_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(lex_token_t));
    pg_assert(new_array != NULL);
    pg_assert(((u64)new_array) % 16 == 0);

    array->values =
        memcpy(new_array, array->values, array->len * sizeof(lex_token_t));
    pg_assert(array->values != NULL);
    pg_assert(((u64)array->values) % 16 == 0);
    array->cap = new_cap;
  }

  array->values[array->len] = *x;
  const u64 index = array->len + 1;
  pg_assert(index > 0);
  pg_assert(index <= array->len + 1);
  array->len += 1;
  return index;
}

typedef struct {
  u32 line;
  u32 start_offset;
} lex_line_table_t;

typedef struct {
  u64 len;
  u64 cap;
  lex_line_table_t *values;
  arena_t *arena;
} lex_line_table_array_t;

lex_line_table_array_t lex_line_table_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (lex_line_table_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(lex_line_table_t)),
      .arena = arena,
  };
}

u16 lex_line_table_array_push(lex_line_table_array_t *array,
                              const lex_line_table_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT32_MAX);
  pg_assert(array->values != NULL);
  pg_assert(((u64)array->values) % 16 == 0);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    lex_line_table_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(lex_line_table_t));
    pg_assert(new_array != NULL);
    pg_assert(((u64)new_array) % 16 == 0);

    array->values =
        memcpy(new_array, array->values, array->len * sizeof(lex_line_table_t));
    pg_assert(array->values != NULL);
    pg_assert(((u64)array->values) % 16 == 0);
    array->cap = new_cap;
  }

  array->values[array->len] = *x;
  const u64 index = array->len + 1;
  pg_assert(index > 0);
  pg_assert(index <= array->len + 1);
  array->len += 1;
  return index;
}

typedef struct {
  string_t file_path;
  lex_token_array_t tokens;
  lex_line_table_array_t line_table;
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
                           const char **current) {
  pg_assert(lexer != NULL);
  pg_assert(lexer->tokens.values != NULL);
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
    lex_token_array_push(&lexer->tokens, &token);
  } else if (mem_eq_c(identifier, identifier_len, "println")) {
    const lex_token_t token = {
        .kind = TOKEN_KIND_BUILTIN_PRINTLN,
        .source_offset = start_offset,
    };
    lex_token_array_push(&lexer->tokens, &token);
  } else {
    const lex_token_t token = {
        .kind = TOKEN_KIND_IDENTIFIER,
        .source_offset = start_offset,
    };
    lex_token_array_push(&lexer->tokens, &token);
  }
}

static void lex_number(lex_lexer_t *lexer, const char *buf, u32 buf_len,
                       const char **current) {
  pg_assert(lexer != NULL);
  pg_assert(lexer->tokens.values != NULL);
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
  lex_token_array_push(&lexer->tokens, &token);
}

static void lex_lex(lex_lexer_t *lexer, const char *buf, u32 buf_len,
                    const char **current) {
  pg_assert(lexer != NULL);
  pg_assert(lexer->line_table.values != NULL);
  pg_assert(lexer->line_table.len == 0);
  pg_assert(lexer->tokens.values != NULL);
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  // Push first line.
  const lex_line_table_t line = {
      .line = 1,
      .start_offset = 0,
  };
  lex_line_table_array_push(&lexer->line_table, &line);

  // Push first dummy token.
  const lex_token_t dummy_token = {0};
  lex_token_array_push(&lexer->tokens, &dummy_token);

  while (!lex_is_at_end(buf, buf_len, current)) {
    const u8 c = **current;

    switch (c) {
    case '(': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_LEFT_PAREN,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case ')': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_RIGHT_PAREN,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case ',': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_COMMA,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case ':': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_COLON,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '!': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_NOT,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '{': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_LEFT_BRACE,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '}': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_RIGHT_BRACE,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '+': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_PLUS,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '.': {
      const lex_token_t token = {
          .kind = TOKEN_KIND_DOT,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '\n': {
      const lex_line_table_t line = {
          .line = lexer->line_table.values[lexer->line_table.len - 1].line + 1,
          .start_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_line_table_array_push(&lexer->line_table, &line);
      lex_advance(buf, buf_len, current);
      break;
    }
    case ' ': {
      lex_advance(buf, buf_len, current);
      break;
    }
    default: {
      if (ut_char_is_alphabetic(**current)) {
        lex_identifier(lexer, buf, buf_len, current);
      } else if (lex_is_digit(buf, buf_len, current)) {
        lex_number(lexer, buf, buf_len, current);
      } else {
        pg_assert(0 && "unimplemented");
      }
    }
    }
  }
}

static u32 lex_find_token_length(const lex_lexer_t *lexer, const char *buf,
                                 const u32 buf_len, lex_token_t token) {
  pg_assert(lexer != NULL);
  pg_assert(buf != NULL);

  switch (token.kind) {
  case TOKEN_KIND_NONE:
    return 0;
  case TOKEN_KIND_NUMBER:
    return lex_number_length(buf, buf_len, token.source_offset);

  case TOKEN_KIND_PLUS:
  case TOKEN_KIND_LEFT_PAREN:
  case TOKEN_KIND_RIGHT_PAREN:
  case TOKEN_KIND_LEFT_BRACE:
  case TOKEN_KIND_RIGHT_BRACE:
  case TOKEN_KIND_COMMA:
  case TOKEN_KIND_DOT:
  case TOKEN_KIND_COLON:
  case TOKEN_KIND_NOT:
    return 1;

  case TOKEN_KIND_BUILTIN_PRINTLN:
    return 7;

  case TOKEN_KIND_KEYWORD_FUN:
    return 3;

  case TOKEN_KIND_IDENTIFIER:
    return lex_identifier_length(buf, buf_len, token.source_offset);
  }
}

// ------------------------------ Parser

typedef enum {
  AST_KIND_NONE,
  AST_KIND_NUM,
  AST_KIND_ADD,
  AST_KIND_BUILTIN_PRINTLN,
  AST_KIND_FUNCTION_DEFINITION,
  AST_KIND_BINARY,
  AST_KIND_MAX,
} par_ast_node_kind_t;

static const char *par_ast_node_kind_to_string[AST_KIND_MAX] = {
    [AST_KIND_NONE] = "AST_KIND_NONE",
    [AST_KIND_NUM] = "AST_KIND_NUM",
    [AST_KIND_ADD] = "AST_KIND_ADD",
    [AST_KIND_BUILTIN_PRINTLN] = "AST_KIND_BUILTIN_PRINTLN",
    [AST_KIND_FUNCTION_DEFINITION] = "AST_KIND_FUNCTION_DEFINITION",
    [AST_KIND_BINARY] = "AST_KIND_BINARY",
};

typedef struct {
  par_ast_node_kind_t kind;
  u32 main_token;
  u32 lhs;
  u32 rhs;
} par_ast_node_t;

typedef struct {
  u64 len;
  u64 cap;
  par_ast_node_t *values;
  arena_t *arena;
} par_ast_node_array_t;

par_ast_node_array_t par_ast_node_array_make(u64 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (par_ast_node_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap, sizeof(par_ast_node_t)),
      .arena = arena,
  };
}

u16 par_ast_node_array_push(par_ast_node_array_t *array,
                            const par_ast_node_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT32_MAX);
  pg_assert(array->values != NULL);
  pg_assert(((u64)array->values) % 16 == 0);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    par_ast_node_t *const new_array =
        arena_alloc(array->arena, new_cap, sizeof(par_ast_node_t));
    pg_assert(new_array != NULL);
    pg_assert(((u64)new_array) % 16 == 0);

    array->values =
        memcpy(new_array, array->values, array->len * sizeof(par_ast_node_t));
    pg_assert(array->values != NULL);
    pg_assert(((u64)array->values) % 16 == 0);
    array->cap = new_cap;
  }

  array->values[array->len++] = *x;
  return array->len - 1;
}

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
  par_ast_node_array_t nodes;
  par_parser_state_t state;
} par_parser_t;

void ut_fwrite_indent(FILE *file, u16 indent) {
  for (u16 i = 0; i < indent; i++) {
    fputc(' ', file);
  }
}

static void par_ast_fprint_node(const par_parser_t *parser,
                                const par_ast_node_t *node, FILE *file,
                                u16 indent) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(node != NULL);

  if (node->kind == AST_KIND_NONE)
    return;

  const char *const kind_string = par_ast_node_kind_to_string[node->kind];
  const lex_token_t token = parser->lexer->tokens.values[node->main_token];
  const u32 length =
      lex_find_token_length(parser->lexer, parser->buf, parser->buf_len, token);
  const char *const token_string = &parser->buf[token.source_offset];
  ut_fwrite_indent(file, indent);
  fprintf(file, "%s %.*s\n", kind_string, length, token_string);

  pg_assert(indent < UINT16_MAX - 1); // Avoid overflow.
  par_ast_fprint_node(parser, &parser->nodes.values[node->lhs], file,
                      indent + 2);
  par_ast_fprint_node(parser, &parser->nodes.values[node->rhs], file,
                      indent + 2);
}

static void par_ast_fprint(const par_parser_t *parser, FILE *file) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  pg_assert(parser->nodes.len >= 1); // First is dummy.

  // Second is the root.
  if (parser->nodes.len > 1)
    par_ast_fprint_node(parser, &parser->nodes.values[1], file, 0);
}

static bool par_is_at_end(const par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser->tokens_i == parser->lexer->tokens.len;
}

static lex_token_t par_peek_token(const par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser->lexer->tokens.values[parser->tokens_i];
}

static lex_token_t par_advance_token(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser->lexer->tokens.values[parser->tokens_i++];
}

static bool par_match_token(par_parser_t *parser, lex_token_kind_t kind) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (par_peek_token(parser).kind == kind) {
    par_advance_token(parser);
    return true;
  }
  return false;
}

static void par_find_token_position(par_parser_t *parser, lex_token_t token,
                                    u32 *line, u32 *column,
                                    string_t *token_string) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(line != NULL);
  pg_assert(column != NULL);
  pg_assert(token_string != NULL);

  token_string->value = &parser->buf[token.source_offset];
  token_string->len =
      lex_find_token_length(parser->lexer, parser->buf, parser->buf_len, token);

  for (u32 i = 0; i < parser->lexer->line_table.len; i++) {
    const lex_line_table_t entry = parser->lexer->line_table.values[i];
    if (token.source_offset > entry.start_offset) {
      *line = entry.line;
      *column = 1 + token.source_offset - entry.start_offset;

      return;
    }
  }
  pg_assert(*line > 0);
  pg_assert(*line <= parser->lexer->line_table.len);
  pg_assert(*column > 0);
}

static void par_error(par_parser_t *parser, lex_token_t token,
                      const char *error) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  switch (parser->state) {
  case PARSER_STATE_OK: {
    u32 line = 0;
    u32 column = 0;
    string_t token_string = {0};
    par_find_token_position(parser, token, &line, &column, &token_string);

    fprintf(stderr, "%.*s:%u:%u: got `%.*s`, %s\n",
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
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (!par_match_token(parser, kind)) {
    par_error(parser, par_peek_token(parser), error);
  }
}

static u64 par_number(const par_parser_t *parser, lex_token_t token) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

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

static u32 par_parse_expression(par_parser_t *parser);

static u32 par_parse_builtin_println(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  par_expect_token(parser, TOKEN_KIND_LEFT_PAREN, "expected left parenthesis");

  par_ast_node_t node = {
      .kind = AST_KIND_BUILTIN_PRINTLN,
      .main_token = parser->tokens_i - 2,
      .lhs = par_parse_expression(parser),
  };
  const u32 node_i = par_ast_node_array_push(&parser->nodes, &node);

  par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                   "expected right parenthesis");
  return node_i;
}

static u32 par_parse_primary_expression(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (par_match_token(parser, TOKEN_KIND_NUMBER)) {
    const par_ast_node_t node = {
        .kind = AST_KIND_NUM,
        .main_token = parser->tokens_i - 1,
    };
    return par_ast_node_array_push(&parser->nodes, &node);
  }

  par_advance_token(parser);
  return 0;
}

static u32 par_parse_statement(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (par_match_token(parser, TOKEN_KIND_BUILTIN_PRINTLN))
    return par_parse_builtin_println(parser);
  else
    return par_parse_expression(parser);
}

static u32 par_parse_postfix_unary_expression(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return par_parse_primary_expression(
      parser); // TODO: parse {0,n} postfix unary suffix.
}

static u32 par_parse_prefix_unary_expression(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (par_match_token(parser, TOKEN_KIND_NOT)) {
    pg_assert(0 && "todo");
  }

  return par_parse_postfix_unary_expression(parser);
}

static u32 par_parse_multiplicative_expression(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return par_parse_prefix_unary_expression(parser);
}

static u32 par_parse_additive_expression(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const par_ast_node_t node = {
      .kind = AST_KIND_BINARY,
      .lhs = par_parse_multiplicative_expression(parser),
  };
  u32 last_node_i = par_ast_node_array_push(&parser->nodes, &node);

  const u32 root_i = last_node_i;

  while (par_match_token(parser, TOKEN_KIND_PLUS)) // TODO: minus.
  {
    const u32 main_token = parser->tokens_i - 1;
    const par_ast_node_t node = {
        .kind = AST_KIND_BINARY,
        .main_token = main_token,
        .lhs = par_parse_multiplicative_expression(parser),
    };
    last_node_i = parser->nodes.values[last_node_i].rhs =
        par_ast_node_array_push(&parser->nodes, &node);
  }
  return root_i;
}

static u32 par_parse_expression(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return par_parse_additive_expression(parser);
}

static u32 par_parse_block(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  // Empty block.
  if (par_match_token(parser, TOKEN_KIND_RIGHT_BRACE))
    return 0;

  const par_ast_node_t root = {
      .kind = AST_KIND_BINARY,
  };
  u32 last_list_i = par_ast_node_array_push(&parser->nodes, &root);
  const u32 root_i = last_list_i;

  while (!(par_is_at_end(parser) ||
           par_peek_token(parser).kind == TOKEN_KIND_RIGHT_BRACE)) {
    const par_ast_node_t list = {
        .kind = AST_KIND_BINARY,
        .lhs = par_parse_statement(parser),
    };
    const u32 list_i = par_ast_node_array_push(&parser->nodes, &list);
    parser->nodes.values[last_list_i].rhs = list_i;
    last_list_i = list_i;
  }

  par_expect_token(parser, TOKEN_KIND_RIGHT_BRACE,
                   "expected right curly brace after the arguments");
  return root_i;
}

static u32 par_parse_function_arguments(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  // No arguments.
  if (par_match_token(parser, TOKEN_KIND_RIGHT_PAREN))
    return 0;

  const par_ast_node_t root = {
      .kind = AST_KIND_BINARY,
  };
  u32 last_list_i = par_ast_node_array_push(&parser->nodes, &root);
  const u32 root_i = last_list_i;

  do {
    const par_ast_node_t list = {
        .kind = AST_KIND_BINARY,
        .lhs = par_parse_expression(parser),
    };
    const u32 list_i = par_ast_node_array_push(&parser->nodes, &list);
    parser->nodes.values[last_list_i].rhs = list_i;
    last_list_i = list_i;
  } while (par_match_token(parser, TOKEN_KIND_COMMA));

  par_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                   "expected right parenthesis after the arguments");
  return root_i;
}

static u32 par_parse_function_definition(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  par_expect_token(parser, TOKEN_KIND_IDENTIFIER,
                   "expected function name (identifier)");
  const u32 start_token = parser->tokens_i - 1;

  par_expect_token(parser, TOKEN_KIND_LEFT_PAREN,
                   "expected left parenthesis before the arguments");
  const u32 arguments = par_parse_function_arguments(parser);

  par_expect_token(parser, TOKEN_KIND_LEFT_BRACE,
                   "expected left curly brace before the arguments");
  const u32 body = par_parse_block(parser);

  const par_ast_node_t node = {.kind = AST_KIND_FUNCTION_DEFINITION,
                               .main_token = start_token,
                               .lhs = arguments,
                               .rhs = body};
  return par_ast_node_array_push(&parser->nodes, &node);
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

static u32 par_parse_declaration(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  u32 new_node_i = 0;
  if (par_match_token(parser, TOKEN_KIND_KEYWORD_FUN))
    new_node_i = par_parse_function_definition(parser);
  else
    new_node_i = par_parse_statement(parser);

  par_sync_if_panicked(parser);

  return new_node_i;
}

static u32 par_parse(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const par_ast_node_t dummy = {0};
  par_ast_node_array_push(&parser->nodes, &dummy);

  const par_ast_node_t root = {
      .kind = AST_KIND_BINARY,
  };
  u32 last_list_i = par_ast_node_array_push(&parser->nodes, &root);
  const u32 root_i = last_list_i;

  while (!par_is_at_end(parser)) {
    const par_ast_node_t list = {
        .kind = AST_KIND_BINARY,
        .lhs = par_parse_declaration(parser),
    };
    const u32 list_i = par_ast_node_array_push(&parser->nodes, &list);
    parser->nodes.values[last_list_i].rhs = list_i;
    last_list_i = list_i;
  }
  return root_i;
}

// --------------------------------- Code generation

typedef struct {
  cf_attribute_code_t *code;
  cf_frame_t *frame;
  u16 println_method_ref_i;
  cf_type_method_t *println_type;
  u16 out_field_ref_i;
} cg_generator_t;

static void cg_generate_node(cg_generator_t *gen, par_parser_t *parser,
                             cf_class_file_t *class_file,
                             const par_ast_node_t *node, arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(parser->nodes.len > 0);
  pg_assert(class_file != NULL);
  pg_assert(node != NULL);

  switch (node->kind) {
  case AST_KIND_NONE:
    return;
  case AST_KIND_NUM: {
    pg_assert(node->main_token < parser->lexer->tokens.len);

    lex_token_t token = parser->lexer->tokens.values[node->main_token];

    const cf_constant_t constant = {.kind = CONSTANT_POOL_KIND_INT,
                                    .v = {.number = par_number(parser, token)}};
    const u16 number_i =
        cf_constant_array_push(&class_file->constant_pool, &constant);

    pg_assert(gen->code != NULL);
    pg_assert(gen->code->code.values != NULL);
    pg_assert(gen->frame != NULL);

    cf_asm_load_constant(&gen->code->code, number_i, gen->frame);
    break;
  }
  case AST_KIND_ADD: {
    pg_assert(0 && "todo");
    break;
  }
  case AST_KIND_BUILTIN_PRINTLN: {
    pg_assert(gen->println_method_ref_i > 0);
    pg_assert(gen->println_type != NULL);
    pg_assert(gen->out_field_ref_i > 0);

    cf_asm_get_static(&gen->code->code, gen->out_field_ref_i, gen->frame);

    if (node->lhs != 0) {
      cg_generate_node(gen, parser, class_file,
                       &parser->nodes.values[node->lhs], arena);
    }

    cf_asm_invoke_virtual(&gen->code->code, gen->println_method_ref_i,
                          gen->frame, gen->println_type);
    break;
  }
  case AST_KIND_FUNCTION_DEFINITION: {
    const u32 token_name_i = node->main_token;
    pg_assert(token_name_i < parser->lexer->tokens.len);
    const lex_token_t token_name = parser->lexer->tokens.values[token_name_i];
    pg_assert(token_name.kind == TOKEN_KIND_IDENTIFIER);

    string_t method_name = {
        .len = lex_identifier_length(parser->buf, parser->buf_len,
                                     token_name.source_offset),
        .value = &parser->buf[token_name.source_offset],
    };
    const u16 method_name_i =
        cf_add_constant_string(&class_file->constant_pool, method_name);

    // FIXME: hardcoded type.
    cf_type_t void_type = {.kind = TYPE_VOID};
    const string_t string_class_name =
        string_make_from_c("java/lang/String", arena);
    cf_type_t string_type = {
        .kind = TYPE_INSTANCE_REFERENCE,
        .v = {.class_name = string_class_name},
    };
    cf_type_t main_argument_types[] = {{
        .kind = TYPE_ARRAY_REFERENCE,
        .v = {.array_type = &string_type},
    }};
    cf_type_t type = {
        .kind = TYPE_METHOD,
        .v =
            {
                .method =
                    {
                        .argument_count = 1,
                        .return_type = &void_type,
                        .argument_types = main_argument_types,
                    },
            },
    };
    string_t type_descriptor = string_reserve(64, arena);
    cf_fill_type_descriptor_string(&type, &type_descriptor);
    const u16 descriptor_i =
        cf_add_constant_string(&class_file->constant_pool, type_descriptor);

    cf_method_t method = {
        .access_flags = CAF_ACC_STATIC | CAF_ACC_PUBLIC /* FIXME */,
        .name = method_name_i,
        .descriptor = descriptor_i,
        .attributes = cf_attribute_array_make(8, arena),
    };

    cf_attribute_code_t code = {.max_locals = type.v.method.argument_count};
    cf_attribute_code_init(&code, arena);
    gen->code = &code;
    cf_frame_t frame = {0};
    gen->frame = &frame;

    // `lhs` is the arguments, `rhs` is the body.
    // TODO: Handle `lhs`.
    if (node->lhs > 0)
      pg_assert(0 && "todo");

    pg_assert(node->rhs < parser->nodes.len);
    cg_generate_node(gen, parser, class_file, &parser->nodes.values[node->rhs],
                     arena);

    cf_asm_return(&code.code);

    gen->code->max_stack = gen->frame->max_stack;
    cf_attribute_t attribute_code = {
        .kind = ATTRIBUTE_KIND_CODE,
        .name = cf_add_constant_cstring(&class_file->constant_pool, "Code"),
        .v = {.code = code}};
    cf_attribute_array_push(&method.attributes, &attribute_code);
    cf_method_array_push(&class_file->methods, &method);

    gen->code = NULL;
    break;
  }
  case AST_KIND_BINARY: {
    pg_assert(node->lhs < parser->nodes.len);
    pg_assert(node->rhs < parser->nodes.len);

    if (node->lhs != 0) {
      cg_generate_node(gen, parser, class_file,
                       &parser->nodes.values[node->lhs], arena);
    }
    if (node->rhs != 0) {
      cg_generate_node(gen, parser, class_file,
                       &parser->nodes.values[node->rhs], arena);
    }
    break;
  }
  default:
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

static void cg_generate_synthetic_class(cg_generator_t *gen,
                                        par_parser_t *parser,
                                        cf_class_file_t *class_file,
                                        arena_t *arena) {
  pg_assert(gen != NULL);
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(parser->nodes.len > 0);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  // FIXME: println(Int)
  {
    cf_type_t *const println_argument_types =
        arena_alloc(arena, 1, sizeof(cf_type_t));
    println_argument_types->kind = TYPE_INT;

    cf_type_t *const void_type = arena_alloc(arena, 1, sizeof(cf_type_t));
    void_type->kind = TYPE_VOID;

    gen->println_type = arena_alloc(arena, 1, sizeof(cf_type_method_t));
    *gen->println_type = (cf_type_method_t){
        .argument_count = 1,
        .return_type = void_type,
        .argument_types = println_argument_types,
    };

    cf_type_t const println_type = {
        .kind = TYPE_METHOD,
        .v =
            {
                .method = *gen->println_type,
            },
    };
    string_t println_type_s = string_reserve(30, arena);
    cf_fill_type_descriptor_string(&println_type, &println_type_s);

    const u16 descriptor_i =
        cf_add_constant_string(&class_file->constant_pool, println_type_s);

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

    gen->println_method_ref_i = method_ref_i;

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

static void cg_generate(par_parser_t *parser, cf_class_file_t *class_file,
                        arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->lexer->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(parser->nodes.len > 0);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  cg_generator_t gen = {0};
  cg_generate_synthetic_class(&gen, parser, class_file, arena);

  if (parser->nodes.len == 1)
    return;

  // Second node is the root.
  const par_ast_node_t *const root = &parser->nodes.values[1];
  cg_generate_node(&gen, parser, class_file, root, arena);
}
