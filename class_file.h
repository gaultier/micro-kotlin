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

// ------------------- Utils

typedef struct {
  u8 *base;
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
  u8 *value;
  arena_t *arena;
} string_t;

string_t string_reserve(u16 cap, arena_t *arena) {
  pg_assert(arena != NULL);

  return (string_t){
      .cap = cap,
      .value = arena_alloc(arena, cap, sizeof(u8)),
      .arena = arena,
  };
}

string_t string_make_from_c(const char *s, arena_t *arena) {
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

bool string_eq(string_t a, string_t b) {
  return a.len == b.len && memcmp(a.value, b.value, a.len) == 0;
}

bool string_eq_c(string_t a, char *b) {
  pg_assert(b != NULL);

  const u64 b_len = strlen(b);
  return a.len == b_len && memcmp(a.value, b, a.len) == 0;
}

void string_append_char(string_t *s, u8 c) {
  pg_assert(s != NULL);
  pg_assert(s->cap != 0);
  pg_assert(s->len <= s->cap);
  pg_assert(s->arena != NULL);

  if (s->len == s->cap - 1) {
    s->cap *= 2;
    u8 *const new_s = arena_alloc(s->arena, s->cap, sizeof(u8));
    s->value = memcpy(new_s, s->value, s->len);
  }

  s->value[s->len] = c;
  s->len += 1;

  pg_assert(s->value != NULL);
  pg_assert(s->len <= s->cap);
  pg_assert(s->arena != NULL);
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
  CFO_ALOAD_0 = 0x2a,
  CFO_INVOKE_SPECIAL = 0xb7,
  CFO_RETURN = 0xb1,
  CFO_GET_STATIC = 0xb2,
  CFO_LDC = 0x12,
  CFO_LDC_W = 0x13,
  CFO_INVOKE_VIRTUAL = 0xb6,
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
    CTY_VOID,
    CTY_BYTE,
    CTY_CHAR,
    CTY_DOUBLE,
    CTY_FLOAT,
    CTY_INT,
    CTY_LONG,
    CTY_INSTANCE_REFERENCE,
    CTY_SHORT,
    CTY_BOOLEAN,
    CTY_ARRAY_REFERENCE,
    CTY_METHOD,
    CTY_CONSTRUCTOR,
  } kind;
  union {
    string_t class_name;          // CTY_INSTANCE_REFERENCE
    cf_type_method_t method;      // CTY_METHOD, CTY_CONSTRUCTOR
    struct cf_type_t *array_type; // CTY_ARRAY_REFERENCE
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
  u8 *values;
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
    u8 *const new_array = arena_alloc(array->arena, new_cap, sizeof(u8));
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
    CIK_UTF8 = 1,
    CIK_INT = 3,
    CIK_FLOAT = 4,
    CIK_LONG = 5,
    CIK_DOUBLE = 6,
    CIK_CLASS_INFO = 7,
    CIK_STRING = 8,
    CIK_FIELD_REF = 9,
    CIK_METHOD_REF = 10,
    CIK_INTERFACE_METHOD_REF = 11,
    CIK_NAME_AND_TYPE = 12,
    CIK_METHOD_HANDLE = 15,
    CIK_METHOD_TYPE = 16,
    CIK_DYNAMIC = 17,
    CIK_INVOKE_DYNAMIC = 18,
    CIK_MODULE = 19,
    CIK_PACKAGE = 20,
  } kind;
  union {
    string_t s;        // CIK_UTF8
    u16 string_utf8_i; // CIK_STRING
    struct cf_constant_method_ref_t {
      u16 class;
      u16 name_and_type;
    } method_ref;   // CIK_METHOD_REF
    u16 class_name; // CIK_CLASS_INFO
    struct cf_constant_name_and_type_t {
      u16 name;
      u16 type_descriptor;
    } name_and_type; // CIK_NAME_AND_TYPE
    struct cf_constant_field_ref_t {
      u16 name;
      u16 type_descriptor;
    } field_ref; // CIK_FIELD_REF
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
  const u16 index = array->len + 1;
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
  case CTY_VOID: {
    string_append_char(type_descriptor, 'V');
    break;
  }
  case CTY_BYTE: {
    string_append_char(type_descriptor, 'B');
    break;
  }
  case CTY_CHAR: {
    string_append_char(type_descriptor, 'C');
    break;
  }
  case CTY_DOUBLE: {
    string_append_char(type_descriptor, 'D');
    break;
  }
  case CTY_FLOAT: {
    string_append_char(type_descriptor, 'F');
    break;
  }
  case CTY_INT: {
    string_append_char(type_descriptor, 'I');
    break;
  }
  case CTY_LONG: {
    string_append_char(type_descriptor, 'J');
    break;
  }
  case CTY_INSTANCE_REFERENCE: {
    const string_t class_name = type->v.class_name;

    string_append_char(type_descriptor, 'L');
    string_append_string(type_descriptor, &class_name);
    string_append_char(type_descriptor, ';');

    break;
  }
  case CTY_SHORT: {
    string_append_char(type_descriptor, 'S');
    break;
  }
  case CTY_BOOLEAN: {
    string_append_char(type_descriptor, 'Z');
    break;
  }
  case CTY_ARRAY_REFERENCE: {
    string_append_char(type_descriptor, '[');

    const cf_type_t *const array_type = type->v.array_type;
    pg_assert(array_type != NULL);
    cf_fill_type_descriptor_string(array_type, type_descriptor);

    break;
  }
  case CTY_CONSTRUCTOR:
  case CTY_METHOD: {
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

void cf_asm_load_constant_string(cf_code_array_t *code, u16 constant_i,
                                 cf_frame_t *vm) {
  pg_assert(code != NULL);
  pg_assert(constant_i > 0);
  pg_assert(vm != NULL);

  cf_code_array_push_u8(code, CFO_LDC_W);
  cf_code_array_push_u16(code, constant_i);

  vm->current_stack += 1;
  pg_assert(vm->current_stack < UINT16_MAX);
  vm->max_stack = pg_max(vm->max_stack, vm->current_stack);
}

void cf_asm_invoke_virtual(cf_code_array_t *code, u16 method_ref_i,
                           cf_frame_t *vm,
                           const cf_type_method_t *method_type) {
  pg_assert(code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(vm != NULL);

  cf_code_array_push_u8(code, CFO_INVOKE_VIRTUAL);
  cf_code_array_push_u16(code, method_ref_i);

  // FIXME: long, double takes 2 spots on the stack!
  pg_assert(vm->current_stack >= method_type->argument_count);
  vm->current_stack -= method_type->argument_count;
}

void cf_asm_get_static(cf_code_array_t *code, u16 field_i, cf_frame_t *vm) {
  pg_assert(code != NULL);
  pg_assert(field_i > 0);
  pg_assert(vm != NULL);

  cf_code_array_push_u8(code, CFO_GET_STATIC);
  cf_code_array_push_u16(code, field_i);

  vm->current_stack += 1;
  pg_assert(vm->current_stack < UINT16_MAX);
  vm->max_stack = pg_max(vm->max_stack, vm->current_stack);
}

void cf_asm_return(cf_code_array_t *code) {
  cf_code_array_push_u8(code, CFO_RETURN);

  // TODO
}

void cf_asm_invoke_special(cf_code_array_t *code, u16 method_ref_i,
                           cf_frame_t *vm,
                           const cf_type_method_t *method_type) {
  pg_assert(code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(vm != NULL);

  cf_code_array_push_u8(code, CFO_INVOKE_SPECIAL);
  cf_code_array_push_u16(code, method_ref_i);

  // FIXME: long, double takes 2 spots on the stack!
  pg_assert(vm->current_stack >= method_type->argument_count);
  vm->current_stack -= method_type->argument_count;
}

void cf_asm_call_superclass_constructor(cf_code_array_t *code,
                                        u16 super_class_constructor_i,
                                        cf_frame_t *vm,
                                        const cf_type_t *constructor_type) {
  pg_assert(code != NULL);
  pg_assert(super_class_constructor_i > 0);
  pg_assert(vm != NULL);
  pg_assert(constructor_type != NULL);
  pg_assert(constructor_type->kind == CTY_CONSTRUCTOR);

  cf_code_array_push_u8(
      code, CFO_ALOAD_0); // TODO: move the responsability to the caller?

  const cf_type_method_t *const method_type = &constructor_type->v.method;
  pg_assert(method_type != NULL);
  cf_asm_invoke_special(code, super_class_constructor_i, vm, method_type);
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
    CAK_SOURCE_FILE,
    CAK_CODE,
    CAK_LINE_NUMBER_TABLE,
    CAK_STACK_MAP_TABLE,
  } kind;

  u16 name;

  union {
    struct cf_attribute_code_t {
      u16 max_stack;
      u16 max_locals;
      cf_code_array_t code;
      cf_exception_array_t exceptions;
      cf_attribute_array_t attributes;
    } code; // CAK_CODE

    struct cf_attribute_source_file_t {
      u16 source_file;
    } source_file; // CAK_SOURCE_FILE

    struct cf_attribute_line_number_table_t {
      u16 line_number_table_count;
      cf_line_number_table_t *line_number_tables;
    } line_number_table; // CAK_LINE_NUMBER_TABLE
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

u16 buf_read_be_u16(u8 *buf, u64 size, u8 **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 2 <= buf + size);

  const u8 *const ptr = *current;
  const u16 x = (((u16)(ptr[0] & 0xff)) << 8) | ((u16)((ptr[1] & 0xff)) << 0);
  *current += 2;
  return x;
}

u32 buf_read_be_u32(u8 *buf, u64 size, u8 **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 4 <= buf + size);

  const u8 *const ptr = *current;
  const u32 x = ((u32)(ptr[0] & 0xff) << 24) | (((u32)(ptr[1] & 0xff)) << 16) |
                (((u32)(ptr[2] & 0xff)) << 8) | (((u32)(ptr[3] & 0xff)) << 0);
  *current += 4;
  return x;
}

void buf_read_n_u8(u8 *buf, u64 size, u8 *dst, u64 dst_len, u8 **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + dst_len <= buf + size);

  if (dst != NULL)
    memcpy(dst, *current, dst_len);

  *current += dst_len;
}

u8 buf_read_u8(u8 *buf, u64 size, u8 **current) {
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
  pg_assert(constant->kind == CIK_UTF8);
  return constant->v.s;
}

void cf_buf_read_attributes(u8 *buf, u64 buf_len, u8 **current,
                            cf_class_file_t *class_file,
                            cf_attribute_array_t *attributes, arena_t *arena);

void cf_buf_read_sourcefile_attribute(u8 *buf, u64 buf_len, u8 **current,
                                      cf_class_file_t *class_file,
                                      cf_attribute_array_t *attributes) {

  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);

  const u8 *const current_start = *current;

  cf_attribute_source_file_t source_file = {0};
  source_file.source_file = buf_read_be_u16(buf, buf_len, current);
  pg_assert(source_file.source_file > 0);
  pg_assert(source_file.source_file <= class_file->constant_pool.len);

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == 2);

  cf_attribute_t attribute = {.kind = CAK_SOURCE_FILE,
                              .v = {.source_file = source_file}};
  cf_attribute_array_push(attributes, &attribute);
}

void cf_buf_read_code_attribute_exceptions(u8 *buf, u64 buf_len, u8 **current,
                                           cf_class_file_t *class_file,
                                           cf_exception_array_t *exceptions,
                                           arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(exceptions != NULL);

  const u8 *const current_start = *current;

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

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == sizeof(u16) + table_len * sizeof(u16) * 4);
}

void cf_buf_read_code_attribute(u8 *buf, u64 buf_len, u8 **current,
                                cf_class_file_t *class_file, u32 attribute_len,
                                u16 name, cf_attribute_array_t *attributes,
                                arena_t *arena) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u8 *const current_start = *current;

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
      .kind = CAK_CODE, .name = name, .v = {.code = code}};
  cf_attribute_array_push(attributes, &attribute);

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_stack_map_table_attribute(u8 *buf, u64 buf_len, u8 **current,
                                           cf_class_file_t *class_file,
                                           u32 attribute_len, arena_t *arena) {
  pg_unused(arena);
  pg_unused(class_file);
  const u8 *const current_start = *current;

  buf_read_n_u8(buf, buf_len, NULL, attribute_len, current);

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_line_number_table_attribute(u8 *buf, u64 buf_len, u8 **current,
                                             cf_class_file_t *class_file,
                                             u32 attribute_len,
                                             arena_t *arena) {
  pg_unused(arena);
  pg_unused(class_file);

  const u8 *const current_start = *current;

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

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_local_variable_table_attribute(u8 *buf, u64 buf_len,
                                                u8 **current,
                                                cf_class_file_t *class_file,
                                                u32 attribute_len,
                                                arena_t *arena) {
  pg_unused(arena);
  const u8 *const current_start = *current;

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
  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_local_variable_type_table_attribute(
    u8 *buf, u64 buf_len, u8 **current, cf_class_file_t *class_file,
    u32 attribute_len, arena_t *arena) {
  pg_unused(arena);
  const u8 *const current_start = *current;

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
  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_signature_attribute(u8 *buf, u64 buf_len, u8 **current,
                                     cf_class_file_t *class_file,
                                     u32 attribute_len, arena_t *arena) {
  pg_unused(arena);
  pg_unused(class_file);

  const u8 *const current_start = *current;

  pg_assert(attribute_len == 2);
  const u16 signature_i = buf_read_be_u16(buf, buf_len, current);
  pg_unused(signature_i);
  // TODO store.

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

// TODO: store this data.
void cf_buf_read_exceptions_attribute(u8 *buf, u64 buf_len, u8 **current,
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

  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  const u16 entry_size = sizeof(u16);
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 exception_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(exception_i > 0);
    pg_assert(exception_i <= class_file->constant_pool.len);
  }
  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_inner_classes_attribute(u8 *buf, u64 buf_len, u8 **current,
                                         cf_class_file_t *class_file,
                                         u32 attribute_len, arena_t *arena) {
  pg_unused(arena);
  const u8 *const current_start = *current;

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
  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

// FIXME: each function call here should take the `attributes` argument and push
// to it!
void cf_buf_read_attribute(u8 *buf, u64 buf_len, u8 **current,
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

void cf_buf_read_attributes(u8 *buf, u64 buf_len, u8 **current,
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

void cf_buf_read_constant(u8 *buf, u64 buf_len, u8 **current,
                          cf_class_file_t *class_file, u64 *i,
                          u16 constant_pool_len) {
  u8 kind = buf_read_u8(buf, buf_len, current);

  if (!(kind == CIK_UTF8 || kind == CIK_INT || kind == CIK_FLOAT ||
        kind == CIK_LONG || kind == CIK_DOUBLE || kind == CIK_CLASS_INFO ||
        kind == CIK_STRING || kind == CIK_FIELD_REF || kind == CIK_METHOD_REF ||
        kind == CIK_INTERFACE_METHOD_REF || kind == CIK_NAME_AND_TYPE ||
        kind == CIK_METHOD_HANDLE || kind == CIK_METHOD_TYPE ||
        kind == CIK_DYNAMIC || kind == CIK_INVOKE_DYNAMIC ||
        kind == CIK_MODULE || kind == CIK_PACKAGE)) {
    fprintf(stderr, "Unknown constant kind found: offset=%lu kind=%u\n",
            *current - buf - 1, kind);
    pg_assert(0);
  }

  switch (kind) {
  case CIK_UTF8: { // FIXME: It's actually modified utf8!
    u16 len = buf_read_be_u16(buf, buf_len, current);

    u8 *const s = *current;
    buf_read_n_u8(buf, buf_len, NULL, len, current);

    LOG("[%lu/%hu] CIK_UTF8 len=%u s=%.*s", *i, constant_pool_len, len, len, s);

    cf_constant_t constant = {.kind = CIK_UTF8,
                              .v = {.s = {.len = len, .value = s}}};
    cf_constant_array_push(&class_file->constant_pool, &constant);

    break;
  }
  case CIK_INT: {
    const u32 value = buf_read_be_u32(buf, buf_len, current);
    pg_unused(value);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_FLOAT: {
    const u32 value = buf_read_be_u32(buf, buf_len, current);
    pg_unused(value);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_LONG: {
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
  case CIK_DOUBLE: {
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
  case CIK_CLASS_INFO: {
    const u16 class_name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_name_i > 0);
    pg_assert(class_name_i <= constant_pool_len);

    const cf_constant_t constant = {.kind = CIK_CLASS_INFO,
                                    .v = {.class_name = class_name_i}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_STRING: {
    const u16 utf8_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(utf8_i > 0);
    pg_assert(utf8_i <= constant_pool_len);
    LOG("[%lu/%hu] CIK_STRING utf8_i=%u", *i, constant_pool_len, utf8_i);

    const cf_constant_t constant = {.kind = CIK_STRING,
                                    .v = {.string_utf8_i = utf8_i}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_FIELD_REF: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_len);

    const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_len);

    LOG("[%lu/%hu] CIK_FIELD_REF name_i=%u descriptor_i=%u", *i,
        constant_pool_len, name_i, descriptor_i);

    const cf_constant_t constant = {
        .kind = CIK_FIELD_REF,
        .v = {.field_ref = {.name = name_i, .type_descriptor = descriptor_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_METHOD_REF: {
    const u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_len);

    const u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_len);

    LOG("[%lu/%hu] CIK_METHOD_REF class_i=%u name_and_type_i=%u", *i,
        constant_pool_len, class_i, name_and_type_i);

    const cf_constant_t constant = {
        .kind = CIK_METHOD_REF,
        .v = {.method_ref = {.name_and_type = name_and_type_i,
                             .class = class_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_INTERFACE_METHOD_REF: {
    const u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_len);

    const u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_len);

    LOG("[%lu/%hu] CIK_INSTANCE_REF class_i=%u name_and_type_i=%u", *i,
        constant_pool_len, class_i, name_and_type_i);

    const cf_constant_t constant = {
        .kind = CIK_INTERFACE_METHOD_REF,
    }; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_NAME_AND_TYPE: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_len);

    const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_len);

    LOG("[%lu/%hu] CIK_NAME_AND_TYPE class_i=%u name_and_type_i=%u", *i,
        constant_pool_len, name_i, descriptor_i);

    const cf_constant_t constant = {
        .kind = CIK_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = name_i,
                                .type_descriptor = descriptor_i}}};
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_METHOD_HANDLE: {
    const u8 reference_kind = buf_read_u8(buf, buf_len, current);
    pg_unused(reference_kind);
    const u16 reference_i = buf_read_be_u16(buf, buf_len, current);
    pg_unused(reference_i);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_METHOD_TYPE: {
    const u16 descriptor = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor > 0);
    pg_assert(descriptor <= constant_pool_len);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_DYNAMIC: {
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
  case CIK_INVOKE_DYNAMIC: {
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
  case CIK_MODULE: {
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_len);

    const cf_constant_t constant = {0}; // FIXME
    cf_constant_array_push(&class_file->constant_pool, &constant);
    break;
  }
  case CIK_PACKAGE: {
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

void cf_buf_read_constants(u8 *buf, u64 buf_len, u8 **current,
                           cf_class_file_t *class_file, u16 constant_pool_len) {
  for (u64 i = 1; i <= constant_pool_len; i++) {
    cf_buf_read_constant(buf, buf_len, current, class_file, &i,
                         constant_pool_len);
  }
}

void cf_buf_read_method(u8 *buf, u64 buf_len, u8 **current,
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

void cf_buf_read_methods(u8 *buf, u64 buf_len, u8 **current,
                         cf_class_file_t *class_file, arena_t *arena) {

  const u16 methods_count = buf_read_be_u16(buf, buf_len, current);
  class_file->methods = cf_method_array_make(methods_count, arena);

  for (u64 i = 0; i < methods_count; i++) {
    cf_buf_read_method(buf, buf_len, current, class_file, arena);
  }
}

void cf_buf_read_interfaces(u8 *buf, u64 buf_len, u8 **current,
                            cf_class_file_t *class_file, arena_t *arena) {

  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  const u8 *const current_start = *current;

  const u16 interfaces_count = buf_read_be_u16(buf, buf_len, current);
  class_file->interfaces = cf_interface_array_make(interfaces_count, arena);

  for (u16 i = 0; i < interfaces_count; i++) {
    const u16 interface_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(interface_i > 0);
    pg_assert(interface_i <= class_file->constant_pool.len);

    cf_interface_array_push(&class_file->interfaces, interface_i);
  }

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == sizeof(u16) + interfaces_count * sizeof(u16));
}

void cf_buf_read_field(u8 *buf, u64 buf_len, u8 **current,
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

void cf_buf_read_fields(u8 *buf, u64 buf_len, u8 **current,
                        cf_class_file_t *class_file, arena_t *arena) {

  const u16 fields_count = buf_read_be_u16(buf, buf_len, current);
  class_file->fields = cf_field_array_make(fields_count, arena);

  for (u16 i = 0; i < fields_count; i++) {
    cf_buf_read_field(buf, buf_len, current, class_file, arena);
  }
}

void cf_buf_read_class_file(u8 *buf, u64 buf_len, u8 **current,
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
  LOG("read=%ld rem=%ld", *current - buf, remaining);
  pg_assert(remaining == 0);
}

void cf_write_constant(const cf_class_file_t *class_file, FILE *file,
                       const cf_constant_t *constant) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);
  pg_assert(constant != NULL);

  switch (constant->kind) {
  case CIK_UTF8: {
    fwrite(&constant->kind, sizeof(u8), 1, file);
    const string_t *const s = &constant->v.s;
    file_write_be_16(file, s->len);
    fwrite(s->value, sizeof(u8), s->len, file);
    break;
  }
  case CIK_INT:
    pg_assert(0 && "unimplemented");
    break;
  case CIK_FLOAT:
    pg_assert(0 && "unimplemented");
    break;
  case CIK_LONG:
    pg_assert(0 && "unimplemented");
    break;
  case CIK_DOUBLE:
    pg_assert(0 && "unimplemented");
    break;
  case CIK_CLASS_INFO:
    fwrite(&constant->kind, sizeof(u8), 1, file);
    file_write_be_16(file, constant->v.class_name);
    break;
  case CIK_STRING:
    fwrite(&constant->kind, sizeof(u8), 1, file);
    file_write_be_16(file, constant->v.string_utf8_i);
    break;
  case CIK_FIELD_REF: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const cf_constant_field_ref_t *const field_ref = &constant->v.field_ref;

    file_write_be_16(file, field_ref->name);
    file_write_be_16(file, field_ref->type_descriptor);
    break;
  }
  case CIK_METHOD_REF: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const cf_constant_method_ref_t *const method_ref = &constant->v.method_ref;

    file_write_be_16(file, method_ref->class);
    file_write_be_16(file, method_ref->name_and_type);
    break;
  }
  case CIK_INTERFACE_METHOD_REF:
    pg_assert(0 && "unimplemented");
    break;
  case CIK_NAME_AND_TYPE: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const cf_constant_name_and_type_t *const name_and_type =
        &constant->v.name_and_type;

    file_write_be_16(file, name_and_type->name);
    file_write_be_16(file, name_and_type->type_descriptor);
    break;
  }
  case CIK_INVOKE_DYNAMIC:
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
    LOG("action=writing constant i=%lu/%lu", i, class_file->constant_pool.len);
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
  case CAK_SOURCE_FILE:
    return 2;
  case CAK_CODE: {
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
  case CAK_LINE_NUMBER_TABLE: {
    const cf_attribute_line_number_table_t *const attribute_line_number_table =
        &attribute->v.line_number_table;
    return sizeof(attribute_line_number_table->line_number_table_count) +
           attribute_line_number_table->line_number_table_count *
               sizeof(cf_line_number_table_t);
  }
  case CAK_STACK_MAP_TABLE:
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
  case CAK_SOURCE_FILE: {
    const u32 size = cf_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const cf_attribute_source_file_t *const source_file =
        &attribute->v.source_file;
    file_write_be_16(file, source_file->source_file);

    break;
  }
  case CAK_CODE: {
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
  case CAK_LINE_NUMBER_TABLE: {
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
  case CAK_STACK_MAP_TABLE: {
    pg_assert(0 && "unimplemented");
    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
}

void cf_write_attributes(FILE *file, const cf_attribute_array_t *attributes) {
  LOG("action=writing attributes %lu", attributes->len);
  file_write_be_16(file, attributes->len);

  for (uint64_t i = 0; i < attributes->len; i++) {
    const cf_attribute_t *const attribute = &attributes->values[i];
    LOG("action=writing attribute i=%lu/%lu", i, attributes->len);
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
    LOG("action=writing methods i=%lu/%lu", i, class_file->methods.len);
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

  const cf_constant_t constant = {.kind = CIK_UTF8, .v = {.s = s}};
  return cf_constant_array_push(constant_pool, &constant);
}

u16 cf_add_constant_cstring(cf_constant_array_t *constant_pool, char *s) {
  pg_assert(constant_pool != NULL);
  pg_assert(s != NULL);

  const cf_constant_t constant = {.kind = CIK_UTF8,
                                  .v = {.s = {
                                            .len = strlen(s),
                                            .value = (u8 *)s,
                                        }}};
  return cf_constant_array_push(constant_pool, &constant);
}

u16 cf_add_constant_jstring(cf_constant_array_t *constant_pool,
                            u16 constant_utf8_i) {
  pg_assert(constant_pool != NULL);
  pg_assert(constant_utf8_i > 0);

  const cf_constant_t constant = {.kind = CIK_STRING,
                                  .v = {.string_utf8_i = constant_utf8_i}};

  return cf_constant_array_push(constant_pool, &constant);
}

const char *cf_memrchr(const char *s, char c, u64 n) {
  pg_assert(s != NULL);
  pg_assert(n > 0);

  const char *res = s + n - 1;
  while (res-- != s) {
    if (*res == c)
      return res;
  }
  return NULL;
}

char *cf_make_class_file_name(const char *source_file_name, arena_t *arena) {
  pg_assert(source_file_name != NULL);
  pg_assert(arena != NULL);

  const u64 source_file_name_len = strlen(source_file_name);
  const char *const dot =
      cf_memrchr(source_file_name, '.', source_file_name_len);
  pg_assert(dot != NULL);

  const u64 extension_len = sizeof(".class");
  const u64 before_dot_incl_len = dot - source_file_name;
  pg_assert(before_dot_incl_len > 0);
  const u64 class_file_name_len = before_dot_incl_len + extension_len;
  pg_assert(class_file_name_len > extension_len);

  char *class_file_name = arena_alloc(arena, class_file_name_len, sizeof(u8));
  memcpy(class_file_name, source_file_name, before_dot_incl_len);
  memcpy(class_file_name + before_dot_incl_len, ".class", extension_len);

  class_file_name[class_file_name_len - 1] = 0;

  return class_file_name;
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
  const u16 index = array->len + 1;
  pg_assert(index > 0);
  pg_assert(index <= array->len + 1);
  array->len += 1;
  return index;
}

// TODO: one thread that walks the directory recursively and one/many worker
// threads to parse class files?
void cf_read_class_files(const char *path, u64 path_len,
                         cf_class_file_array_t *class_files, arena_t *arena) {
  pg_assert(path != NULL);
  pg_assert(path_len > 0);
  pg_assert(class_files != NULL);
  pg_assert(arena != NULL);

  struct stat st = {0};
  if (stat(path, &st) == -1) {
    LOG("fact='failed to stat(2)' path=%s errno=%d", path, errno);
    return;
  }

  if (S_ISREG(st.st_mode) && cstring_ends_with(path, path_len, ".class", 6)) {
    const int fd = open(path, O_RDONLY);
    pg_assert(fd > 0);

    u8 *buf = arena_alloc(arena, st.st_size, sizeof(u8));
    const ssize_t read_bytes = read(fd, buf, st.st_size);
    pg_assert(read_bytes == st.st_size);
    close(fd);

    u8 *current = buf;
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
    pg_assert(this_class->kind == CIK_CLASS_INFO);
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
  LTK_NUMBER,
  LTK_PLUS,
  LTK_LEFT_PAREN,
  LTK_RIGHT_PAREN,
  LTK_LEFT_BRACE,
  LTK_RIGHT_BRACE,
  LTK_BUILTIN_PRINTLN,
  LTK_KEYWORD_FUN,
  LTK_IDENTIFIER,
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
  const u16 index = array->len + 1;
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
  const u16 index = array->len + 1;
  pg_assert(index > 0);
  pg_assert(index <= array->len + 1);
  array->len += 1;
  return index;
}

typedef struct {
  lex_token_array_t tokens;
  lex_line_table_array_t line_table;
} lex_lexer_t;

static u32 lex_get_current_offset(const u8 *buf, u32 buf_len,
                                  const u8 *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return *current - buf;
}

static bool lex_is_at_end(const u8 *buf, u32 buf_len,
                          const u8 *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return lex_get_current_offset(buf, buf_len, current) == buf_len;
}

static u8 lex_peek(const u8 *buf, u32 buf_len, const u8 *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  return lex_is_at_end(buf, buf_len, current) ? 0 : **current;
}

static u8 lex_advance(const u8 *buf, u32 buf_len, const u8 **current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  const u8 c = **current;

  *current += 1;

  return lex_is_at_end(buf, buf_len, current) ? 0 : c;
}

static bool lex_is_alphabetic(const u8 *buf, u32 buf_len,
                              const u8 *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return ('a' <= **current && **current <= 'z') ||
         ('A' <= **current && **current <= 'Z');
}

static bool lex_is_digit(const u8 *buf, u32 buf_len, const u8 *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return ('0' <= **current && **current <= '9');
}

static bool lex_is_identifier_char(const u8 *buf, u32 buf_len,
                                   const u8 *const *current) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);

  return lex_is_alphabetic(buf, buf_len, current) ||
         lex_is_digit(buf, buf_len, current) ||
         lex_peek(buf, buf_len, current) == '_';
}

static u32 lex_identifier_length(const u8 *buf, u32 buf_len,
                                 u32 current_offset) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current_offset < buf_len);

  const u32 start_offset = current_offset;
  const u8 *current = &buf[current_offset];
  pg_assert(lex_is_alphabetic(buf, buf_len, &current));

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

static void lex_identifier(lex_lexer_t *lexer, const u8 *buf, u32 buf_len,
                           const u8 **current) {
  pg_assert(lexer != NULL);
  pg_assert(lexer->tokens.values != NULL);
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(*current - buf <= buf_len);
  pg_assert(lex_is_alphabetic(buf, buf_len, current));

  const u32 start_offset = lex_get_current_offset(buf, buf_len, current);
  const string_t identifier = {
      .len = lex_identifier_length(buf, buf_len, start_offset),
      .value = *current,
  };
  *current += identifier.len;
  if (string_eq_c(identifier, "fun")) {
    const lex_token_t token = {
        .kind = LTK_KEYWORD_FUN,
        .source_offset = start_offset,
    };
    lex_token_array_push(&lexer->tokens, &token);
  } else if (string_eq_c(identifier, "println")) {
    const lex_token_t token = {
        .kind = LTK_BUILTIN_PRINTLN,
        .source_offset = start_offset,
    };
    lex_token_array_push(&lexer->tokens, &token);
  } else {
    const lex_token_t token = {
        .kind = LTK_IDENTIFIER,
        .source_offset = start_offset,
    };
    lex_token_array_push(&lexer->tokens, &token);
  }
}

static void lex_number(lex_lexer_t *lexer, const u8 *buf, u32 buf_len,
                       const u8 **current) {
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
      .kind = LTK_NUMBER,
      .source_offset = start_offset,
  };
  lex_token_array_push(&lexer->tokens, &token);
}

static void lex_lex(lex_lexer_t *lexer, const u8 *buf, u32 buf_len,
                    const u8 **current) {
  pg_assert(lexer != NULL);
  pg_assert(lexer->line_table.values != NULL);
  pg_assert(lexer->tokens.values != NULL);
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  while (!lex_is_at_end(buf, buf_len, current)) {
    const u8 c = **current;

    switch (c) {
    case '(': {
      const lex_token_t token = {
          .kind = LTK_LEFT_PAREN,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case ')': {
      const lex_token_t token = {
          .kind = LTK_RIGHT_PAREN,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '{': {
      const lex_token_t token = {
          .kind = LTK_LEFT_BRACE,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '}': {
      const lex_token_t token = {
          .kind = LTK_RIGHT_BRACE,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '+': {
      const lex_token_t token = {
          .kind = LTK_PLUS,
          .source_offset = lex_get_current_offset(buf, buf_len, current),
      };
      lex_token_array_push(&lexer->tokens, &token);
      lex_advance(buf, buf_len, current);
      break;
    }
    case '\n': {
      const lex_line_table_t line = {
          .line =
              lexer->line_table.len == 0
                  ? 1
                  : lexer->line_table.values[lexer->line_table.len - 1].line +
                        1,
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
      if (lex_is_alphabetic(buf, buf_len, current)) {
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

// ------------------------------ Parser

typedef enum {
  PAK_NUM,
  PAK_ADD,
  PAK_BUILTIN_PRINTLN,
  PAK_FUNCTION_DEFINITION,
  PAK_BLOCK,
} par_ast_node_kind_t;

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

  array->values[array->len] = *x;
  const u16 index = array->len + 1;
  pg_assert(index > 0);
  pg_assert(index <= array->len + 1);
  array->len += 1;
  return index;
}

typedef struct {
  u8 *buf;
  u32 buf_len;
  u32 tokens_i;
  lex_token_array_t tokens;
  par_ast_node_array_t nodes;
} par_parser_t;

typedef enum {
  PAR_NONE,
  PAR_OK,
  PAR_ERR_UNEXPECTED_TOKEN,
} par_result_t;

static bool par_is_at_end(const par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);

  return parser->tokens_i == parser->tokens.len;
}

static lex_token_t par_peek(const par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);

  return parser->tokens.values[parser->tokens_i];
}

static lex_token_t par_advance(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);

  return parser->tokens.values[parser->tokens_i++];
}

static par_result_t par_parse_declaration(par_parser_t *parser,
                                          u32 *new_node_i);
static par_result_t par_parse_expression(par_parser_t *parser, u32 *new_node_i);

static u32 par_last_node(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);

  return parser->nodes.len - 1;
}

static par_result_t par_parse_builtin_println(par_parser_t *parser,
                                              u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  pg_assert(par_peek(parser).kind == LTK_BUILTIN_PRINTLN);
  const u32 main_token = parser->tokens_i;
  par_advance(parser);

  if (par_peek(parser).kind != LTK_LEFT_PAREN)
    return PAR_ERR_UNEXPECTED_TOKEN;
  par_advance(parser);

  if (par_peek(parser).kind != LTK_RIGHT_PAREN) { // Parse parameters.

    par_result_t result = par_parse_expression(parser, new_node_i);
    if (result == PAR_NONE) {
      pg_assert(0 && "todo error"); // No arguments.
    }
    if (result == PAR_OK) {
    } // Ok.
    else {
      // Error.
      return result;
    }
  }

  if (par_peek(parser).kind != LTK_RIGHT_PAREN)
    return PAR_ERR_UNEXPECTED_TOKEN;
  par_advance(parser);

  const par_ast_node_t node = {
      .kind = PAK_BUILTIN_PRINTLN,
      .lhs = par_last_node(parser),
      .main_token = main_token,
  };
  par_ast_node_array_push(&parser->nodes, &node);
  *new_node_i = par_last_node(parser);

  return PAR_OK;
}

static u64 par_number(const par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);

  pg_assert(par_peek(parser).kind == LTK_NUMBER);

  const lex_token_t token = parser->tokens.values[parser->tokens_i];
  const u32 start = token.source_offset;
  const u8 *current = &parser->buf[start];
  while (lex_is_digit(parser->buf, parser->buf_len, &current)) {
    lex_advance(parser->buf, parser->buf_len, &current);
  }
  const u32 end_excl =
      lex_get_current_offset(parser->buf, parser->buf_len, &current);
  const u32 length = end_excl - start;
  pg_assert(length <= 20);

  u64 number = 0;

  for (i64 i = length - 1; i >= 0; i--) {
    pg_assert(i < parser->buf_len);

    const u8 c = parser->buf[i];
    number += 10 * i * (c - '0');
  }

  return number;
}

static par_result_t par_parse_primary_expression(par_parser_t *parser,
                                                 u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  if (par_peek(parser).kind == LTK_BUILTIN_PRINTLN)
    return par_parse_builtin_println(parser, new_node_i);

  if (par_peek(parser).kind == LTK_NUMBER) {
    // const u64 number = par_number(parser);
    const par_ast_node_t node = {
        .kind = PAK_NUM,
        .main_token = parser->tokens_i,
    };
    par_ast_node_array_push(&parser->nodes, &node);
    *new_node_i = par_last_node(parser);

    par_advance(parser);
    return PAR_OK;
  }

  return PAR_NONE;
}

static par_result_t par_parse_postfix_unary_expression(par_parser_t *parser,
                                                       u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_primary_expression(parser, new_node_i);
}

static par_result_t par_parse_prefix_unary_expression(par_parser_t *parser,
                                                      u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_postfix_unary_expression(parser, new_node_i);
}

static par_result_t par_parse_as_expression(par_parser_t *parser,
                                            u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_prefix_unary_expression(parser, new_node_i);
}

static par_result_t par_parse_multiplication_expression(par_parser_t *parser,
                                                        u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  // FIXME: *
  return par_parse_as_expression(parser, new_node_i);
}

static par_result_t par_parse_additive_expression(par_parser_t *parser,
                                                  u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_multiplication_expression(parser, new_node_i);
}

static par_result_t par_parse_range_expression(par_parser_t *parser,
                                               u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_additive_expression(parser, new_node_i);
}

static par_result_t par_parse_infix_function_call(par_parser_t *parser,
                                                  u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_range_expression(parser, new_node_i);
}

static par_result_t par_parse_elvis_expression(par_parser_t *parser,
                                               u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_infix_function_call(parser, new_node_i);
}

static par_result_t par_parse_infix(par_parser_t *parser, u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_elvis_expression(parser, new_node_i);
}

static par_result_t par_parse_generic_call_like_comparison(par_parser_t *parser,
                                                           u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_infix(parser, new_node_i);
}

static par_result_t par_parse_comparison(par_parser_t *parser,
                                         u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_generic_call_like_comparison(parser, new_node_i);
}

static par_result_t par_parse_equality(par_parser_t *parser, u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_comparison(parser, new_node_i);
}

static par_result_t par_parse_conjunction(par_parser_t *parser,
                                          u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_equality(parser, new_node_i);
}

static par_result_t par_parse_disjunction(par_parser_t *parser,
                                          u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  return par_parse_conjunction(parser, new_node_i);
}

static par_result_t par_parse_expression(par_parser_t *parser,
                                         u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);

  return par_parse_disjunction(parser, new_node_i);
}

static par_result_t par_parse_statement(par_parser_t *parser, u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  par_result_t result = PAR_NONE;

  if ((result = par_parse_declaration(parser, new_node_i)) != PAR_NONE)
    return result;

  return par_parse_expression(parser, new_node_i);

  return PAR_OK;
}

static par_result_t par_parse_statements(par_parser_t *parser,
                                         u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  par_result_t result = PAR_NONE;

  const par_ast_node_t node = {
      .kind = PAK_BLOCK,
      .main_token = parser->tokens_i - 1,
  };
  par_ast_node_array_push(&parser->nodes, &node);
  u32 last_block_i = *new_node_i = par_last_node(parser);

  while (1) {
    u32 new_child_i = 0;
    result = par_parse_statement(parser, &new_child_i);
    if (result == PAR_OK) {
      const par_ast_node_t node = {
          .kind = PAK_BLOCK,
          .main_token = parser->tokens_i - 1,
          .lhs = new_child_i,
      };
      par_ast_node_array_push(&parser->nodes, &node);

      parser->nodes.values[last_block_i].rhs =
          par_last_node(parser); // Linked-list of blocks.

      last_block_i = par_last_node(parser);

      continue;
    }
    if (result == PAR_NONE)
      return PAR_OK;
    // Error
    return result;
  }

  return PAR_OK;
}

static par_result_t par_parse_block(par_parser_t *parser, u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  if (par_peek(parser).kind != LTK_LEFT_BRACE)
    return PAR_NONE;
  par_advance(parser);

  // TODO: scope.

  par_result_t result = PAR_NONE;
  if ((result = par_parse_statements(parser, new_node_i)) != PAR_OK)
    return result;

  if (par_peek(parser).kind != LTK_RIGHT_BRACE)
    return PAR_NONE;
  par_advance(parser);

  return PAR_OK;
}

static par_result_t par_parse_function_definition(par_parser_t *parser,
                                                  u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  if (par_peek(parser).kind != LTK_KEYWORD_FUN)
    return PAR_NONE;
  par_advance(parser);

  const par_ast_node_t node = {
      .kind = PAK_FUNCTION_DEFINITION,
      .main_token = parser->tokens_i,
  };
  par_ast_node_array_push(&parser->nodes, &node);
  *new_node_i = par_last_node(parser);

  if (par_peek(parser).kind != LTK_IDENTIFIER)
    return PAR_ERR_UNEXPECTED_TOKEN;
  par_advance(parser);

  if (par_peek(parser).kind != LTK_LEFT_PAREN)
    return PAR_ERR_UNEXPECTED_TOKEN;
  par_advance(parser);

  if (par_peek(parser).kind != LTK_RIGHT_PAREN)
    return PAR_ERR_UNEXPECTED_TOKEN;
  par_advance(parser);

  u32 fn_body_i = 0;
  par_result_t result = par_parse_block(parser, &fn_body_i);
  if (result == PAR_NONE || result == PAR_OK) {
    pg_assert(fn_body_i > 0);
    parser->nodes.values[*new_node_i].lhs = fn_body_i;
  }
  return result;
}

static par_result_t par_parse_declaration(par_parser_t *parser,
                                          u32 *new_node_i) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(new_node_i != NULL);

  par_result_t result = PAR_NONE;
  if ((result = par_parse_function_definition(parser, new_node_i)) !=
      PAR_NONE) {
    return result;
  }

  return PAR_NONE;
}

static par_result_t par_parse(par_parser_t *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);

  while (!par_is_at_end(parser)) {
    u32 new_node_i = 0;
    const par_result_t result = par_parse_declaration(parser, &new_node_i);
    if (result == PAR_OK) {
      // TODO: use new_node_i
      continue;
    }
    if (result == PAR_NONE)
      return PAR_OK; // The end.

    // Error.
    return result;
  }

  return PAR_OK;
}

// --------------------------------- Code generation

static void cg_generate_node(par_parser_t *parser, cf_class_file_t *class_file,
                             const par_ast_node_t *node, arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(parser->nodes.len > 0);
  pg_assert(class_file != NULL);
  pg_assert(node != NULL);

  switch (node->kind) {
  case PAK_NUM: {
    break;
  }
  case PAK_ADD: {
    break;
  }
  case PAK_BUILTIN_PRINTLN: {
    break;
  }
  case PAK_FUNCTION_DEFINITION: {
    const u32 token_name_i = node->main_token;
    pg_assert(token_name_i < parser->tokens.len);
    const lex_token_t token_name = parser->tokens.values[token_name_i];
    pg_assert(token_name.kind == LTK_IDENTIFIER);

    string_t method_name = {
        .len = lex_identifier_length(parser->buf, parser->buf_len,
                                     token_name.source_offset),
        .value = &parser->buf[token_name.source_offset],
    };
    const u16 method_name_i =
        cf_add_constant_string(&class_file->constant_pool, method_name);

    // FIXME: type.
    cf_type_t void_type = {.kind = CTY_VOID};
    cf_type_t type = {
        .kind = CTY_METHOD,
        .v =
            {
                .method =
                    {
                        .argument_count = 0,
                        .return_type = &void_type,
                    },
            },
    };
    string_t type_descriptor = string_reserve(64, arena);
    cf_fill_type_descriptor_string(&type, &type_descriptor);
    const u16 descriptor_i =
        cf_add_constant_string(&class_file->constant_pool, type_descriptor);

    cf_method_t method = {
        .access_flags = CAF_ACC_PUBLIC /* FIXME */,
        .name = method_name_i,
        .descriptor = descriptor_i,
        .attributes = cf_attribute_array_make(8, arena),
    };
    cf_method_array_push(&class_file->methods, &method);
    break;
  }
  case PAK_BLOCK: {
    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
}

static void cg_generate(par_parser_t *parser, cf_class_file_t *class_file,
                        arena_t *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens.values != NULL);
  pg_assert(parser->nodes.values != NULL);
  pg_assert(parser->tokens_i <= parser->tokens.len);
  pg_assert(parser->nodes.len > 0);
  pg_assert(class_file != NULL);

  const par_ast_node_t *const root = &parser->nodes.values[0];
  cg_generate_node(parser, class_file, root, arena);
}
