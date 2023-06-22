#pragma once

#include <arpa/inet.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>

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

#define pg_assert(condition)                                                   \
  do {                                                                         \
    if (!(condition))                                                          \
      __builtin_trap();                                                        \
  } while (0)

#define pg_max(a, b) ((a) > (b) ? (a) : (b))

typedef enum {
  CFO_ALOAD_0 = 0x2a,
  CFO_INVOKE_SPECIAL = 0xb7,
  CFO_RETURN = 0xb1,
  CFO_GET_STATIC = 0xb2,
  CFO_LDC = 0x12,
  CFO_LDC_W = 0x13,
  CFO_INVOKE_VIRTUAL = 0xb6,
} cf_op_kind_t;

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

static void *arena_alloc(arena_t *arena, u64 len) {
  pg_assert(arena != NULL);
  pg_assert(arena->current_offset < arena->capacity);
  pg_assert(arena->current_offset + len < arena->capacity);

  // TODO: align?
  arena->current_offset = align_forward_16(arena->current_offset + len);
  pg_assert((arena->current_offset % 16) == 0);

  return arena->base + arena->current_offset - len;
}

typedef struct {
  u16 cap;
  u16 len;
  u8 *value;
  arena_t *arena;
} string_t;

string_t string_reserve(u16 cap, arena_t *arena) {
  return (string_t){
      .cap = cap,
      .value = arena_alloc(arena, cap),
      .arena = arena,
  };
}

string_t string_make_from_c(char *s, arena_t *arena) {
  const u64 len = strlen(s);
  string_t res = string_reserve(len, arena);
  res.len = len;
  memcpy(res.value, s, len);
  return res;
}

bool string_eq(string_t a, string_t b) {
  return a.len == b.len && memcmp(a.value, b.value, a.len) == 0;
}

bool string_eq_c(string_t a, char *b) {
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
    u8 *const new_s = arena_alloc(s->arena, s->cap);
    s->value = memcpy(new_s, s->value, s->len);
  }

  s->value[s->len] = c;
  s->len += 1;
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
}

#define LOG(fmt, ...) fprintf(stderr, fmt "\n", ##__VA_ARGS__)

// ------------------------

static char *const CF_INIT_CONSTRUCTOR_STRING = "<init>";

typedef struct {
  u16 current;
  u16 max;
} cf_stack_t;

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
  } kind;
  union {
    string_t class_name;     // CTY_INSTANCE_REFERENCE
    cf_type_method_t method; // CTY_METHOD
  } v;
};
typedef struct cf_type_t cf_type_t;

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
      .values = arena_alloc(arena, cap * sizeof(u8)),
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
    u8 *const new_array = arena_alloc(array->arena, new_cap);
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
    CIK_INVOKE_DYNAMIC = 18,
    // CIK_LONG_HIGH,
    // CIK_LONG_LOW,
    // CIK_DOUBLE_HIGH,
    // CIK_DOUBLE_LOW,
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
      .values = arena_alloc(arena, cap * sizeof(cf_constant_t)),
      .arena = arena,
  };
}

u16 cf_constant_array_push(cf_constant_array_t *array, const cf_constant_t *x) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_constant_t *const new_array = arena_alloc(array->arena, new_cap);
    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_constant_t));
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
cf_constant_array_at(const cf_constant_array_t *constant_pool, u16 i) {
  pg_assert(constant_pool != NULL);
  pg_assert(i > 0);
  pg_assert(i <= constant_pool->len);

  return &constant_pool->values[i];
}

void cf_fill_type_descriptor_string(const cf_type_t *type,
                                    string_t *type_descriptor) {
  pg_assert(type != NULL);
  pg_assert(type_descriptor != NULL);

  switch (type->kind) {
  case CTY_VOID: {
    string_append_char(type_descriptor, 'V');
    break;
  };
  case CTY_BYTE: {
    string_append_char(type_descriptor, 'B');
    break;
  };
  case CTY_CHAR: {
    string_append_char(type_descriptor, 'C');
    break;
  };
  case CTY_DOUBLE: {
    string_append_char(type_descriptor, 'D');
    break;
  };
  case CTY_FLOAT: {
    string_append_char(type_descriptor, 'F');
    break;
  };
  case CTY_INT: {
    string_append_char(type_descriptor, 'I');
    break;
  };
  case CTY_LONG: {
    string_append_char(type_descriptor, 'J');
    break;
  };
  case CTY_INSTANCE_REFERENCE: {
    const string_t class_name = type->v.class_name;

    string_append_char(type_descriptor, 'L');
    string_append_string(type_descriptor, &class_name);
    string_append_char(type_descriptor, ';');

    break;
  };
  case CTY_SHORT: {
    string_append_char(type_descriptor, 'S');
    break;
  };
  case CTY_BOOLEAN: {
    string_append_char(type_descriptor, 'Z');
    break;
  };
  case CTY_ARRAY_REFERENCE: {
    string_append_char(type_descriptor, '[');
    break;
  };
  case CTY_METHOD: {
    const cf_type_method_t *const method_type = &type->v.method;
    string_append_char(type_descriptor, '(');

    for (u64 i = 0; i < method_type->argument_count; i++) {
      const cf_type_t *const argument_type = &method_type->argument_types[i];
      cf_fill_type_descriptor_string(argument_type, type_descriptor);
    }

    string_append_char(type_descriptor, ')');

    cf_fill_type_descriptor_string(method_type->return_type, type_descriptor);

    break;
  };
  default:
    pg_assert(0 && "unreachable");
  }
}

void cf_asm_load_constant_string(cf_code_array_t *code, u16 constant_i,
                                 cf_stack_t *stack) {
  pg_assert(code != NULL);
  pg_assert(constant_i > 0);
  pg_assert(stack != NULL);

  cf_code_array_push_u8(code, CFO_LDC_W);
  cf_code_array_push_u16(code, constant_i);

  stack->current += 1;
  pg_assert(stack->current < UINT16_MAX);
  stack->max = pg_max(stack->max, stack->current);
}

void cf_asm_invoke_virtual(cf_code_array_t *code, u16 method_ref_i,
                           cf_stack_t *stack) {
  pg_assert(code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(stack != NULL);

  cf_code_array_push_u8(code, CFO_INVOKE_VIRTUAL);
  cf_code_array_push_u8(code, method_ref_i);

  // TODO
}

void cf_asm_get_static(cf_code_array_t *code, u16 field_i, cf_stack_t *stack) {
  pg_assert(code != NULL);
  pg_assert(field_i > 0);
  pg_assert(stack != NULL);

  cf_code_array_push_u8(code, CFO_GET_STATIC);
  cf_code_array_push_u8(code, field_i);

  stack->current += 1;
  pg_assert(stack->current < UINT16_MAX);
  stack->max = pg_max(stack->max, stack->current);
}

void cf_asm_return(cf_code_array_t *code) {
  cf_code_array_push_u8(code, CFO_RETURN);

  // TODO
}

void cf_asm_call_superclass_constructor(cf_code_array_t *code,
                                        u16 super_class_constructor_i) {
  cf_code_array_push_u8(code, CFO_ALOAD_0);
  cf_code_array_push_u8(code, CFO_INVOKE_SPECIAL);
  cf_code_array_push_u16(code, super_class_constructor_i);
}

typedef struct {
} cf_field_t;

typedef struct cf_attribute_t cf_attribute_t;
typedef struct {
  u64 len;
  u64 cap;
  cf_attribute_t *values;
  arena_t *arena;
} cf_attribute_array_t;

typedef struct cf_method_t cf_method_t;
typedef struct {
  u64 len;
  u64 cap;
  cf_method_t *values;
  arena_t *arena;
} cf_method_array_t;

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
      u16 exception_table_count;
      void *exception_table; // TODO
      cf_attribute_array_t attributes;
    } code; // CAK_CODE

    struct cf_attribute_source_file_t {
      u16 source_file;
    } source_file; // CAK_SOURCE_FILE

    struct cf_attribute_line_number_table_t {
      u16 line_number_table_count;
      cf_line_number_table_t *line_number_tables;
    } line_number_table;
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
      .values = arena_alloc(arena, cap * sizeof(cf_attribute_t)),
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
    cf_attribute_t *const new_array = arena_alloc(array->arena, new_cap);
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
      .values = arena_alloc(arena, cap * sizeof(cf_method_t)),
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
    cf_method_t *const new_array = arena_alloc(array->arena, new_cap);
    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_method_t));
    array->cap = new_cap;
  }

  array->values[array->len++] = *x;
}

const u32 cf_MAGIC_NUMBER = 0xbebafeca;
const u16 cf_MAJOR_VERSION_6 = 50;
const u16 cf_MINOR_VERSION = 0;

typedef struct {
  u32 magic;
  u16 minor_version;
  u16 major_version;
  cf_constant_array_t constant_pool;
  u16 access_flags;
  u16 this_class;
  u16 super_class;
  u16 interfaces_count;
  u16 fields_count;
  cf_field_t *fields;
  cf_method_array_t methods;
  cf_attribute_array_t attributes;
} cf_class_file_t;

void file_write_be_16(FILE *file, u16 x) {
  pg_assert(file != NULL);

  const u16 x_be = htons(x);
  fwrite(&x_be, sizeof(x_be), 1, file);
}

void file_write_be_32(FILE *file, u32 x) {
  pg_assert(file != NULL);

  const u32 x_be = htonl(x);
  fwrite(&x_be, sizeof(x_be), 1, file);
}

u16 buf_read_be_u16(u8 *buf, u64 size, u8 **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 2 <= buf + size);

  const u16 *const ptr = (u16 *)*current;
  const u16 x_be = ptr[0];
  *current += 2;
  return ntohs(x_be);
}

u32 buf_read_be_u32(u8 *buf, u64 size, u8 **current) {
  pg_assert(buf != NULL);
  pg_assert(size > 0);
  pg_assert(current != NULL);
  pg_assert(*current + 4 <= buf + size);

  const u32 *const ptr = (u32 *)*current;
  const u32 x_be = ptr[0];
  *current += 4;
  return ntohl(x_be);
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
cf_constant_array_at_as_string(const cf_constant_array_t *constant_pool,
                               u16 i) {
  const cf_constant_t *const constant = cf_constant_array_at(constant_pool, i);
  pg_assert(constant->kind == CIK_UTF8);
  return constant->v.s;
}

void cf_buf_read_attributes(u8 *buf, u64 buf_len, u8 **current,
                            cf_constant_array_t *constant_pool);

void cf_buf_read_sourcefile_attribute(u8 *buf, u64 buf_len, u8 **current,
                                      cf_constant_array_t *constant_pool,
                                      u32 attribute_len) {
  const u8 *const current_start = *current;

  const u16 source_file_i = buf_read_be_u16(buf, buf_len, current);
  pg_assert(source_file_i > 0);
  pg_assert(source_file_i <= constant_pool->len);
  LOG("attribute_source_file source_file_i=%hu", source_file_i);
  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
  pg_assert(2 == attribute_len);
}

void cf_buf_read_code_attribute(u8 *buf, u64 buf_len, u8 **current,
                                cf_constant_array_t *constant_pool,
                                u32 attribute_len) {
  const u8 *const current_start = *current;

  const u16 max_stack = buf_read_be_u16(buf, buf_len, current);
  const u16 max_locals = buf_read_be_u16(buf, buf_len, current);
  const u32 code_len = buf_read_be_u32(buf, buf_len, current);
  pg_assert(*current + code_len <= buf + buf_len);

  buf_read_n_u8(buf, buf_len, NULL, code_len, current);

  const u16 exception_table_len = buf_read_be_u16(buf, buf_len, current);
  LOG("attribute_code max_stack=%hu max_locals=%hu code_len=%u "
      "exception_table_len=%hu",
      max_stack, max_locals, code_len, exception_table_len);

  cf_buf_read_attributes(buf, buf_len, current, constant_pool);

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_stack_map_table_attribute(u8 *buf, u64 buf_len, u8 **current,
                                           cf_constant_array_t *constant_pool,
                                           u32 attribute_len) {
  const u8 *const current_start = *current;

  buf_read_n_u8(buf, buf_len, NULL, attribute_len, current);

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_line_number_table_attribute(u8 *buf, u64 buf_len, u8 **current,
                                             cf_constant_array_t *constant_pool,
                                             u32 attribute_len) {

  const u8 *const current_start = *current;

  const u16 line_number_len = buf_read_be_u16(buf, buf_len, current);
  pg_assert(sizeof(line_number_len) +
                line_number_len * (sizeof(u16) + sizeof(u16)) ==
            attribute_len);

  for (u16 i = 0; i < line_number_len; i++) {
    const u16 start_pc = buf_read_be_u16(buf, buf_len, current);
    const u16 line_number = buf_read_be_u16(buf, buf_len, current);
    LOG("[%hu/%hu] Line number table entry: start_pc=%hu line_number=%hu", i,
        line_number_len, start_pc, line_number);
  }

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_local_variable_table_attribute(
    u8 *buf, u64 buf_len, u8 **current, cf_constant_array_t *constant_pool,
    u32 attribute_len) {
  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  const u16 entry_size = sizeof(u16) * 5;
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 start_pc = buf_read_be_u16(buf, buf_len, current);
    const u16 len = buf_read_be_u16(buf, buf_len, current);
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool->len);

    const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    const u16 idx = buf_read_be_u16(buf, buf_len, current);

    LOG("[%hu/%hu] Local variable table entry: start_pc=%hu "
        "attribute_len=%hu name_i=%hu descriptor_i=%hu index=%hu",
        i, table_len, start_pc, len, name_i, descriptor_i, idx);
  }
  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_local_variable_type_table_attribute(
    u8 *buf, u64 buf_len, u8 **current, cf_constant_array_t *constant_pool,
    u32 attribute_len) {
  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, buf_len, current);
  const u16 entry_size = sizeof(u16) * 5;
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 start_pc = buf_read_be_u16(buf, buf_len, current);
    const u16 len = buf_read_be_u16(buf, buf_len, current);
    const u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool->len);

    const u16 signature_i = buf_read_be_u16(buf, buf_len, current);
    const u16 idx = buf_read_be_u16(buf, buf_len, current);

    LOG("[%hu/%hu] Local variable type table entry: start_pc=%hu "
        "attribute_len=%hu name_i=%hu signature_i=%hu index=%hu",
        i, table_len, start_pc, len, name_i, signature_i, idx);
  }
  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_signature_attribute(u8 *buf, u64 buf_len, u8 **current,
                                     cf_constant_array_t *constant_pool,
                                     u32 attribute_len) {

  const u8 *const current_start = *current;

  pg_assert(attribute_len == 2);
  const u16 signature_i = buf_read_be_u16(buf, buf_len, current);
  LOG("Signature #%hu", signature_i);

  const u8 *const current_end = *current;
  const u64 read_bytes = current_end - current_start;
  pg_assert(read_bytes == attribute_len);
}

void cf_buf_read_attribute(u8 *buf, u64 buf_len, u8 **current,
                           cf_constant_array_t *constant_pool) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(constant_pool != NULL);

  const u16 name_i = buf_read_be_u16(buf, buf_len, current);
  pg_assert(name_i > 0);
  const u32 size = buf_read_be_u32(buf, buf_len, current);

  LOG("attribute name_i=%hu size=%u", name_i, size);
  pg_assert(*current + size <= buf + buf_len);

  pg_assert(name_i < constant_pool->len);
  const cf_constant_t constant = constant_pool->values[name_i - 1];
  pg_assert(constant.kind == CIK_UTF8);
  const string_t attribute_name = constant.v.s;

  if (string_eq_c(attribute_name, "SourceFile")) {
    cf_buf_read_sourcefile_attribute(buf, buf_len, current, constant_pool,
                                     size);
  } else if (string_eq_c(attribute_name, "Code")) {
    cf_buf_read_code_attribute(buf, buf_len, current, constant_pool, size);
  } else if (string_eq_c(attribute_name, "StackMapTable")) {
    cf_buf_read_stack_map_table_attribute(buf, buf_len, current, constant_pool,
                                          size);
  } else if (string_eq_c(attribute_name, "Exceptions")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "InnerClasses")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "EnclosingMethod")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "Synthetic")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "Signature")) {
    cf_buf_read_signature_attribute(buf, buf_len, current, constant_pool, size);
  } else if (string_eq_c(attribute_name, "SourceDebugExtension")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "LineNumberTable")) {
    cf_buf_read_line_number_table_attribute(buf, buf_len, current,
                                            constant_pool, size);
  } else if (string_eq_c(attribute_name, "LocalVariableTable")) {
    cf_buf_read_local_variable_table_attribute(buf, buf_len, current,
                                               constant_pool, size);
  } else if (string_eq_c(attribute_name, "LocalVariableTypeTable")) {
    cf_buf_read_local_variable_type_table_attribute(buf, buf_len, current,
                                                    constant_pool, size);
  } else if (string_eq_c(attribute_name, "Deprecated")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "RuntimeVisibleAnnotations")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "RuntimeInvisibleAnnotations")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name,
                         "RuntimeVisibleParameterAnnotations")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name,
                         "RuntimeInvisibleParameterAnnotations")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "RuntimeInvisibleAnnotations")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "AnnotationsDefault")) {
    pg_assert(0 && "unreachable");
  } else if (string_eq_c(attribute_name, "BootstrapMethods")) {
    pg_assert(0 && "unreachable");
  } else {
    pg_assert(0 && "unreachable");
  }
}

void cf_buf_read_attributes(u8 *buf, u64 buf_len, u8 **current,
                            cf_constant_array_t *constant_pool) {
  pg_assert(buf != NULL);
  pg_assert(buf_len > 0);
  pg_assert(current != NULL);
  pg_assert(constant_pool != NULL);

  const u16 attribute_count = buf_read_be_u16(buf, buf_len, current);

  for (u64 i = 0; i < attribute_count; i++) {
    LOG("[%lu/%hu] attribute", i, attribute_count);
    cf_buf_read_attribute(buf, buf_len, current, constant_pool);
  }
}

void cf_read_constant(u8 *buf, u64 buf_len, u8 **current,
                      cf_constant_array_t *constant_pool, u16 i,
                      u16 constant_pool_len) {
  u8 kind = buf_read_u8(buf, buf_len, current);

  if (!(kind == CIK_UTF8 || kind == CIK_INT || kind == CIK_FLOAT ||
        kind == CIK_LONG || kind == CIK_DOUBLE || kind == CIK_CLASS_INFO ||
        kind == CIK_STRING || kind == CIK_FIELD_REF || kind == CIK_METHOD_REF ||
        kind == CIK_INTERFACE_METHOD_REF || kind == CIK_NAME_AND_TYPE ||
        kind == CIK_INVOKE_DYNAMIC)) {
    fprintf(stderr, "Unknown constant kind found: offset=%lu kind=%u\n",
            *current - buf - 1, kind);
    pg_assert(0);
  }

  switch (kind) {
  case CIK_UTF8: {
    u16 len = buf_read_be_u16(buf, buf_len, current);
    pg_assert(len > 0);

    u8 *const s = *current;
    buf_read_n_u8(buf, buf_len, NULL, len, current);

    LOG("[%hu/%hu] CIK_UTF8 len=%u s=%.*s", i, constant_pool_len, len, len, s);

    cf_constant_t constant = {.kind = CIK_UTF8,
                              .v = {.s = {.len = len, .value = s}}};
    cf_constant_array_push(constant_pool, &constant);

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
  case CIK_CLASS_INFO: {
    u16 class_name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_name_i > 0);
    pg_assert(class_name_i <= constant_pool_len);

    LOG("[%hu/%hu] CIK_CLASS_INFO class_name_i=%u", i, constant_pool_len,
        class_name_i);

    cf_constant_t constant = {0}; // TODO
    cf_constant_array_push(constant_pool, &constant);
    break;
  }
  case CIK_STRING: {
    u16 utf8_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(utf8_i > 0);
    pg_assert(utf8_i <= constant_pool_len);
    LOG("[%hu/%hu] CIK_STRING utf8_i=%u", i, constant_pool_len, utf8_i);

    cf_constant_t constant = {0}; // TODO
    cf_constant_array_push(constant_pool, &constant);
    break;
  }
  case CIK_FIELD_REF: {
    u16 name_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_len);

    u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_len);

    LOG("[%hu/%hu] CIK_FIELD_REF name_i=%u descriptor_i=%u", i,
        constant_pool_len, name_i, descriptor_i);

    cf_constant_t constant = {0}; // TODO
    cf_constant_array_push(constant_pool, &constant);
    break;
  }
  case CIK_METHOD_REF: {
    u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_len);

    u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_len);

    LOG("[%hu/%hu] CIK_METHOD_REF class_i=%u name_and_type_i=%u", i,
        constant_pool_len, class_i, name_and_type_i);

    cf_constant_t constant = {0}; // TODO
    cf_constant_array_push(constant_pool, &constant);
    break;
  }
  case CIK_INTERFACE_METHOD_REF: {
    u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_len);

    u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_len);

    LOG("[%hu/%hu] CIK_INSTANCE_REF class_i=%u name_and_type_i=%u", i,
        constant_pool_len, class_i, name_and_type_i);

    cf_constant_t constant = {0}; // TODO
    cf_constant_array_push(constant_pool, &constant);
    break;
  }
  case CIK_NAME_AND_TYPE: {
    u16 class_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_len);

    u16 name_and_type_i = buf_read_be_u16(buf, buf_len, current);
    pg_assert(name_and_type_i > 0);
    pg_assert(name_and_type_i <= constant_pool_len);

    LOG("[%hu/%hu] CIK_NAME_AND_TYPE class_i=%u name_and_type_i=%u", i,
        constant_pool_len, class_i, name_and_type_i);

    cf_constant_t constant = {0}; // TODO
    cf_constant_array_push(constant_pool, &constant);
    break;
  }
  case CIK_INVOKE_DYNAMIC:
    pg_assert(0 && "unimplemented");
    break;
  default:
    pg_assert(0 && "unreachable");
  }
}

void cf_read_constants(u8 *buf, u64 buf_len, u8 **current,
                       cf_constant_array_t *constant_pool,
                       u16 constant_pool_len) {
  for (u64 i = 1; i <= constant_pool_len; i++) {
    cf_read_constant(buf, buf_len, current, constant_pool, i,
                     constant_pool_len);
  }
}

void cf_read_method(u8 *buf, u64 buf_len, u8 **current,
                    cf_constant_array_t *constant_pool, u16 i,
                    u16 methods_count) {
  const u16 access_flags = buf_read_be_u16(buf, buf_len, current);
  const u16 method_name_i = buf_read_be_u16(buf, buf_len, current);
  pg_assert(method_name_i > 0);
  pg_assert(method_name_i <= constant_pool->len);

  const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
  pg_assert(descriptor_i > 0);
  pg_assert(descriptor_i <= constant_pool->len);
  LOG("[%hu/%u] method access_flags=%x method_name_i=%hu "
      "descriptor_i=%hu",
      i, methods_count, access_flags, method_name_i, descriptor_i);
  cf_buf_read_attributes(buf, buf_len, current, constant_pool);
}

void cf_read_methods(u8 *buf, u64 buf_len, u8 **current,
                     cf_constant_array_t *constant_pool) {

  const u16 methods_count = buf_read_be_u16(buf, buf_len, current);
  LOG("methods count=%x", methods_count);
  pg_assert(methods_count > 0);

  for (u64 i = 0; i < methods_count; i++) {
    cf_read_method(buf, buf_len, current, constant_pool, i, methods_count);
  }
}

void cf_read_interfaces(u8 *buf, u64 buf_len, u8 **current,
                        cf_constant_array_t *constant_pool) {

  const u16 interfaces_count = buf_read_be_u16(buf, buf_len, current);
  LOG("interfaces count=%x", interfaces_count);
  for (u16 i = 0; i < interfaces_count; i++) {
    const u16 interface_i = buf_read_be_u16(buf, buf_len, current);
    LOG("[%hu/%hu] Interface #%hu", i, interfaces_count, interface_i);
    pg_assert(interface_i > 0);
    pg_assert(interface_i <= constant_pool->len);
  }
}

void cf_read_field(u8 *buf, u64 buf_len, u8 **current,
                   cf_constant_array_t *constant_pool) {
  const u16 access_flags = buf_read_be_u16(buf, buf_len, current);
  const u16 name_i = buf_read_be_u16(buf, buf_len, current);
  pg_assert(name_i > 0);
  pg_assert(name_i <= constant_pool->len);

  const u16 descriptor_i = buf_read_be_u16(buf, buf_len, current);
  pg_assert(descriptor_i > 0);
  pg_assert(descriptor_i <= constant_pool->len);

  cf_buf_read_attributes(buf, buf_len, current, constant_pool);

  LOG("Attribute access_flags=%hu name_i=%hu descriptor_i=%hu", access_flags,
      name_i, descriptor_i);
}

void cf_read_fields(u8 *buf, u64 buf_len, u8 **current,
                    cf_constant_array_t *constant_pool) {

  const u16 fields_count = buf_read_be_u16(buf, buf_len, current);
  LOG("fields count=%x", fields_count);
  for (u16 i = 0; i < fields_count; i++) {
    LOG("[%hu/%hu] Field", i, fields_count);
    cf_read_field(buf, buf_len, current, constant_pool);
  }
}

void cf_read_class_file(u8 *buf, u64 buf_len, u8 **current,

                        cf_constant_array_t *constant_pool) {

  pg_assert(buf_len > 0);

  pg_assert(buf_read_u8(buf, buf_len, current) == 0xca);
  pg_assert(buf_read_u8(buf, buf_len, current) == 0xfe);
  pg_assert(buf_read_u8(buf, buf_len, current) == 0xba);
  pg_assert(buf_read_u8(buf, buf_len, current) == 0xbe);

  const u16 minor_version = buf_read_be_u16(buf, buf_len, current);
  const u16 major_version = buf_read_be_u16(buf, buf_len, current);
  LOG("Version %hu.%hu", major_version, minor_version);

  const u16 constant_pool_size = buf_read_be_u16(buf, buf_len, current) - 1;
  pg_assert(constant_pool_size > 0);

  cf_read_constants(buf, buf_len, current, constant_pool, constant_pool_size);

  const u16 access_flags = buf_read_be_u16(buf, buf_len, current);
  LOG("access flags=%x", access_flags);

  const u16 this_class_i = buf_read_be_u16(buf, buf_len, current);
  LOG("this class=%x", this_class_i);
  pg_assert(this_class_i > 0);
  pg_assert(this_class_i <= constant_pool_size);

  const u16 super_class_i = buf_read_be_u16(buf, buf_len, current);
  LOG("super class=%x", super_class_i);
  pg_assert(super_class_i > 0);
  pg_assert(super_class_i <= constant_pool_size);

  cf_read_interfaces(buf, buf_len, current, constant_pool);

  cf_read_fields(buf, buf_len, current, constant_pool);

  cf_read_methods(buf, buf_len, current, constant_pool);

  cf_buf_read_attributes(buf, buf_len, current, constant_pool);

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
    pg_assert(0 && "unreachable");
  }
}

void cf_write_constant_pool(const cf_class_file_t *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  const u16 len = class_file->constant_pool.len + 1;
  file_write_be_16(file, len);

  for (u64 i = 0; i < class_file->constant_pool.len; i++) {
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

    pg_assert(code->exception_table_count == 0 && "unimplemented");

    const u16 exception_table_item_sizeof = 4 * sizeof(u16);
    u32 size = sizeof(code->max_stack) + sizeof(code->max_locals) +
               sizeof(u32) + code->code.len +
               sizeof(code->exception_table_count) +
               +code->exception_table_count * exception_table_item_sizeof +
               sizeof(u16) // attributes length
        ;

    for (uint64_t i = 0; i < code->attributes.len; i++) {
      const cf_attribute_t *const attribute = &code->attributes.values[i];
      size += cf_compute_attribute_size(attribute);
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

    file_write_be_16(file, code->exception_table_count);

    pg_assert(code->exception_table == NULL && "unimplemented");

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
  fwrite(&class_file->magic, sizeof(class_file->magic), 1, file);

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
  class_file->attributes = cf_attribute_array_make(1024, arena);

  class_file->methods = cf_method_array_make(1024, arena);

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

  char *class_file_name = arena_alloc(arena, class_file_name_len);
  memcpy(class_file_name, source_file_name, before_dot_incl_len);
  memcpy(class_file_name + before_dot_incl_len, ".class", extension_len);

  class_file_name[class_file_name_len - 1] = 0;

  return class_file_name;
}
