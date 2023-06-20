#pragma once

#include <arpa/inet.h>
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
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

typedef enum {
  CFO_ALOAD_0 = 0x2a,
  CFO_INVOKE_SPECIAL = 0xb7,
  CFO_RETURN = 0xb1,
  CFO_GET_STATIC = 0xb2,
  CFO_LDC = 0x12,
  CFO_INVOKE_VIRTUAL = 0xb6,
} cf_op_kind_t;

typedef struct {
  u8 *base;
  u64 current_offset;
  u64 capacity;
} arena_t;

static void arena_init(arena_t *arena, u64 capacity) {
  assert(arena != NULL);

  arena->base = mmap(NULL, capacity, PROT_READ | PROT_WRITE,
                     MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  assert(arena->base != NULL);
  arena->capacity = capacity;
  arena->current_offset = 0;
}

static u64 align_forward_16(u64 n) {
  const u64 modulo = n & (16 - 1);
  if (modulo != 0)
    n += 16 - modulo;

  assert((n % 16) == 0);
  return n;
}

static void *arena_alloc(arena_t *arena, u64 len) {
  assert(arena != NULL);
  assert(arena->current_offset < arena->capacity);
  assert(arena->current_offset + len < arena->capacity);

  // TODO: align?
  arena->current_offset = align_forward_16(arena->current_offset + len);
  assert((arena->current_offset % 16) == 0);

  return arena->base + arena->current_offset - len;
}

typedef struct {
  u64 len;
  u64 cap;
  u8 *values;
  arena_t *arena;
} cf_code_array_t;

cf_code_array_t cf_code_array_make(u64 cap, arena_t *arena) {
  assert(arena != NULL);

  return (cf_code_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap * sizeof(u8)),
      .arena = arena,
  };
}

void cf_code_array_push_u8(cf_code_array_t *array, u8 x) {
  assert(array != NULL);
  assert(array->len < UINT32_MAX);
  assert(array->values != NULL);
  assert(array->cap != 0);

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
  u16 len;
  u8 *s;
} string_t;

bool string_eq(string_t a, string_t b) {
  return a.len == b.len && memcmp(a.s, b.s, a.len) == 0;
}

bool string_eq_c(string_t a, char *b) {
  const u64 b_len = strlen(b);
  return a.len == b_len && memcmp(a.s, b, a.len) == 0;
}

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
    CIK_INSTANCE_METHOD_REF = 11,
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
  assert(arena != NULL);

  return (cf_constant_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap * sizeof(cf_constant_t)),
      .arena = arena,
  };
}

u16 cf_constant_array_push(cf_constant_array_t *array, const cf_constant_t *x) {
  assert(array != NULL);
  assert(x != NULL);
  assert(array->len < UINT16_MAX);
  assert(array->values != NULL);
  assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    cf_constant_t *const new_array = arena_alloc(array->arena, new_cap);
    array->values =
        memcpy(new_array, array->values, array->len * sizeof(cf_constant_t));
    array->cap = new_cap;
  }

  array->values[array->len] = *x;
  const u16 index = array->len + 1;
  assert(index > 0);
  assert(index <= array->len + 1);
  array->len += 1;
  return index;
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
  assert(arena != NULL);

  return (cf_attribute_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap * sizeof(cf_attribute_t)),
      .arena = arena,
  };
}

void cf_attribute_array_push(cf_attribute_array_t *array,
                             const cf_attribute_t *x) {
  assert(array != NULL);
  assert(x != NULL);
  assert(array->len < UINT16_MAX);
  assert(array->values != NULL);
  assert(array->cap != 0);

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
  assert(arena != NULL);

  return (cf_method_array_t){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, cap * sizeof(cf_method_t)),
      .arena = arena,
  };
}

void cf_method_array_push(cf_method_array_t *array, const cf_method_t *x) {
  assert(array != NULL);
  assert(x != NULL);
  assert(array->len < UINT16_MAX);
  assert(array->values != NULL);
  assert(array->cap != 0);

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
} cf_t;

void file_write_be_16(FILE *file, u16 x) {
  assert(file != NULL);

  const u16 x_be = htons(x);
  fwrite(&x_be, sizeof(x_be), 1, file);
}

void file_write_be_32(FILE *file, u32 x) {
  assert(file != NULL);

  const u32 x_be = htonl(x);
  fwrite(&x_be, sizeof(x_be), 1, file);
}

#define LOG(fmt, ...) fprintf(stderr, fmt "\n", ##__VA_ARGS__)

void cf_write_constant(const cf_t *class_file, FILE *file,
                       const cf_constant_t *constant) {
  assert(class_file != NULL);
  assert(file != NULL);
  assert(constant != NULL);

  switch (constant->kind) {
  case CIK_UTF8: {
    fwrite(&constant->kind, sizeof(u8), 1, file);
    const string_t *const s = &constant->v.s;
    file_write_be_16(file, s->len);
    fwrite(s->s, sizeof(u8), s->len, file);
    break;
  }
  case CIK_INT:
    assert(0 && "unimplemented");
    break;
  case CIK_FLOAT:
    assert(0 && "unimplemented");
    break;
  case CIK_LONG:
    assert(0 && "unimplemented");
    break;
  case CIK_DOUBLE:
    assert(0 && "unimplemented");
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
  case CIK_INSTANCE_METHOD_REF:
    assert(0 && "unimplemented");
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
    assert(0 && "unimplemented");
    break;
  default:
    assert(0 && "unreachable");
  }
}

void cf_write_constant_pool(const cf_t *class_file, FILE *file) {
  assert(class_file != NULL);
  assert(file != NULL);

  const u16 len = class_file->constant_pool.len + 1;
  file_write_be_16(file, len);

  for (u64 i = 0; i < class_file->constant_pool.len; i++) {
    const cf_constant_t *const constant = &class_file->constant_pool.values[i];
    LOG("action=writing constant i=%lu/%lu", i, class_file->constant_pool.len);
    cf_write_constant(class_file, file, constant);
  }
}
void cf_write_interfaces(const cf_t *class_file, FILE *file) {
  assert(class_file != NULL);
  assert(file != NULL);

  file_write_be_16(file, class_file->interfaces_count);

  assert(class_file->interfaces_count == 0 && "unimplemented");
}

void cf_write_fields(const cf_t *class_file, FILE *file) {
  assert(class_file != NULL);
  assert(file != NULL);

  file_write_be_16(file, class_file->fields_count);

  assert(class_file->fields_count == 0 && "unimplemented");
}

u32 cf_compute_attribute_size(const cf_attribute_t *attribute) {
  assert(attribute != NULL);

  switch (attribute->kind) {
  case CAK_SOURCE_FILE:
    return 2;
  case CAK_CODE: {
    const cf_attribute_code_t *const code = &attribute->v.code;

    assert(code->exception_table_count == 0 && "unimplemented");

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
    assert(0 && "unimplemented");
  }
  assert(0 && "unreachable");
}

void cf_write_attributes(FILE *file, const cf_attribute_array_t *attributes);
void cf_write_attribute(FILE *file, const cf_attribute_t *attribute) {
  assert(file != NULL);
  assert(attribute != NULL);

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

    assert(code->exception_table == NULL && "unimplemented");

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
    assert(0 && "unimplemented");
    break;
  }
  default:
    assert(0 && "unreachable");
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

void cf_write_methods(const cf_t *class_file, FILE *file) {
  assert(class_file != NULL);
  assert(file != NULL);

  file_write_be_16(file, class_file->methods.len);

  for (uint64_t i = 0; i < class_file->methods.len; i++) {
    const cf_method_t *const method = &class_file->methods.values[i];
    LOG("action=writing methods i=%lu/%lu", i, class_file->methods.len);
    cf_write_method(file, method);
  }
}

void cf_write(const cf_t *class_file, FILE *file) {
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

void cf_init(cf_t *class_file, arena_t *arena) {
  assert(class_file != NULL);
  assert(arena != NULL);

  class_file->constant_pool = cf_constant_array_make(1024, arena);
  class_file->attributes = cf_attribute_array_make(1024, arena);

  class_file->methods = cf_method_array_make(1024, arena);

  class_file->attributes = cf_attribute_array_make(1024, arena);
}

void cf_attribute_code_init(cf_attribute_code_t *code, arena_t *arena) {
  assert(code != NULL);
  assert(arena != NULL);

  code->code = cf_code_array_make(32, arena);
  code->attributes = cf_attribute_array_make(1024, arena);
}

void cf_method_init(cf_method_t *method, arena_t *arena) {
  assert(method != NULL);
  assert(arena != NULL);

  method->attributes = cf_attribute_array_make(1024, arena);
}

u16 cf_add_constant_cstring(cf_constant_array_t *constant_pool, char *s) {
  assert(constant_pool != NULL);
  assert(s != NULL);

  const cf_constant_t constant = {.kind = CIK_UTF8,
                                  .v = {.s = {
                                            .len = strlen(s),
                                            .s = (u8 *)s,
                                        }}};
  return cf_constant_array_push(constant_pool, &constant);
}

u16 cf_add_constant_jstring(cf_constant_array_t *constant_pool,
                            u16 constant_utf8_i) {
  assert(constant_pool != NULL);
  assert(constant_utf8_i > 0);

  const cf_constant_t constant = {.kind = CIK_STRING,
                                  .v = {.string_utf8_i = constant_utf8_i}};

  return cf_constant_array_push(constant_pool, &constant);
}
