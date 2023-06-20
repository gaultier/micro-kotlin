#include <arpa/inet.h>
#include <assert.h>
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
} class_file_op_kind_t;

typedef struct {
  u8 *base;
  u64 current_offset;
  u64 capacity;
} arena_t;

static void arena_init(arena_t *arena, u64 capacity) {
  assert(arena != NULL);

  arena->base = mmap(NULL, capacity, PROT_READ | PROT_WRITE,
                     MAP_ANON | MAP_PRIVATE, -1, 0);
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

typedef enum {
  CAF_ACC_PUBLIC = 0x0001,
  CAF_ACC_STATIC = 0x0008,
  CAF_ACC_SUPER = 0x0020,
} class_file_access_flags_t;

typedef struct {
  u16 len;
  u8 *s;
} string_t;

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
    struct class_file_constant_method_ref_t {
      u16 class;
      u16 name_and_type;
    } method_ref;   // CIK_METHOD_REF
    u16 class_name; // CIK_CLASS_INFO
    struct class_file_constant_name_and_type_t {
      u16 name;
      u16 type_descriptor;
    } name_and_type; // CIK_NAME_AND_TYPE
    struct class_file_constant_field_ref_t {
      u16 name;
      u16 type_descriptor;
    } field_ref; // CIK_FIELD_REF
  } v;
} class_file_constant_t;

typedef struct class_file_constant_method_ref_t
    class_file_constant_method_ref_t;

typedef struct class_file_constant_name_and_type_t
    class_file_constant_name_and_type_t;

typedef struct class_file_constant_field_ref_t class_file_constant_field_ref_t;

typedef struct {
} class_file_field_t;

typedef struct class_file_attribute_t class_file_attribute_t;
typedef struct {
  u64 len;
  u64 cap;
  class_file_attribute_t *values;
  arena_t *arena;
} attribute_array_t;

typedef struct {
  u16 start_pc;
  u16 line_number;
} class_file_line_number_table_t;

struct class_file_attribute_t {
  enum class_file_attribute_kind_t {
    CAK_SOURCE_FILE,
    CAK_CODE,
    CAK_LINE_NUMBER_TABLE,
    CAK_STACK_MAP_TABLE,
  } kind;

  u16 name;

  union {
    struct class_file_attribute_code_t {
      u16 max_stack;
      u16 max_locals;
      u32 code_count;
      u8 *code;
      u16 exception_table_count;
      void *exception_table; // TODO
      u16 attributes_count;
      attribute_array_t attributes;
    } code; // CAK_CODE

    struct class_file_attribute_source_file_t {
      u16 source_file;
    } source_file; // CAK_SOURCE_FILE

    struct class_file_attribute_line_number_table_t {
      u16 line_number_table_count;
      class_file_line_number_table_t *line_number_tables;
    } line_number_table;
  } v;
};

typedef struct class_file_attribute_line_number_table_t
    class_file_attribute_line_number_table_t;

typedef struct class_file_attribute_code_t class_file_attribute_code_t;

typedef struct class_file_attribute_source_file_t
    class_file_attribute_source_file_t;

attribute_array_t attribute_array_make(u64 cap, arena_t *arena) {
  assert(arena != NULL);

  return (attribute_array_t){
      .cap = cap,
      .len = 0,
      .arena = arena,
      .values = arena_alloc(arena, cap * sizeof(class_file_attribute_t)),
  };
}

void attribute_array_push(attribute_array_t *array,
                          const class_file_attribute_t *x) {
  assert(array != NULL);
  assert(x != NULL);
  assert(array->len < UINT16_MAX);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    class_file_attribute_t *const new_array =
        arena_alloc(array->arena, new_cap);
    memcpy(new_array, array->values,
           array->len * sizeof(class_file_attribute_t));
    array->values = new_array;
    array->cap = new_cap;
  }

  array->values[array->len] = *x;
  array->len += 1;
}

typedef struct {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  u16 attributes_count;
  attribute_array_t attributes;
} class_file_method_t;

const u32 CLASS_FILE_MAGIC_NUMBER = 0xbebafeca;
const u16 CLASS_FILE_MAJOR_VERSION_6 = 50;
const u16 CLASS_FILE_MINOR_VERSION = 0;

typedef struct {
  u32 magic;
  u16 minor_version;
  u16 major_version;
  u16 constant_pool_count;
  class_file_constant_t *constant_pool;
  u16 access_flags;
  u16 this_class;
  u16 super_class;
  u16 interfaces_count;
  u16 fields_count;
  class_file_field_t *fields;
  u16 method_count;
  class_file_method_t *methods;
  u16 attribute_count;
  attribute_array_t attributes;
} class_file_t;

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

void class_file_write_constant(const class_file_t *class_file, FILE *file,
                               const class_file_constant_t *constant) {
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

    const class_file_constant_field_ref_t *const field_ref =
        &constant->v.field_ref;

    file_write_be_16(file, field_ref->name);
    file_write_be_16(file, field_ref->type_descriptor);
    break;
  }
  case CIK_METHOD_REF: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const class_file_constant_method_ref_t *const method_ref =
        &constant->v.method_ref;

    file_write_be_16(file, method_ref->class);
    file_write_be_16(file, method_ref->name_and_type);
    break;
  }
  case CIK_INSTANCE_METHOD_REF:
    assert(0 && "unimplemented");
    break;
  case CIK_NAME_AND_TYPE: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const class_file_constant_name_and_type_t *const name_and_type =
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

void class_file_write_constant_pool(const class_file_t *class_file,
                                    FILE *file) {
  assert(class_file != NULL);
  assert(file != NULL);

  const u16 len = class_file->constant_pool_count + 1;
  file_write_be_16(file, len);

  for (u64 i = 0; i < class_file->constant_pool_count; i++) {
    const class_file_constant_t *const constant = &class_file->constant_pool[i];
    class_file_write_constant(class_file, file, constant);
  }
}
void class_file_write_interfaces(const class_file_t *class_file, FILE *file) {
  assert(class_file != NULL);
  assert(file != NULL);

  file_write_be_16(file, class_file->interfaces_count);

  assert(class_file->interfaces_count == 0 && "unimplemented");
}

void class_file_write_fields(const class_file_t *class_file, FILE *file) {
  assert(class_file != NULL);
  assert(file != NULL);

  file_write_be_16(file, class_file->fields_count);

  assert(class_file->fields_count == 0 && "unimplemented");
}

u32 class_file_compute_attribute_size(const class_file_attribute_t *attribute) {
  assert(attribute != NULL);

  switch (attribute->kind) {
  case CAK_SOURCE_FILE:
    return 2;
  case CAK_CODE: {
    const class_file_attribute_code_t *const code = &attribute->v.code;

    assert(code->exception_table_count == 0 && "unimplemented");

    u32 size = sizeof(code->max_stack) + sizeof(code->max_locals) +
               sizeof(code->code_count) + code->code_count +
               sizeof(code->exception_table_count) +
               sizeof(code->attributes_count);

    for (uint64_t i = 0; i < code->attributes_count; i++) {
      const class_file_attribute_t *const attribute =
          &code->attributes.values[i];
      size += class_file_compute_attribute_size(attribute);
    }
    return size;
  }
  case CAK_LINE_NUMBER_TABLE: {
    const class_file_attribute_line_number_table_t
        *const attribute_line_number_table = &attribute->v.line_number_table;
    return sizeof(attribute_line_number_table->line_number_table_count) +
           attribute_line_number_table->line_number_table_count *
               sizeof(class_file_line_number_table_t);
  }
  case CAK_STACK_MAP_TABLE:
    assert(0 && "unimplemented");
  }
  assert(0 && "unreachable");
}

void class_file_write_attributes(FILE *file,
                                 const attribute_array_t *attributes);
void class_file_write_attribute(FILE *file,
                                const class_file_attribute_t *attribute) {
  assert(file != NULL);
  assert(attribute != NULL);

  file_write_be_16(file, attribute->name);

  switch (attribute->kind) {
  case CAK_SOURCE_FILE: {
    const u32 size = class_file_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const class_file_attribute_source_file_t *const source_file =
        &attribute->v.source_file;
    file_write_be_16(file, source_file->source_file);

    break;
  }
  case CAK_CODE: {
    const u32 size = class_file_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const class_file_attribute_code_t *const code = &attribute->v.code;

    file_write_be_16(file, code->max_stack);

    file_write_be_16(file, code->max_locals);

    file_write_be_32(file, code->code_count);
    fwrite(code->code, code->code_count, sizeof(u8), file);

    file_write_be_16(file, code->exception_table_count);

    assert(code->exception_table == NULL && "unimplemented");

    class_file_write_attributes(file, &code->attributes);

    break;
  }
  case CAK_LINE_NUMBER_TABLE: {
    const u32 size = class_file_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const class_file_attribute_line_number_table_t
        *const attribute_line_number_table = &attribute->v.line_number_table;

    for (u64 i = 0; i < attribute_line_number_table->line_number_table_count;
         i++) {
      class_file_line_number_table_t line_number_table =
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

void class_file_write_attributes(FILE *file,
                                 const attribute_array_t *attributes) {
  file_write_be_16(file, attributes->len);

  for (uint64_t i = 0; i < attributes->len; i++) {
    const class_file_attribute_t *const attribute = &attributes->values[i];
    class_file_write_attribute(file, attribute);
  }
}

void class_file_write_method(FILE *file, const class_file_method_t *method) {
  file_write_be_16(file, method->access_flags);
  file_write_be_16(file, method->name);
  file_write_be_16(file, method->descriptor);

  class_file_write_attributes(file, &method->attributes);
}

void class_file_write_methods(const class_file_t *class_file, FILE *file) {
  assert(class_file != NULL);
  assert(file != NULL);

  file_write_be_16(file, class_file->method_count);

  for (uint64_t i = 0; i < class_file->method_count; i++) {
    const class_file_method_t *const method = &class_file->methods[i];
    class_file_write_method( file, method);
  }
}

void class_file_write(const class_file_t *class_file, FILE *file) {
  fwrite(&class_file->magic, sizeof(class_file->magic), 1, file);

  file_write_be_16(file, class_file->minor_version);
  file_write_be_16(file, class_file->major_version);
  class_file_write_constant_pool(class_file, file);
  file_write_be_16(file, class_file->access_flags);
  file_write_be_16(file, class_file->this_class);
  file_write_be_16(file, class_file->super_class);

  class_file_write_interfaces(class_file, file);
  class_file_write_fields(class_file, file);
  class_file_write_methods(class_file, file);
  class_file_write_attributes(file, &class_file->attributes);
  fflush(file);
}

u16 class_file_add_constant(class_file_t *class_file,
                            const class_file_constant_t *constant) {
  assert(class_file->constant_pool_count < UINT16_MAX);

  class_file->constant_pool[class_file->constant_pool_count] = *constant;

  // Constant pool is 1-indexed, so we return index + 1.
  return ++class_file->constant_pool_count;
}

void class_file_init(class_file_t *class_file, arena_t *arena) {
  assert(class_file != NULL);
  assert(arena != NULL);

  class_file->constant_pool =
      arena_alloc(arena, UINT16_MAX * sizeof(class_file_constant_t));
  class_file->attributes = attribute_array_make(1024, arena);

  class_file->methods =
      arena_alloc(arena, UINT16_MAX * sizeof(class_file_method_t));

  class_file->attributes = attribute_array_make(1024, arena);
}

u16 class_file_add_method(class_file_t *class_file,
                          const class_file_method_t *method) {
  assert(class_file != NULL);
  assert(method != NULL);

  assert(class_file->method_count < UINT16_MAX);
  class_file->methods[class_file->method_count] = *method;

  return class_file->method_count++;
}

u32 class_file_add_code_u8(u8 *code, u32 *code_count, u8 op) {
  assert(code != NULL);
  assert(code_count != NULL);
  assert(*code_count < UINT16_MAX); // TODO: UINT32_MAX vs ENOMEM

  code[*code_count] = op;
  *code_count += 1;
  return *code_count - 1;
}

u32 class_file_add_code_u16(u8 *code, u32 *code_count, u16 x) {
  assert(code != NULL);
  assert(code_count != NULL);
  assert(*code_count < UINT16_MAX - 1); // TODO: UINT32_MAX vs ENOMEM

  code[*code_count] = (x & 0xff00);
  *code_count += 1;
  code[*code_count] = (x & 0x00ff);
  *code_count += 1;
  return *code_count - 1;
}

void class_file_attribute_code_init(class_file_attribute_code_t *code,
                                    arena_t *arena) {
  assert(code != NULL);
  assert(arena != NULL);

  code->code = arena_alloc(arena, UINT16_MAX * sizeof(u8));
  code->attributes = attribute_array_make(1024, arena);
}

void class_file_method_init(class_file_method_t *method, arena_t *arena) {
  assert(method != NULL);
  assert(arena != NULL);

  method->attributes = attribute_array_make(1024, arena);
  method->attributes = attribute_array_make(1024, arena);
}

u16 class_file_add_constant_cstring(class_file_t *class_file, char *s) {
  assert(class_file != NULL);
  assert(s != NULL);

  const class_file_constant_t constant = {.kind = CIK_UTF8,
                                          .v = {.s = {
                                                    .len = __builtin_strlen(s),
                                                    .s = (u8 *)s,
                                                }}};
  return class_file_add_constant(class_file, &constant);
}

u16 class_file_add_constant_jstring(class_file_t *class_file,
                                    u16 constant_utf8_i) {
  assert(class_file != NULL);
  assert(constant_utf8_i > 0);

  const class_file_constant_t constant = {
      .kind = CIK_STRING, .v = {.string_utf8_i = constant_utf8_i}};

  return class_file_add_constant(class_file, &constant);
}

int main() {
  arena_t arena = {0};
  arena_init(&arena, 1 << 26);

  class_file_t class_file = {
      .magic = CLASS_FILE_MAGIC_NUMBER,
      .minor_version = CLASS_FILE_MINOR_VERSION,
      .major_version = CLASS_FILE_MAJOR_VERSION_6,
      .access_flags = CAF_ACC_SUPER | CAF_ACC_PUBLIC,
  };

  class_file_init(&class_file, &arena);

  const u16 constant_java_lang_object_string_i =
      class_file_add_constant_cstring(&class_file, "java/lang/Object");

  const u16 constant_void_method_descriptor_string_i =
      class_file_add_constant_cstring(&class_file, "()V");

  const u16 constant_class_object_name_and_type_name_i =
      class_file_add_constant_cstring(&class_file, "<init>");

  const class_file_constant_t constant_class_object = {
      .kind = CIK_CLASS_INFO,
      .v = {.class_name = constant_java_lang_object_string_i}};
  const u16 constant_class_object_i =
      class_file_add_constant(&class_file, &constant_class_object);
  class_file.super_class = constant_class_object_i;

  const class_file_constant_t constant_class_object_name_and_type = {
      .kind = CIK_NAME_AND_TYPE,
      .v = {.name_and_type = {
                .name = constant_class_object_name_and_type_name_i,
                .type_descriptor = constant_void_method_descriptor_string_i}}};
  const u16 constant_class_object_name_and_type_i = class_file_add_constant(
      &class_file, &constant_class_object_name_and_type);

  const class_file_constant_t constant_object_method_ref_constructor = {
      .kind = CIK_METHOD_REF,
      .v = {.method_ref = {.class = constant_class_object_i,
                           .name_and_type =
                               constant_class_object_name_and_type_i}}};
  const u16 constant_object_method_ref_constructor_i = class_file_add_constant(
      &class_file, &constant_object_method_ref_constructor);

  const u16 constant_this_class_name_i =
      class_file_add_constant_cstring(&class_file, "PgMain");
  const class_file_constant_t constant_this_class = {
      .kind = CIK_CLASS_INFO, .v = {.class_name = constant_this_class_name_i}};
  const u16 constant_this_class_i =
      class_file_add_constant(&class_file, &constant_this_class);
  class_file.this_class = constant_this_class_i;

  const u16 constant_string_code_i =
      class_file_add_constant_cstring(&class_file, "Code");

  const u16 constant_string_line_number_table_i =
      class_file_add_constant_cstring(&class_file, "LineNumberTable");

  const u16 constant_string_main_i =
      class_file_add_constant_cstring(&class_file, "main");

  const u16 constant_string_main_type_descriptor_i =
      class_file_add_constant_cstring(&class_file, "([Ljava/lang/String;)V");

  const u16 constant_string_source_file_i =
      class_file_add_constant_cstring(&class_file, "SourceFile");

  const u16 constant_string_file_i =
      class_file_add_constant_cstring(&class_file, "PgMain.java");

  const u16 constant_string_java_lang_system_class_i =
      class_file_add_constant_cstring(&class_file, "java/lang/System");
  const class_file_constant_t constant_java_lang_system_class_info = {
      .kind = CIK_CLASS_INFO,
      .v = {.class_name = constant_string_java_lang_system_class_i}};
  const u16 constant_java_lang_system_class_info_i = class_file_add_constant(
      &class_file, &constant_java_lang_system_class_info);

  const u16 constant_string_out_i =
      class_file_add_constant_cstring(&class_file, "out");

  const u16 constant_string_java_io_printstream_i =
      class_file_add_constant_cstring(&class_file, "java/io/PrintStream");

  const class_file_constant_t constant_string_java_io_printstream_class = {
      .kind = CIK_CLASS_INFO,
      .v = {.class_name = constant_string_java_io_printstream_i}};
  const u16 constant_string_java_io_printstream_class_i =
      class_file_add_constant(&class_file,
                              &constant_string_java_io_printstream_class);

  const u16 constant_string_java_io_printstream_descriptor_i =
      class_file_add_constant_cstring(&class_file, "Ljava/io/PrintStream;");

  const class_file_constant_t constant_out_name_and_type = {
      .kind = CIK_NAME_AND_TYPE,
      .v = {.name_and_type = {
                .name = constant_string_out_i,
                .type_descriptor =
                    constant_string_java_io_printstream_descriptor_i}}};
  const u16 constant_out_name_and_type_i =
      class_file_add_constant(&class_file, &constant_out_name_and_type);

  const class_file_constant_t constant_out_fieldref = {
      .kind = CIK_FIELD_REF,
      .v = {.field_ref = {.name = constant_java_lang_system_class_info_i,
                          .type_descriptor = constant_out_name_and_type_i}}};
  const u16 constant_out_fieldref_i =
      class_file_add_constant(&class_file, &constant_out_fieldref);

  const class_file_attribute_t source_file_attribute = {
      .kind = CAK_SOURCE_FILE,
      .name = constant_string_source_file_i,
      .v = {.source_file = {.source_file = constant_string_file_i}}};
  attribute_array_push(&class_file.attributes, &source_file_attribute);

  const u16 constant_string_hello_i =
      class_file_add_constant_cstring(&class_file, "Hello, world!");
  const u16 constant_jstring_hello_i =
      class_file_add_constant_jstring(&class_file, constant_string_hello_i);

  const u16 constant_string_println_i =
      class_file_add_constant_cstring(&class_file, "println");
  const u16 constant_println_method_descriptor_string_i =
      class_file_add_constant_cstring(&class_file, "(Ljava/lang/String;)V");
  const class_file_constant_t constant_println_name_and_type = {
      .kind = CIK_NAME_AND_TYPE,
      .v = {
          .name_and_type = {.name = constant_string_println_i,
                            .type_descriptor =
                                constant_println_method_descriptor_string_i}}};
  const u16 constant_println_name_and_type_i =
      class_file_add_constant(&class_file, &constant_println_name_and_type);
  const class_file_constant_t constant_println_method_ref = {
      .kind = CIK_METHOD_REF,
      .v = {.method_ref = {.class = constant_string_java_io_printstream_class_i,
                           .name_and_type = constant_println_name_and_type_i}}};
  const u16 constant_println_method_ref_i =
      class_file_add_constant(&class_file, &constant_println_method_ref);

  // This's class Constructor
  {
    class_file_attribute_code_t constructor_code = {.max_stack = 1,
                                                    .max_locals = 1};
    class_file_attribute_code_init(&constructor_code, &arena);
    class_file_add_code_u8(constructor_code.code, &constructor_code.code_count,
                           CFO_ALOAD_0);
    class_file_add_code_u8(constructor_code.code, &constructor_code.code_count,
                           CFO_INVOKE_SPECIAL);
    class_file_add_code_u16(constructor_code.code, &constructor_code.code_count,
                            constant_object_method_ref_constructor_i);
    class_file_add_code_u8(constructor_code.code, &constructor_code.code_count,
                           CFO_RETURN);

    class_file_method_t constructor = {
        .access_flags = CAF_ACC_PUBLIC,
        .name = constant_class_object_name_and_type_name_i,
        .descriptor = constant_void_method_descriptor_string_i,
    };
    class_file_method_init(&constructor, &arena);
    class_file_attribute_t constructor_attribute_code = {
        .kind = CAK_CODE,
        .name = constant_string_code_i,
        .v = {.code = constructor_code}};
    attribute_array_push(&constructor.attributes, &constructor_attribute_code);

    class_file_add_method(&class_file, &constructor);
  }
  // This's class main
  {
    class_file_attribute_code_t main_code = {.max_stack = 2, .max_locals = 1};
    class_file_attribute_code_init(&main_code, &arena);

    class_file_add_code_u8(main_code.code, &main_code.code_count,
                           CFO_GET_STATIC);
    class_file_add_code_u16(main_code.code, &main_code.code_count,
                            constant_out_fieldref_i);

    class_file_add_code_u8(main_code.code, &main_code.code_count, CFO_LDC);
    class_file_add_code_u8(main_code.code, &main_code.code_count,
                           constant_jstring_hello_i);

    class_file_add_code_u8(main_code.code, &main_code.code_count,
                           CFO_INVOKE_VIRTUAL);
    class_file_add_code_u16(main_code.code, &main_code.code_count,
                            constant_println_method_ref_i);

    class_file_add_code_u8(main_code.code, &main_code.code_count, CFO_RETURN);

    class_file_method_t main = {
        .name = constant_string_main_i,
        .access_flags = CAF_ACC_PUBLIC | CAF_ACC_STATIC,
        .descriptor = constant_string_main_type_descriptor_i,
    };
    class_file_method_init(&main, &arena);
    class_file_attribute_t main_attribute_code = {.kind = CAK_CODE,
                                                  .name =
                                                      constant_string_code_i,
                                                  .v = {.code = main_code}};
    attribute_array_push(&main.attributes, &main_attribute_code);

    class_file_add_method(&class_file, &main);
  }

  FILE *file = fopen("PgMain.class", "w");
  assert(file != NULL);
  class_file_write(&class_file, file);
}
