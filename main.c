#include <arpa/inet.h>
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>

#define u64 uint64_t
#define i64 int64_t
#define u32 uint32_t
#define i32 int32_t
#define u16 uint16_t
#define i16 int16_t
#define u8 uint8_t
#define i8 int8_t

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

static void arena_reset_at(arena_t *arena, u64 offset) {
  assert(arena != NULL);
  assert(arena->current_offset < arena->capacity);
  assert((arena->current_offset % 16) == 0);

  arena->current_offset = offset;
}

typedef enum {
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
    string_t s; // CIK_UTF8
    struct class_file_constant_method_ref_t {
      u16 class;
      u16 name_and_type;
    } method_ref;   // CIK_METHOD_REF
    u16 class_name; // CIK_CLASS_INFO
    struct class_file_constant_name_and_type_t {
      u16 name;
      u16 type_descriptor;
    } name_and_type; // CIK_NAME_AND_TYPE
  } v;
} class_file_constant_t;

typedef struct class_file_constant_method_ref_t
    class_file_constant_method_ref_t;

typedef struct class_file_constant_name_and_type_t
    class_file_constant_name_and_type_t;

typedef struct {
} class_file_field_t;

typedef struct class_file_attribute_t class_file_attribute_t;

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
      class_file_attribute_t *attributes;
    } code;

    struct class_file_attribute_source_file_t {
      u16 source_file;
    } source_file;
  } v;
};

typedef struct class_file_attribute_code_t class_file_attribute_code_t;

typedef struct class_file_attribute_source_file_t
    class_file_attribute_source_file_t;

typedef struct {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  u16 attributes_count;
  class_file_attribute_t *attributes;
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
  u16 methods_count;
  class_file_method_t *methods;
  u16 attribute_count;
  class_file_attribute_t *attributes;
} class_file_t;

void file_write_be_16(FILE *file, u16 x) {
  const u16 x_be = htons(x);
  fwrite(&x_be, sizeof(x_be), 1, file);
}

void file_write_be_32(FILE *file, u32 x) {
  const u32 x_be = htonl(x);
  fwrite(&x_be, sizeof(x_be), 1, file);
}

void class_file_write_constant(const class_file_t *class_file, FILE *file,
                               const class_file_constant_t *constant) {
  switch (constant->kind) {
  case CIK_UTF8: {
    fwrite(&constant->kind, sizeof(u8), 1, file);
    const string_t *const s = (string_t *)&constant->v;
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
    assert(0 && "unimplemented");
    break;
  case CIK_FIELD_REF:
    assert(0 && "unimplemented");
    break;
  case CIK_METHOD_REF: {
    fwrite(&constant->kind, sizeof(u8), 1, file);

    const class_file_constant_method_ref_t *const method_ref =
        (const class_file_constant_method_ref_t *)&constant->v.method_ref;

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
        (const class_file_constant_name_and_type_t *)&constant->v.name_and_type;

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
  const u16 len = class_file->constant_pool_count + 1;
  file_write_be_16(file, len);

  // Constant pool is 1-indexed, we skip the first (dummy) one.
  for (u64 i = 1; i < class_file->constant_pool_count; i++) {
    const class_file_constant_t *const constant = &class_file->constant_pool[i];
    class_file_write_constant(class_file, file, constant);
  }
}
void class_file_write_interfaces(const class_file_t *class_file, FILE *file) {
  file_write_be_16(file, class_file->interfaces_count);

  assert(class_file->interfaces_count == 0 && "unimplemented");
}

void class_file_write_fields(const class_file_t *class_file, FILE *file) {
  file_write_be_16(file, class_file->fields_count);

  assert(class_file->fields_count == 0 && "unimplemented");
}

u32 class_file_compute_attribute_size(const class_file_attribute_t *attribute) {
  switch (attribute->kind) {
  case CAK_SOURCE_FILE:
    return 2 + 4 + 2;
  case CAK_CODE: {
    const class_file_attribute_code_t *const code =
        (const class_file_attribute_code_t *)&attribute->v;

    assert(code->exception_table_count == 0 && "unimplemented");

    u32 size = 2 + 4 + sizeof(code->max_stack) + sizeof(code->max_locals) +
               sizeof(code->code_count) + code->code_count +
               sizeof(code->exception_table_count) +
               sizeof(code->attributes_count);

    for (uint64_t i = 0; i < code->attributes_count; i++) {
      size += class_file_compute_attribute_size(&code->attributes[i]);
    }
    return size;
  }
  case CAK_LINE_NUMBER_TABLE: {

    assert(0 && "unimplemented");
  }
  case CAK_STACK_MAP_TABLE:
    assert(0 && "unimplemented");
  }
  assert(0 && "unreachable");
}

void class_file_write_attributes(const class_file_t *class_file, FILE *file,
                                 u16 attribute_count,
                                 const class_file_attribute_t *attributes);
void class_file_write_attribute(const class_file_t *class_file, FILE *file,
                                const class_file_attribute_t *attribute) {
  file_write_be_16(file, attribute->name);

  switch (attribute->kind) {
  case CAK_SOURCE_FILE: {
    const u32 size = class_file_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const class_file_attribute_source_file_t *const source_file =
        (const class_file_attribute_source_file_t *)&attribute->v;
    file_write_be_16(file, source_file->source_file);

    break;
  }
  case CAK_CODE: {
    const u32 size = class_file_compute_attribute_size(attribute);
    file_write_be_32(file, size);

    const class_file_attribute_code_t *const code =
        (const class_file_attribute_code_t *)&attribute->v;

    file_write_be_16(file, code->max_stack);

    file_write_be_16(file, code->max_locals);

    file_write_be_32(file, code->code_count);
    fwrite(code->code, code->code_count, sizeof(u8), file);

    file_write_be_16(file, code->exception_table_count);

    assert(code->exception_table == NULL && "unimplemented");

    class_file_write_attributes(class_file, file, code->attributes_count,
                                code->attributes);

    break;
  }
  case CAK_LINE_NUMBER_TABLE: {
    assert(0 && "unimplemented");
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

void class_file_write_attributes(const class_file_t *class_file, FILE *file,
                                 u16 attribute_count,
                                 const class_file_attribute_t *attributes) {
  file_write_be_16(file, attribute_count);

  for (uint64_t i = 0; i < attribute_count; i++) {
    const class_file_attribute_t *const attribute = &attributes[i];
    class_file_write_attribute(class_file, file, attribute);
  }
}

void class_file_write_method(const class_file_t *class_file, FILE *file,
                             const class_file_method_t *method) {
  file_write_be_16(file, method->access_flags);
  file_write_be_16(file, method->name);
  file_write_be_16(file, method->descriptor);

  // TODO: attributes.
}

void class_file_write_methods(const class_file_t *class_file, FILE *file) {
  file_write_be_16(file, class_file->methods_count);

  for (uint64_t i = 0; i < class_file->methods_count; i++) {
    const class_file_method_t *const method = &class_file->methods[i];
    class_file_write_method(class_file, file, method);
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
  class_file_write_attributes(class_file, file, class_file->attribute_count,
                              class_file->attributes);
}

u16 class_file_add_constant(class_file_t *class_file,
                            const class_file_constant_t *constant) {
  assert(class_file->constant_pool_count < UINT16_MAX);

  class_file->constant_pool[class_file->constant_pool_count] = *constant;

  return class_file->constant_pool_count++;
}

void class_file_init(class_file_t *class_file, arena_t *arena) {
  class_file->constant_pool =
      arena_alloc(arena, UINT16_MAX * sizeof(class_file_constant_t));

  // Constant pool is 1-indexed so we insert a dummy at position 0.
  const class_file_constant_t dummy = {0};
  class_file_add_constant(class_file, &dummy);
}

u16 class_file_add_attributer(class_file_t *class_file,
                              class_file_attribute_t *attribute) {
  assert(class_file->attribute_count < UINT16_MAX);
  class_file->attributes[class_file->attribute_count] = *attribute;

  return class_file->attribute_count++;
}

int main() {
  arena_t arena = {0};
  arena_init(&arena, 1 << 24);

  class_file_t class_file = {
      .magic = CLASS_FILE_MAGIC_NUMBER,
      .minor_version = CLASS_FILE_MINOR_VERSION,
      .major_version = CLASS_FILE_MAJOR_VERSION_6,
      .access_flags = CAF_ACC_SUPER,
  };

  class_file_init(&class_file, &arena);

  const class_file_constant_t constant_class_object_name = {
      .kind = CIK_UTF8, .v = {.s = {.len = 16, .s = (u8 *)"java/lang/Object"}}};

  const class_file_constant_t
      constant_class_object_name_and_type_type_descriptor = {
          .kind = CIK_UTF8, .v = {.s = {.len = 3, .s = (u8 *)"()V"}}};

  const class_file_constant_t constant_class_object_name_and_type_name = {
      .kind = CIK_UTF8, .v = {.s = {.len = 6, .s = (u8 *)"<init>"}}};

  const class_file_constant_t constant_class_object = {
      .kind = CIK_CLASS_INFO,
      .v = {.class_name = class_file_add_constant(
                &class_file, &constant_class_object_name)}};

  const class_file_constant_t constant_class_object_name_and_type = {
      .kind = CIK_NAME_AND_TYPE,
      .v = {.name_and_type = {
                .name = class_file_add_constant(
                    &class_file, &constant_class_object_name_and_type_name),
                .type_descriptor = class_file_add_constant(
                    &class_file,
                    &constant_class_object_name_and_type_type_descriptor)}}};

  const class_file_constant_t constant_object = {
      .kind = CIK_METHOD_REF,
      .v = {.method_ref = {
                .class = class_file_add_constant(&class_file,
                                                 &constant_class_object),
                .name_and_type = class_file_add_constant(
                    &class_file, &constant_class_object_name_and_type)}}};
  class_file_add_constant(&class_file, &constant_object);

  const class_file_constant_t constant_class_name = {
      .kind = CIK_UTF8, .v = {.s = {.len = 5, .s = (u8 *)"Empty"}}};
  const class_file_constant_t constant_class = {
      .kind = CIK_CLASS_INFO,
      .v = {.class_name =
                class_file_add_constant(&class_file, &constant_class_name)}};

  const class_file_constant_t constant_string_code = {
      .kind = CIK_UTF8, .v = {.s = {.len = 4, .s = (u8 *)"Code"}}};
  class_file_add_constant(&class_file, &constant_string_code);

  const class_file_constant_t constant_string_line_number_table = {
      .kind = CIK_UTF8, .v = {.s = {.len = 15, .s = (u8 *)"LineNumberTable"}}};
  class_file_add_constant(&class_file, &constant_string_line_number_table);

  const class_file_constant_t constant_string_main = {
      .kind = CIK_UTF8, .v = {.s = {.len = 4, .s = (u8 *)"main"}}};
  class_file_add_constant(&class_file, &constant_string_main);

  const class_file_constant_t constant_string_main_type_descriptor = {
      .kind = CIK_UTF8,
      .v = {.s = {.len = 22, .s = (u8 *)"([Ljava/lang/String;)V"}}};
  class_file_add_constant(&class_file, &constant_string_main_type_descriptor);

  const class_file_constant_t constant_string_source_file = {
      .kind = CIK_UTF8, .v = {.s = {.len = 10, .s = (u8 *)"SourceFile"}}};
  class_file_add_constant(&class_file, &constant_string_source_file);

  const class_file_constant_t constant_string_file = {
      .kind = CIK_UTF8, .v = {.s = {.len = 10, .s = (u8 *)"Empty.java"}}};
  class_file_add_constant(&class_file, &constant_string_file);

  FILE *file = fopen("PgMain.class", "w");
  assert(file != NULL);
  class_file_write(&class_file, file);
}
