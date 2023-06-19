#include <arpa/inet.h>
#include <stdint.h>
#include <stdio.h>

#define u64 uint64_t
#define i64 int64_t
#define u32 uint32_t
#define i32 int32_t
#define u16 uint16_t
#define i16 int16_t
#define u8 uint8_t
#define i8 int8_t

typedef struct {
  enum cp_info_kind_t {
    CIK_UTF8,
    CIK_CLASS_INFO,
    CIK_METHOD_REF,
    CIK_FIELD_REF,
    CIK_NAME_AND_TYPE,
    CIK_CString,
    CIK_INT,
    CIK_FLOAT,
    CIK_LONG,
    CIK_LONG_HIGH,
    CIK_LONG_LOW,
    CIK_DOUBLE,
    CIK_DOUBLE_HIGH,
    CIK_DOUBLE_LOW,
  } kind;
  union {
  } v;
} cp_info_t;

typedef struct {
} field_info_t;

typedef struct {
} method_info_t;

typedef struct {
} attribute_info_t;

const u32 CLASS_FILE_MAGIC_NUMBER = 0xbebafeca;
const u16 CLASS_FILE_MAJOR_VERSION_6 = 50;
const u16 CLASS_FILE_MINOR_VERSION = 0;

typedef struct {
  u32 magic;
  u16 minor_version;
  u16 major_version;
  u16 constant_pool_count;
  cp_info_t *constant_pool;
  u16 access_flags;
  u16 this_class;
  u16 super_class;
  u16 interfaces_count;
  u16 fields_count;
  field_info_t *fields;
  u16 methods_count;
  method_info_t *methods;
  u16 attribute_count;
  attribute_info_t attributes;
} class_file_t;

void file_write_be_16(FILE *file, u16 x) {
  const u16 x_be = htons(x);
  fwrite(&x_be, sizeof(x_be), 1, file);
}

void file_write_be_32(FILE *file, u32 x) {
  const u32 x_be = htonl(x);
  fwrite(&x_be, sizeof(x_be), 1, file);
}

void class_file_write(class_file_t *const class_file, FILE *file) {
  fwrite(&class_file->magic, sizeof(class_file->magic), 1, file);

  file_write_be_16(file, class_file->minor_version);
  file_write_be_16(file, class_file->major_version);
}

void class_file_write_constant(class_file_t *const class_file, FILE *file,
                               const cp_info_t *constant) {}

void class_file_write_constant_pool(class_file_t *const class_file,
                                    FILE *file) {
  const u16 len = class_file->constant_pool_count + 1;
  file_write_be_16(file, len);

  for (u64 i = 0; i < class_file->constant_pool_count; i++) {
    const cp_info_t *const constant = &class_file->constant_pool[i];
    class_file_write_constant(class_file, file, constant);
  }
}

int main() {
  class_file_t class_file = {
      .magic = CLASS_FILE_MAGIC_NUMBER,
      .minor_version = CLASS_FILE_MINOR_VERSION,
      .major_version = CLASS_FILE_MAJOR_VERSION_6,
  };

  class_file_write(&class_file, stdout);
}
