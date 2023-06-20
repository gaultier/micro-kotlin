#include "class_file.h"
#include <assert.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static cf_constant_array_t constant_pool = {0};

u16 read_be_16(u8 *buf, u8 **current, u64 size) {
  pg_assert(*current + 2 <= buf + size);

  u16 *ptr = (u16 *)*current;
  u16 x_be = ptr[0];
  *current += 2;
  return ntohs(x_be);
}

u32 read_be_32(u8 *buf, u8 **current, u64 size) {
  pg_assert(*current + 4 <= buf + size);

  u32 *ptr = (u32 *)*current;
  u32 x_be = ptr[0];
  *current += 4;
  return ntohl(x_be);
}

void read_n(u8 *buf, u8 **current, u64 size, u8 *res, u64 n) {
  pg_assert(*current + n <= buf + size);

  memcpy(res, *current, n);
  *current += n;
}

u8 read_u8(u8 *buf, u8 **current, u64 size) {
  pg_assert(*current + 1 <= buf + size);

  u8 x = (*current)[0];
  *current += 1;
  return x;
}

void read_attribute(u8 *buf, u8 **current, u64 read_bytes) {
  u16 name_i = read_be_16(buf, current, read_bytes);
  assert(name_i > 0);
  u32 size = read_be_32(buf, current, read_bytes);

  printf("attribute name_i=%hu size=%u\n", name_i, size);
  pg_assert(*current + size <= buf + read_bytes);

  assert(name_i < constant_pool.len);
  cf_constant_t constant = constant_pool.values[name_i - 1];
  assert(constant.kind == CIK_UTF8);
  string_t attribute_name = constant.v.s;

  if (string_eq_c(attribute_name, "SourceFile")) {
    u16 source_file_i = read_be_16(buf, current, read_bytes);
    printf("attribute_source_file source_file_i=%hu\n", source_file_i);
  } else if (string_eq_c(attribute_name, "Code")) {

    u16 max_stack = read_be_16(buf, current, read_bytes);
    u16 max_locals = read_be_16(buf, current, read_bytes);
    u32 code_len = read_be_32(buf, current, read_bytes);
    pg_assert(*current + code_len <= buf + read_bytes);

    u8 code[1024] = {0}; // FIXME
    read_n(buf, current, read_bytes, code, code_len);

    u16 exception_table_len = read_be_16(buf, current, read_bytes);
    u16 attribute_count = read_be_16(buf, current, read_bytes);
    printf("attribute_code max_stack=%hu max_locals=%hu code_len=%u "
           "exception_table_len=%hu attribute_count=%hu\n",
           max_stack, max_locals, code_len, exception_table_len,
           attribute_count);

    pg_assert(attribute_count == 0); // TODO
  } else {
    pg_assert(0 && "unreachable");
  }
}

void read_attributes(u8 *buf, u8 **current, u64 read_bytes) {
  u16 attribute_count = read_be_16(buf, current, read_bytes);

  for (u64 i = 0; i < attribute_count; i++) {
    printf("[%lu/%hu] attribute\n", i, attribute_count);
    read_attribute(buf, current, read_bytes);
  }
}

int main(int argc, char *argv[]) {
  pg_assert(argc == 2);

  arena_t arena = {0};
  arena_init(&arena, 1 << 26);
  constant_pool = cf_constant_array_make(1024, &arena);

  int fd = open(argv[1], O_RDONLY);
  pg_assert(fd > 0);

  u8 buf[1 << 14] = {0};
  ssize_t read_bytes = read(fd, buf, sizeof(buf));
  u8 *current = buf;

  pg_assert(read_bytes > 0);

  pg_assert(read_u8(buf, &current, read_bytes) == 0xca);
  pg_assert(read_u8(buf, &current, read_bytes) == 0xfe);
  pg_assert(read_u8(buf, &current, read_bytes) == 0xba);
  pg_assert(read_u8(buf, &current, read_bytes) == 0xbe);
  pg_assert(read_u8(buf, &current, read_bytes) == 0x00);
  pg_assert(read_u8(buf, &current, read_bytes) == 0x00);
  pg_assert(read_u8(buf, &current, read_bytes) == 0x00);
  pg_assert(read_u8(buf, &current, read_bytes) == 0x32);

  u16 constant_pool_size = read_be_16(buf, &current, read_bytes);
  pg_assert(constant_pool_size > 0);
  constant_pool_size -= 1;

  for (u64 i = 1; i <= constant_pool_size; i++) {
    u8 kind = read_u8(buf, &current, read_bytes);

    if (!(kind == CIK_UTF8 || kind == CIK_INT || kind == CIK_FLOAT ||
          kind == CIK_LONG || kind == CIK_DOUBLE || kind == CIK_CLASS_INFO ||
          kind == CIK_STRING || kind == CIK_FIELD_REF ||
          kind == CIK_METHOD_REF || kind == CIK_INSTANCE_METHOD_REF ||
          kind == CIK_NAME_AND_TYPE || kind == CIK_INVOKE_DYNAMIC)) {
      fprintf(stderr, "Unknown constant kind found: i=%lu offset=%lu kind=%u\n",
              i, current - buf - 1, kind);
      exit(1);
    }

    switch (kind) {
    case CIK_UTF8: {
      u16 len = read_be_16(buf, &current, read_bytes);
      pg_assert(len > 0);

      u8 *s = current;
      u8 dummy[UINT16_MAX] = {0};
      read_n(buf, &current, read_bytes, dummy, len);

      printf("[%lu/%hu] CIK_UTF8 len=%u s=%.*s\n", i, constant_pool_size, len,
             len, s);

      cf_constant_t constant = {.kind = CIK_UTF8,
                                .v = {.s = {.len = len, .s = s}}};
      cf_constant_array_push(&constant_pool, &constant);

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
      u16 class_name_i = read_be_16(buf, &current, read_bytes);
      pg_assert(class_name_i > 0);
      pg_assert(class_name_i <= constant_pool_size);

      printf("[%lu/%hu] CIK_CLASS_INFO class_name_i=%u\n", i,
             constant_pool_size, class_name_i);

      cf_constant_t constant = {0}; // TODO
      cf_constant_array_push(&constant_pool, &constant);
      break;
    }
    case CIK_STRING: {
      u16 utf8_i = read_be_16(buf, &current, read_bytes);
      pg_assert(utf8_i > 0);
      pg_assert(utf8_i <= constant_pool_size);
      printf("[%lu/%hu] CIK_STRING utf8_i=%u\n", i, constant_pool_size, utf8_i);

      cf_constant_t constant = {0}; // TODO
      cf_constant_array_push(&constant_pool, &constant);
      break;
    }
    case CIK_FIELD_REF: {
      u16 name_i = read_be_16(buf, &current, read_bytes);
      pg_assert(name_i > 0);
      pg_assert(name_i <= constant_pool_size);

      u16 descriptor_i = read_be_16(buf, &current, read_bytes);
      pg_assert(descriptor_i > 0);
      pg_assert(descriptor_i <= constant_pool_size);

      printf("[%lu/%hu] CIK_FIELD_REF name_i=%u descriptor_i=%u\n", i,
             constant_pool_size, name_i, descriptor_i);

      cf_constant_t constant = {0}; // TODO
      cf_constant_array_push(&constant_pool, &constant);
      break;
    }
    case CIK_METHOD_REF: {
      u16 class_i = read_be_16(buf, &current, read_bytes);
      pg_assert(class_i > 0);
      pg_assert(class_i <= constant_pool_size);

      u16 name_and_type_i = read_be_16(buf, &current, read_bytes);
      pg_assert(name_and_type_i > 0);
      pg_assert(name_and_type_i <= constant_pool_size);

      printf("[%lu/%hu] CIK_METHOD_REF class_i=%u name_and_type_i=%u\n", i,
             constant_pool_size, class_i, name_and_type_i);

      cf_constant_t constant = {0}; // TODO
      cf_constant_array_push(&constant_pool, &constant);
      break;
    }
    case CIK_INSTANCE_METHOD_REF:
      pg_assert(0 && "unimplemented");
      break;
    case CIK_NAME_AND_TYPE: {
      u16 class_i = read_be_16(buf, &current, read_bytes);
      pg_assert(class_i > 0);
      pg_assert(class_i <= constant_pool_size);

      u16 name_and_type_i = read_be_16(buf, &current, read_bytes);
      pg_assert(name_and_type_i > 0);
      pg_assert(name_and_type_i <= constant_pool_size);

      printf("[%lu/%hu] CIK_NAME_AND_TYPE class_i=%u name_and_type_i=%u\n", i,
             constant_pool_size, class_i, name_and_type_i);

      cf_constant_t constant = {0}; // TODO
      cf_constant_array_push(&constant_pool, &constant);
      break;
    }
    case CIK_INVOKE_DYNAMIC:
      pg_assert(0 && "unimplemented");
      break;
    default:
      pg_assert(0 && "unreachable");
    }
  }

  u16 access_flags = read_be_16(buf, &current, read_bytes);
  printf("access flags=%x\n", access_flags);

  u16 this_class_i = read_be_16(buf, &current, read_bytes);
  printf("this class=%x\n", this_class_i);
  pg_assert(this_class_i > 0);
  pg_assert(this_class_i <= constant_pool_size);

  u16 super_class_i = read_be_16(buf, &current, read_bytes);
  printf("super class=%x\n", super_class_i);
  pg_assert(super_class_i > 0);
  pg_assert(super_class_i <= constant_pool_size);

  u16 interfaces_count = read_be_16(buf, &current, read_bytes);
  printf("interfaces count=%x\n", interfaces_count);
  pg_assert(interfaces_count == 0);

  u16 fields_count = read_be_16(buf, &current, read_bytes);
  printf("fields count=%x\n", fields_count);
  pg_assert(fields_count == 0);

  u16 methods_count = read_be_16(buf, &current, read_bytes);
  printf("methods count=%x\n", methods_count);
  pg_assert(methods_count > 0);

  for (u64 i = 0; i < methods_count; i++) {
    u16 access_flags = read_be_16(buf, &current, read_bytes);
    u16 method_name_i = read_be_16(buf, &current, read_bytes);
    pg_assert(method_name_i > 0);
    pg_assert(method_name_i <= constant_pool.len);
    u16 descriptor_i = read_be_16(buf, &current, read_bytes);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool.len);
    printf("[%lu/%u] method access_flags=%x method_name_i=%hu descriptor_i=%hu"
           "\n",
           i, methods_count, access_flags, method_name_i, descriptor_i);
    read_attributes(buf, &current, read_bytes);
  }

  read_attributes(buf, &current, read_bytes);

  u64 remaining = buf + read_bytes - current;
  printf("read=%ld rem=%ld\n", current - buf, remaining);
  pg_assert(remaining == 0);
}
