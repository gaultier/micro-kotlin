#include "class_file.h"
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

u16 read_be_16(u8 *buf, u8 **current, u64 size) {
  assert(*current + 2 < buf + size);

  u16 *ptr = (u16 *)*current;
  u16 x_be = ptr[0];
  *current += 2;
  return ntohs(x_be);
}

void read_n(u8 *buf, u8 **current, u64 size, u8 *res, u64 n) {
  assert(*current + n < buf + size);

  memcpy(res, *current, n);
  *current += n;
}

u8 read_u8(u8 *buf, u8 **current, u64 size) {
  assert(*current + 1 < buf + size);

  u8 x = (*current)[0];
  *current += 1;
  return x;
}

int main(int argc, char *argv[]) {
  assert(argc == 2);

  int fd = open(argv[1], O_RDONLY);
  assert(fd > 0);

  u8 buf[1 << 14] = {0};
  ssize_t read_bytes = read(fd, buf, sizeof(buf));
  u8 *current = buf;

  assert(read_bytes > 0);

  assert(read_u8(buf, &current, read_bytes) == 0xca);
  assert(read_u8(buf, &current, read_bytes) == 0xfe);
  assert(read_u8(buf, &current, read_bytes) == 0xba);
  assert(read_u8(buf, &current, read_bytes) == 0xbe);
  assert(read_u8(buf, &current, read_bytes) == 0x00);
  assert(read_u8(buf, &current, read_bytes) == 0x00);
  assert(read_u8(buf, &current, read_bytes) == 0x00);
  assert(read_u8(buf, &current, read_bytes) == 0x32);

  u16 constant_pool_size = read_be_16(buf, &current, read_bytes);
  assert(constant_pool_size > 0);
  constant_pool_size -= 1;

  for (u64 i = 0; i < constant_pool_size; i++) {
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
      assert(len > 0);

      u8 s[UINT16_MAX] = {0};
      read_n(buf, &current, read_bytes, s, len);

      printf("[%lu/%hu] CIK_UTF8 len=%u s=%.*s\n", i, constant_pool_size, len,
             len, s);
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
    case CIK_CLASS_INFO: {
      u16 class_name_i = read_be_16(buf, &current, read_bytes);
      assert(class_name_i > 0);
      assert(class_name_i <= constant_pool_size);

      printf("[%lu/%hu] CIK_CLASS_INFO class_name_i=%u\n", i,
             constant_pool_size, class_name_i);
      break;
    }
    case CIK_STRING: {
      u16 utf8_i = read_be_16(buf, &current, read_bytes);
      assert(utf8_i > 0);
      assert(utf8_i <= constant_pool_size);
      printf("[%lu/%hu] CIK_STRING utf8_i=%u\n", i, constant_pool_size, utf8_i);
      break;
    }
    case CIK_FIELD_REF: {
      u16 name_i = read_be_16(buf, &current, read_bytes);
      assert(name_i > 0);
      assert(name_i <= constant_pool_size);

      u16 descriptor_i = read_be_16(buf, &current, read_bytes);
      assert(descriptor_i > 0);
      assert(descriptor_i <= constant_pool_size);

      printf("[%lu/%hu] CIK_FIELD_REF name_i=%u descriptor_i=%u\n", i,
             constant_pool_size, name_i, descriptor_i);
      break;
    }
    case CIK_METHOD_REF: {
      u16 class_i = read_be_16(buf, &current, read_bytes);
      assert(class_i > 0);
      assert(class_i <= constant_pool_size);

      u16 name_and_type_i = read_be_16(buf, &current, read_bytes);
      assert(name_and_type_i > 0);
      assert(name_and_type_i <= constant_pool_size);

      printf("[%lu/%hu] CIK_METHOD_REF class_i=%u name_and_type_i=%u\n", i,
             constant_pool_size, class_i, name_and_type_i);
      break;
    }
    case CIK_INSTANCE_METHOD_REF:
      assert(0 && "unimplemented");
      break;
    case CIK_NAME_AND_TYPE: {
      u16 class_i = read_be_16(buf, &current, read_bytes);
      assert(class_i > 0);
      assert(class_i <= constant_pool_size);

      u16 name_and_type_i = read_be_16(buf, &current, read_bytes);
      assert(name_and_type_i > 0);
      assert(name_and_type_i <= constant_pool_size);

      printf("[%lu/%hu] CIK_NAME_AND_TYPE class_i=%u name_and_type_i=%u\n", i,
             constant_pool_size, class_i, name_and_type_i);
      break;
    }
    case CIK_INVOKE_DYNAMIC:
      assert(0 && "unimplemented");
      break;
    default:
      assert(0 && "unreachable");
    }
  }

  u16 access_flags = read_be_16(buf, &current, read_bytes);
  printf("access flags=%x\n", access_flags);

  u16 this_class_i = read_be_16(buf, &current, read_bytes);
  printf("this class=%x\n", this_class_i);
  assert(this_class_i>0);
  assert(this_class_i<=constant_pool_size);

  u16 super_class_i = read_be_16(buf, &current, read_bytes);
  printf("super class=%x\n", super_class_i);
  assert(super_class_i>0);
  assert(super_class_i<=constant_pool_size);
}
