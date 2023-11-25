#pragma once

#include "arena.h"
#include "array.h"

#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <unistd.h>

// String builder, like a dynamic array.
typedef struct {
  u8 *data;
  u64 len;
  u64 cap;
} str_builder;

// String view, immutable.
typedef struct {
  u8 *data;
  u64 len;
} str;

typedef struct str_set_t str_set_t;
struct str_set_t {
  str_set_t *child[4];
  str key;
};

// FNV-1a
__attribute__((warn_unused_result)) static u64 str_hash(str s) {
  u64 h = 0x100;
  for (u64 i = 0; i < s.len; i++) {
    h ^= s.data[i];
    h *= 1111111111111111111u;
  }
  return h;
}

__attribute__((warn_unused_result)) static bool str_eq(str a, str b) {
  if (a.len == 0 && b.len != 0)
    return false;
  if (b.len == 0 && a.len != 0)
    return false;

  if (a.len == 0 && b.len == 0)
    return true;

  pg_assert(a.data != NULL);
  pg_assert(b.data != NULL);

  return a.len == b.len && memcmp(a.data, b.data, a.len) == 0;
}

static bool str_set_find_or_create(str_set_t **set, str s, arena_t *arena) {
  for (u64 h = str_hash(s); *set; h <<= 2) {
    if (str_eq(s, (*set)->key)) {
      return false;
    }
    set = &(*set)->child[h >> 62];
  }
  *set = arena_alloc(arena, sizeof(str_set_t), _Alignof(str_set_t), 1);
  (*set)->key = s;

  return true;
}

__attribute__((warn_unused_result)) static str str_from_c(char *s) {
  return (str){.data = (u8 *)s, .len = s == NULL ? 0 : strlen(s)};
}

#define str_from_c_literal(s) ((str){.data = (u8 *)s, .len = sizeof(s) - 1})

__attribute__((warn_unused_result)) static u8 *ut_memrchr(u8 *s, u8 c, u64 n) {
  pg_assert(s != NULL);
  pg_assert(n > 0);

  u8 *res = s + n - 1;
  while (res-- != s) {
    if (*res == c)
      return res;
  }
  return NULL;
}

// https://graphics.stanford.edu/~seander/bithacks.html#RoundUpPowerOf2
__attribute__((warn_unused_result)) static u64 ut_next_power_of_two(u64 n) {
  n += !n; // Ensure n>0

  n--;
  n |= n >> 1;
  n |= n >> 2;
  n |= n >> 4;
  n |= n >> 8;
  n |= n >> 16;
  n |= n >> 32;
  n++;

  pg_assert(__builtin_popcount(n) == 1);

  return n;
}

__attribute__((warn_unused_result)) static str str_new(u8 *s, u64 n) {
  return (str){.data = s, .len = n};
}

__attribute__((warn_unused_result)) static str str_clone(str s,
                                                         arena_t *arena) {
  // Optimization: no alloc.
  if (s.len == 0)
    return s;

  u8 *data = arena_alloc(arena, sizeof(u8), _Alignof(u8), s.len);
  pg_assert(data);
  pg_assert(s.data);

  pg_assert(s.data);
  memmove(data, s.data, s.len);

  return (str){.data = data, .len = s.len};
}

__attribute__((warn_unused_result)) static str str_advance(str s, u64 n) {
  if (n > s.len)
    return (str){0};
  return (str){.data = s.data + n, .len = s.len - n};
}

__attribute__((warn_unused_result)) static u8 str_first(str s) {
  return s.len > 0 ? s.data[0] : 0;
}

__attribute__((warn_unused_result)) static bool str_ends_with(str haystack,
                                                              str needle) {
  if (needle.len > haystack.len)
    return false;

  u64 start = haystack.len - needle.len;
  return memcmp(&haystack.data[start], needle.data, needle.len) == 0;
}

__attribute__((warn_unused_result)) static bool str_ends_with_c(str haystack,
                                                                char *needle) {
  return str_ends_with(haystack, str_from_c(needle));
}

__attribute__((warn_unused_result)) static bool str_is_empty(str s) {
  return s.len == 0;
}

__attribute__((warn_unused_result)) static bool str_eq_c(str a, char *b) {
  return str_eq(a, str_from_c(b));
}

__attribute__((warn_unused_result)) static bool
str_contains_element(str haystack, u8 needle) {
  for (i64 i = 0; i < (i64)haystack.len - 1; i++) {
    if (haystack.data[i] == needle)
      return true;
  }
  return false;
}

typedef struct {
  str left, right;
  u64 found_pos;
  bool found;
  pg_pad(7);
} str_split_result_t;

__attribute__((warn_unused_result)) static str_split_result_t
str_split(str haystack, u8 needle) {
  u8 *at = memchr(haystack.data, needle, haystack.len);
  if (at == NULL)
    return (str_split_result_t){.left = haystack, .right = haystack};

  u64 found_pos = at - haystack.data;

  return (str_split_result_t){
      .left = (str){.data = haystack.data, .len = found_pos},
      .right = (str){.data = at + 1, .len = haystack.len - found_pos - 1},
      .found_pos = found_pos,
      .found = true,
  };
}

__attribute__((warn_unused_result)) static str_split_result_t
str_rsplit(str haystack, u8 needle) {
  u8 *at = ut_memrchr(haystack.data, needle, haystack.len);
  if (at == NULL)
    return (str_split_result_t){.left = haystack, .right = haystack};

  u64 found_pos = at - haystack.data;

  return (str_split_result_t){
      .left = (str){.data = haystack.data, .len = found_pos},
      .right = (str){.data = at + 1, .len = haystack.len - found_pos - 1},
      .found_pos = found_pos,
      .found = true,
  };
}

__attribute__((warn_unused_result)) static u64 sb_space(str_builder sb) {
  pg_assert(sb.len < sb.cap);

  return sb.cap - sb.len - 1;
}

__attribute__((warn_unused_result)) static str_builder
sb_reserve_at_least(str_builder sb, u64 more, arena_t *arena) {
  pg_assert(sb.len <= sb.cap);

  if (more <= sb_space(sb))
    return sb;

  u64 new_cap = ut_next_power_of_two(sb.cap + more + 1 /* NUL terminator */);
  pg_assert(new_cap > sb.len);

  u8 *new_data = arena_alloc(arena, sizeof(u8), _Alignof(u8), new_cap);
  pg_assert(new_data);
  pg_assert(sb.data);

  if (sb.data)
    memmove(new_data, sb.data, sb.len);

  pg_assert(sb.data[sb.len] == 0);
  pg_assert(new_data[sb.len] == 0);

  return (str_builder){.len = sb.len, .cap = new_cap, .data = new_data};
}

__attribute__((warn_unused_result)) static u8 *sb_end_c(str_builder sb) {
  return sb.data + sb.len;
}

__attribute__((warn_unused_result)) static str_builder
sb_append(str_builder sb, str more, arena_t *arena) {
  sb = sb_reserve_at_least(sb, more.len, arena);

  if (more.data)
    memmove(sb_end_c(sb), more.data, more.len);

  sb.data[sb.len + more.len] = 0;
  return (str_builder){
      .len = sb.len + more.len, .data = sb.data, .cap = sb.cap};
}

__attribute__((warn_unused_result)) static str_builder
sb_append_c(str_builder sb, char *more, arena_t *arena) {
  return sb_append(sb, str_from_c(more), arena);
}

__attribute__((warn_unused_result)) static str_builder
sb_append_char(str_builder sb, u8 c, arena_t *arena) {
  sb = sb_reserve_at_least(sb, 1, arena);
  sb.data[sb.len] = c;
  sb.data[sb.len + 1] = 0;
  return (str_builder){.len = sb.len + 1, .data = sb.data, .cap = sb.cap};
}

__attribute__((warn_unused_result)) static str_builder sb_new(u64 initial_cap,
                                                              arena_t *arena) {
  return (str_builder){
      .data = arena_alloc(arena, sizeof(u8), _Alignof(u8), initial_cap + 1),
      .cap = initial_cap + 1,
  };
}

__attribute__((warn_unused_result)) static str_builder
sb_assume_appended_n(str_builder sb, u64 more) {
  return (str_builder){.len = sb.len + more, .data = sb.data, .cap = sb.cap};
}

__attribute__((warn_unused_result)) static str sb_build(str_builder sb) {
  pg_assert(sb.data);
  pg_assert(sb.cap > 0);
  pg_assert(sb.data[sb.len] == 0);

  return (str){.data = sb.data, .len = sb.len};
}

__attribute__((warn_unused_result)) static str_builder
sb_append_u64(str_builder sb, u64 n, arena_t *arena) {
  char tmp[25] = "";
  snprintf(tmp, sizeof(tmp) - 1, "%lu", n);
  return sb_append_c(sb, tmp, arena);
}

__attribute__((warn_unused_result)) static str_builder
sb_capitalize_at(str_builder sb, u64 pos) {
  pg_assert(pos < sb.len);

  if ('a' <= sb.data[pos] && sb.data[pos] <= 'z')
    sb.data[pos] -= 'a' - 'A';

  return sb;
}

__attribute__((warn_unused_result)) static str_builder
sb_clone(str src, arena_t *arena) {
  str_builder res = sb_new(src.len, arena);
  pg_assert(res.data);
  pg_assert(src.len <= res.cap);
  pg_assert(src.data);

  if (src.data)
    memmove(res.data, src.data, src.len);

  res.len = src.len;
  return res;
}

__attribute__((warn_unused_result)) static str_builder
sb_replace_element_starting_at(str_builder sb, u64 start, u8 from, u8 to) {
  for (u64 i = start; i < sb.len; i++) {
    if (sb.data[i] == from)
      sb.data[i] = to;
  }
  return sb;
}

// ------------------- Utils

__attribute__((warn_unused_result)) static bool ut_char_is_alphabetic(u8 c) {
  return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
}

typedef struct {
  str content;
  int error;
  pg_pad(4);
} ut_read_result_t;

__attribute__((warn_unused_result)) static ut_read_result_t
ut_read_all_from_fd(int fd, str_builder sb) {
  pg_assert(fd > 0);

  while (sb_space(sb) > 0) {
    pg_assert(sb.len <= sb.cap);

    const i64 read_bytes = read(fd, sb_end_c(sb), sb_space(sb));
    if (read_bytes == -1)
      return (ut_read_result_t){.error = errno};
    if (read_bytes == 0)
      return (ut_read_result_t){.error = EINVAL}; // TODO: retry?

    sb = sb_assume_appended_n(sb, read_bytes);
    pg_assert(sb.len <= sb.cap);
  }
  return (ut_read_result_t){.content = sb_build(sb)};
}

__attribute__((warn_unused_result)) static char *str_to_c(str s,
                                                          arena_t *arena) {
  char *c_str = arena_alloc(arena, sizeof(u8), _Alignof(u8), s.len + 1);
  if (s.data)
    memmove(c_str, s.data, s.len);

  pg_assert(strlen(c_str) == s.len);

  c_str[s.len] = 0;

  return c_str;
}

__attribute__((warn_unused_result)) static ut_read_result_t
ut_read_all_from_file_path(char *path, arena_t *arena) {
  const int fd = open(path, O_RDONLY);
  if (fd == -1) {
    return (ut_read_result_t){.error = errno};
  }

  struct stat st = {0};
  if (stat(path, &st) == -1) {
    fprintf(stderr, "Failed to get the file size %s: %s\n", path,
            strerror(errno));
    close(fd);
    return (ut_read_result_t){.error = errno};
  }

  if (st.st_size == 0) {
    close(fd);
    return (ut_read_result_t){0};
  }

  ut_read_result_t res = ut_read_all_from_fd(fd, sb_new(st.st_size, arena));
  close(fd);
  return res;
}

// --------------------------- Profile memory allocations

typedef struct {
  u64 in_use_space, in_use_objects, alloc_space, alloc_objects;
  u64 *call_stack;
} mem_record;

struct mem_profile {
  mem_record *records;
  u64 in_use_space, in_use_objects, alloc_space, alloc_objects;
  arena_t arena;
};

// TODO: Maybe use varints to reduce the size.
__attribute__((warn_unused_result)) static u8 ut_record_call_stack(u64 *dst,
                                                                   u64 cap) {
  uintptr_t *rbp = __builtin_frame_address(0);

  u64 len = 0;

  while (rbp != 0 && ((u64)rbp & 7) == 0 && (u64)rbp > 8 && *rbp != 0) {
    const uintptr_t rip = *(rbp + 1);
    rbp = (uintptr_t *)*rbp;

    // `rip` points to the return instruction in the caller, once this call is
    // done. But: We want the location of the call i.e. the `call xxx`
    // instruction, so we subtract one byte to point inside it, which is not
    // quite 'at it' but good enough.
    pg_assert(rip > 0);
    dst[len++] = rip - 1;

    if (len >= cap)
      return len;
  }
  return len;
}

static void mem_profile_record_alloc(mem_profile_t *profile, u64 objects_count,
                                     u64 bytes_count) {
  // Record the call stack by stack walking.
  u64 call_stack[64] = {0};
  u64 call_stack_len = ut_record_call_stack(
      call_stack, sizeof(call_stack) / sizeof(call_stack[0]));

  // Update the sums.
  profile->alloc_objects += objects_count;
  profile->alloc_space += bytes_count;
  profile->in_use_objects += objects_count;
  profile->in_use_space += bytes_count;

  // Upsert the record.
  for (u64 i = 0; i < pg_array_len(profile->records); i++) {
    mem_record *r = &profile->records[i];

    if (pg_array_len(r->call_stack) == call_stack_len &&
        memcmp(r->call_stack, call_stack, call_stack_len * sizeof(u64)) == 0) {
      // Found an existing record, update it.
      r->alloc_objects += objects_count;
      r->alloc_space += bytes_count;
      r->in_use_objects += objects_count;
      r->in_use_space += bytes_count;
      return;
    }
  }

  // Not found, insert a new record.
  mem_record record = {
      .alloc_objects = objects_count,
      .alloc_space = bytes_count,
      .in_use_objects = objects_count,
      .in_use_space = bytes_count,
  };
  pg_array_init_reserve(record.call_stack, call_stack_len, &profile->arena);
  memcpy(record.call_stack, call_stack, call_stack_len * sizeof(u64));
  pg_array_header(record.call_stack)->len = call_stack_len;

  pg_array_append(profile->records, record, &profile->arena);
}

static void mem_profile_write(mem_profile_t *profile, FILE *out) {
  // clang-format off
  // heap profile:    <in_use>:  <nbytes1> [   <space>:  <nbytes2>] @ heapprofile
  // <in_use>: <nbytes1> [<space>: <nbytes2>] @ <rip1> <rip2> <rip3> [...]
  // <in_use>: <nbytes1> [<space>: <nbytes2>] @ <rip1> <rip2> <rip3> [...]
  // <in_use>: <nbytes1> [<space>: <nbytes2>] @ <rip1> <rip2> <rip3> [...]
  //
  // MAPPED_LIBRARIES:
  // [...]
  // clang-format on

  fprintf(out, "heap profile: %lu: %lu [     %lu:    %lu] @ heapprofile\n",
          profile->in_use_objects, profile->in_use_space,
          profile->alloc_objects, profile->alloc_space);

  for (u64 i = 0; i < pg_array_len(profile->records); i++) {
    mem_record r = profile->records[i];

    fprintf(out, "%lu: %lu [%lu: %lu] @ ", r.in_use_objects, r.in_use_space,
            r.alloc_objects, r.alloc_space);

    for (u64 j = 0; j < pg_array_len(r.call_stack); j++) {
      fprintf(out, "%#lx ", r.call_stack[j]);
    }
    fputc('\n', out);
  }

  fputs("\nMAPPED_LIBRARIES:\n", out);

  static u8 mem[4096] = {0};
  int fd = open("/proc/self/maps", O_RDONLY);
  pg_assert(fd != -1);
  isize read_bytes = read(fd, mem, sizeof(mem));
  pg_assert(read_bytes != -1);
  close(fd);

  fwrite(mem, 1, read_bytes, out);

  fflush(out);
}
