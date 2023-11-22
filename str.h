#pragma once

#include "arena.h"
#include "array.h"
#include "pprof.pb-c.c"
#include "pprof.pb-c.h"

#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
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

static str str_from_c(char *s) {
  return (str){.data = (u8 *)s, .len = s == NULL ? 0 : strlen(s)};
}

#define str_from_c_literal(s) ((str){.data = (u8 *)s, .len = sizeof(s) - 1})

static u8 *ut_memrchr(u8 *s, u8 c, u64 n) {
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
static u64 ut_next_power_of_two(u64 n) {
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

static str str_new(u8 *s, u64 n) { return (str){.data = s, .len = n}; }

static str str_clone(str s, arena_t *arena) {
  u8 *data = arena_alloc(arena, sizeof(u8), _Alignof(u8), s.len);
  memcpy(data, s.data, s.len);
  return (str){.data = data, .len = s.len};
}

static str str_advance(str s, u64 n) {
  if (n > s.len)
    return (str){0};
  return (str){.data = s.data + n, .len = s.len - n};
}

static u8 str_first(str s) { return s.len > 0 ? s.data[0] : 0; }

static bool str_ends_with(str haystack, str needle) {
  if (needle.len > haystack.len)
    return false;

  u64 start = haystack.len - needle.len;
  return memcmp(&haystack.data[start], needle.data, needle.len) == 0;
}

static bool str_ends_with_c(str haystack, char *needle) {
  return str_ends_with(haystack, str_from_c(needle));
}

static bool str_is_empty(str s) { return s.len == 0; }

static bool str_eq(str a, str b) {
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

static bool str_eq_c(str a, char *b) { return str_eq(a, str_from_c(b)); }

static bool str_contains_element(str haystack, u8 needle) {
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

static str_split_result_t str_split(str haystack, u8 needle) {
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

static str_split_result_t str_rsplit(str haystack, u8 needle) {
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

static u64 sb_space(str_builder sb) {
  pg_assert(sb.len < sb.cap);

  return sb.cap - sb.len - 1;
}

static str_builder sb_reserve_at_least(str_builder sb, u64 more,
                                       arena_t *arena) {

  more += 1; // Null terminator.

  if (sb_space(sb) >= more)
    return sb;

  u64 new_cap = ut_next_power_of_two(sb_space(sb) + more);
  u8 *new_data = arena_alloc(arena, sizeof(u8), _Alignof(u8), new_cap);
  memcpy(new_data, sb.data, sb.len);

  return (str_builder){.len = sb.len, .cap = new_cap, .data = new_data};
}

static u8 *sb_end_c(str_builder sb) { return sb.data + sb.len; }

static str_builder sb_append(str_builder sb, str more, arena_t *arena) {
  sb = sb_reserve_at_least(sb, more.len, arena);
  memcpy(sb_end_c(sb), more.data, more.len);
  sb.data[sb.len + more.len] = 0;
  return (str_builder){
      .len = sb.len + more.len, .data = sb.data, .cap = sb.cap};
}

static str_builder sb_append_c(str_builder sb, char *more, arena_t *arena) {
  return sb_append(sb, str_from_c(more), arena);
}

static str_builder sb_append_char(str_builder sb, u8 c, arena_t *arena) {
  sb = sb_reserve_at_least(sb, 1, arena);
  sb.data[sb.len] = c;
  sb.data[sb.len + 1] = 0;
  return (str_builder){.len = sb.len + 1, .data = sb.data, .cap = sb.cap};
}

static str_builder sb_new(u64 initial_cap, arena_t *arena) {
  return (str_builder){
      .data = arena_alloc(arena, sizeof(u8), _Alignof(u8), initial_cap + 1),
      .cap = initial_cap + 1,
  };
}

static str_builder sb_assume_appended_n(str_builder sb, u64 more) {
  return (str_builder){.len = sb.len + more, .data = sb.data, .cap = sb.cap};
}

static str sb_build(str_builder sb) {
  return (str){.data = sb.data, .len = sb.len};
}

static str_builder sb_append_u64(str_builder sb, u64 n, arena_t *arena) {
  char tmp[25] = "";
  snprintf(tmp, sizeof(tmp) - 1, "%lu", n);
  return sb_append_c(sb, tmp, arena);
}

static str_builder sb_capitalize_at(str_builder sb, u64 pos) {
  pg_assert(pos < sb.len);

  if ('a' <= sb.data[pos] && sb.data[pos] <= 'z')
    sb.data[pos] -= 'a' - 'A';

  return sb;
}

static str_builder sb_clone(str src, arena_t *arena) {
  str_builder res = sb_new(src.len, arena);
  memcpy(res.data, src.data, src.len);
  res.len = src.len;
  return res;
}

static str_builder sb_replace_element_starting_at(str_builder sb, u64 start,
                                                  u8 from, u8 to) {
  for (u64 i = start; i < sb.len; i++) {
    if (sb.data[i] == from)
      sb.data[i] = to;
  }
  return sb;
}

// ------------------- Utils

static bool ut_char_is_alphabetic(u8 c) {
  return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
}

typedef struct {
  str content;
  int error;
  pg_pad(4);
} ut_read_result_t;

static ut_read_result_t ut_read_all_from_fd(int fd, str_builder sb) {
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

static char *str_to_c(str s, arena_t *arena) {
  char *c_str = arena_alloc(arena, sizeof(u8), _Alignof(u8), s.len + 1);
  memcpy(c_str, s.data, s.len);

  c_str[s.len] = 0;

  return c_str;
}

static ut_read_result_t
ut_read_all_from_file_path(str path, arena_t scratch_arena, arena_t *arena) {
  char *path_c_str = str_to_c(path, &scratch_arena);
  const int fd = open(path_c_str, O_RDONLY);
  if (fd == -1) {
    return (ut_read_result_t){.error = errno};
  }

  struct stat st = {0};
  if (stat(path_c_str, &st) == -1) {
    fprintf(stderr, "Failed to get the file size %s: %s\n", path_c_str,
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
struct mem_profile {
  struct Perftools__Profiles__Profile profile;
  arena_t arena;
};

// TODO: Maybe use varints to reduce the size.
inline static u8 ut_record_call_stack(u64 *dst, u64 cap) {
  uintptr_t *rbp = __builtin_frame_address(0);

  u64 len = 0;

  while (rbp != 0 && ((u64)rbp & 7) == 0 && *rbp != 0) {
    const uintptr_t rip = *(rbp + 1);
    rbp = (uintptr_t *)*rbp;

    if (len >= cap)
      return len;

    // `rip` points to the return instruction in the caller, once this call is
    // done. But: We want the location of the call i.e. the `call xxx`
    // instruction, so we subtract one byte to point inside it, which is not
    // quite 'at it' but good enough.
    dst[len++] = rip - 1;
  }
  return len;
}

void mem_profile_record(mem_profile *profile, u64 bytes_count) {
  u64 call_stack[64] = {0};
  u64 call_stack_len = ut_record_call_stack(
      call_stack, sizeof(call_stack) / sizeof(call_stack[0]));
  pg_assert(call_stack_len >= 2);
}

void mem_profile_write(mem_profile *profile, FILE *out) {
  u64 string_count_index = 0;
  u64 string_bytes_index = 0;
  u64 string_space_index = 0;
  u64 string_allocations_index = 0;
  u64 string_heap_index = 0;

  profile->profile =
      (Perftools__Profiles__Profile)PERFTOOLS__PROFILES__PROFILE__INIT;
  // string_table
  {
    u64 index = 0;

    profile->profile.n_string_table = 6;
    profile->profile.string_table =
        arena_alloc(&profile->arena, sizeof(uintptr_t), _Alignof(uintptr_t),
                    profile->profile.n_string_table);

    profile->profile.string_table[index] =
        str_to_c(str_from_c_literal(""), &profile->arena);
    string_allocations_index = index++;

    profile->profile.string_table[index] =
        str_to_c(str_from_c_literal("allocations"), &profile->arena);
    string_allocations_index = index++;

    profile->profile.string_table[index] =
        str_to_c(str_from_c_literal("count"), &profile->arena);
    string_count_index = index++;

    profile->profile.string_table[index] =
        str_to_c(str_from_c_literal("space"), &profile->arena);
    string_space_index = index++;

    profile->profile.string_table[index] =
        str_to_c(str_from_c_literal("bytes"), &profile->arena);
    string_bytes_index = index++;

    profile->profile.string_table[index] =
        str_to_c(str_from_c_literal("heap"), &profile->arena);
    string_heap_index = index++;
  }

  // sample_type
  {
    profile->profile.n_sample_type = 2;
    profile->profile.sample_type =
        arena_alloc(&profile->arena, sizeof(uintptr_t), _Alignof(uintptr_t),
                    profile->profile.n_sample_type);

    {
      Perftools__Profiles__ValueType *value_type =
          arena_alloc(&profile->arena, sizeof(Perftools__Profiles__ValueType),
                      _Alignof(Perftools__Profiles__ValueType), 1);
      *value_type =
          (Perftools__Profiles__ValueType)PERFTOOLS__PROFILES__VALUE_TYPE__INIT;

      value_type->type = string_allocations_index;
      value_type->unit = string_count_index;
      profile->profile.sample_type[0] = value_type;
    }
    {
      Perftools__Profiles__ValueType *value_type =
          arena_alloc(&profile->arena, sizeof(Perftools__Profiles__ValueType),
                      _Alignof(Perftools__Profiles__ValueType), 1);

      *value_type =
          (Perftools__Profiles__ValueType)PERFTOOLS__PROFILES__VALUE_TYPE__INIT;
      value_type->unit = string_bytes_index;
      value_type->type = string_space_index;
      profile->profile.sample_type[1] = value_type;
    }
  }
  // TODO: time_nanos, duration_nanos

  // period_type
  {
    Perftools__Profiles__ValueType *value_type =
        arena_alloc(&profile->arena, sizeof(Perftools__Profiles__ValueType),
                    _Alignof(Perftools__Profiles__ValueType), 1);
    *value_type =
        (Perftools__Profiles__ValueType)PERFTOOLS__PROFILES__VALUE_TYPE__INIT;

    value_type->type = string_space_index;
    value_type->unit = string_bytes_index;

    profile->profile.period_type = value_type;
  }

  // sample
  {
    profile->profile.n_sample = 1; // FIXME
    profile->profile.sample =
        arena_alloc(&profile->arena, sizeof(uintptr_t), _Alignof(uintptr_t),
                    profile->profile.n_sample_type);

    {

      Perftools__Profiles__Sample *sample =
          arena_alloc(&profile->arena, sizeof(Perftools__Profiles__Sample),
                      _Alignof(Perftools__Profiles__Sample), 1);

      *sample = (Perftools__Profiles__Sample)PERFTOOLS__PROFILES__SAMPLE__INIT;

      sample->n_value = profile->profile.n_sample_type;
      sample->value = arena_alloc(&profile->arena, sizeof(i64), _Alignof(i64),
                                  sample->n_value);

      sample->value[0] = 1;
      sample->value[1] = 42; // FIXME

      // FIXME
      {
        u64 call_stack[64] = {0};
        u64 call_stack_len = ut_record_call_stack(
            call_stack, sizeof(call_stack) / sizeof(call_stack[0]));
        pg_assert(call_stack_len >= 2);

        sample->n_location_id = call_stack_len;
        sample->location_id = arena_alloc(&profile->arena, sizeof(u64),
                                          _Alignof(u64), sample->n_location_id);

        profile->profile.n_location = call_stack_len;
        profile->profile.location =
            arena_alloc(&profile->arena, sizeof(uintptr_t), _Alignof(uintptr_t),
                        profile->profile.n_location);

        u64 glocation_id = 0;
        for (u64 i = 0; i < call_stack_len; i++) {
          u64 address = call_stack[i];

          Perftools__Profiles__Location *location = arena_alloc(
              &profile->arena, sizeof(Perftools__Profiles__Location),
              _Alignof(Perftools__Profiles__Location), 1);
          *location = (Perftools__Profiles__Location)
              PERFTOOLS__PROFILES__LOCATION__INIT;
          location->id = glocation_id++;
          location->address = address;
          profile->profile.location[i] = location;

          sample->location_id[i] = location->id;
        }
      }

      profile->profile.sample[0] = sample;
    }
  }

  // Serialize.
  {
    u64 pack_size =
        perftools__profiles__profile__get_packed_size(&profile->profile);
    u8 *buf = arena_alloc(&profile->arena, sizeof(u8), _Alignof(u8), pack_size);
    perftools__profiles__profile__pack(&profile->profile, buf);

    int fd = open("profile.pb", O_WRONLY | O_CREAT | O_TRUNC, 0700);
    if (fd == -1) {
      abort();
    }
    pg_assert(write(fd, buf, pack_size) == (isize)pack_size);

    close(fd);
  }
}
