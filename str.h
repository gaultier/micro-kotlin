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

typedef struct {
  u64 value;
} mem_address;

/* typedef struct { */
/* } mem_unique_string_array; */

/* typedef struct { */
/* } mem_native_symbol_table; */

typedef struct {
  str name, path, debug_name, debug_path, breakpad_id;
} mem_lib;

typedef struct {
  i64 value;
} mem_string_table_index;

typedef struct {
  u64 value;
} mem_lib_index;

typedef struct {
  u64 value;
} mem_bytes;

typedef struct {
  u64 length;
  mem_lib_index *lib;
  mem_string_table_index *name;
} mem_resource_table;

typedef struct {
  i64 value;
} mem_resource_table_index;

typedef struct {
  i64 value;
} mem_stack_table_index;

typedef struct {
  u64 value;
} mem_frame_table_index;

typedef struct {
  u64 value;
} mem_func_table_index;

typedef struct {
  u64 value;
} mem_category_list_index;

typedef struct {
  u64 length;
  mem_string_table_index *name;
  mem_resource_table_index *resource;
} mem_func_table;

typedef struct {
  u64 length;
  mem_address *address;
  mem_func_table_index *func;
} mem_frame_table;

typedef struct {
  float value;
} mem_milliseconds;

typedef struct {
  mem_milliseconds *time;
  mem_bytes *weight;
  mem_stack_table_index *stack;
  u64 length;
} mem_unbalanced_native_allocations_table;

typedef struct {
  u64 length;
  mem_frame_table_index *frame;
  mem_category_list_index *category;
  mem_stack_table_index *prefix;
} mem_stack_table;

typedef struct {
  mem_unbalanced_native_allocations_table native_allocations;
  mem_stack_table stack_table;
  mem_frame_table frame_table;
  /* mem_unique_string_array string_table; */
  mem_func_table func_table;
  mem_resource_table resource_table;
  /* mem_native_symbol_table native_symbols; */
} mem_thread;

typedef struct {
} mem_meta;

struct mem_profile {
  arena_t arena;
  mem_meta meta;
  mem_thread thread[1];
};

// TODO: Maybe use varints to reduce the size.
static u8 ut_record_call_stack(u64 *dst, u64 cap) {
  uintptr_t *rbp = __builtin_frame_address(0);

  u64 len = 0;

  while (rbp != 0 && ((u64)rbp & 7) == 0 && *rbp != 0) {
    const uintptr_t rip = *(rbp + 1);
    rbp = (uintptr_t *)*rbp;

    if (len >= cap)
      return len;

    dst[len++] = rip;
  }
  return len;
}

u64 mem_frame_table_add_address(mem_frame_table *frame_table,
                                mem_address address, arena_t *arena) {
  for (u64 i = 0; i < frame_table->length; i++) {
    if (frame_table->address[i].value == address.value)
      return i;
  }

  pg_array_append(frame_table->address, address, arena);
  pg_array_append(frame_table->func, (mem_func_table_index){0},
                  arena); // FIXME
  return frame_table->length++;
}

mem_stack_table_index mem_add_or_find_address(mem_thread *t,
                                              mem_address address,
                                              mem_stack_table_index parent,
                                              arena_t *arena) {
  // Either we don't know who is the parent, or we know there is none.
  // TODO: Optimize the latter by skipping the search?
  if (parent.value == -1) {
    for (i64 i = t->stack_table.length - 1; i >= 0; i--) {
      mem_frame_table_index frame_table_index = t->stack_table.frame[i];
      mem_address frame_address =
          t->frame_table.address[frame_table_index.value];

      if (frame_address.value == address.value)
        return (mem_stack_table_index){i};
    }
  }

  // No parent: This is the root. Insert the relevant entries.

  pg_array_append(t->frame_table.address, address, arena);
  pg_array_append(t->frame_table.func, (mem_func_table_index){0}, arena);
  mem_frame_table_index frame_table_index =
      (mem_frame_table_index){t->frame_table.length};
  t->frame_table.length += 1;

  pg_array_append(t->stack_table.frame, frame_table_index, arena);
  pg_array_append(t->stack_table.category, (mem_category_list_index){0},
                  arena); // FIXME?
  pg_array_append(t->stack_table.prefix, (mem_stack_table_index){-1}, arena);

  mem_stack_table_index res = {t->stack_table.length};
  t->stack_table.length += 1;

  return res;
}

void mem_profile_record(mem_profile *profile, u64 bytes_count) {
  u64 call_stack[64] = {0};
  u64 call_stack_len = ut_record_call_stack(
      call_stack, sizeof(call_stack) / sizeof(call_stack[0]));
  pg_assert(call_stack_len >= 2);

  mem_thread *t = &profile->thread[0];
  mem_unbalanced_native_allocations_table *allocs = &t->native_allocations;

  struct timeval tv = {0};
  gettimeofday(&tv, NULL);
  u64 now = (float)tv.tv_sec + (float)tv.tv_usec / 1000.0f;
  pg_array_append(allocs->time, (mem_milliseconds){now}, &profile->arena);

  pg_array_append(allocs->weight, (mem_bytes){bytes_count}, &profile->arena);

  mem_stack_table_index stack_table_index = {-1};
  // Insert whole call chain starting from the root caller to be used then in
  // its callee, and so on.
  for (i64 i = call_stack_len - 1; i >= 0; i--) {
    mem_address address = (mem_address){call_stack[i]};
    // TODO: Potential optimization: if we just inserted the parent, pass
    // `stack_table_index` as prefix!
    stack_table_index =
        mem_add_or_find_address(t, address, stack_table_index, &profile->arena);
  }
  pg_assert(stack_table_index.value != -1);

  pg_array_append(allocs->stack, stack_table_index, &profile->arena);

  allocs->length += 1;
}

void mem_profile_write(mem_profile *profile, FILE *out) {
  pg_assert(profile->thread[0].func_table.length == 0);
  pg_assert(profile->thread[0].resource_table.length == 0);

  profile->thread[0].func_table.length = 1;

  pg_array_append(profile->thread[0].func_table.name,
                  (mem_string_table_index){-1}, &profile->arena);
  pg_array_append(profile->thread[0].func_table.resource,
                  (mem_resource_table_index){-1}, &profile->arena);

  fwrite("{\n", 1, 2, out);

  // meta
  {
    str meta_key = str_from_c("\"meta\":{");
    fwrite(meta_key.data, 1, meta_key.len, out);

    str categories = str_from_c(""
                                "\"categories\": [\n"
                                "{\n"
                                "\"name\": \"Other\",\n"
                                "\"color\": \"grey\",\n"
                                "\"subcategories\": [\n"
                                "\"Other\"\n"
                                "]\n"
                                "},\n"
                                "{\n"
                                "\"name\": \"User\",\n"
                                "\"color\": \"yellow\",\n"
                                "\"subcategories\": [\n"
                                "\"Other\"\n"
                                "]\n"
                                "},\n"
                                "{\n"
                                "\"name\": \"Kernel\",\n"
                                "\"color\": \"orange\",\n"
                                "\"subcategories\": [\n"
                                "\"Other\"\n"
                                "]\n"
                                "}\n"
                                "],\n"
                                "\"debug\": false,\n"
                                "\"extensions\": {\n"
                                "\"baseURL\": [],\n"
                                "\"id\": [],\n"
                                "\"length\": 0,\n"
                                "\"name\": []\n"
                                "}\n"
                                ",\n"
                                "\"interval\": 1,\n"
                                "\"preprocessedProfileVersion\": 44,\n"
                                "\"processType\": 0,\n"
                                "\"product\": \"./micro-kotlin\",\n"
                                "\"sampleUnits\": {\n"
                                "\"eventDelay\": \"ms\",\n"
                                "\"threadCPUDelta\": \"µs\",\n"
                                "\"time\": \"ms\"\n"
                                "},\n"
                                "\"symbolicated\": false,\n"
                                "\"pausedRanges\": [],\n"
                                "\"version\": 24,\n"
                                "\"usesOnlyOneStackType\": true,\n"
                                "\"doesNotUseFrameImplementation\": true,\n"
                                "\"sourceCodeIsNotOnSearchfox\": true,\n"
                                "\"markerSchema\": []\n");
    fwrite(categories.data, 1, categories.len, out);
    // TODO: startup time?

    fwrite("},\n", 1, 3, out);
  }

  // libs ?
  {}

  // profile
  {
    str threads_key = str_from_c("\"threads\":[{\n");
    fwrite(threads_key.data, 1, threads_key.len, out);

    mem_thread *t = &profile->thread[0];
    // thread
    {

      // frameTable
      {
        str frame_table_key = str_from_c("\"frameTable\":{\n");
        fwrite(frame_table_key.data, 1, frame_table_key.len, out);

        {
          str key = str_from_c("\"length\":");
          fwrite(key.data, 1, key.len, out);
          fprintf(out, "%lu,\n", t->frame_table.length);
        }

        {
          str key = str_from_c("\"address\":[\n");
          fwrite(key.data, 1, key.len, out);
          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "%lu%s", t->frame_table.address[i].value,
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 3, out);
        }

        {
          str key = str_from_c("\"inlineDepth\":[\n");
          fwrite(key.data, 1, key.len, out);
          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "0%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 3, out);
        }

        {
          str key = str_from_c("\"func\":[\n");
          fwrite(key.data, 1, key.len, out);
          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "%lu%s", t->frame_table.func[i].value,
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"nativeSymbol\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"func\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "0%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"category\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "-1%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"subcategory\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "0%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"innerWindowID\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"implementation\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"line\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"column\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"optimizations\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->frame_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->frame_table.length ? "\n" : ",\n");
          }
          fwrite("]\n", 1, 2, out);
        }

        fwrite("},\n", 1, 3, out);
      }

      // funcTable
      {
        str key = str_from_c("\"funcTable\":{\n");
        fwrite(key.data, 1, key.len, out);

        {
          str key = str_from_c("\"length\":");
          fwrite(key.data, 1, key.len, out);
          fprintf(out, "%lu,\n", t->func_table.length);
        }

        {
          str key = str_from_c("\"name\":[");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->func_table.length; i++) {
            fprintf(out, "%ld%s", t->func_table.name[i].value,
                    (i + 1) == t->func_table.length ? "\n" : ",\n");
          }

          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"isJS\":[");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->func_table.length; i++) {
            fprintf(out, "false%s",
                    (i + 1) == t->func_table.length ? "\n" : ",\n");
          }

          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"relevantForJS\":[");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->func_table.length; i++) {
            fprintf(out, "false%s",
                    (i + 1) == t->func_table.length ? "\n" : ",\n");
          }

          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"resource\":[");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->func_table.length; i++) {
            fprintf(out, "%ld%s", t->func_table.resource[i].value,
                    (i + 1) == t->func_table.length ? "\n" : ",\n");
          }

          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"fileName\":[");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->func_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->func_table.length ? "\n" : ",\n");
          }

          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"lineNumber\":[");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->func_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->func_table.length ? "\n" : ",\n");
          }

          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"columnNumber\":[");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->func_table.length; i++) {
            fprintf(out, "null%s",
                    (i + 1) == t->func_table.length ? "\n" : ",\n");
          }

          fwrite("]\n", 1, 2, out);
        }
        fwrite("},\n", 1, 3, out);
      }

      // nativeAllocations
      {

        str key = str_from_c("\"nativeAllocations\":{\n");
        fwrite(key.data, 1, key.len, out);

        {
          str key = str_from_c("\"length\":");
          fwrite(key.data, 1, key.len, out);
          fprintf(out, "%lu,\n", t->native_allocations.length);
        }

        {
          str key = str_from_c("\"weigthType\":\"bytes\",\n");
          fwrite(key.data, 1, key.len, out);
        }

        {
          str key = str_from_c("\"stack\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->native_allocations.length; i++) {
            fprintf(out, "%lu%s", t->native_allocations.stack[i].value,
                    (i + 1) == t->native_allocations.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 3, out);
        }

        {
          str key = str_from_c("\"weight\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->native_allocations.length; i++) {
            fprintf(out, "%lu%s", t->native_allocations.weight[i].value,
                    (i + 1) == t->native_allocations.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 3, out);
        }
        {
          str key = str_from_c("\"time\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->native_allocations.length; i++) {
            fprintf(out, "%f%s", t->native_allocations.time[i].value,
                    (i + 1) == t->native_allocations.length ? "\n" : ",\n");
          }
          fwrite("]\n", 1, 2, out);
        }

        fwrite("},\n", 1, 3, out);
      }

      // stackTable
      {
        str key = str_from_c("\"stackTable\":{\n");
        fwrite(key.data, 1, key.len, out);

        {
          str key = str_from_c("\"length\":");
          fwrite(key.data, 1, key.len, out);
          fprintf(out, "%lu,\n", t->stack_table.length);
        }

        {
          str key = str_from_c("\"prefix\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->stack_table.length; i++) {
            fprintf(out, "%lu%s", t->stack_table.prefix[i].value,
                    (i + 1) == t->stack_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 3, out);
        }

        {
          str key = str_from_c("\"frame\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->stack_table.length; i++) {
            fprintf(out, "%lu%s", t->stack_table.frame[i].value,
                    (i + 1) == t->stack_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 3, out);
        }

        {
          str key = str_from_c("\"category\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->stack_table.length; i++) {
            fprintf(out, "%lu%s", t->stack_table.category[i].value,
                    (i + 1) == t->stack_table.length ? "\n" : ",\n");
          }
          fwrite("],\n", 1, 2, out);
        }

        {
          str key = str_from_c("\"subcategory\":[\n");
          fwrite(key.data, 1, key.len, out);

          for (u64 i = 0; i < t->stack_table.length; i++) {
            fprintf(out, "0%s",
                    (i + 1) == t->stack_table.length ? "\n" : ",\n");
          }
          fwrite("]\n", 1, 2, out);
        }

        fwrite("},\n", 1, 3, out);
      }

      // samples (empty)
      {
        str samples = str_from_c("\"samples\":{\n"
                                 "  \"length\": 0,\n"
                                 "  \"stack\":[],\n"
                                 "  \"time\":[],\n"
                                 "  \"weight\":[],\n"
                                 "  \"weighttype\": \"samples\",\n"
                                 "  \"threadcpudelta\": []\n"
                                 "},\n");
        fwrite(samples.data, 1, samples.len, out);
      }

      // stringsArray
      {
        str strings = str_from_c("\"stringArray\":[],\n");
        fwrite(strings.data, 1, strings.len, out);
      }

      // resourceTable
      {
        str key = str_from_c("\"resourceTable\":{\n");
        fwrite(key.data, 1, key.len, out);

        {
          str key = str_from_c("\"length\":0");
          fwrite(key.data, 1, key.len, out);
        }

        fwrite("},\n", 1, 3, out);
      }

      str thread_trailer =
          str_from_c("\"markers\": {\n"
                     "  \"length\": 0,\n"
                     "  \"category\": [],\n"
                     "  \"data\": [],\n"
                     "  \"endTime\": [],\n"
                     "  \"name\": [],\n"
                     "  \"phase\": [],\n"
                     "  \"startTime\": []\n"
                     "},\n"
                     "\"name\": \"GeckoMain\",\n"
                     "\"nativeSymbols\": {\n"
                     "\"length\": 0,\n"
                     "\"address\": [],\n"
                     "\"functionSize\": [],\n"
                     "\"libIndex\": [],\n"
                     "\"name\": []\n"
                     "},\n"
                     "\"pausedRanges\": [],\n"
                     // "\"pid\": 3676029,\n"
                     // "\"processName\": \"<3676029>\",\n"
                     // "\"processShutdownTime\": 186843702.162049,\n"
                     "\"processStartupTime\": 0,\n"
                     "\"processType\": \"default\",\n"
                     "\"registerTime\": 0\n");
      fwrite(thread_trailer.data, 1, thread_trailer.len, out);
    }

    fwrite("}]\n", 1, 3, out);
  }

  fwrite("}", 1, 1, out);
}
