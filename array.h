#pragma once
#include "arena.h"

// --------------------------- Growable typed array

#define Array32(T) Array32_##T

#define Array32_struct(T)                                                      \
  typedef struct {                                                             \
    u32 len, cap;                                                              \
    T *data;                                                                   \
  } Array32(T);

#define array32_make(T, _len, _cap, _arena)                                    \
  (pg_assert(_len <= _cap),                                                    \
   ((Array32(T)){                                                              \
       .len = _len,                                                            \
       .cap = _cap,                                                            \
       .data = arena_alloc(_arena, sizeof(T), _Alignof(T), _cap),              \
   }))

static void array32_grow(u32 len, u32 *cap, void **data, u32 item_size,
                         u32 item_align, Arena *arena) {
  // Big initial capacity because resizing is costly in an arena.
  *cap = *cap == 0 ? 512 : *cap * 2;
  void *new_data = arena_alloc(arena, item_size, item_align, *cap);
  pg_assert(new_data);

  if (*data && len > 0)
    *data = memcpy(new_data, *data, len * item_size);
  else
    *data = new_data;
}

#define array32_push(array, arena)                                             \
  ((array)->len >= (array)->cap                                                \
   ? array32_grow((array)->len, &(array)->cap, (void **)&(array)->data,        \
                  sizeof(*(array)->data), _Alignof(*(array)->data), arena),    \
   (array)->data + (array)->len++ : (array)->data + (array)->len++)

#define array32_make_from_slice(T, src, _len, arena)                           \
  ((Array32(T)){                                                               \
      .len = _len,                                                             \
      .cap = _len,                                                             \
      .data = ((_len) > 0)                                                     \
                  ? memcpy(arena_alloc(arena, sizeof(T), _Alignof(T), _len),   \
                           (void *)src, (_len) * sizeof(T))                    \
                  : NULL,                                                      \
  })

#define array32_is_empty(array) ((array).len == 0)

#define array32_last(array)                                                    \
  (pg_assert(!array32_is_empty(array) && (array).data != NULL),                \
   &(array).data[(array).len - 1])

#define array32_penultimate(array)                                             \
  (pg_assert((array).len >= 2 && (array).data != NULL),                        \
   &(array).data[(array).len - 2])

#define array32_last_index(array)                                              \
  (pg_assert(!array32_is_empty(array)), (array).len - 1)

#define array32_clear(array) ((array)->len = 0)

#define array32_drop(array, n)                                                 \
  (pg_assert(n <= (array)->len), (array)->len -= (n),                          \
   memset(&(array)->data[(array)->len], 0, (n) * sizeof((array)->data[0])))

#define array32_clone(T, dst, src, arena)                                      \
  do {                                                                         \
    *(dst) = array32_make(T, (src).len, (src).len, arena);                     \
    if ((src).len > 0)                                                         \
      memcpy((dst)->data, (src).data, sizeof((src).data[0]) * (src).len);      \
  } while (0)

#define array32_remove_at_unordered(array, i)                                  \
  do {                                                                         \
    pg_assert(i < (array)->len);                                               \
    (array)->data[i] = *array32_last(*(array)); /* Swap. */                    \
    array32_drop(array, 1);                                                    \
  } while (0)

#define array32_append_slice(array, src, src_len)

Array32_struct(_Bool);
typedef Array32(_Bool) Array32(bool);
Array32_struct(u8);
Array32_struct(u16);
Array32_struct(u32);
Array32_struct(u64);
Array32_struct(usize);
Array32_struct(isize);

// ----------------------
