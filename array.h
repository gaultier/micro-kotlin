#pragma once
#include "arena.h"

// --------------------------- Array

typedef struct pg_array_header_t {
  u64 len;
  u64 cap;
} pg_array_header_t;

#define pg_array_t(Type) Type *
#define pg_array_header(x) (((pg_array_header_t *)((void *)x)) - 1)
#define pg_array_len(x) (((x) == NULL) ? 0 : (pg_array_header(x)->len))
#define pg_array_cap(x) (pg_array_header(x)->cap)

#define pg_array_init_reserve(x, arg_capacity, arg_arena)                      \
  do {                                                                         \
    u64 capacity = pg_max((u64)(arg_capacity), 8);                             \
    pg_array_header_t *pg__ah = (pg_array_header_t *)arena_alloc(              \
        arg_arena,                                                             \
        sizeof(pg_array_header_t) + sizeof(*(x)) * ((u64)(capacity)),          \
        _Alignof(pg_array_header_t), 1);                                       \
    pg__ah->len = 0;                                                           \
    pg__ah->cap = capacity;                                                    \
    x = (void *)(pg__ah + 1);                                                  \
    pg_assert((u64)x == (u64)pg__ah + 2 * sizeof(u64));                        \
    pg_assert(pg_array_cap(x) == capacity);                                    \
    pg_assert(pg_array_len(x) == 0);                                           \
  } while (0)

#define pg_array_last_index(x) (pg_array_len(x) - 1)
#define pg_array_last(x) (&(x)[pg_array_last_index(x)])
#define pg_array_drop_last(x)                                                  \
  do {                                                                         \
    pg_assert(x != NULL);                                                      \
    pg_assert(pg_array_len(x) > 0);                                            \
    pg_array_header(x)->len -= 1;                                              \
  } while (0)

#define pg_array_clear(x) pg_array_header(x)->len = 0

#define pg_array_clone(dst, src, arena)                                        \
  do {                                                                         \
    pg_array_init_reserve(dst, pg_array_len(src), arena);                      \
    pg_array_header(dst)->len = pg_array_len(src);                             \
    if (pg_array_len(src) > 0)                                                 \
      memmove(dst, src, pg_array_len(src) * sizeof(src[0]));                   \
  } while (0)

#define pg_array_append(x, item, arena)                                        \
  do {                                                                         \
    if (x == NULL)                                                             \
      pg_array_init_reserve(x, 64, arena);                                     \
    pg_assert(pg_array_len(x) <= pg_array_cap(x));                             \
    if (pg_array_len(x) == pg_array_cap(x)) {                                  \
      pg_assert(pg_array_cap(x) >= 8);                                         \
      const u64 new_cap = pg_array_cap(x) * 2;                                 \
      LOG("%s:%d: grow: old_cap=%lu new_cap=%lu len=%lu", __FILE__, __LINE__,  \
          pg_array_cap(x), new_cap, pg_array_len(x));                          \
      const u64 old_physical_len =                                             \
          sizeof(pg_array_header_t) + sizeof(*(x)) * pg_array_cap(x);          \
      const u64 new_physical_len =                                             \
          sizeof(pg_array_header_t) + sizeof(*(x)) * new_cap;                  \
      pg_array_header_t *const pg__ah = arena_alloc(                           \
          arena, new_physical_len, _Alignof(pg_array_header_t), 1);            \
      LOG("grow: old_physical_len=%lu new_physical_len=%lu old_ptr=%p "        \
          "new_ptr=%p diff=%lu",                                               \
          old_physical_len, new_physical_len, (void *)pg_array_header(x),      \
          (void *)pg__ah, (u64)pg__ah - (u64)pg_array_header(x));              \
      pg_assert((u64)pg__ah >= (u64)pg_array_header(x) + old_physical_len);    \
      memmove(pg__ah, pg_array_header(x), old_physical_len);                   \
      x = (void *)(pg__ah + 1);                                                \
      pg_array_header(x)->cap = new_cap;                                       \
    }                                                                          \
    (x)[pg_array_header(x)->len++] = (item);                                   \
  } while (0)

#define pg_array_drop_last_n(x, n)                                             \
  do {                                                                         \
    for (u64 i = 0; i < n; i++)                                                \
      pg_array_drop_last(x);                                                   \
  } while (0)

#define pg_array_swap_remove_at(x, i)                                          \
  do {                                                                         \
    pg_assert(i < pg_array_len(x));                                            \
    x[i] = x[pg_array_len(x) - 1]; /* Swap. */                                 \
    pg_array_drop_last(x);                                                     \
  } while (0)

// --------------

#define Array32(T) Array32_##T

#define Array32_struct(T)                                                      \
  typedef struct {                                                             \
    u32 len, cap;                                                              \
    T *data;                                                                   \
  } Array32(T);

#define array32_make(T, _len, _cap, _arena)                                    \
  ((Array32(T)){                                                               \
      .len = _len,                                                             \
      .cap = _cap,                                                             \
      .data = arena_alloc(_arena, sizeof(T), _Alignof(T), _cap),               \
  })

static void array32_grow(u32 len, u32 *cap, void **data, u32 item_size,
                         u32 item_align, Arena *arena) {
  *cap = *cap == 0 ? 16 : *cap * 2;
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

#define array32_make_from_c(T, src, _len, arena)                               \
  ((Array32(T)){                                                               \
      .len = _len,                                                             \
      .cap = _len,                                                             \
      .data = ((_len) > 0)                                                     \
                  ? memcpy(arena_alloc(arena, sizeof(T), _Alignof(T), _len),   \
                           (void *)src, (_len) * sizeof(T))                    \
                  : NULL,                                                      \
  })

#define array32_is_empty(array) (array.len == 0)

#define array32_last(array)                                                    \
  (pg_assert(!array32_is_empty(array) && (array).data != NULL),                \
   &(array).data[(array).len - 1])

#define array32_penultimate(array)                                             \
  (pg_assert((array).len >= 2 && (array).data != NULL),                        \
   &(array).data[(array).len - 2])

#define array32_last_index(array)                                              \
  (pg_assert(!array32_is_empty(array)), (array).len - 1)

#define array32_clear(array) (array)->len = 0

#define array32_drop(array, n)                                                 \
  (pg_assert(n <= (array)->len), (array)->len -= (n),                          \
   memset(&(array)->data[(array)->len], 0, (n) * sizeof((array)->data[0])))

#define array32_clone(T, dst, src, arena)                                      \
  do {                                                                         \
    *(dst) = array32_make(T, (src).len, (src).len, arena);                     \
    if ((src).len > 0)                                                         \
      memcpy((dst)->data, (src).data, sizeof((src).data[0]) * (src).len);      \
  } while (0)

Array32_struct(_Bool);
typedef Array32(_Bool) Array32(bool);
Array32_struct(u8);
Array32_struct(u16);
Array32_struct(u32);
Array32_struct(u64);
Array32_struct(usize);
Array32_struct(isize);

// ----------------------

typedef struct List List;
struct List {
  List *next;
  List *last;
};

#define LIST List *next, *last

#define list_append(_list, _new)                                               \
  do {                                                                         \
    List *list = (List *)_list;                                                \
    List *new = (List *)_new;                                                  \
    List *last = list->last ? list->last : list;                               \
    list->last = last->next = new;                                             \
  } while (0)

#define list_for_each(l) for (List *it = l; it; it = it->next)
