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
        arg_arena, 1,                                                          \
        sizeof(pg_array_header_t) + sizeof(*(x)) * ((u64)(capacity)),          \
        ALLOCATION_ARRAY);                                                     \
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
      memcpy(dst, src, pg_array_len(src) * sizeof(src[0]));                    \
  } while (0)

#define pg_array_append(x, item, arena)                                        \
  do {                                                                         \
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
      pg_array_header_t *const pg__ah =                                        \
          arena_alloc(arena, 1, new_physical_len, ALLOCATION_ARRAY);           \
      LOG("grow: old_physical_len=%lu new_physical_len=%lu old_ptr=%p "        \
          "new_ptr=%p diff=%lu",                                               \
          old_physical_len, new_physical_len, (void *)pg_array_header(x),      \
          (void *)pg__ah, (u64)pg__ah - (u64)pg_array_header(x));              \
      pg_assert((u64)pg__ah >= (u64)pg_array_header(x) + old_physical_len);    \
      memcpy(pg__ah, pg_array_header(x), old_physical_len);                    \
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
