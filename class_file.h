#pragma once

#include "arena.h"
#include "array.h"
#include "str.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#ifdef WITH_ZLIB
#include <zlib.h>
#endif

typedef enum {
  HANDLE_FLAGS_AST = 1 << 31,
  HANDLE_FLAGS_TYPE = 1 << 30,
} Handle_flags;

typedef struct {
  u32 value;
} Ast_handle;
Array32_struct(Ast_handle);

static const Ast_handle ast_handle_nil = {0};

static bool ast_handle_is_nil(Ast_handle handle) { return handle.value == 0; }

typedef struct {
  u32 value;
} Type_handle;
Array32_struct(Type_handle);

static const Type_handle type_handle_nil = {0};
static bool type_handle_handles_nil(Type_handle handle) {
  return handle.value == 0;
}

static Array32(Str)
    class_path_string_to_class_path_entries(Str class_path, Arena *arena) {
  pg_assert(!str_is_empty(class_path));

  const u8 sep = ':';
  const u32 sep_count = str_count(class_path, sep);
  Array32(Str) entries = array32_make(Str, 0, sep_count, arena);

  Str_split_result split = {.right = class_path};
  do {
    split = str_split(split.right, sep);
    if (!str_is_empty(split.left))
      *array32_push(&entries, arena) = split.left;
  } while (split.found);

  // Ensure "." is in the array so that it will be searched (but also do not
  // duplicate it).
  {
    bool found = false;
    Str needle = str_from_c(".");

    for (u64 i = 0; i < entries.len; i++) {
      if (str_eq(entries.data[i], needle)) {
        found = true;
        break;
      }
    }

    if (!found)
      *array32_push(&entries, arena) = needle;
  }

  return entries;
}

// ------------------------ Class file code

typedef enum __attribute__((packed)) {
  BYTECODE_NOP = 0x00,
  BYTECODE_ALOAD_0 = 0x2a,
  BYTECODE_GET_STATIC = 0xb2,
  BYTECODE_BIPUSH = 0x10,
  BYTECODE_LDC = 0x12,
  BYTECODE_LDC_W = 0x13,
  BYTECODE_LDC2_W = 0x14,
  BYTECODE_ILOAD = 0x15,
  BYTECODE_LLOAD = 0x16,
  BYTECODE_ALOAD = 0x19,
  BYTECODE_LLOAD_0 = 0x1e,
  BYTECODE_LLOAD_1 = 0x1f,
  BYTECODE_LLOAD_2 = 0x20,
  BYTECODE_LLOAD_3 = 0x21,
  BYTECODE_ILOAD_0 = 0x1a,
  BYTECODE_ILOAD_1 = 0x1b,
  BYTECODE_ILOAD_3 = 0x1c,
  BYTECODE_ISTORE = 0x36,
  BYTECODE_LSTORE = 0x37,
  BYTECODE_ASTORE = 0x3a,
  BYTECODE_ISTORE_0 = 0x3b,
  BYTECODE_ISTORE_1 = 0x3c,
  BYTECODE_ISTORE_2 = 0x3d,
  BYTECODE_ISTORE_3 = 0x3e,
  BYTECODE_POP = 0x57,
  BYTECODE_IADD = 0x60,
  BYTECODE_LADD = 0x61,
  BYTECODE_IMUL = 0x68,
  BYTECODE_LMUL = 0x69,
  BYTECODE_IDIV = 0x6c,
  BYTECODE_LDIV = 0x6d,
  BYTECODE_IREM = 0x70,
  BYTECODE_LREM = 0x71,
  BYTECODE_INEG = 0x74,
  BYTECODE_LNEG = 0x75,
  BYTECODE_IAND = 0x7e,
  BYTECODE_LAND = 0x7f,
  BYTECODE_IOR = 0x80,
  BYTECODE_LOR = 0x80,
  BYTECODE_IXOR = 0x82,
  BYTECODE_I2L = 0x85,
  BYTECODE_LCMP = 0x94,
  BYTECODE_IFEQ = 0x99,
  BYTECODE_IFNE = 0x9a,
  BYTECODE_IF_ICMPEQ = 0x9f,
  BYTECODE_IF_ICMPNE = 0xa0,
  BYTECODE_IF_ICMPLT = 0xa1,
  BYTECODE_IF_ICMPGE = 0xa2,
  BYTECODE_IF_ICMPGT = 0xa3,
  BYTECODE_IF_ICMPLE = 0xa4,
  BYTECODE_GOTO = 0xa7,
  BYTECODE_IRETURN = 0xac,
  BYTECODE_LRETURN = 0xad,
  BYTECODE_RETURN = 0xb1,
  BYTECODE_INVOKE_VIRTUAL = 0xb6,
  BYTECODE_INVOKE_SPECIAL = 0xb7,
  BYTECODE_INVOKE_STATIC = 0xb8,
  BYTECODE_IMPDEP1 = 0xfe,
  BYTECODE_IMPDEP2 = 0xff,
} Jvm_bytecode;

typedef struct {
  u32 scope_depth;
  Ast_handle var_definition_ast_handle;
  Str name;
} Type_variable;
Array32_struct(Type_variable);

typedef enum __attribute__((packed)) {
  VERIFICATION_INFO_TOP = 0,
  VERIFICATION_INFO_INT = 1,
  VERIFICATION_INFO_FLOAT = 2,
  VERIFICATION_INFO_DOUBLE = 3,
  VERIFICATION_INFO_LONG = 4,
  VERIFICATION_INFO_NULL = 6,
  VERIFICATION_INFO_OBJECT = 7,
  VERIFICATION_INFO_UNINITIALIZED = 8,
} Jvm_verification_info_kind;

typedef struct {
  Jvm_verification_info_kind kind;
  pg_pad(1);
  u16 extra_data;
} Jvm_verification_info;
Array32_struct(Jvm_verification_info);

typedef struct {
  Ast_handle ast_handle;
  Type_handle type_handle;
  u32 scope_depth;
  Jvm_verification_info verification_info;
} Jvm_variable;
Array32_struct(Jvm_variable);

struct codegen_frame;
typedef struct codegen_frame codegen_frame;
typedef struct {
  u16 pc;
  // TODO: Should we actually memoize this or not?
  u16 offset_delta;
  bool tombstone; // Skip in case of duplicates.
  u8 kind;
  pg_pad(2);
  // Immutable clone of the frame when the stack map
  // frame was created.
  codegen_frame *frame;
} Stack_map_frame;
Array32_struct(Stack_map_frame);

static char *const CONSTRUCTOR_JVM_NAME = "<init>";

struct codegen_frame {
  Array32(Jvm_variable) locals;
  Array32(Jvm_verification_info) stack;
  u16 max_physical_stack;
  u16 max_physical_locals;
  u32 scope_depth;
  u16 locals_physical_count;
  u16 stack_physical_count;
  pg_pad(4);
};

struct Jvm_constant_pool;
typedef struct Jvm_constant_pool Jvm_constant_pool;

typedef struct {
  u16 start_pc;
  u16 end_pc;
  u16 handler_pc;
  u16 catch_type;
} Jvm_exception;
Array32_struct(Jvm_exception);

typedef enum __attribute__((packed)) {
  AST_KIND_NONE,
  AST_KIND_NUMBER,
  AST_KIND_BOOL,
  AST_KIND_FUNCTION_DEFINITION,
  AST_KIND_FUNCTION_PARAMETER,
  AST_KIND_TYPE,
  AST_KIND_BINARY,
  AST_KIND_ASSIGNMENT,
  AST_KIND_THEN_ELSE,
  AST_KIND_UNARY,
  AST_KIND_VAR_DEFINITION,
  AST_KIND_VAR_REFERENCE,
  AST_KIND_CLASS_REFERENCE,
  AST_KIND_IF,
  AST_KIND_LIST,
  AST_KIND_WHILE_LOOP,
  AST_KIND_STRING,
  AST_KIND_NAVIGATION,
  AST_KIND_UNRESOLVED_NAME,
  AST_KIND_RETURN,
  AST_KIND_CALL,
  AST_KIND_MAX,
} Ast_kind;

static Str ast_kind_to_string[AST_KIND_MAX] = {
    [AST_KIND_NONE] = str_from_c_literal("NONE"),
    [AST_KIND_NUMBER] = str_from_c_literal("NUMBER"),
    [AST_KIND_BOOL] = str_from_c_literal("BOOL"),
    [AST_KIND_FUNCTION_DEFINITION] = str_from_c_literal("FUNCTION_DEFINITION"),
    [AST_KIND_FUNCTION_PARAMETER] = str_from_c_literal("FUNCTION_PARAMETER"),
    [AST_KIND_TYPE] = str_from_c_literal("TYPE"),
    [AST_KIND_BINARY] = str_from_c_literal("BINARY"),
    [AST_KIND_ASSIGNMENT] = str_from_c_literal("ASSIGNMENT"),
    [AST_KIND_THEN_ELSE] = str_from_c_literal("THEN_ELSE"),
    [AST_KIND_UNARY] = str_from_c_literal("UNARY"),
    [AST_KIND_VAR_DEFINITION] = str_from_c_literal("VAR_DEFINITION"),
    [AST_KIND_VAR_REFERENCE] = str_from_c_literal("VAR_REFERENCE"),
    [AST_KIND_CLASS_REFERENCE] = str_from_c_literal("CLASS_REFERENCE"),
    [AST_KIND_IF] = str_from_c_literal("IF"),
    [AST_KIND_LIST] = str_from_c_literal("LIST"),
    [AST_KIND_WHILE_LOOP] = str_from_c_literal("WHILE_LOOP"),
    [AST_KIND_STRING] = str_from_c_literal("STRING"),
    [AST_KIND_NAVIGATION] = str_from_c_literal("NAVIGATION"),
    [AST_KIND_UNRESOLVED_NAME] = str_from_c_literal("UNRESOLVED_NAME"),
    [AST_KIND_RETURN] = str_from_c_literal("RETURN"),
    [AST_KIND_CALL] = str_from_c_literal("CALL"),
};

enum __attribute__((packed)) Type_kind {
  TYPE_ANY = 0,
  TYPE_UNIT = 1 << 0,
  TYPE_BOOLEAN = 1 << 1,
  TYPE_BYTE = 1 << 2,
  TYPE_CHAR = 1 << 3,
  TYPE_SHORT = 1 << 4,
  TYPE_INT = 1 << 5,
  TYPE_FLOAT = 1 << 6,
  TYPE_LONG = 1 << 7,
  TYPE_DOUBLE = 1 << 8,
  TYPE_STRING = 1 << 9,
  TYPE_METHOD = 1 << 10,
  TYPE_INSTANCE = 1 << 11,
  TYPE_ARRAY = 1 << 12,
  TYPE_INTEGER_LITERAL = 1 << 13,
  TYPE_CONSTRUCTOR = 1 << 14,
};

typedef enum Type_kind Type_kind;
typedef struct {
  Str name;
  Str source_file_name;
  Array32(u8) code;                 // In case of InlineOnly.
  Jvm_constant_pool *constant_pool; // In case of InlineOnly.
  Array32(Type_handle) argument_type_handles;
  Type_handle return_type_handle;
  Type_handle this_class_type_handle;
  // TODO: Move to `type.flags` to reduce size?
  u16 access_flags;
  u16 source_line;
  pg_pad(4);
} Method;

typedef enum {
  TYPE_FLAG_INLINE_ONLY = 1 << 10,
} Type_flag;

struct Type {
  Str this_class_name;
  Str super_class_name;
  Str package_name;
  union {
    Method method;                 // TYPE_METHOD, TYPE_CONSTRUCTOR
    Type_handle array_type_handle; // TYPE_ARRAY_REFERENCE
    u16 integer_literal_types;     // TYPE_INTEGER_LITERAL: OR'ed integer types.
  } v;
  Type_kind kind;
  u16 flags;
  Type_handle super_type_handle;
  Type_handle list_next;
  pg_pad(4);
};

typedef struct Type Type;
Array32_struct(Type);

// TODO: compact fields.
typedef struct Ast Ast;
struct Ast {
  u32 main_token_i;
  Ast_handle lhs;
  Ast_handle rhs;
  Type_handle type_handle; // TODO: should it be separate?
  Array32(Ast_handle) nodes;
  u64 extra_data;
  u16 flags;
  Ast_kind kind;
  pg_pad(1);
  Ast_handle return_type_ast; // Type if it's a function definition and the
                              // return type was specified.
};
Array32_struct(Ast);

static Ast_handle new_ast(const Ast *ast, Arena *arena) {
  Ast *const ast_ptr = arena_alloc(arena, sizeof(Ast), _Alignof(Ast), 1);
  *ast_ptr = *ast;

  const u32 offset = arena_offset_from_end(ast_ptr, *arena);

  pg_assert((offset & ((u32)1 << (32 - 3))) == 0);

  return (Ast_handle){offset | (u32)HANDLE_FLAGS_AST};
}

static Ast *ast_handle_to_ptr(Ast_handle handle, Arena arena) {
  pg_assert((handle.value & (u32)HANDLE_FLAGS_AST) == (u32)HANDLE_FLAGS_AST);

  handle.value &= ~(u32)HANDLE_FLAGS_AST;
  pg_assert(((u8 *)(u64)handle.value) < arena.end);

  return (Ast *)(arena.end - handle.value);
}

static Type_handle new_type(const Type *type, Arena *arena) {
  Type *const type_ptr = arena_alloc(arena, sizeof(Type), _Alignof(Type), 1);
  *type_ptr = *type;

  const u32 offset = arena_offset_from_end(type_ptr, *arena);

  pg_assert((offset & ((u32)1 << (32 - 3))) == 0);

  return (Type_handle){offset | (u32)HANDLE_FLAGS_TYPE};
}

static Type *type_handle_to_ptr(Type_handle handle, Arena arena) {
  pg_assert((handle.value & (u32)HANDLE_FLAGS_TYPE) == (u32)HANDLE_FLAGS_TYPE);

  handle.value &= ~(u32)HANDLE_FLAGS_TYPE;
  pg_assert(((u8 *)(u64)handle.value) < arena.end);

  return (Type *)(arena.end - handle.value);
}

typedef enum __attribute__((packed)) {
  PARSER_STATE_OK,
  PARSER_STATE_ERROR,
  PARSER_STATE_PANIC,
  PARSER_STATE_SYNCED,
} Parser_state;

typedef enum __attribute__((packed)) {
  TOKEN_KIND_NONE,
  TOKEN_KIND_NUMBER,
  TOKEN_KIND_PLUS,
  TOKEN_KIND_MINUS,
  TOKEN_KIND_STAR,
  TOKEN_KIND_SLASH,
  TOKEN_KIND_PERCENT,
  TOKEN_KIND_AMPERSAND,
  TOKEN_KIND_AMPERSAND_AMPERSAND,
  TOKEN_KIND_PIPE,
  TOKEN_KIND_PIPE_PIPE,
  TOKEN_KIND_LEFT_PAREN,
  TOKEN_KIND_RIGHT_PAREN,
  TOKEN_KIND_LEFT_BRACE,
  TOKEN_KIND_RIGHT_BRACE,
  TOKEN_KIND_KEYWORD_FUN,
  TOKEN_KIND_KEYWORD_RETURN,
  TOKEN_KIND_KEYWORD_FALSE,
  TOKEN_KIND_KEYWORD_TRUE,
  TOKEN_KIND_KEYWORD_VAR,
  TOKEN_KIND_KEYWORD_IF,
  TOKEN_KIND_KEYWORD_ELSE,
  TOKEN_KIND_KEYWORD_WHILE,
  TOKEN_KIND_IDENTIFIER,
  TOKEN_KIND_EQUAL,
  TOKEN_KIND_COMMA,
  TOKEN_KIND_DOT,
  TOKEN_KIND_COLON,
  TOKEN_KIND_NOT,
  TOKEN_KIND_EQUAL_EQUAL,
  TOKEN_KIND_NOT_EQUAL,
  TOKEN_KIND_LE,
  TOKEN_KIND_LT,
  TOKEN_KIND_GE,
  TOKEN_KIND_GT,
  TOKEN_KIND_STRING_LITERAL,
} Token_kind;

typedef struct {
  u32 source_offset;
  Token_kind kind;
  pg_pad(3);
} Token;

Array32_struct(Token);

typedef struct {
  Str file_path;
  Array32(Token) tokens;
  Array32(u32) line_table; // line_table[i] is the start offset of the LOC `i+1`
} Lexer;

typedef struct {
  Str buf;
  Lexer *lexer;
  Str current_package;
  Ast_handle current_function_handle;
  u32 buf_len;
  u32 tokens_i;
  Parser_state state;
  pg_pad(3);
} Parser;

typedef struct {
  Type *first_type;
  Type *last_type;

  Parser *parser;
  Str this_class_name;
  Array32(Str) class_path_entries;
  Array32(Str) imported_package_names;
  u64 class_file_loaded_count;
  Array32(Type_variable) variables;
  Type_handle current_type_handle;
  u32 scope_depth;
  Ast_handle current_function_handle;
  pg_pad(4);
} Resolver;

static Str codegen_make_class_name_from_path(Str path, Arena *arena);
static Type_handle resolver_add_type(Resolver *resolver, Type *new_type,
                                     Arena *arena);

static void resolver_init(Resolver *resolver, Parser *parser,
                          Array32(Str) class_path_entries, Str class_file_path,
                          Arena *arena) {

  resolver->parser = parser;

  resolver->first_type =
      type_handle_to_ptr(new_type(&(Type){0}, arena), *arena);
  resolver->last_type = resolver->first_type;

  resolver->class_path_entries = class_path_entries;
  resolver->this_class_name =
      codegen_make_class_name_from_path(class_file_path, arena);

  resolver->variables = array32_make(Type_variable, 0, 512, arena);
  resolver->imported_package_names = array32_make(Str, 0, 256, arena);
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin");

  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin.annotation");
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin.collections");
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin.comparisons");
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin.io");
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin.ranges");
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin.sequences");
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin.text");
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("java.lang");
  *array32_push(&resolver->imported_package_names, arena) =
      str_from_c("kotlin.jvm");
  *array32_push(&resolver->imported_package_names, arena) =
      parser->current_package;
}

static void type_init_package_and_name(Str fully_qualified_jvm_name,
                                       Str *package_name, Str *name,
                                       Arena *arena) {
  Str_split_result slash_rplit_res = str_rsplit(fully_qualified_jvm_name, '/');

  // No package component.
  if (!slash_rplit_res.found) {
    *name = str_clone(fully_qualified_jvm_name, arena);
    return;
  }

  Str_builder package_name_builder = sb_clone(slash_rplit_res.left, arena);
  package_name_builder =
      sb_replace_element_starting_at(package_name_builder, 0, '/', '.');
  *package_name = sb_build(package_name_builder);

  *name = str_clone(slash_rplit_res.right, arena);
}

static const Type *resolver_eval_type(Type_handle in_handle, Arena arena) {
  const Type *const in = type_handle_to_ptr(in_handle, arena);
  if (in->kind != TYPE_METHOD)
    return in;

  return resolver_eval_type(in->v.method.return_type_handle, arena);
}

static bool resolver_is_type_integer(Type_handle type, Arena arena) {
  switch (type_handle_to_ptr(type, arena)->kind) {
  case TYPE_BYTE:
  case TYPE_SHORT:
  case TYPE_INT:
  case TYPE_LONG:
  case TYPE_INTEGER_LITERAL:
    return true;
  default:
    return false;
  }
}

static bool resolver_are_types_equal(const Resolver *resolver,
                                     Type_handle lhs_handle,
                                     Type_handle rhs_handle, Arena arena) {
  if (type_handle_handles_nil(lhs_handle) &&
      type_handle_handles_nil(rhs_handle))
    return true;
  if (type_handle_handles_nil(lhs_handle) &&
      !type_handle_handles_nil(rhs_handle))
    return false;
  if (!type_handle_handles_nil(lhs_handle) &&
      type_handle_handles_nil(rhs_handle))
    return false;

  const Type *const lhs = type_handle_to_ptr(lhs_handle, arena);
  const Type *const rhs = type_handle_to_ptr(rhs_handle, arena);

  if (lhs->kind != rhs->kind)
    return false;

  // Instances: Check the class name is the same.
  if (lhs->kind == TYPE_INSTANCE && rhs->kind == TYPE_INSTANCE) {
    return str_eq(lhs->this_class_name, rhs->this_class_name);
  }

  // Methods: Check that the class name, argument types, and return types, are
  // the same.
  if (lhs->kind == TYPE_METHOD && rhs->kind == TYPE_METHOD) {
    const Method *const lhs_method = &lhs->v.method;
    const Method *const rhs_method = &rhs->v.method;

    if (!str_eq(lhs->this_class_name, rhs->this_class_name))
      return false;

    if (!resolver_are_types_equal(resolver, lhs_method->return_type_handle,
                                  rhs_method->return_type_handle, arena))
      return false;

    if (lhs_method->argument_type_handles.len !=
        rhs_method->argument_type_handles.len)
      return false;

    for (u64 i = 0; i < lhs_method->argument_type_handles.len; i++) {
      const Type_handle lhs_arg_handle =
          lhs_method->argument_type_handles.data[i];
      const Type_handle rhs_arg_handle =
          rhs_method->argument_type_handles.data[i];

      if (!resolver_are_types_equal(resolver, lhs_arg_handle, rhs_arg_handle,
                                    arena))
        return false;
    }

    return true;
  }

  // Otherwise, having the same `kind` is enough.
  return true;
}

static u16 resolver_widen_integer_type(Type_handle type_handle, Arena arena) {
  pg_assert(resolver_is_type_integer(type_handle, arena));

  const Type *const type = type_handle_to_ptr(type_handle, arena);

  if (type->kind == TYPE_INT) {
    return TYPE_INT | TYPE_LONG | TYPE_BYTE | TYPE_SHORT;
  } else if (type->kind == TYPE_SHORT) {
    return TYPE_BYTE | TYPE_SHORT;
  } else {
    return type->kind;
  }
}

static bool resolver_is_integer_type_subtype_of(Type_handle a_handle,
                                                Type_handle b_handle,
                                                Arena arena) {
  pg_assert(resolver_is_type_integer(a_handle, arena));

  const Type *const a = type_handle_to_ptr(a_handle, arena);
  const Type *const b = type_handle_to_ptr(b_handle, arena);

  // Every type is a subtype of Any.
  if (b->kind == TYPE_ANY)
    return true;

  // Integer types are subtypes of nothing else than Any (well to be exact they
  // are subtypes of Comparable but we do not implement interfaces yet).
  if (!resolver_is_type_integer(b_handle, arena))
    return false;

  // > All integer literal type are equivalent w.r.t. subtyping
  // > ILT(T1,…,TK)<:ILT(U1,…,UN)
  // > ILT(U1,…,UN)<:ILT(T1,…,TK)
  // > ∀Ti∈{T1,…,TK}:ILT(T1,…,TK)<:Ti
  // > ∀Ti∈{T1,…,TK}:Ti<:ILT(T1,…,TK)
  if (a->kind == TYPE_INTEGER_LITERAL || b->kind == TYPE_INTEGER_LITERAL)
    return true;

  return (resolver_widen_integer_type(a_handle, arena) &
          resolver_widen_integer_type(b_handle, arena)) ==
         resolver_widen_integer_type(b_handle, arena);
}

static bool resolver_resolve_super_lazily(Resolver *resolver,
                                          Type_handle type_handle,

                                          Arena scratch_arena, Arena *arena);

static bool resolver_is_type_subtype_of(Resolver *resolver,
                                        Type_handle a_handle,
                                        Type_handle b_handle,
                                        Arena scratch_arena, Arena *arena) {

  // `A <: A` always.
  if (resolver_are_types_equal(resolver, a_handle, b_handle, *arena))
    return true;

  const Type *const a = type_handle_to_ptr(a_handle, *arena);
  const Type *const b = type_handle_to_ptr(b_handle, *arena);

  // Every type is a subtype of Any.
  if (b->kind == TYPE_ANY)
    return true;

  // Integers have special rules.
  if (resolver_is_type_integer(a_handle, *arena))
    return resolver_is_integer_type_subtype_of(a_handle, b_handle, *arena);

  switch (a->kind) {
    // Those types are not a subtype of anything (expect Any but we handled that
    // case already).
  case TYPE_METHOD:
  case TYPE_CONSTRUCTOR:
  case TYPE_DOUBLE:
  case TYPE_FLOAT:
  case TYPE_CHAR:
  case TYPE_ANY:
    return false;

  case TYPE_INSTANCE: {
    Type_handle it_handle = a_handle;

    while (true) {
      if (!resolver_resolve_super_lazily(resolver, it_handle, scratch_arena,
                                         arena))
        return false;

      const Type *const it = type_handle_to_ptr(it_handle, *arena);

      if (type_handle_handles_nil(it->super_type_handle))
        return false; // Reached the top

      if (resolver_are_types_equal(resolver, it_handle, b_handle, *arena))
        return true;
    }
    return false;
  }
  case TYPE_STRING: {
    return b->kind == TYPE_INSTANCE && str_eq_c(b->package_name, "java.lang") &&
           str_eq_c(b->this_class_name, "Object");
  }

  default:
    pg_assert(0 && "unreachable");
  }
}

static bool resolver_is_function_candidate_applicable(
    Resolver *resolver, Array32(Type_handle) call_site_argument_types_handle,
    Type_handle function_definition_type_handle, Arena scratch_arena,
    Arena *arena) {
  const Type *const function_definition_type =
      type_handle_to_ptr(function_definition_type_handle, *arena);
  pg_assert(function_definition_type->kind == TYPE_METHOD);

  const Method *definition = &function_definition_type->v.method;

  const u8 call_argument_count = (u8)call_site_argument_types_handle.len;
  const u8 definition_argument_count =
      (u8)definition->argument_type_handles.len;

  // Technically there is no such check in the spec but since we do not
  // implement varargs or default arguments yet, this will do for now.
  if (call_argument_count != definition_argument_count)
    return false;

  for (u8 i = 0; i < call_argument_count; i++) {
    const Type_handle call_site_argument_type_handle =
        call_site_argument_types_handle.data[i];

    const bool is_call_argument_subtype_of_definition_argument =
        resolver_is_type_subtype_of(resolver, call_site_argument_type_handle,
                                    definition->argument_type_handles.data[i],
                                    scratch_arena, arena);

    // TODO: Technically, we need to add the constraint `call argument <:
    // definition_argument` and afterwards check the soundness, but for now it
    // should do until we have generics (or varargs perhaps).
    if (!is_call_argument_subtype_of_definition_argument)
      return false;
  }

  // Per spec, the return type is not checked.

  return true;
}

static u16
jvm_verification_info_kind_word_count(Jvm_verification_info_kind kind) {
  switch (kind) {
  case VERIFICATION_INFO_TOP:
  case VERIFICATION_INFO_INT:
  case VERIFICATION_INFO_FLOAT:
  case VERIFICATION_INFO_NULL:
  case VERIFICATION_INFO_OBJECT:
  case VERIFICATION_INFO_UNINITIALIZED:
    return 1;
  case VERIFICATION_INFO_DOUBLE:
  case VERIFICATION_INFO_LONG:
    return 2;
  }
  pg_assert(0 && "unreachable");
}

static Jvm_verification_info
codegen_type_to_verification_info(const Type *type) {

  switch (type->kind) {
  case TYPE_BOOLEAN:
  case TYPE_BYTE:
  case TYPE_CHAR:
  case TYPE_SHORT:
  case TYPE_INT:
    return (Jvm_verification_info){.kind = VERIFICATION_INFO_INT};
  case TYPE_LONG:
    return (Jvm_verification_info){.kind = VERIFICATION_INFO_LONG};
  case TYPE_FLOAT:
    return (Jvm_verification_info){.kind = VERIFICATION_INFO_FLOAT};
  case TYPE_DOUBLE:
    return (Jvm_verification_info){.kind = VERIFICATION_INFO_DOUBLE};
  case TYPE_INSTANCE:
  case TYPE_STRING:
    return (Jvm_verification_info){
        .kind = VERIFICATION_INFO_OBJECT,
        .extra_data = 0, // Patched later.
    };

  default:
    pg_assert(0 && "unreachable");
  }
}

static void codegen_frame_stack_push(codegen_frame *frame,
                                     Jvm_verification_info verification_info,
                                     Arena *arena) {
  pg_assert(frame != NULL);
  pg_assert(arena != NULL);

  const u16 word_count =
      jvm_verification_info_kind_word_count(verification_info.kind);

  pg_assert(frame->stack_physical_count + word_count < UINT16_MAX);
  *array32_push(&frame->stack, arena) = verification_info;

  frame->stack_physical_count += word_count;
  frame->max_physical_stack =
      pg_max(frame->max_physical_stack, frame->stack_physical_count);
}

static void codegen_frame_stack_pop(codegen_frame *frame) {
  pg_assert(frame != NULL);
  pg_assert(frame->stack.len >= 1);
  pg_assert(frame->stack_physical_count >= 1);
  pg_assert(frame->max_physical_stack >= 1);

  array32_drop(&frame->stack, 1);

  frame->stack_physical_count -= 1;
}

static codegen_frame *codegen_frame_clone(const codegen_frame *src,
                                          Arena *arena);

static void jvm_code_push_u8(Array32(u8) * array, u8 x, Arena *arena) {
  *array32_push(array, arena) = x;
}

static void jvm_code_array_push_u16(Array32(u8) * array, u16 x, Arena *arena) {
  jvm_code_push_u8(array, (u8)((x & 0xff00) >> 8), arena);
  jvm_code_push_u8(array, (u8)(x & 0x00ff), arena);
}

typedef enum __attribute__((packed)) {
  ACCESS_FLAGS_PUBLIC = 0x0001,
  ACCESS_FLAGS_PRIVATE = 0x0002,
  ACCESS_FLAGS_PROTECTED = 0x0004,
  ACCESS_FLAGS_STATIC = 0x0008,
  ACCESS_FLAGS_FINAL = 0x0010,
  ACCESS_FLAGS_SYNCHRONIZED = 0x0020,
  ACCESS_FLAGS_SUPER = 0x0020,
  ACCESS_FLAGS_VOLATILE = 0x0040,
  ACCESS_FLAGS_BRIDGE = 0x0040,
  ACCESS_FLAGS_TRANSIENT = 0x0080,
  ACCESS_FLAGS_VARARGS = 0x0080,
  ACCESS_FLAGS_NATIVE = 0x0100,
  ACCESS_FLAGS_INTERFACE = 0x0200,
  ACCESS_FLAGS_ABSTRACT = 0x0400,
  ACCESS_FLAGS_STRICT = 0x0800,
  ACCESS_FLAGS_SYNTHETIC = 0x1000,
  ACCESS_FLAGS_ANNOTATION = 0x2000,
  ACCESS_FLAGS_ENUM = 0x4000,
  ACCESS_FLAGS_MODULE = 0x8000,
} Jvm_access_flags;

typedef struct {
  union {
    u64 number;        // CONSTANT_POOL_KIND_INT
    Str s;             // CONSTANT_POOL_KIND_UTF8
    u16 string_utf8_i; // CONSTANT_POOL_KIND_STRING
    struct Jvm_constant_method_ref {
      u16 class;
      u16 name_and_type;
    } method_ref;        // CONSTANT_POOL_KIND_METHOD_REF
    u16 java_class_name; // CONSTANT_POOL_KIND_CLASS_INFO
    struct Jvm_constant_name_and_type {
      u16 name;
      u16 descriptor;
    } name_and_type; // CONSTANT_POOL_KIND_NAME_AND_TYPE
    struct Jvm_constant_field_ref {
      u16 name;
      u16 descriptor;
    } field_ref; // CONSTANT_POOL_KIND_FIELD_REF
  } v;
  enum __attribute__((packed)) Jvm_constant_pool_kind {
    CONSTANT_POOL_KIND_UTF8 = 1,
    CONSTANT_POOL_KIND_INT = 3,
    CONSTANT_POOL_KIND_FLOAT = 4,
    CONSTANT_POOL_KIND_LONG = 5,
    CONSTANT_POOL_KIND_DOUBLE = 6,
    CONSTANT_POOL_KIND_CLASS_INFO = 7,
    CONSTANT_POOL_KIND_STRING = 8,
    CONSTANT_POOL_KIND_FIELD_REF = 9,
    CONSTANT_POOL_KIND_METHOD_REF = 10,
    CONSTANT_POOL_KIND_INTERFACE_METHOD_REF = 11,
    CONSTANT_POOL_KIND_NAME_AND_TYPE = 12,
    CONSTANT_POOL_KIND_METHOD_HANDLE = 15,
    CONSTANT_POOL_KIND_METHOD_TYPE = 16,
    CONSTANT_POOL_KIND_DYNAMIC = 17,
    CONSTANT_POOL_KIND_INVOKE_DYNAMIC = 18,
    CONSTANT_POOL_KIND_MODULE = 19,
    CONSTANT_POOL_KIND_PACKAGE = 20,
  } kind;
  pg_pad(7);
} Jvm_constant_pool_entry;

typedef struct Jvm_constant_method_ref Jvm_constant_method_ref;

typedef struct Jvm_constant_name_and_type Jvm_constant_name_and_type;

typedef struct Jvm_constant_field_ref Jvm_constant_field_ref;

typedef enum Jvm_constant_pool_kind Jvm_constant_pool_kind;

struct Jvm_constant_pool {
  u64 len;
  u64 cap;
  Jvm_constant_pool_entry *values;
};

static Jvm_constant_pool jvm_constant_array_make(u64 cap, Arena *arena) {
  pg_assert(arena != NULL);

  return (Jvm_constant_pool){
      .len = 0,
      .cap = cap,
      .values = arena_alloc(arena, sizeof(Jvm_constant_pool_entry),
                            _Alignof(Jvm_constant_pool_entry), cap),
  };
}

static u16 jvm_constant_array_push(Jvm_constant_pool *array,
                                   const Jvm_constant_pool_entry *x,
                                   Arena *arena) {
  pg_assert(array != NULL);
  pg_assert(x != NULL);
  pg_assert(array->len < UINT16_MAX);
  pg_assert(array->values != NULL);
  pg_assert(((u64)(array->values)) % 8 == 0);
  pg_assert(array->cap != 0);

  if (array->len == array->cap) {
    const u64 new_cap = array->cap * 2;
    Jvm_constant_pool_entry *const new_array =
        arena_alloc(arena, sizeof(Jvm_constant_pool_entry),
                    _Alignof(Jvm_constant_pool_entry), new_cap);
    pg_assert(new_array != NULL);
    array->values = memmove(new_array, array->values,
                            array->len * sizeof(Jvm_constant_pool_entry));
    pg_assert(array->values != NULL);
    pg_assert(((u64)(array->values)) % 16 == 0);
    array->cap = new_cap;
  }

  array->values[array->len] = *x;
  const u64 index = array->len + 1;
  pg_assert(index > 0);
  pg_assert(index <= array->len + 1);
  array->len += 1;
  return (u16)index;
}

static void codegen_frame_init(codegen_frame *frame, Arena *arena) {
  pg_assert(frame != NULL);
  pg_assert(arena != NULL);

  frame->locals = array32_make(Jvm_variable, 0, 512, arena);
  frame->stack = array32_make(Jvm_verification_info, 0, 256, arena);
}

static codegen_frame *codegen_frame_clone(const codegen_frame *src,
                                          Arena *arena) {
  pg_assert(src != NULL);
  pg_assert(src->stack.len <= UINT16_MAX);
  pg_assert(arena != NULL);

  codegen_frame *dst =
      arena_alloc(arena, sizeof(codegen_frame), _Alignof(codegen_frame), 1);
  codegen_frame_init(dst, arena);

  dst->max_physical_stack = src->max_physical_stack;
  dst->max_physical_locals = src->max_physical_locals;
  dst->scope_depth = src->scope_depth;
  dst->stack_physical_count = src->stack_physical_count;
  dst->locals_physical_count = src->locals_physical_count;

  array32_clone(Jvm_variable, &dst->locals, src->locals, arena);
  array32_clone(Jvm_verification_info, &dst->stack, src->stack, arena);

  return dst;
}

static Jvm_constant_pool *
jvm_constant_array_clone(const Jvm_constant_pool *constant_pool, Arena *arena) {
  Jvm_constant_pool *res = arena_alloc(arena, sizeof(Jvm_constant_pool),
                                       _Alignof(Jvm_constant_pool), 1);
  res->cap = res->len = constant_pool->len;
  res->values =
      arena_alloc(arena, sizeof(Jvm_constant_pool_entry),
                  _Alignof(Jvm_constant_pool_entry), constant_pool->len);

  for (u64 i = 0; i < res->len; i++) {
    const Jvm_constant_pool_entry constant = constant_pool->values[i];
    res->values[i] = constant;

    if (constant.kind == CONSTANT_POOL_KIND_UTF8) {
      res->values[i].v.s = constant.v.s;
    }
  }

  return res;
}

static const Jvm_constant_pool_entry *
jvm_constant_array_get(const Jvm_constant_pool *constant_pool, u16 i) {
  pg_assert(constant_pool != NULL);
  pg_assert(i > 0);
  pg_assert(i <= constant_pool->len);
  pg_assert(constant_pool->values != NULL);
  pg_assert(((u64)(constant_pool->values)) % 8 == 0);

  return &constant_pool->values[i - 1];
}

static Str_builder jvm_fill_descriptor_string(Str_builder sb,
                                              Type_handle type_handle,
                                              Arena *arena) {

  const Type *const type = type_handle_to_ptr(type_handle, *arena);

  switch (type->kind) {
  case TYPE_UNIT: {
    return sb_append_char(sb, 'V', arena);
  }
  case TYPE_BYTE: {
    return sb_append_char(sb, 'B', arena);
  }
  case TYPE_CHAR: {
    return sb_append_char(sb, 'C', arena);
  }
  case TYPE_DOUBLE: {
    return sb_append_char(sb, 'D', arena);
  }
  case TYPE_FLOAT: {
    return sb_append_char(sb, 'F', arena);
  }
  case TYPE_INT: {
    return sb_append_char(sb, 'I', arena);
  }
  case TYPE_LONG: {
    return sb_append_char(sb, 'J', arena);
  }
  case TYPE_STRING: {
    return sb_append_c(sb, "Ljava/lang/String;", arena);
  }
  case TYPE_INSTANCE: {
    Str java_class_name = type->this_class_name;

    sb = sb_append_char(sb, 'L', arena);
    sb = sb_append(sb, java_class_name, arena);
    return sb_append_char(sb, ';', arena);
  }
  case TYPE_SHORT: {
    return sb_append_char(sb, 'S', arena);
  }
  case TYPE_BOOLEAN: {
    return sb_append_char(sb, 'Z', arena);
  }
  case TYPE_ARRAY: {
    sb = sb_append_char(sb, '[', arena);
    return jvm_fill_descriptor_string(sb, type->v.array_type_handle, arena);
  }
  case TYPE_METHOD:
  case TYPE_CONSTRUCTOR: {
    const Method *const method_type = &type->v.method;
    sb = sb_append_char(sb, '(', arena);

    for (u64 i = 0; i < method_type->argument_type_handles.len; i++) {
      sb = jvm_fill_descriptor_string(
          sb, method_type->argument_type_handles.data[i], arena);
    }

    sb = sb_append_char(sb, ')', arena);

    return jvm_fill_descriptor_string(sb, method_type->return_type_handle,
                                      arena);
  }
  default:
    pg_assert(0 && "unreachable");
  }
}

static Str jvm_parse_descriptor(Resolver *resolver, Str descriptor, Type *type,
                                Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(type != NULL);
  pg_assert(arena != NULL);

  if (str_is_empty(descriptor))
    return (Str){0};

  Str remaining = descriptor;

  switch (remaining.data[0]) {
  case 'V': {
    type->kind = TYPE_UNIT;
    return str_advance(remaining, 1);
  }

  case 'S': {
    type->kind = TYPE_SHORT;

    return str_advance(remaining, 1);
  }

  case 'B': {
    type->kind = TYPE_BYTE;

    return str_advance(remaining, 1);
  }

  case 'C': {
    type->kind = TYPE_CHAR;

    return str_advance(remaining, 1);
  }

  case 'D': {
    type->kind = TYPE_DOUBLE;

    return str_advance(remaining, 1);
  }

  case 'F': {
    type->kind = TYPE_FLOAT;

    return str_advance(remaining, 1);
  }

  case 'I': {
    type->kind = TYPE_INT;

    return str_advance(remaining, 1);
  }

  case 'J': {
    type->kind = TYPE_LONG;

    return str_advance(remaining, 1);
  }

  case 'Z': {
    type->kind = TYPE_BOOLEAN;

    return str_advance(remaining, 1);
  }

  case 'L': {
    remaining = str_advance(remaining, 1);
    Str_split_result semicolon_split = str_split(remaining, ';');
    pg_assert(semicolon_split.found);
    Str fqn = semicolon_split.left;

    if (str_eq_c(type->this_class_name, "java/lang/String")) {
      type->kind = TYPE_STRING;
    } else {
      type->kind = TYPE_INSTANCE;
    }
    type_init_package_and_name(fqn, &type->package_name, &type->this_class_name,
                               arena);

    return semicolon_split.right;
  }

  case '[': {
    type->kind = TYPE_ARRAY;
    Type item_type = {0};

    Str descriptor_remaining = {
        .data = remaining.data + 1,
        .len = remaining.len - 1,
    };
    remaining =
        jvm_parse_descriptor(resolver, descriptor_remaining, &item_type, arena);

    if (!str_is_empty(item_type.this_class_name)) {
      type_init_package_and_name(item_type.this_class_name, &type->package_name,
                                 &type->this_class_name, arena);
    }

    type->v.array_type_handle = resolver_add_type(resolver, &item_type, arena);
    return remaining;
  }

  case '(': {
    // Might be: TYPE_CONSTRUCTOR, but we cannot know based on the type
    // descriptor, only based on the name.
    // Hence, the caller will have to patch the kind afterwards.
    type->kind = TYPE_METHOD;
    remaining = str_advance(remaining, 1);

    Array32(Type_handle) argument_types_handle =
        array32_make(Type_handle, 0, (u32)remaining.len, arena);

    for (u64 i = 0; i < 255; i++) {
      if (str_first(remaining) == ')')
        break;

      Type argument_type = {0};
      remaining =
          jvm_parse_descriptor(resolver, remaining, &argument_type, arena);
      const Type_handle argument_type_handle =
          resolver_add_type(resolver, &argument_type, arena);
      *array32_push(&argument_types_handle, arena) = argument_type_handle;
    }
    pg_assert(remaining.len >= 1);
    pg_assert(remaining.data[0] = ')');
    remaining = str_advance(remaining, 1);

    Type return_type = {0};
    remaining = jvm_parse_descriptor(resolver, remaining, &return_type, arena);
    // TODO: Check cache before adding the type.

    type->v.method.argument_type_handles = argument_types_handle;
    type->v.method.return_type_handle =
        resolver_add_type(resolver, &return_type, arena);

    return remaining;
  }
  default:
    pg_assert(0 && "unreachable");
  }

  __builtin_unreachable();
}

typedef struct {
  u16 type_name_index;
  u16 const_name_index;
} Jvm_enum_const_value;

typedef struct Jvm_element_value Jvm_element_value;
Array32_struct(Jvm_element_value);

typedef struct Jvm_annotation Jvm_annotation;
Array32_struct(Jvm_annotation);

struct Jvm_element_value {
  union {
    u16 const_value_index;
    Jvm_enum_const_value enum_const_value;
    u16 class_info_index;
    Jvm_annotation *annotation_value;
    Array32(Jvm_element_value) array_value;
  } v;
  u8 tag;
  pg_pad(7);
};

typedef struct {
  u16 element_name_index;
  pg_pad(6);
  Jvm_element_value element_value;
} Jvm_element_value_pair;
Array32_struct(Jvm_element_value_pair);

struct Jvm_annotation {
  u16 type_index;
  pg_pad(6);
  Array32(Jvm_element_value_pair) element_value_pairs;
};

typedef struct Jvm_attribute Jvm_attribute;
Array32_struct(Jvm_attribute);

typedef struct {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  pg_pad(2);
  Array32(Jvm_attribute) attributes;
} Jvm_field;
Array32_struct(Jvm_field);

typedef struct Jvm_method Jvm_method;
Array32_struct(Jvm_method);

typedef struct Jvm_interfaces Jvm_interfaces;

typedef struct {
  u16 start_pc;
  u16 line_number;
} Jvm_line_number_table_entry;
Array32_struct(Jvm_line_number_table_entry);

struct Jvm_attribute {
  union {
    struct Jvm_attribute_code {
      u16 max_physical_stack;
      u16 max_physical_locals;
      pg_pad(4);
      Array32(u8) bytecode;
      Array32(Jvm_exception) exceptions;
      Array32(Jvm_attribute) attributes;
    } code; // ATTRIBUTE_KIND_CODE

    struct Jvm_attribute_source_file {
      u16 source_file;
    } source_file; // ATTRIBUTE_KIND_SOURCE_FILE

    Array32(Jvm_line_number_table_entry)
        line_number_table_entries; // ATTRIBUTE_KIND_LINE_NUMBER_TABLE

    Array32(Stack_map_frame) stack_map_table; // ATTRIBUTE_KIND_STACK_MAP_TABLE
    Array32(Jvm_annotation)
        runtime_invisible_annotations; // ATTRIBUTE_KIND_RUNTIME_INVISIBLE_ANNOTATIONS

    Array32(u16) exception_index_table; // ATTRIBUTE_KIND_EXCEPTIONS
  } v;
  u16 name;
  enum __attribute__((packed)) Jvm_attribute_kind {
    ATTRIBUTE_KIND_SOURCE_FILE,
    ATTRIBUTE_KIND_CODE,
    ATTRIBUTE_KIND_LINE_NUMBER_TABLE,
    ATTRIBUTE_KIND_STACK_MAP_TABLE,
    ATTRIBUTE_KIND_RUNTIME_INVISIBLE_ANNOTATIONS,
    ATTRIBUTE_KIND_EXCEPTIONS,
  } kind;
  pg_pad(5);
};

typedef enum Jvm_attribute_kind Jvm_attribute_kind;

typedef struct Jvm_attribute_line_number_table Jvm_attribute_line_number_table;

typedef struct Jvm_attribute_code Jvm_attribute_code;

typedef struct Jvm_attribute_source_file Jvm_attribute_source_file;

struct Jvm_method {
  u16 access_flags;
  u16 name;
  u16 descriptor;
  pg_pad(2);
  Array32(Jvm_attribute) attributes;
};

static const u32 jvm_MAGIC_NUMBER = 0xbebafeca;
static const u16 jvm_MAJOR_VERSION_6 = 50;
static const u16 jvm_MAJOR_VERSION_7 = 51;
static const u16 jvm_MINOR_VERSION = 0;

struct Jvm_class_file {
  Str archive_file_path;
  Str class_file_path;
  Str class_name;
  u16 minor_version;
  u16 major_version;
  u16 access_flags;
  u16 this_class;
  u16 super_class;
  u16 interfaces_count;
  u16 fields_count;
  pg_pad(2);
  Array32(u16) interfaces;
  Array32(Jvm_field) fields;
  Array32(Jvm_method) methods;
  Array32(Jvm_attribute) attributes;
  Jvm_constant_pool constant_pool;
};
typedef struct Jvm_class_file Class_file;

static void file_write_u8(FILE *file, u8 x) {
  pg_assert(file != NULL);
  fwrite(&x, sizeof(x), 1, file);
}
static void file_write_be_u16(FILE *file, u16 x) {
  pg_assert(file != NULL);

  const u8 x_be[2] = {
      (u8)((x & (u16)0xff00) >> 8),
      (u8)((x & (u16)0x00ff) >> 0),
  };
  fwrite(x_be, sizeof(x_be), 1, file);
}

static void file_write_be_u32(FILE *file, u32 x) {
  pg_assert(file != NULL);

  const u8 x_be[4] = {
      (u8)((x & 0xff000000U) >> 24),
      (u8)((x & 0x00ff0000U) >> 16),
      (u8)((x & 0x0000ff00U) >> 8),
      (u8)((x & 0x000000ffU) >> 0),
  };
  fwrite(x_be, sizeof(x_be), 1, file);
}

static void file_write_be_u64(FILE *file, u64 x) {
  pg_assert(file != NULL);

  const u8 x_be[8] = {
      (u8)((x & 0xfff0000000000000UL) >> 56),
      (u8)((x & 0x00ff000000000000UL) >> 48),
      (u8)((x & 0x0000ff0000000000UL) >> 40),
      (u8)((x & 0x000000ff00000000UL) >> 32),
      (u8)((x & 0x00000000ff000000UL) >> 24),
      (u8)((x & 0x0000000000ff0000UL) >> 16),
      (u8)((x & 0x000000000000ff00UL) >> 8),
      (u8)((x & 0x00000000000000ffUL) >> 0),
  };
  fwrite(x_be, sizeof(x_be), 1, file);
}

static u16 buf_read_be_u16(Str buf, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current + sizeof(u16) <= buf.data + buf.len);

  const u8 *const ptr = *current;
  const u16 x =
      (u16)((((u16)(ptr[0] & (u16)0xff)) << 8) | ((u16)((ptr[1] & 0xff)) << 0));
  *current += sizeof(u16);
  return x;
}

static u16 buf_read_le_u16(Str buf, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current + sizeof(u16) <= buf.data + buf.len);

  const u8 *const ptr = *current;
  const u16 x =
      (u16)((((u16)(ptr[1] & 0xff)) << 8) | ((u16)((ptr[0] & 0xff)) << 0));
  *current += sizeof(u16);
  return x;
}

static u32 buf_read_be_u32(Str buf, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current + sizeof(u32) <= buf.data + buf.len);

  const u8 *const ptr = *current;
  const u32 x = ((u32)(ptr[0] & 0xff) << 24) | (((u32)(ptr[1] & 0xff)) << 16) |
                (((u32)(ptr[2] & 0xff)) << 8) | (((u32)(ptr[3] & 0xff)) << 0);
  *current += sizeof(u32);
  return x;
}

static u32 buf_read_le_u32(Str buf, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current + sizeof(u32) <= buf.data + buf.len);

  const u8 *const ptr = *current;
  const u32 x = ((u32)(ptr[3] & 0xff) << 24) | (((u32)(ptr[2] & 0xff)) << 16) |
                (((u32)(ptr[1] & 0xff)) << 8) | (((u32)(ptr[0] & 0xff)) << 0);
  *current += sizeof(u32);
  return x;
}

static Str buf_read_n_u8(Str buf, u64 n, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current + n <= buf.data + buf.len);

  Str res = {.data = *current, .len = n};
  *current += n;

  return res;
}

static u8 buf_read_u8(Str buf, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current + sizeof(u8) <= buf.data + buf.len);

  const u8 x = (*current)[0];
  *current += 1;
  return x;
}

static Str
jvm_constant_array_get_as_string(const Jvm_constant_pool *constant_pool,
                                 u16 i) {
  const Jvm_constant_pool_entry *const constant =
      jvm_constant_array_get(constant_pool, i);
  pg_assert(constant->kind == CONSTANT_POOL_KIND_UTF8);
  return constant->v.s;
}

static void jvm_buf_read_attributes(Str buf, u8 **current,
                                    Class_file *class_file,
                                    Array32(Jvm_attribute) * attributes,
                                    Arena *arena);

static void
jvm_buf_read_sourcefile_attribute(Str buf, u8 **current, Class_file *class_file,
                                  Array32(Jvm_attribute) * attributes,
                                  Arena *arena) {

  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);

  const u8 *const current_start = *current;

  Jvm_attribute_source_file source_file = {0};
  source_file.source_file = buf_read_be_u16(buf, current);
  pg_assert(source_file.source_file > 0);
  pg_assert(source_file.source_file <= class_file->constant_pool.len);

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == 2);

  Jvm_attribute attribute = {.kind = ATTRIBUTE_KIND_SOURCE_FILE,
                             .v = {.source_file = source_file}};
  *array32_push(&*attributes, arena) = attribute;
}

static void jvm_buf_read_code_attribute_exceptions(Str buf, u8 **current,
                                                   Class_file *class_file,
                                                   Array32(Jvm_exception) *
                                                       exceptions,
                                                   Arena *arena) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(exceptions != NULL);

  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, current);
  *exceptions = array32_make(Jvm_exception, 0, table_len, arena);

  for (u16 i = 0; i < table_len; i++) {
    Jvm_exception exception = {0};

    exception.start_pc = buf_read_be_u16(buf, current);
    exception.end_pc = buf_read_be_u16(buf, current);
    exception.handler_pc = buf_read_be_u16(buf, current);
    exception.catch_type = buf_read_be_u16(buf, current);

    *array32_push(&*exceptions, arena) = exception;
  }

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == sizeof(u16) + table_len * sizeof(u16) * 4);
}

static void jvm_buf_read_code_attribute(Str buf, u8 **current,
                                        Class_file *class_file,
                                        u32 attribute_len, u16 name_i,
                                        Array32(Jvm_attribute) * attributes,
                                        Arena *arena) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current + 2 <= buf.data + buf.len);
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u8 *const current_start = *current;

  Jvm_attribute_code code = {0};
  code.max_physical_stack = buf_read_be_u16(buf, current);
  code.max_physical_locals = buf_read_be_u16(buf, current);
  const u32 code_len = buf_read_be_u32(buf, current);
  pg_assert(*current + code_len <= buf.data + buf.len);
  pg_assert(code_len <= UINT16_MAX); // Actual limit per spec.

  Str code_slice = buf_read_n_u8(buf, code_len, current);
  code.bytecode = array32_make_from_slice(u8, code_slice.data, code_len, arena);

  jvm_buf_read_code_attribute_exceptions(buf, current, class_file,
                                         &code.exceptions, arena);

  jvm_buf_read_attributes(buf, current, class_file, &code.attributes, arena);

  Jvm_attribute attribute = {
      .kind = ATTRIBUTE_KIND_CODE, .name = name_i, .v = {.code = code}};
  *array32_push(&*attributes, arena) = attribute;

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

static void
jvm_buf_read_stack_map_table_attribute_verification_infos(Str buf, u8 **current,
                                                          u16 count) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);

  for (u16 i = 0; i < count; i++) {
    const u8 kind = buf_read_u8(buf, current);

    if (kind < 7)
      continue;

    if (kind > 8)
      pg_assert(0 && "invalid");

    buf_read_be_u16(buf, current);
  }
}

static void jvm_buf_read_stack_map_table_attribute(
    Str buf, u8 **current, u32 attribute_len, u16 name_i,
    Array32(Jvm_attribute) * attributes, Arena *arena) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u8 *const current_start = *current;

  const u16 len = buf_read_be_u16(buf, current);
  Array32(Stack_map_frame) stack_map_frames =
      array32_make(Stack_map_frame, 0, len, arena);

  for (u16 i = 0; i < len; i++) {
    Stack_map_frame stack_map_frame = {
        .kind = buf_read_u8(buf, current),
    };

    if (stack_map_frame.kind <= 63) // same_frame
    {
      stack_map_frame.offset_delta = stack_map_frame.kind;
    } else if (64 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 127) { // same_locals_1_stack_item_frame
      stack_map_frame.offset_delta = stack_map_frame.kind - 64;
      jvm_buf_read_stack_map_table_attribute_verification_infos(buf, current,
                                                                1);

    } else if (128 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 246) { // reserved
      pg_assert(0 && "unreachable");
    } else if (247 <= stack_map_frame.kind &&
               stack_map_frame.kind <=
                   247) { // same_locals_1_stack_item_frame_extended
      stack_map_frame.offset_delta = buf_read_be_u16(buf, current);
      jvm_buf_read_stack_map_table_attribute_verification_infos(buf, current,
                                                                1);

    } else if (248 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 250) { // chop_frame
      stack_map_frame.offset_delta = buf_read_be_u16(buf, current);

    } else if (251 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 251) { // same_frame_extended
      stack_map_frame.offset_delta = buf_read_be_u16(buf, current);

    } else if (252 <= stack_map_frame.kind &&
               stack_map_frame.kind <= 254) { // append_frame
      stack_map_frame.offset_delta = buf_read_be_u16(buf, current);
      const u16 verification_info_count = stack_map_frame.kind - 251;
      jvm_buf_read_stack_map_table_attribute_verification_infos(
          buf, current, verification_info_count);

    } else { // full_frame_attribute
      stack_map_frame.offset_delta = buf_read_be_u16(buf, current);
      const u16 locals_count = buf_read_be_u16(buf, current);
      jvm_buf_read_stack_map_table_attribute_verification_infos(buf, current,
                                                                locals_count);
      const u16 stack_items_count = buf_read_be_u16(buf, current);
      jvm_buf_read_stack_map_table_attribute_verification_infos(
          buf, current, stack_items_count);
    }
    *array32_push(&stack_map_frames, arena) = stack_map_frame;
  }

  Jvm_attribute attribute = {
      .kind = ATTRIBUTE_KIND_STACK_MAP_TABLE,
      .name = name_i,
      .v = {.stack_map_table = stack_map_frames},
  };
  *array32_push(&*attributes, arena) = attribute;

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

static void jvm_buf_read_line_number_table_attribute(
    Str buf, u8 **current, Class_file *class_file, u32 attribute_len,
    Array32(Jvm_attribute) * attributes, Arena *arena) {
  pg_unused(arena);
  pg_unused(class_file);

  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, current);
  pg_assert(sizeof(table_len) + table_len * (sizeof(u16) + sizeof(u16)) ==
            attribute_len);

  Jvm_attribute attribute = {.kind = ATTRIBUTE_KIND_LINE_NUMBER_TABLE};
  attribute.v.line_number_table_entries =
      array32_make(Jvm_line_number_table_entry, 0, table_len, arena);

  for (u16 i = 0; i < table_len; i++) {
    Jvm_line_number_table_entry entry = {
        .start_pc = buf_read_be_u16(buf, current),
        .line_number = buf_read_be_u16(buf, current),
    };
    *array32_push(&attribute.v.line_number_table_entries, arena) = entry;
  }

  *array32_push(&*attributes, arena) = attribute;

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

static void jvm_buf_read_local_variable_table_attribute(Str buf, u8 **current,
                                                        Class_file *class_file,
                                                        u32 attribute_len,
                                                        Arena *arena) {
  pg_unused(arena);
  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, current);
  const u16 entry_size = sizeof(u16) * 5;
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 start_pc = buf_read_be_u16(buf, current);
    pg_unused(start_pc);
    const u16 len = buf_read_be_u16(buf, current);
    pg_unused(len);
    const u16 name_i = buf_read_be_u16(buf, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= class_file->constant_pool.len);

    const u16 descriptor_i = buf_read_be_u16(buf, current);
    pg_unused(descriptor_i);
    const u16 idx = buf_read_be_u16(buf, current);
    pg_unused(idx);

    // TODO store.
  }
  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

static void jvm_buf_read_local_variable_type_table_attribute(
    Str buf, u8 **current, Class_file *class_file, u32 attribute_len,
    Arena *arena) {
  pg_unused(arena);
  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, current);
  const u16 entry_size = sizeof(u16) * 5;
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 start_pc = buf_read_be_u16(buf, current);
    pg_unused(start_pc);
    const u16 len = buf_read_be_u16(buf, current);
    pg_unused(len);
    const u16 name_i = buf_read_be_u16(buf, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= class_file->constant_pool.len);

    const u16 signature_i = buf_read_be_u16(buf, current);
    pg_unused(signature_i);
    const u16 idx = buf_read_be_u16(buf, current);
    pg_unused(idx);

    // TODO store.
  }
  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

static void jvm_buf_read_signature_attribute(Str buf, u8 **current,
                                             Class_file *class_file,
                                             u32 attribute_len, Arena *arena) {
  pg_unused(arena);
  pg_unused(class_file);

  const u8 *const current_start = *current;

  pg_assert(attribute_len == 2);
  const u16 signature_i = buf_read_be_u16(buf, current);
  pg_unused(signature_i);
  // TODO store.

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

// TODO: store this data.
static void jvm_buf_read_exceptions_attribute(
    Str buf, u8 **current, Class_file *class_file, u32 attribute_len,
    Array32(Jvm_attribute) * attributes, Arena *arena) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, current);
  const u16 entry_size = sizeof(u16);
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  Jvm_attribute attribute = {
      .kind = ATTRIBUTE_KIND_EXCEPTIONS,
      .v.exception_index_table = array32_make(u16, 0, table_len, arena),
  };

  for (u16 i = 0; i < table_len; i++) {
    const u16 exception_i = buf_read_be_u16(buf, current);
    pg_assert(exception_i > 0);
    pg_assert(exception_i <= class_file->constant_pool.len);
  }

  *array32_push(&*attributes, arena) = attribute;

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

static void jvm_buf_read_inner_classes_attribute(Str buf, u8 **current,
                                                 Class_file *class_file,
                                                 u32 attribute_len,
                                                 Arena *arena) {
  pg_unused(arena);
  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, current);
  const u16 entry_size = sizeof(u16) * 4;
  pg_assert(sizeof(table_len) + table_len * entry_size == attribute_len);

  for (u16 i = 0; i < table_len; i++) {
    const u16 inner_class_info_i = buf_read_be_u16(buf, current);
    pg_assert(inner_class_info_i > 0);
    pg_assert(inner_class_info_i <= class_file->constant_pool.len);

    const u16 outer_class_info_i = buf_read_be_u16(buf, current);
    // Could be 0.
    pg_assert(outer_class_info_i <= class_file->constant_pool.len);

    const u16 inner_name_i = buf_read_be_u16(buf, current);
    // Could be 0.
    pg_assert(inner_name_i <= class_file->constant_pool.len);

    const u16 inner_class_access_flags = buf_read_be_u16(buf, current);
    pg_unused(inner_class_access_flags);

    // TODO store.
  }
  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

static void jvm_buf_read_annotation(Str buf, u8 **current,
                                    Class_file *class_file,
                                    Jvm_annotation *annotation, Arena *arena);

static void jvm_buf_read_element_value(Str buf, u8 **current,
                                       Class_file *class_file,
                                       Jvm_element_value *element_value,
                                       Arena *arena) {
  element_value->tag = buf_read_u8(buf, current);
  switch (element_value->tag) {
  case 'B':
  case 'C':
  case 'D':
  case 'I':
  case 'J':
  case 'S':
  case 'Z':
  case 's':
    element_value->v.const_value_index = buf_read_be_u16(buf, current);
    break;

  case 'e':
    element_value->v.enum_const_value.type_name_index =
        buf_read_be_u16(buf, current);
    element_value->v.enum_const_value.const_name_index =
        buf_read_be_u16(buf, current);
    break;

  case 'c':
    element_value->v.class_info_index = buf_read_be_u16(buf, current);
    break;

  case '@': {
    element_value->v.annotation_value =
        arena_alloc(arena, sizeof(Jvm_annotation), _Alignof(Jvm_annotation), 1);

    jvm_buf_read_annotation(buf, current, class_file,
                            element_value->v.annotation_value, arena);

    break;
  }

  case '[': {
    const u16 table_len = buf_read_be_u16(buf, current);
    element_value->v.array_value =
        array32_make(Jvm_element_value, 0, table_len, arena);

    for (u64 i = 0; i < table_len; i++) {
      Jvm_element_value element_value_child = {0};
      jvm_buf_read_element_value(buf, current, class_file, &element_value_child,
                                 arena);

      *array32_push(&element_value->v.array_value, arena) = element_value_child;
    }
    break;
  }

  default:
    pg_assert(0 && "Unexpected value");
  }
}

static void jvm_buf_read_annotation(Str buf, u8 **current,
                                    Class_file *class_file,
                                    Jvm_annotation *annotation, Arena *arena) {

  annotation->type_index = buf_read_be_u16(buf, current);
  const u16 num_element_value_pairs = buf_read_be_u16(buf, current);

  annotation->element_value_pairs =
      array32_make(Jvm_element_value_pair, 0, num_element_value_pairs, arena);

  for (u64 i = 0; i < num_element_value_pairs; i++) {
    Jvm_element_value_pair element_value_pair = {
        .element_name_index = buf_read_be_u16(buf, current),
    };
    jvm_buf_read_element_value(buf, current, class_file,
                               &element_value_pair.element_value, arena);

    *array32_push(&annotation->element_value_pairs, arena) = element_value_pair;
  }
}

static void jvm_buf_read_runtime_invisible_annotations_attribute(
    Str buf, u8 **current, Class_file *class_file, u32 attribute_len,
    Array32(Jvm_attribute) * attributes, Arena *arena) {

  const u8 *const current_start = *current;

  const u16 table_len = buf_read_be_u16(buf, current);

  Jvm_attribute attribute = {
      .kind = ATTRIBUTE_KIND_RUNTIME_INVISIBLE_ANNOTATIONS,
      .v.runtime_invisible_annotations =
          array32_make(Jvm_annotation, 0, table_len, arena),
  };

  for (u64 i = 0; i < table_len; i++) {
    Jvm_annotation annotation = {0};
    jvm_buf_read_annotation(buf, current, class_file, &annotation, arena);
    *array32_push(&attribute.v.runtime_invisible_annotations, arena) =
        annotation;
  }
  *array32_push(attributes, arena) = attribute;

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == attribute_len);
}

static void jvm_buf_read_attribute(Str buf, u8 **current,
                                   Class_file *class_file,
                                   Array32(Jvm_attribute) * attributes,
                                   Arena *arena) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u16 name_i = buf_read_be_u16(buf, current);
  pg_assert(name_i > 0);
  const u32 size = buf_read_be_u32(buf, current);
  pg_assert(*current + size <= buf.data + buf.len);

  pg_assert(name_i <= class_file->constant_pool.len);
  Str attribute_name =
      jvm_constant_array_get_as_string(&class_file->constant_pool, name_i);

  if (str_eq_c(attribute_name, "SourceFile")) {
    pg_assert(2 == size);
    jvm_buf_read_sourcefile_attribute(buf, current, class_file, attributes,
                                      arena);
  } else if (str_eq_c(attribute_name, "Code")) {
    jvm_buf_read_code_attribute(buf, current, class_file, size, name_i,
                                attributes, arena);
  } else if (str_eq_c(attribute_name, "StackMapTable")) {
    jvm_buf_read_stack_map_table_attribute(buf, current, size, name_i,
                                           attributes, arena);
  } else if (str_eq_c(attribute_name, "Exceptions")) {
    jvm_buf_read_exceptions_attribute(buf, current, class_file, size,
                                      attributes, arena);
  } else if (str_eq_c(attribute_name, "InnerClasses")) {
    jvm_buf_read_inner_classes_attribute(buf, current, class_file, size, arena);
  } else if (str_eq_c(attribute_name, "EnclosingMethod")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "Synthetic")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "Signature")) {
    jvm_buf_read_signature_attribute(buf, current, class_file, size, arena);
  } else if (str_eq_c(attribute_name, "SourceDebugExtension")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "LineNumberTable")) {
    jvm_buf_read_line_number_table_attribute(buf, current, class_file, size,
                                             attributes, arena);
  } else if (str_eq_c(attribute_name, "LocalVariableTable")) {
    jvm_buf_read_local_variable_table_attribute(buf, current, class_file, size,
                                                arena);
  } else if (str_eq_c(attribute_name, "LocalVariableTypeTable")) {
    jvm_buf_read_local_variable_type_table_attribute(buf, current, class_file,
                                                     size, arena);
  } else if (str_eq_c(attribute_name, "Deprecated")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "RuntimeVisibleAnnotations")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "RuntimeInvisibleAnnotations")) {
    jvm_buf_read_runtime_invisible_annotations_attribute(
        buf, current, class_file, size, attributes, arena);
  } else if (str_eq_c(attribute_name, "RuntimeVisibleParameterAnnotations")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "RuntimeInvisibleParameterAnnotations")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "RuntimeInvisibleAnnotations")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "AnnotationsDefault")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "BootstrapMethods")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "NestMembers")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "NestHost")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "ConstantValue")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "Module")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "ModulePackages")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "ModuleMainClass")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "Record")) {
    *current += size; // TODO
  } else if (str_eq_c(attribute_name, "PermittedSubclasses")) {
    *current += size; // TODO
  } else {
    *current += size; // TODO
  }
}

static void jvm_buf_read_attributes(Str buf, u8 **current,
                                    Class_file *class_file,
                                    Array32(Jvm_attribute) * attributes,
                                    Arena *arena) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(attributes != NULL);
  pg_assert(arena != NULL);

  const u16 attribute_count = buf_read_be_u16(buf, current);
  *attributes = array32_make(Jvm_attribute, 0, attribute_count, arena);

  for (u64 i = 0; i < attribute_count; i++) {
    jvm_buf_read_attribute(buf, current, class_file, attributes, arena);
  }
}

// Returns the number of incoming slots to skip:
// - `1` in the case of CONSTANT_POOL_KIND_LONG or CONSTANT_POOL_KIND_DOUBLE
// - `0` otherwise
static u8 jvm_buf_read_constant(Str buf, u8 **current, Class_file *class_file,
                                u16 constant_pool_count, Arena *arena) {
  u8 kind = buf_read_u8(buf, current);

  if (!(kind == CONSTANT_POOL_KIND_UTF8 || kind == CONSTANT_POOL_KIND_INT ||
        kind == CONSTANT_POOL_KIND_FLOAT || kind == CONSTANT_POOL_KIND_LONG ||
        kind == CONSTANT_POOL_KIND_DOUBLE ||
        kind == CONSTANT_POOL_KIND_CLASS_INFO ||
        kind == CONSTANT_POOL_KIND_STRING ||
        kind == CONSTANT_POOL_KIND_FIELD_REF ||
        kind == CONSTANT_POOL_KIND_METHOD_REF ||
        kind == CONSTANT_POOL_KIND_INTERFACE_METHOD_REF ||
        kind == CONSTANT_POOL_KIND_NAME_AND_TYPE ||
        kind == CONSTANT_POOL_KIND_METHOD_HANDLE ||
        kind == CONSTANT_POOL_KIND_METHOD_TYPE ||
        kind == CONSTANT_POOL_KIND_DYNAMIC ||
        kind == CONSTANT_POOL_KIND_INVOKE_DYNAMIC ||
        kind == CONSTANT_POOL_KIND_MODULE ||
        kind == CONSTANT_POOL_KIND_PACKAGE)) {
    fprintf(stderr, "Unknown constant kind found: offset=%lu kind=%u\n",
            *current - buf.data - 1, kind);
    pg_assert(0);
  }

  switch (kind) {
  case CONSTANT_POOL_KIND_UTF8: { // FIXME: It's actually modified utf8!
    u16 len = buf_read_be_u16(buf, current);

    u8 *const s = *current;
    buf_read_n_u8(buf, len, current);

    Jvm_constant_pool_entry constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                        .v = {.s = str_new(s, len)}};
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);

    break;
  }
  case CONSTANT_POOL_KIND_INT: {
    const u32 value = buf_read_be_u32(buf, current);
    pg_unused(value);

    const Jvm_constant_pool_entry constant = {.kind = kind,
                                              .v = {.number = 0}}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_FLOAT: {
    const u32 value = buf_read_be_u32(buf, current);
    pg_unused(value);

    const Jvm_constant_pool_entry constant = {.kind = kind,
                                              .v = {.number = 0}}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_DOUBLE:
  case CONSTANT_POOL_KIND_LONG: {
    const u32 high = buf_read_be_u32(buf, current);
    pg_unused(high);
    const u32 low = buf_read_be_u32(buf, current);
    pg_unused(low);

    const Jvm_constant_pool_entry constant = {.kind = kind,
                                              .v = {.number = 0}}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    const Jvm_constant_pool_entry dummy = {0};
    jvm_constant_array_push(&class_file->constant_pool, &dummy, arena);
    return 1;
  }
  case CONSTANT_POOL_KIND_CLASS_INFO: {
    const u16 java_class_name_i = buf_read_be_u16(buf, current);
    pg_assert(java_class_name_i > 0);
    pg_assert(java_class_name_i <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {.java_class_name = java_class_name_i}};
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_STRING: {
    const u16 utf8_i = buf_read_be_u16(buf, current);
    pg_assert(utf8_i > 0);
    pg_assert(utf8_i <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {.kind = CONSTANT_POOL_KIND_STRING,
                                              .v = {.string_utf8_i = utf8_i}};
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_FIELD_REF: {
    const u16 name_i = buf_read_be_u16(buf, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_count);

    const u16 descriptor_i = buf_read_be_u16(buf, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {
        .kind = CONSTANT_POOL_KIND_FIELD_REF,
        .v = {.field_ref = {.name = name_i, .descriptor = descriptor_i}}};
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_REF: {
    const u16 class_i = buf_read_be_u16(buf, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_count);

    const u16 name_and_type_handle = buf_read_be_u16(buf, current);
    pg_assert(name_and_type_handle > 0);
    pg_assert(name_and_type_handle <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {
        .kind = CONSTANT_POOL_KIND_METHOD_REF,
        .v = {.method_ref = {.name_and_type = name_and_type_handle,
                             .class = class_i}}};
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_INTERFACE_METHOD_REF: {
    const u16 class_i = buf_read_be_u16(buf, current);
    pg_assert(class_i > 0);
    pg_assert(class_i <= constant_pool_count);

    const u16 name_and_type_handle = buf_read_be_u16(buf, current);
    pg_assert(name_and_type_handle > 0);
    pg_assert(name_and_type_handle <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {
        .kind = CONSTANT_POOL_KIND_INTERFACE_METHOD_REF,
    }; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_NAME_AND_TYPE: {
    const u16 name_i = buf_read_be_u16(buf, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_count);

    const u16 descriptor_i = buf_read_be_u16(buf, current);
    pg_assert(descriptor_i > 0);
    pg_assert(descriptor_i <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = name_i, .descriptor = descriptor_i}}};
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_HANDLE: {
    const u8 reference_kind = buf_read_u8(buf, current);
    pg_unused(reference_kind);
    const u16 reference_i = buf_read_be_u16(buf, current);
    pg_unused(reference_i);

    const Jvm_constant_pool_entry constant = {.kind = kind}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_TYPE: {
    const u16 descriptor = buf_read_be_u16(buf, current);
    pg_assert(descriptor > 0);
    pg_assert(descriptor <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {.kind = kind}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_DYNAMIC: {
    const u16 bootstrap_method_attr_index = buf_read_be_u16(buf, current);
    pg_unused(bootstrap_method_attr_index);

    const u16 name_and_type_index = buf_read_be_u16(buf, current);
    pg_assert(name_and_type_index > 0);
    pg_assert(name_and_type_index <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {.kind = kind}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_INVOKE_DYNAMIC: {
    const u16 bootstrap_method_attr_index = buf_read_be_u16(buf, current);
    pg_unused(bootstrap_method_attr_index);

    const u16 name_and_type_index = buf_read_be_u16(buf, current);
    pg_assert(name_and_type_index > 0);
    pg_assert(name_and_type_index <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {.kind = kind}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_MODULE: {
    const u16 name_i = buf_read_be_u16(buf, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {.kind = kind}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  case CONSTANT_POOL_KIND_PACKAGE: {
    const u16 name_i = buf_read_be_u16(buf, current);
    pg_assert(name_i > 0);
    pg_assert(name_i <= constant_pool_count);

    const Jvm_constant_pool_entry constant = {.kind = kind}; // FIXME
    jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
  return 0;
}

static void jvm_buf_read_constants(Str buf, u8 **current,
                                   Class_file *class_file,
                                   u16 constant_pool_count, Arena *arena) {
  for (u64 i = 0; i < constant_pool_count; i++) {
    pg_assert((u64)(*current - buf.data) < buf.len);
    i += jvm_buf_read_constant(buf, current, class_file, constant_pool_count,
                               arena);
    pg_assert((u64)(*current - buf.data) <= buf.len);
  }
  pg_assert(constant_pool_count <= class_file->constant_pool.len);
}

static void jvm_buf_read_method(Str buf, u8 **current, Class_file *class_file,
                                Arena *arena) {
  Jvm_method method = {0};
  method.access_flags = buf_read_be_u16(buf, current);
  method.name = buf_read_be_u16(buf, current);
  pg_assert(
      jvm_constant_array_get(&class_file->constant_pool, method.name)->kind ==
      CONSTANT_POOL_KIND_UTF8);

  method.descriptor = buf_read_be_u16(buf, current);
  pg_assert(
      jvm_constant_array_get(&class_file->constant_pool, method.name)->kind ==
      CONSTANT_POOL_KIND_UTF8);

  jvm_buf_read_attributes(buf, current, class_file, &method.attributes, arena);

  *array32_push(&class_file->methods, arena) = method;
}

static void jvm_buf_read_methods(Str buf, u8 **current, Class_file *class_file,
                                 Arena *arena) {

  const u16 methods_count = buf_read_be_u16(buf, current);
  class_file->methods = array32_make(Jvm_method, 0, methods_count, arena);

  for (u64 i = 0; i < methods_count; i++) {
    jvm_buf_read_method(buf, current, class_file, arena);
  }
}

static void jvm_buf_read_interfaces(Str buf, u8 **current,
                                    Class_file *class_file, Arena *arena) {

  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  const u8 *const current_start = *current;

  const u16 interfaces_count = buf_read_be_u16(buf, current);
  class_file->interfaces = array32_make(u16, 0, interfaces_count, arena);

  for (u16 i = 0; i < interfaces_count; i++) {
    const u16 interface_i = buf_read_be_u16(buf, current);
    pg_assert(interface_i > 0);
    pg_assert(interface_i <= class_file->constant_pool.len);

    *array32_push(&class_file->interfaces, arena) = interface_i;
  }

  const u8 *const current_end = *current;
  const u64 read_bytes = (u64)current_end - (u64)current_start;
  pg_assert(read_bytes == sizeof(u16) + interfaces_count * sizeof(u16));
}

static void jvm_buf_read_field(Str buf, u8 **current, Class_file *class_file,
                               Arena *arena) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  Jvm_field field = {0};
  field.access_flags = buf_read_be_u16(buf, current);
  field.name = buf_read_be_u16(buf, current);
  pg_assert(field.name > 0);
  pg_assert(field.name <= class_file->constant_pool.len);

  field.descriptor = buf_read_be_u16(buf, current);
  pg_assert(field.descriptor > 0);
  pg_assert(field.descriptor <= class_file->constant_pool.len);

  jvm_buf_read_attributes(buf, current, class_file, &field.attributes, arena);

  *array32_push(&class_file->fields, arena) = field;
}

static void jvm_buf_read_fields(Str buf, u8 **current, Class_file *class_file,
                                Arena *arena) {

  const u16 fields_count = buf_read_be_u16(buf, current);
  class_file->fields = array32_make(Jvm_field, 0, fields_count, arena);

  for (u16 i = 0; i < fields_count; i++) {
    jvm_buf_read_field(buf, current, class_file, arena);
  }
}

static void jvm_buf_read_class_file(Str buf, u8 **current,
                                    Class_file *class_file, Arena *arena) {

  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  // Magic.
  pg_assert(buf_read_u8(buf, current) == 0xca);
  pg_assert(buf_read_u8(buf, current) == 0xfe);
  pg_assert(buf_read_u8(buf, current) == 0xba);
  pg_assert(buf_read_u8(buf, current) == 0xbe);

  class_file->minor_version = buf_read_be_u16(buf, current);
  class_file->major_version = buf_read_be_u16(buf, current);

  const u16 constant_pool_count = buf_read_be_u16(buf, current) - 1;
  pg_assert(constant_pool_count > 0);
  class_file->constant_pool = jvm_constant_array_make(
      constant_pool_count * 2,
      arena); // Worst case: only LONG or DOUBLE entries which take 2 slots.
  pg_assert(class_file->constant_pool.values != NULL);
  pg_assert(((u64)class_file->constant_pool.values) % 8 == 0);

  jvm_buf_read_constants(buf, current, class_file, constant_pool_count, arena);

  class_file->access_flags = buf_read_be_u16(buf, current);

  class_file->this_class = buf_read_be_u16(buf, current);
  pg_assert(class_file->this_class > 0);
  pg_assert(class_file->this_class <= constant_pool_count);
  const Jvm_constant_pool_entry *const this_class = jvm_constant_array_get(
      &class_file->constant_pool, class_file->this_class);
  pg_assert(this_class->kind == CONSTANT_POOL_KIND_CLASS_INFO);
  class_file->class_name = jvm_constant_array_get_as_string(
      &class_file->constant_pool, this_class->v.string_utf8_i);

  class_file->super_class = buf_read_be_u16(buf, current);
  pg_assert(class_file->super_class <= constant_pool_count);

  jvm_buf_read_interfaces(buf, current, class_file, arena);

  jvm_buf_read_fields(buf, current, class_file, arena);

  jvm_buf_read_methods(buf, current, class_file, arena);

  jvm_buf_read_attributes(buf, current, class_file, &class_file->attributes,
                          arena);

  const u64 remaining = (u64)buf.data + buf.len - (u64)*current;
  pg_assert(remaining == 0);
}

// Returns the number of incoming slots to skip:
// - `1` in the case of CONSTANT_POOL_KIND_LONG or CONSTANT_POOL_KIND_DOUBLE
// - `0` otherwise
static u8 jvm_write_constant(const Class_file *class_file, FILE *file,
                             const Jvm_constant_pool_entry *constant) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);
  pg_assert(constant != NULL);

  fwrite(&constant->kind, sizeof(u8), 1, file);
  switch (constant->kind) {
  case CONSTANT_POOL_KIND_UTF8: {
    Str s = constant->v.s;
    pg_assert(s.len <= UINT16_MAX);
    file_write_be_u16(file, (u16)s.len);
    fwrite(s.data, sizeof(u8), s.len, file);
    break;
  }
  case CONSTANT_POOL_KIND_FLOAT:
  case CONSTANT_POOL_KIND_INT:
    pg_assert(constant->v.number <= UINT32_MAX);
    file_write_be_u32(file, (u32)constant->v.number);
    break;
  case CONSTANT_POOL_KIND_LONG:
  case CONSTANT_POOL_KIND_DOUBLE:
    file_write_be_u64(file, constant->v.number);
    return 1;
  case CONSTANT_POOL_KIND_CLASS_INFO:
    file_write_be_u16(file, constant->v.java_class_name);
    break;
  case CONSTANT_POOL_KIND_STRING:
    file_write_be_u16(file, constant->v.string_utf8_i);
    break;
  case CONSTANT_POOL_KIND_FIELD_REF: {

    const Jvm_constant_field_ref *const field_ref = &constant->v.field_ref;

    file_write_be_u16(file, field_ref->name);
    file_write_be_u16(file, field_ref->descriptor);
    break;
  }
  case CONSTANT_POOL_KIND_METHOD_REF: {

    const Jvm_constant_method_ref *const method_ref = &constant->v.method_ref;

    file_write_be_u16(file, method_ref->class);
    file_write_be_u16(file, method_ref->name_and_type);
    break;
  }
  case CONSTANT_POOL_KIND_INTERFACE_METHOD_REF:
    pg_assert(0 && "unimplemented");
    break;
  case CONSTANT_POOL_KIND_NAME_AND_TYPE: {

    const Jvm_constant_name_and_type *const name_and_type =
        &constant->v.name_and_type;

    file_write_be_u16(file, name_and_type->name);
    file_write_be_u16(file, name_and_type->descriptor);
    break;
  }
  case CONSTANT_POOL_KIND_INVOKE_DYNAMIC:
    pg_assert(0 && "unimplemented");
    break;
  default:
    pg_assert(0 && "unreachable/unimplemented");
  }
  return 0;
}

static void jvm_write_constant_pool(const Class_file *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);
  pg_assert(class_file->constant_pool.len < UINT16_MAX);
  file_write_be_u16(file, (u16)class_file->constant_pool.len + 1);

  for (u64 i = 0; i < class_file->constant_pool.len; i++) {
    pg_assert(class_file->constant_pool.values != NULL);
    pg_assert(((u64)class_file->constant_pool.values) % 8 == 0);

    const Jvm_constant_pool_entry *const constant =
        &class_file->constant_pool.values[i];
    i += jvm_write_constant(class_file, file, constant);
  }
}
static void jvm_write_interfaces(const Class_file *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  file_write_be_u16(file, class_file->interfaces_count);

  pg_assert(class_file->interfaces_count == 0 && "unimplemented");
}

static void jvm_write_fields(const Class_file *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  file_write_be_u16(file, class_file->fields_count);

  pg_assert(class_file->fields_count == 0 && "unimplemented");
}

static u32
jvm_compute_verification_info_size(Jvm_verification_info verification_info) {
  pg_assert(verification_info.kind <= 8);

  return verification_info.kind < 7 ? sizeof(u8) : sizeof(u8) + sizeof(u16);
}

static u32
jvm_compute_verification_infos_size(const Stack_map_frame *stack_map_frame) {
  pg_assert(stack_map_frame != NULL);

  if (stack_map_frame->kind <= 63) // same_frame
  {
    return 0;
  } else if (64 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 127) { // same_locals_1_stack_item_frame
    const Jvm_verification_info verification_info =
        *array32_last(stack_map_frame->frame->stack);
    pg_assert(verification_info.kind != VERIFICATION_INFO_TOP);

    return jvm_compute_verification_info_size(verification_info);
  } else if (128 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 246) { // reserved
    pg_assert(0 && "unreachable");
  } else if (247 <= stack_map_frame->kind &&
             stack_map_frame->kind <=
                 247) { // same_locals_1_stack_item_frame_extended
    const Jvm_verification_info verification_info =
        *array32_last(stack_map_frame->frame->stack);
    pg_assert(verification_info.kind != VERIFICATION_INFO_TOP);

    return jvm_compute_verification_info_size(verification_info);
  } else if (248 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 250) { // chop_frame
    return 0;
  } else if (251 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 251) { // same_frame_extended
    return 0;
  } else if (252 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 254) { // append_frame
    const u64 count = stack_map_frame->kind - 251;
    u32 size = 0;

    for (u64 i = stack_map_frame->frame->locals.len - count;
         i < stack_map_frame->frame->locals.len; i++) {
      const Jvm_verification_info verification_info =
          stack_map_frame->frame->locals.data[i].verification_info;

      pg_assert(verification_info.kind != VERIFICATION_INFO_TOP);

      size += jvm_compute_verification_info_size(verification_info);
    }

    return size;
  } else { // full_frame
    u32 size = 0;
    for (u64 i = 0; i < stack_map_frame->frame->locals.len; i++) {
      const Jvm_verification_info verification_info =
          stack_map_frame->frame->locals.data[i].verification_info;

      pg_assert(verification_info.kind != VERIFICATION_INFO_TOP);

      size += jvm_compute_verification_info_size(verification_info);
    }

    for (u64 i = 0; i < stack_map_frame->frame->stack.len; i++) {
      const Jvm_verification_info verification_info =
          stack_map_frame->frame->stack.data[i];

      pg_assert(verification_info.kind != VERIFICATION_INFO_TOP);

      size += jvm_compute_verification_info_size(verification_info);
    }

    return size;
  }
  pg_assert(0 && "unreachable");
}

static u32 jvm_compute_attribute_size(const Jvm_attribute *attribute) {
  pg_assert(attribute != NULL);

  switch (attribute->kind) {
  case ATTRIBUTE_KIND_SOURCE_FILE:
    return 2;
  case ATTRIBUTE_KIND_CODE: {
    const Jvm_attribute_code *const code = &attribute->v.code;

    u32 size = (u32)sizeof(code->max_physical_stack) +
               (u32)sizeof(code->max_physical_locals) + (u32)sizeof(u32) +
               code->bytecode.len + (u32)sizeof(u16) /* exception count */ +
               +code->exceptions.len * (u32)sizeof(Jvm_exception) +
               (u32)sizeof(u16) // attributes length
        ;

    for (u64 i = 0; i < code->attributes.len; i++) {
      const Jvm_attribute *const child_attribute = &code->attributes.data[i];
      size += (u32)sizeof(u16) + (u32)sizeof(u32) +
              jvm_compute_attribute_size(child_attribute);
    }
    return size;
  }
  case ATTRIBUTE_KIND_LINE_NUMBER_TABLE: {
    return (u32)sizeof(u16) /* count */ +
           attribute->v.line_number_table_entries.len *
               (u32)sizeof(Jvm_line_number_table_entry);
  }
  case ATTRIBUTE_KIND_STACK_MAP_TABLE: {
    const Array32(Stack_map_frame) stack_map_frames =
        attribute->v.stack_map_table;

    u32 size = sizeof(u16) /* count */;
    for (u16 i = 0; i < stack_map_frames.len; i++) {
      const Stack_map_frame *const stack_map_frame = &stack_map_frames.data[i];

      if (stack_map_frame->kind <= 63) // same_frame
      {
        size += sizeof(u8);
      } else if (64 <= stack_map_frame->kind &&
                 stack_map_frame->kind <=
                     127) { // same_locals_1_stack_item_frame
        const u32 delta =
            sizeof(u8) + jvm_compute_verification_infos_size(stack_map_frame);
        pg_assert(delta >= 2);
        pg_assert(delta <= 4);

        size += delta;
      } else if (128 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 246) { // reserved
        pg_assert(0 && "unreachable");
      } else if (247 <= stack_map_frame->kind &&
                 stack_map_frame->kind <=
                     247) { // same_locals_1_stack_item_frame_extended
        const u32 delta = sizeof(u8) + sizeof(u16) +
                          jvm_compute_verification_infos_size(stack_map_frame);
        pg_assert(delta >= 4);
        pg_assert(delta <= 5);

        size += delta;

      } else if (248 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 250) { // chop_frame
        size += sizeof(u8) + sizeof(u16);
      } else if (251 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 251) { // same_frame_extended
        size += sizeof(u8) + sizeof(u16);
      } else if (252 <= stack_map_frame->kind &&
                 stack_map_frame->kind <= 254) { // append_frame
        const u32 delta = sizeof(u8) + sizeof(u16) +
                          jvm_compute_verification_infos_size(stack_map_frame);

        pg_assert(delta >= 4);
        pg_assert(delta <= 9);

        size += delta;
      } else { // full_frame
        size += (u32)sizeof(u8) + 3 * (u32)sizeof(u16) +
                jvm_compute_verification_infos_size(stack_map_frame);
      }
    }

    return size;
  }
  case ATTRIBUTE_KIND_EXCEPTIONS:
    return (u32)sizeof(u16) /* count */ +
           attribute->v.exception_index_table.len * (u32)sizeof(u16);
  case ATTRIBUTE_KIND_RUNTIME_INVISIBLE_ANNOTATIONS: {
    pg_assert(0 && "todo");
  }
  }
  pg_assert(0 && "unreachable");
}

static void jvm_write_attributes(FILE *file, Array32(Jvm_attribute) attributes);

static void
jvm_write_verification_info(FILE *file,
                            Jvm_verification_info verification_info) {
  pg_assert(file != NULL);
  pg_assert(verification_info.kind <= 8);

  file_write_u8(file, verification_info.kind);

  if (verification_info.kind >= 7) {
    pg_assert(verification_info.extra_data > 0);
    file_write_be_u16(file, verification_info.extra_data);
  }
}

static void
jvm_write_stack_map_table_attribute(FILE *file,
                                    const Stack_map_frame *stack_map_frame) {
  pg_assert(file != NULL);
  pg_assert(stack_map_frame != NULL);

  if (stack_map_frame->kind <= 63) // same_frame
  {
    file_write_u8(file, stack_map_frame->kind);
  } else if (64 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 127) { // same_locals_1_stack_item_frame
    file_write_u8(file, stack_map_frame->kind);
    jvm_write_verification_info(file,
                                *array32_last(stack_map_frame->frame->stack));
  } else if (128 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 246) { // reserved
    pg_assert(0 && "unreachable");
  } else if (247 <= stack_map_frame->kind &&
             stack_map_frame->kind <=
                 247) { // same_locals_1_stack_item_frame_extended
    pg_assert(0 && "todo");
  } else if (248 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 250) { // chop_frame
    file_write_u8(file, stack_map_frame->kind);
    file_write_be_u16(file, stack_map_frame->offset_delta);
  } else if (251 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 251) { // same_frame_extended
    pg_assert(0 && "todo");
  } else if (252 <= stack_map_frame->kind &&
             stack_map_frame->kind <= 254) { // append_frame
    file_write_u8(file, stack_map_frame->kind);
    file_write_be_u16(file, stack_map_frame->offset_delta);

    const u64 count = stack_map_frame->kind - 251;
    for (u64 i = stack_map_frame->frame->locals.len - count;
         i < stack_map_frame->frame->locals.len; i++) {
      const Jvm_verification_info verification_info =
          stack_map_frame->frame->locals.data[i].verification_info;

      pg_assert(verification_info.kind != VERIFICATION_INFO_TOP);

      jvm_write_verification_info(file, verification_info);
    }

  } else { // full_frame

    file_write_u8(file, stack_map_frame->kind);
    file_write_be_u16(file, stack_map_frame->offset_delta);
    pg_assert(stack_map_frame->frame->locals.len <= UINT16_MAX);
    file_write_be_u16(file, (u16)stack_map_frame->frame->locals.len);

    for (u64 i = 0; i < stack_map_frame->frame->locals.len; i++) {
      const Jvm_verification_info verification_info =
          stack_map_frame->frame->locals.data[i].verification_info;

      pg_assert(verification_info.kind != VERIFICATION_INFO_TOP);

      jvm_write_verification_info(file, verification_info);
    }

    pg_assert(stack_map_frame->frame->stack.len <= UINT16_MAX);
    file_write_be_u16(file, (u16)stack_map_frame->frame->stack.len);
    for (u64 i = 0; i < stack_map_frame->frame->stack.len; i++) {
      const Jvm_verification_info verification_info =
          stack_map_frame->frame->stack.data[i];

      pg_assert(verification_info.kind != VERIFICATION_INFO_TOP);

      jvm_write_verification_info(file, verification_info);
    }
  }
}

static void jvm_write_attribute(FILE *file, const Jvm_attribute *attribute) {
  pg_assert(file != NULL);
  pg_assert(attribute != NULL);

  file_write_be_u16(file, attribute->name);

  switch (attribute->kind) {
  case ATTRIBUTE_KIND_SOURCE_FILE: {
    const u32 size = jvm_compute_attribute_size(attribute);
    file_write_be_u32(file, size);

    const Jvm_attribute_source_file *const source_file =
        &attribute->v.source_file;
    file_write_be_u16(file, source_file->source_file);

    break;
  }
  case ATTRIBUTE_KIND_CODE: {
    const u32 size = jvm_compute_attribute_size(attribute);
    file_write_be_u32(file, size);

    const Jvm_attribute_code *const code = &attribute->v.code;

    file_write_be_u16(file, code->max_physical_stack);

    file_write_be_u16(file, code->max_physical_locals);

    pg_assert(code->bytecode.len <= UINT32_MAX);
    file_write_be_u32(file, code->bytecode.len);
    fwrite(code->bytecode.data, code->bytecode.len, sizeof(u8), file);

    pg_assert(code->exceptions.len <= UINT16_MAX);
    file_write_be_u16(file, (u16)code->exceptions.len);
    pg_assert(code->exceptions.len == 0 && "todo");

    jvm_write_attributes(file, code->attributes);

    break;
  }
  case ATTRIBUTE_KIND_LINE_NUMBER_TABLE: {
    const u32 size = jvm_compute_attribute_size(attribute);
    file_write_be_u32(file, size);

    for (u16 i = 0; i < attribute->v.line_number_table_entries.len; i++) {
      Jvm_line_number_table_entry line_number_table =
          attribute->v.line_number_table_entries.data[i];
      file_write_be_u16(file, line_number_table.start_pc);
      file_write_be_u16(file, line_number_table.line_number);
    }

    break;
  }
  case ATTRIBUTE_KIND_STACK_MAP_TABLE: {
    const u32 size = jvm_compute_attribute_size(attribute);
    file_write_be_u32(file, size);

    file_write_be_u16(file, (u16)attribute->v.stack_map_table.len);

    for (u16 i = 0; i < attribute->v.stack_map_table.len; i++) {
      const Stack_map_frame *const stack_map_frame =
          &attribute->v.stack_map_table.data[i];
      jvm_write_stack_map_table_attribute(file, stack_map_frame);
    }
    break;
  }
  default:
    pg_assert(0 && "unreachable");
  }
}

static void jvm_write_attributes(FILE *file,
                                 Array32(Jvm_attribute) attributes) {
  pg_assert(attributes.len <= UINT16_MAX);
  file_write_be_u16(file, (u16)attributes.len);

  for (u64 i = 0; i < attributes.len; i++) {
    const Jvm_attribute *const attribute = &attributes.data[i];
    jvm_write_attribute(file, attribute);
  }
}

static void jvm_write_method(FILE *file, const Jvm_method *method) {
  file_write_be_u16(file, method->access_flags);
  file_write_be_u16(file, method->name);
  file_write_be_u16(file, method->descriptor);

  jvm_write_attributes(file, method->attributes);
}

static void jvm_write_methods(const Class_file *class_file, FILE *file) {
  pg_assert(class_file != NULL);
  pg_assert(file != NULL);

  pg_assert(class_file->methods.len <= UINT16_MAX);
  file_write_be_u16(file, (u16)class_file->methods.len);

  for (u64 i = 0; i < class_file->methods.len; i++) {
    const Jvm_method *const method = &class_file->methods.data[i];
    jvm_write_method(file, method);
  }
}

static void jvm_write(const Class_file *class_file, FILE *file) {
  fwrite(&jvm_MAGIC_NUMBER, sizeof(jvm_MAGIC_NUMBER), 1, file);

  file_write_be_u16(file, class_file->minor_version);
  file_write_be_u16(file, 44 + class_file->major_version);
  jvm_write_constant_pool(class_file, file);
  file_write_be_u16(file, class_file->access_flags);
  file_write_be_u16(file, class_file->this_class);
  file_write_be_u16(file, class_file->super_class);

  jvm_write_interfaces(class_file, file);
  jvm_write_fields(class_file, file);
  jvm_write_methods(class_file, file);
  jvm_write_attributes(file, class_file->attributes);
  fflush(file);
}

static void jvm_init(Class_file *class_file, Arena *arena) {
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  class_file->constant_pool = jvm_constant_array_make(1024, arena);
}

static u16 jvm_add_constant_string(Jvm_constant_pool *constant_pool, Str s,
                                   Arena *arena) {
  pg_assert(constant_pool != NULL);
  pg_assert(!str_is_empty(s));

  const Jvm_constant_pool_entry constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                            .v = {.s = s}};
  return jvm_constant_array_push(constant_pool, &constant, arena);
}

static u16 jvm_add_constant_cstring(Jvm_constant_pool *constant_pool, char *s,
                                    Arena *arena) {
  pg_assert(constant_pool != NULL);
  pg_assert(s != NULL);

  const Jvm_constant_pool_entry constant = {.kind = CONSTANT_POOL_KIND_UTF8,
                                            .v = {.s = str_from_c(s)}};
  return jvm_constant_array_push(constant_pool, &constant, arena);
}

static u16 jvm_add_constant_jstring(Jvm_constant_pool *constant_pool,
                                    u16 constant_utf8_i, Arena *arena) {
  pg_assert(constant_pool != NULL);
  pg_assert(constant_utf8_i > 0);

  const Jvm_constant_pool_entry constant = {
      .kind = CONSTANT_POOL_KIND_STRING,
      .v = {.string_utf8_i = constant_utf8_i}};

  return jvm_constant_array_push(constant_pool, &constant, arena);
}

// TODO: sanitize `source_file_name` in case of spaces, etc.
// Transform: `/a/b/foo.kt` to `/a/b/FooKt.class`
static Str jvm_make_class_file_path_kt(Str source_file_name, Arena *arena) {
  pg_assert(!str_is_empty(source_file_name));
  pg_assert(source_file_name.len > 0);
  pg_assert(arena != NULL);

  Str_split_result file_extension_split = str_rsplit(source_file_name, '.');
  pg_assert(file_extension_split.found);
  pg_assert(str_eq_c(file_extension_split.right, "kt"));

  Str suffix = str_from_c("Kt.class");
  Str_builder res = sb_new(file_extension_split.left.len + suffix.len, arena);
  res = sb_append(res, file_extension_split.left, arena);

  // Capitalize
  {
    Str_split_result last_path_component_split =
        str_rsplit(source_file_name, '/');

    u64 pos = last_path_component_split.found
                  ? last_path_component_split.found_pos + 1
                  : 0;
    res = sb_capitalize_at(res, pos);
  }

  res = sb_append(res, suffix, arena);

  return sb_build(res);
}

__attribute__((unused)) static Str
jvm_get_this_class_name(const Class_file *class_file) {
  pg_assert(class_file != NULL);

  const Jvm_constant_pool_entry *const this_class = jvm_constant_array_get(
      &class_file->constant_pool, class_file->this_class);
  pg_assert(this_class->kind == CONSTANT_POOL_KIND_CLASS_INFO);
  const u16 this_class_i = this_class->v.java_class_name;
  return jvm_constant_array_get_as_string(&class_file->constant_pool,
                                          this_class_i);
}

static const Jvm_attribute *
jvm_method_find_code_attribute(const Jvm_method *method) {
  for (u64 i = 0; i < method->attributes.len; i++) {
    const Jvm_attribute *const attribute = &method->attributes.data[i];

    if (attribute->kind == ATTRIBUTE_KIND_CODE)
      return attribute;
  }
  return NULL;
}

static const Jvm_attribute *jvm_attribute_by_kind(Array32(Jvm_attribute)
                                                      attributes,
                                                  Jvm_attribute_kind kind) {
  for (u64 i = 0; i < attributes.len; i++) {
    const Jvm_attribute *const attribute = &attributes.data[i];

    if (attribute->kind == kind)
      return attribute;
  }
  return NULL;
}

static void jvm_get_source_location_of_function(const Class_file *class_file,
                                                const Jvm_method *method,
                                                Str *filename, u16 *line,
                                                Arena *arena) {
  const Jvm_attribute *const code = jvm_method_find_code_attribute(method);
  if (code == NULL)
    return;

  const Jvm_attribute *const source_file = jvm_attribute_by_kind(
      code->v.code.attributes, ATTRIBUTE_KIND_SOURCE_FILE);
  if (source_file != NULL) {
    *filename = str_clone(
        jvm_constant_array_get_as_string(
            &class_file->constant_pool, source_file->v.source_file.source_file),
        arena);
  }

  const Jvm_attribute *const line_number_table = jvm_attribute_by_kind(
      code->v.code.attributes, ATTRIBUTE_KIND_LINE_NUMBER_TABLE);
  if (line_number_table != NULL) {
    const Array32(Jvm_line_number_table_entry) entries =
        line_number_table->v.line_number_table_entries;

    if (entries.len > 0)
      *line = entries.data[0].line_number;
  }
}

// ---------------------------------- Lexer

static u32 lex_get_current_offset(Str buf, u8 *const *current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert((u64)(*current - buf.data) <= buf.len);

  return (u32)((u64)*current - (u64)buf.data);
}

static bool lex_is_at_end(Str buf, u8 *const *current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert((u64)(*current - buf.data) <= buf.len);

  return lex_get_current_offset(buf, current) == buf.len;
}

static u8 lex_peek(Str buf, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  return lex_is_at_end(buf, current) ? 0 : **current;
}

static u8 lex_peek_next(Str buf, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  u64 remaining = buf.len - lex_get_current_offset(buf, current);
  if (remaining < 1)
    return 0;

  return *(*current + 1);
}

static u8 lex_advance(Str buf, u8 **current) {
  pg_assert(!str_is_empty(buf));
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  const u8 c = **current;

  *current += 1;

  return lex_is_at_end(buf, current) ? 0 : c;
}

static bool lex_match(Str buf, u8 **current, u8 c) {
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  if (lex_peek(buf, current) == c) {
    lex_advance(buf, current);
    return true;
  }
  return false;
}

static void lex_skip_until_incl_1(Str buf, u8 **current, u8 c) {
  while (!(lex_is_at_end(buf, current) || lex_peek(buf, current) == c)) {
    lex_advance(buf, current);
  }
}

static void lex_skip_until_incl_2(Str buf, u8 **current, u8 c1, u8 c2) {
  while (
      !(lex_is_at_end(buf, current) ||
        (lex_peek(buf, current) == c1 && lex_peek_next(buf, current) == c2))) {
    lex_advance(buf, current);
  }

  if (!lex_is_at_end(buf, current)) {
    pg_assert(lex_peek(buf, current) == c1 &&
              lex_peek_next(buf, current) == c2);
    lex_advance(buf, current);
    lex_advance(buf, current);
  }
}

static bool lex_is_digit(u8 c) { return ('0' <= c && c <= '9'); }

static bool lex_is_identifier_char(u8 c) {
  return ut_char_is_alphabetic(c) || lex_is_digit(c) || c == '_';
}

static u32 lex_number_length(Str buf, u32 current_offset) {
  pg_assert(current_offset < buf.len);

  const u32 start_offset = current_offset;
  u8 *current = &buf.data[current_offset];
  pg_assert(lex_is_digit(lex_peek(buf, &current)));

  lex_advance(buf, &current);

  while (!lex_is_at_end(buf, &current)) {
    const u8 c = lex_peek(buf, &current);

    if (!(lex_is_digit(c) || c == '_' || c == 'L'))
      break;
    lex_advance(buf, &current);
  }

  const u32 end_offset_excl = lex_get_current_offset(buf, &current);
  pg_assert(end_offset_excl > start_offset);
  pg_assert(end_offset_excl <= buf.len);

  const u32 len = end_offset_excl - start_offset;
  pg_assert(len >= 1);
  pg_assert(len <= buf.len);
  return len;
}

static u32 lex_string_length(Str buf, u32 current_offset) {
  pg_assert(current_offset < buf.len);

  const u32 start_offset = current_offset;
  const u8 *current = &buf.data[current_offset];
  pg_assert(*(current - 1) == '"');

  u8 *end_quote = memchr(current, '"', buf.len - start_offset);
  pg_assert(end_quote != NULL);

  return (u32)((u64)end_quote - (u64)current);
}

// FIXME: probably need to memoize it actually to be able to support:
// - `a.b.c = 1` => `a` has length 1.
// - `var a: kotlin.Int` => `kotlin.Int` has length 9.
static u32 lex_identifier_length(Str buf, u32 current_offset) {
  pg_assert(current_offset < buf.len);

  const u32 start_offset = current_offset;
  u8 *current = &buf.data[current_offset];
  pg_assert(ut_char_is_alphabetic(*current));

  lex_advance(buf, &current);

  while (!lex_is_at_end(buf, &current)) {
    const u8 c = lex_peek(buf, &current);

    if (!lex_is_identifier_char(c))
      break;
    lex_advance(buf, &current);
  }

  pg_assert(!lex_is_at_end(buf, &current));
  pg_assert(!lex_is_identifier_char(lex_peek(buf, &current)));

  const u32 end_offset_excl = lex_get_current_offset(buf, &current);
  pg_assert(end_offset_excl > start_offset);
  pg_assert(end_offset_excl <= buf.len);

  const u32 len = end_offset_excl - start_offset;
  pg_assert(len >= 1);
  pg_assert(len <= buf.len);
  return len;
}

static void lex_identifier(Lexer *lexer, Str buf, u8 **current, Arena *arena) {
  pg_assert(lexer != NULL);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert((u64)(*current - buf.data) <= buf.len);
  pg_assert(ut_char_is_alphabetic(**current));

  const u32 start_offset = lex_get_current_offset(buf, current);
  Str identifier = str_new(*current, lex_identifier_length(buf, start_offset));
  *current += identifier.len;
  if (str_eq_c(identifier, "fun")) {
    const Token token = {
        .kind = TOKEN_KIND_KEYWORD_FUN,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  } else if (str_eq_c(identifier, "true")) {
    const Token token = {
        .kind = TOKEN_KIND_KEYWORD_TRUE,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  } else if (str_eq_c(identifier, "false")) {
    const Token token = {
        .kind = TOKEN_KIND_KEYWORD_FALSE,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  } else if (str_eq_c(identifier, "var")) {
    const Token token = {
        .kind = TOKEN_KIND_KEYWORD_VAR,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  } else if (str_eq_c(identifier, "if")) {
    const Token token = {
        .kind = TOKEN_KIND_KEYWORD_IF,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  } else if (str_eq_c(identifier, "else")) {
    const Token token = {
        .kind = TOKEN_KIND_KEYWORD_ELSE,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  } else if (str_eq_c(identifier, "while")) {
    const Token token = {
        .kind = TOKEN_KIND_KEYWORD_WHILE,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  } else if (str_eq_c(identifier, "return")) {
    const Token token = {
        .kind = TOKEN_KIND_KEYWORD_RETURN,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  } else {
    const Token token = {
        .kind = TOKEN_KIND_IDENTIFIER,
        .source_offset = start_offset,
    };
    *array32_push(&lexer->tokens, arena) = token;
  }
}

static void lex_number(Lexer *lexer, Str buf, u8 **current, Arena *arena) {
  pg_assert(lexer != NULL);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);
  pg_assert((u64)(*current - buf.data) <= buf.len);
  pg_assert(lex_is_digit(lex_peek(buf, current)));

  const u32 start_offset = lex_get_current_offset(buf, current);

  lex_advance(buf, current);

  while (!lex_is_at_end(buf, current)) {
    const u8 c = lex_peek(buf, current);

    if (!(lex_is_digit(c) || c == '_'))
      break;
    lex_advance(buf, current);
  }

  lex_match(buf, current, 'L'); // Long suffix.

  const Token token = {
      .kind = TOKEN_KIND_NUMBER,
      .source_offset = start_offset,
  };
  *array32_push(&lexer->tokens, arena) = token;
}

static void lex_lex(Lexer *lexer, Str buf, u8 **current, Arena *arena) {
  pg_assert(lexer != NULL);
  pg_assert(current != NULL);
  pg_assert(*current != NULL);

  // tokens[0] is a dummy token.
  lexer->tokens = array32_make(Token, 1, (u32)buf.len, arena);

  // First line is 0.
  lexer->line_table = array32_make(u32, 1, (u32)buf.len, arena);

  while (!lex_is_at_end(buf, current)) {
    const u8 c = **current;

    switch (c) {
    case '(': {
      const Token token = {
          .kind = TOKEN_KIND_LEFT_PAREN,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case ')': {
      const Token token = {
          .kind = TOKEN_KIND_RIGHT_PAREN,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case ',': {
      const Token token = {
          .kind = TOKEN_KIND_COMMA,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case ':': {
      const Token token = {
          .kind = TOKEN_KIND_COLON,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case '!': {
      lex_advance(buf, current);

      if (lex_match(buf, current, '=')) {
        const Token token = {
            .kind = TOKEN_KIND_NOT_EQUAL,
            .source_offset = lex_get_current_offset(buf, current) - 2,
        };
        *array32_push(&lexer->tokens, arena) = token;
      } else {
        const Token token = {
            .kind = TOKEN_KIND_NOT,
            .source_offset = lex_get_current_offset(buf, current) - 1,
        };
        *array32_push(&lexer->tokens, arena) = token;
      }
      break;
    }
    case '{': {
      const Token token = {
          .kind = TOKEN_KIND_LEFT_BRACE,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case '}': {
      const Token token = {
          .kind = TOKEN_KIND_RIGHT_BRACE,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case '+': {
      const Token token = {
          .kind = TOKEN_KIND_PLUS,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case '-': {
      const Token token = {
          .kind = TOKEN_KIND_MINUS,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case '*': {
      const Token token = {
          .kind = TOKEN_KIND_STAR,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case '/': {
      lex_advance(buf, current);
      if (lex_match(buf, current, '/')) { // Line comment.
        lex_skip_until_incl_1(buf, current, '\n');
      } else if (lex_match(buf, current, '*')) { // Delimited comment.
        lex_skip_until_incl_2(buf, current, '*', '/');
      } else {
        const Token token = {
            .kind = TOKEN_KIND_SLASH,
            .source_offset = lex_get_current_offset(buf, current),
        };
        *array32_push(&lexer->tokens, arena) = token;
      }

      break;
    }
    case '%': {
      const Token token = {
          .kind = TOKEN_KIND_PERCENT,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case '.': {
      const Token token = {
          .kind = TOKEN_KIND_DOT,
          .source_offset = lex_get_current_offset(buf, current),
      };
      *array32_push(&lexer->tokens, arena) = token;
      lex_advance(buf, current);
      break;
    }
    case '&': {
      lex_advance(buf, current);

      if (lex_match(buf, current, '&')) {
        const Token token = {
            .kind = TOKEN_KIND_AMPERSAND_AMPERSAND,
            .source_offset = lex_get_current_offset(buf, current) - 2,
        };
        *array32_push(&lexer->tokens, arena) = token;
      } else {
        const Token token = {
            .kind = TOKEN_KIND_AMPERSAND,
            .source_offset = lex_get_current_offset(buf, current) - 1,
        };
        *array32_push(&lexer->tokens, arena) = token;
      }
      break;
    }
    case '|': {
      lex_advance(buf, current);

      if (lex_match(buf, current, '|')) {
        const Token token = {
            .kind = TOKEN_KIND_PIPE_PIPE,
            .source_offset = lex_get_current_offset(buf, current) - 2,
        };
        *array32_push(&lexer->tokens, arena) = token;
      } else {
        const Token token = {
            .kind = TOKEN_KIND_PIPE,
            .source_offset = lex_get_current_offset(buf, current) - 1,
        };
        *array32_push(&lexer->tokens, arena) = token;
      }
      break;
    }
    case '=': {
      lex_advance(buf, current);

      if (lex_match(buf, current, '=')) {
        const Token token = {
            .kind = TOKEN_KIND_EQUAL_EQUAL,
            .source_offset = lex_get_current_offset(buf, current) - 2,
        };
        *array32_push(&lexer->tokens, arena) = token;
      } else {
        const Token token = {
            .kind = TOKEN_KIND_EQUAL,
            .source_offset = lex_get_current_offset(buf, current) - 1,
        };
        *array32_push(&lexer->tokens, arena) = token;
      }
      break;
    }
    case '<': {
      lex_advance(buf, current);

      if (lex_match(buf, current, '=')) {
        const Token token = {
            .kind = TOKEN_KIND_LE,
            .source_offset = lex_get_current_offset(buf, current) - 2,
        };
        *array32_push(&lexer->tokens, arena) = token;
      } else {
        const Token token = {
            .kind = TOKEN_KIND_LT,
            .source_offset = lex_get_current_offset(buf, current) - 1,
        };
        *array32_push(&lexer->tokens, arena) = token;
      }
      break;
    }
    case '>': {
      lex_advance(buf, current);

      if (lex_match(buf, current, '=')) {
        const Token token = {
            .kind = TOKEN_KIND_GE,
            .source_offset = lex_get_current_offset(buf, current) - 2,
        };
        *array32_push(&lexer->tokens, arena) = token;
      } else {
        const Token token = {
            .kind = TOKEN_KIND_GT,
            .source_offset = lex_get_current_offset(buf, current) - 1,
        };
        *array32_push(&lexer->tokens, arena) = token;
      }
      break;
    }
    case '"': {
      lex_advance(buf, current);

      const Token token = {
          .kind = TOKEN_KIND_STRING_LITERAL,
          .source_offset = lex_get_current_offset(buf, current),
      };
      pg_assert(buf.data[token.source_offset - 1] == '"');

      while (!lex_match(buf, current, '"')) {
        lex_advance(buf, current);
      }
      *array32_push(&lexer->tokens, arena) = token;
      break;
    }
    case '\n': {
      lex_advance(buf, current);

      if (!lex_is_at_end(buf, current))
        *array32_push(&lexer->line_table, arena) =
            lex_get_current_offset(buf, current);

      break;
    }
    case ' ': {
      lex_advance(buf, current);
      break;
    }
    default: {
      if (ut_char_is_alphabetic(c)) {
        lex_identifier(lexer, buf, current, arena);
      } else if (lex_is_digit(c)) {
        lex_number(lexer, buf, current, arena);
      } else {
        pg_assert(0 && "unimplemented");
      }
    }
    }
  }
  // Ensure the line table has at least 2 items: line_table=[0]=0,
  // line_table[last]=buf.len, for easier logic later to find token
  // positions.
  *array32_push(&lexer->line_table, arena) = (u32)buf.len;
}

static u32 lex_find_token_length(const Lexer *lexer, Str buf, Token token) {
  pg_assert(lexer != NULL);

  switch (token.kind) {
  case TOKEN_KIND_NONE:
    return 0;
  case TOKEN_KIND_PLUS:
  case TOKEN_KIND_MINUS:
  case TOKEN_KIND_STAR:
  case TOKEN_KIND_SLASH:
  case TOKEN_KIND_PERCENT:
  case TOKEN_KIND_LEFT_PAREN:
  case TOKEN_KIND_RIGHT_PAREN:
  case TOKEN_KIND_LEFT_BRACE:
  case TOKEN_KIND_RIGHT_BRACE:
  case TOKEN_KIND_COMMA:
  case TOKEN_KIND_DOT:
  case TOKEN_KIND_COLON:
  case TOKEN_KIND_NOT:
  case TOKEN_KIND_EQUAL:
  case TOKEN_KIND_LT:
  case TOKEN_KIND_GT:
  case TOKEN_KIND_AMPERSAND:
  case TOKEN_KIND_PIPE:
    return 1;
  case TOKEN_KIND_KEYWORD_IF:
  case TOKEN_KIND_NOT_EQUAL:
  case TOKEN_KIND_LE:
  case TOKEN_KIND_GE:
  case TOKEN_KIND_EQUAL_EQUAL:
  case TOKEN_KIND_AMPERSAND_AMPERSAND:
  case TOKEN_KIND_PIPE_PIPE:
    return 2;
  case TOKEN_KIND_KEYWORD_FUN:
  case TOKEN_KIND_KEYWORD_VAR:
    return 3;
  case TOKEN_KIND_KEYWORD_TRUE:
  case TOKEN_KIND_KEYWORD_ELSE:
    return 4;
  case TOKEN_KIND_KEYWORD_FALSE:
  case TOKEN_KIND_KEYWORD_WHILE:
    return 5;
  case TOKEN_KIND_KEYWORD_RETURN:
    return 6;

  case TOKEN_KIND_NUMBER:
    return lex_number_length(buf, token.source_offset);

  case TOKEN_KIND_IDENTIFIER:
    return lex_identifier_length(buf, token.source_offset);

  case TOKEN_KIND_STRING_LITERAL:
    return lex_string_length(buf, token.source_offset);

  default:
    pg_assert(0 && "unreachable");
  }
  __builtin_unreachable();
}

// ------------------------------ Parser

static void ut_fwrite_indent(FILE *file, u16 indent) {
  for (u16 i = 0; i < indent; i++) {
    fputc(' ', file);
  }
}

static void parser_find_token_position(const Parser *parser, Token token,
                                       u32 *line, u32 *column,
                                       Str *token_string) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(line != NULL);
  pg_assert(column != NULL);
  pg_assert(token_string != NULL);
  pg_assert(parser->lexer->line_table.len > 1);

  *token_string = (Str){
      .data = &parser->buf.data[token.source_offset],
      .len = lex_find_token_length(parser->lexer, parser->buf, token),
  };

  for (u32 i = 0; i < parser->lexer->line_table.len - 1; i++) {
    const u32 line_start_offset = parser->lexer->line_table.data[i];
    const u32 line_end_offset_excl = parser->lexer->line_table.data[i + 1];
    if (line_start_offset <= token.source_offset &&
        token.source_offset <= line_end_offset_excl) {
      *line = i + 1;
      *column = 1 + token.source_offset - line_start_offset;

      return;
    }
  }
  pg_assert(*line <= parser->lexer->line_table.len);
}

static char *typechecker_type_kind_string(Type_handle type_handle,
                                          Arena arena) {
  switch (type_handle_to_ptr(type_handle, arena)->kind) {
  case TYPE_ANY:
    return "TYPE_ANY";
  case TYPE_UNIT:
    return "TYPE_UNIT";
  case TYPE_BOOLEAN:
    return "TYPE_BOOLEAN";
  case TYPE_BYTE:
    return "TYPE_BYTE";
  case TYPE_CHAR:
    return "TYPE_CHAR";
  case TYPE_SHORT:
    return "TYPE_SHORT";
  case TYPE_INT:
    return "TYPE_INT";
  case TYPE_FLOAT:
    return "TYPE_FLOAT";
  case TYPE_LONG:
    return "TYPE_LONG";
  case TYPE_DOUBLE:
    return "TYPE_DOUBLE";
  case TYPE_STRING:
    return "TYPE_STRING";
  case TYPE_METHOD:
    return "TYPE_METHOD";
  case TYPE_CONSTRUCTOR:
    return "TYPE_CONSTRUCTOR";
  case TYPE_ARRAY:
    return "TYPE_ARRAY";
  case TYPE_INSTANCE:
    return "TYPE_INSTANCE";
  case TYPE_INTEGER_LITERAL:
    return "TYPE_INTEGER_LITERAL";
  }
  pg_assert(0 && "unreachable");
}

static Str type_to_human_string(Type_handle type_handle, Arena *arena) {
  const Type *const type = type_handle_to_ptr(type_handle, *arena);

  switch (type->kind) {
  case TYPE_ANY:
    return str_from_c("kotlin.Any");
  case TYPE_BOOLEAN:
    return str_from_c("kotlin.Boolean");
  case TYPE_BYTE:
    return str_from_c("kotlin.Byte");
  case TYPE_CHAR:
    return str_from_c("kotlin.Char");
  case TYPE_SHORT:
    return str_from_c("kotlin.Short");
  case TYPE_INT:
    return str_from_c("kotlin.Int");
  case TYPE_FLOAT:
    return str_from_c("kotlin.Float");
  case TYPE_LONG:
    return str_from_c("kotlin.Long");
  case TYPE_DOUBLE:
    return str_from_c("kotlin.Double");
  case TYPE_STRING:
    return str_from_c("kotlin.String");
  case TYPE_UNIT:
    return str_from_c("kotlin.Unit");
  case TYPE_ARRAY: {
    Str_builder res = sb_new(type->this_class_name.len + 256, arena);
    res = sb_append_c(res, "Array<", arena);
    res = sb_append(res, type_to_human_string(type->v.array_type_handle, arena),
                    arena);
    res = sb_append_char(res, '>', arena);
    return sb_build(res);
  }
  case TYPE_INSTANCE: {
    return type->this_class_name;
  }
  case TYPE_METHOD:
  case TYPE_CONSTRUCTOR: {
    const Method *const method_type = &type->v.method;

    Str_builder res = sb_new(128, arena);
    res = sb_append_c(res, "(", arena);
    for (u64 i = 0; i < method_type->argument_type_handles.len; i++) {
      const Type_handle argument_type_handle =
          method_type->argument_type_handles.data[i];
      res = sb_append(res, type_to_human_string(argument_type_handle, arena),
                      arena);

      if (i < method_type->argument_type_handles.len - 1)
        res = sb_append_c(res, ", ", arena);
    }
    res = sb_append_c(res, "): ", arena);
    res = sb_append(
        res, type_to_human_string(method_type->return_type_handle, arena),
        arena);
    return sb_build(res);
  }
  case TYPE_INTEGER_LITERAL: {
    const u32 possible_types = type->v.integer_literal_types;
    Str_builder res = sb_new(128, arena);
    res = sb_append_c(res, "Integer literal: ", arena);

    if (possible_types & TYPE_BYTE)
      res = sb_append_c(res, "kotlin.Byte | ", arena);
    if (possible_types & TYPE_SHORT)
      res = sb_append_c(res, "kotlin.Short | ", arena);
    if (possible_types & TYPE_INT)
      res = sb_append_c(res, "kotlin.Int | ", arena);
    if (possible_types & TYPE_LONG)
      res = sb_append_c(res, "kotlin.Long | ", arena);

    return sb_build(res);
  }
  }
  pg_assert(0 && "unreachable");
}

static bool parser_is_at_end(const Parser *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser->tokens_i == parser->lexer->tokens.len;
}

static Token parser_peek_token(const Parser *parser) {
  pg_assert(parser != NULL);
  if (parser->tokens_i > parser->lexer->tokens.len - 1)
    return (Token){0};

  return parser->lexer->tokens.data[parser->tokens_i];
}

static Token parser_peek_next_token(const Parser *parser) {
  pg_assert(parser != NULL);
  if (parser->tokens_i > parser->lexer->tokens.len - 2)
    return (Token){0};

  return parser->lexer->tokens.data[parser->tokens_i + 1];
}

static void parser_advance_token(Parser *parser) {
  pg_assert(parser != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  // TODO: should we clamp it to the length?
  parser->tokens_i++;
}

static bool parser_match_token(Parser *parser, Token_kind kind) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (parser_peek_token(parser).kind == kind) {
    parser_advance_token(parser);
    return true;
  }
  return false;
}

static void parser_error(Parser *parser, Token token, const char *error) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  switch (parser->state) {
  case PARSER_STATE_OK: {
    u32 line = 0;
    u32 column = 0;
    Str token_string = {0};
    parser_find_token_position(parser, token, &line, &column, &token_string);

    fprintf(stderr, "%.*s:%u:%u: around `%.*s`, %s\n",
            (int)parser->lexer->file_path.len, parser->lexer->file_path.data,
            line, column, (int)token_string.len, token_string.data, error);

    parser->state = PARSER_STATE_ERROR;
    break;
  }
  case PARSER_STATE_ERROR:
    parser->state = PARSER_STATE_PANIC;
    break;
  case PARSER_STATE_PANIC:
  case PARSER_STATE_SYNCED:
    break;
  }
}

static void parser_expect_token(Parser *parser, Token_kind kind,
                                const char *error) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (!parser_match_token(parser, kind)) {
    parser_error(parser, parser_peek_token(parser), error);
  }
}

static const u8 NODE_NUMBER_FLAGS_OVERFLOW = 1 << 0;
static const u8 NODE_NUMBER_FLAGS_FLOAT = 1 << 4;
static const u8 NODE_NUMBER_FLAGS_DOUBLE = 1 << 5;
static const u8 NODE_NUMBER_FLAGS_LONG = 1 << 6;

static u64 parser_number(const Parser *parser, Token token, u8 *flag) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(flag != NULL);

  pg_assert(token.kind == TOKEN_KIND_NUMBER);

  const u32 start = token.source_offset;
  const u32 length = lex_number_length(parser->buf, start);
  pg_assert(length <= 20);

  u64 number = 0;

  u64 ten_unit = 1;
  for (u32 i = 1; i <= length; i++) {
    pg_assert(i < parser->buf.len);

    const u32 position = start + length - i;
    pg_assert(start <= position);

    const u8 c = parser->buf.data[position];
    pg_assert(lex_is_digit(c) || c == 'L' || c == '_');
    if (c == '_')
      continue;
    // > An integer literal with the long literal mark has type kotlin.Long.
    if (c == 'L') {
      *flag |= NODE_NUMBER_FLAGS_LONG;
      continue;
    }

    const u64 delta = ten_unit * (c - '0');
    i64 number_i64 = (i64)number;
    // > If the value is greater than maximum kotlin.Long value (see built-in
    // integer types), it is an illegal integer literal and should be a
    // compile-time error;
    if (__builtin_add_overflow((i64)number_i64, delta, &number_i64)) {
      *flag |= NODE_NUMBER_FLAGS_OVERFLOW;
      return 0;
    }
    number += delta;
    ten_unit *= 10;
  }

  // > if the value is greater than maximum kotlin.Int value (see built-in
  // integer types), it has type kotlin.Long;
  if (INT32_MAX < number && number <= INT64_MAX)
    *flag |= NODE_NUMBER_FLAGS_LONG;

  // TODO: Float, Double.

  return number;
}

static Str parser_token_to_str_view(Parser *parser, u32 token_i) {
  pg_assert(parser != NULL);
  pg_assert(token_i < parser->lexer->tokens.len);

  const Token token = parser->lexer->tokens.data[token_i];

  return (Str){
      .data = &parser->buf.data[token.source_offset],
      .len = lex_find_token_length(parser->lexer, parser->buf, token),
  };
}

static Str parser_token_range_to_string(Parser *parser, u32 start_token_incl_i,
                                        u32 end_token_excl_i) {
  pg_assert(parser != NULL);
  pg_assert(start_token_incl_i < parser->lexer->tokens.len);
  pg_assert(end_token_excl_i <= parser->lexer->tokens.len);

  const u32 start_token_incl_source_offset =
      parser->lexer->tokens.data[start_token_incl_i].source_offset;
  const u32 end_token_excl_source_offset =
      end_token_excl_i == parser->lexer->tokens.len
          ? (u32)parser->buf.len
          : parser->lexer->tokens.data[end_token_excl_i].source_offset;

  return (Str){
      .data = &parser->buf.data[start_token_incl_source_offset],
      .len = end_token_excl_source_offset - start_token_incl_source_offset,
  };
}

static Ast_handle parser_parse_expression(Parser *parser, Arena *arena);
static Ast_handle parser_parse_block(Parser *parser, Arena *arena);
static Ast_handle parser_parse_postfix_unary_expression(Parser *parser,
                                                        Arena *arena);
static Ast_handle parser_parse_statements(Parser *parser, Arena *arena);
static Ast_handle parser_parse_declaration(Parser *parser, Arena *arena);
static Ast_handle parser_parse_statement(Parser *parser, Arena *arena);
static Ast_handle parser_parse_type(Parser *parser, Arena *arena);

// block:
//     '{'
//     {NL}
//     statements
//     {NL}
//     '}'
static Ast_handle parser_parse_block(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  parser_expect_token(parser, TOKEN_KIND_LEFT_BRACE,
                      "Expected a left curly brace to start a block");
  const Ast_handle ast_handle = parser_parse_statements(parser, arena);
  parser_expect_token(parser, TOKEN_KIND_RIGHT_BRACE,
                      "Expected a right curly brace to end a block");
  return ast_handle;
}

// controlStructureBody:
//     block
//     | statement
static Ast_handle parser_parse_control_structure_body(Parser *parser,
                                                      Arena *arena) {
  pg_assert(parser);
  pg_assert(arena);

  if (parser_peek_token(parser).kind == TOKEN_KIND_LEFT_BRACE)
    return parser_parse_block(parser, arena);
  else
    return parser_parse_statement(parser, arena);
}

//  'if'
//  {NL}
//  '('
//  {NL}
//  expression
//  {NL}
//  ')'
//  {NL}
//  (controlStructureBody | ([controlStructureBody] {NL} [';'] {NL} 'else'
//  {NL} (controlStructureBody | ';')) | ';')
static Ast_handle parser_parse_if_expression(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const u32 main_token_i = parser->tokens_i - 1;

  parser_expect_token(parser, TOKEN_KIND_LEFT_PAREN,
                      "expected left parenthesis following if");

  const Ast_handle condition_handle = parser_parse_expression(parser, arena);

  parser_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                      "expected right parenthesis following if condition");

  // clang-format off
  //
  //               IF 
  //              /  \
  //    condition     THEN_ELSE )
  //                 /      \
  //             then        else
  //
  // clang-format on

  const Ast binary_node = {
      .kind = AST_KIND_THEN_ELSE,
      .main_token_i = parser->tokens_i - 1,
      .lhs = parser_parse_control_structure_body(parser, arena), // Then
      .rhs = parser_match_token(parser, TOKEN_KIND_KEYWORD_ELSE)
                 ? parser_parse_control_structure_body(parser, arena)
                 : ast_handle_nil,
  };
  const Ast_handle binary_ast_handle = new_ast(&binary_node, arena);

  const Ast if_node = {
      .kind = AST_KIND_IF,
      .main_token_i = main_token_i,
      .lhs = condition_handle,
      .rhs = binary_ast_handle,
  };
  return new_ast(&if_node, arena);
}

// jumpExpression:
//     ('throw' {NL} expression)
//     | (('return' | RETURN_AT) [expression])
//     | 'continue'
//     | CONTINUE_AT
//     | 'break'
//     | BREAK_AT
static Ast_handle parser_parse_jump_expression(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  // TODO: check we are in a function.
  if (parser_match_token(parser, TOKEN_KIND_KEYWORD_RETURN)) {
    if (ast_handle_is_nil(parser->current_function_handle)) {
      parser_error(parser, parser_peek_token(parser),
                   "code outside of a function body");
      return ast_handle_nil;
    }

    const Ast node = {.kind = AST_KIND_RETURN,
                      .main_token_i = parser->tokens_i - 1,
                      .lhs = parser_parse_expression(parser, arena)};
    return new_ast(&node, arena);
  }
  return ast_handle_nil;
}

// primaryExpression:
//     parenthesizedExpression
//     | simpleIdentifier
//     | literalConstant
//     | stringLiteral
//     | callableReference
//     | functionLiteral
//     | objectLiteral
//     | collectionLiteral
//     | thisExpression
//     | superExpression
//     | ifExpression
//     | whenExpression
//     | tryExpression
//     | jumpExpression
static Ast_handle parser_parse_primary_expression(Parser *parser,
                                                  Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (parser_match_token(parser, TOKEN_KIND_NUMBER)) {

    const Ast node = {
        .kind = AST_KIND_NUMBER,
        .main_token_i = parser->tokens_i - 1,
    };
    return new_ast(&node, arena);
  } else if (parser_match_token(parser, TOKEN_KIND_KEYWORD_FALSE) ||
             parser_match_token(parser, TOKEN_KIND_KEYWORD_TRUE)) {
    const Token token = parser->lexer->tokens.data[parser->tokens_i - 1];
    const bool is_true = parser->buf.data[token.source_offset] == 't';
    const Ast node = {
        .kind = AST_KIND_BOOL,
        .main_token_i = parser->tokens_i - 1,
        .extra_data = is_true,
    };
    return new_ast(&node, arena);
  } else if (parser_match_token(parser, TOKEN_KIND_LEFT_PAREN)) {
    const Ast_handle ast_handle = parser_parse_expression(parser, arena);
    // TODO: Locate left parenthesis for the error message.
    parser_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                        "Expected matching right parenthesis");
    return ast_handle;
  } else if (parser_match_token(parser, TOKEN_KIND_IDENTIFIER)) {
    Ast node = {
        .kind = AST_KIND_UNRESOLVED_NAME,
        .main_token_i = parser->tokens_i - 1,
    };
    return new_ast(&node, arena);
  } else if (parser_match_token(parser, TOKEN_KIND_STRING_LITERAL)) {
    const Ast node = {.kind = AST_KIND_STRING,
                      .main_token_i = parser->tokens_i - 1};
    return new_ast(&node, arena);
  } else if (parser_match_token(parser, TOKEN_KIND_KEYWORD_IF)) {
    return parser_parse_if_expression(parser, arena);
  } else if (parser_peek_token(parser).kind ==
             TOKEN_KIND_KEYWORD_RETURN) { // TODO: More.
    return parser_parse_jump_expression(parser, arena);
  }

  return ast_handle_nil;
}

// multiVariableDeclaration:
//     '('
//     {NL}
//     variableDeclaration
//     {{NL} ',' {NL} variableDeclaration}
//     [{NL} ',']
//     {NL}
//     ')'
static Ast_handle parser_parse_var_declaration(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  parser_expect_token(parser, TOKEN_KIND_IDENTIFIER,
                      "expected variable name (identifier)");
  const u32 name_token_i = parser->tokens_i - 1;

  parser_expect_token(parser, TOKEN_KIND_COLON,
                      "expected colon between variable name and type");

  const Ast_handle node_type_handle = parser_parse_type(parser, arena);

  parser_expect_token(parser, TOKEN_KIND_EQUAL, "expected type");

  const Ast node = {
      .kind = AST_KIND_VAR_DEFINITION,
      .main_token_i = name_token_i,
      .lhs = node_type_handle,
      .rhs = parser_parse_expression(parser, arena),
  };
  return new_ast(&node, arena);
}

static bool parser_is_lvalue(const Parser *parser, Ast_handle ast_handle,
                             Arena arena) {
  pg_assert(parser != NULL);

  const Ast *const node = ast_handle_to_ptr(ast_handle, arena);
  switch (node->kind) {
  case AST_KIND_VAR_REFERENCE:
    return true;
    // TODO: more

  default:
    return false;
  }
}

// assignment:
//     ((directlyAssignableExpression '=') | (assignableExpression
//     assignmentAndOperator)) {NL} expression
static Ast_handle parser_parse_assignment(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  // We could here try to parse a `directlyAssignableExpression`, and if it
  // fails, or if it succeeds but the next token is *not* `TOKEN_KIND_EQUAL`,
  // backtrack.
  // But that potentially means we are parsing twice every
  // expression and lots of expensive cloning/resetting.
  // Instead, we first parse it as an expression, and if the next
  // token is `TOKEN_KIND_EQUAL`, we check that this expression was indeed a
  // lvalue. Otherwise, we just return this expression, no more work to do.
  Ast_handle lhs_handle = parser_parse_expression(parser, arena);

  if (parser_match_token(parser, TOKEN_KIND_EQUAL)) { // Assignment
    const u32 main_token_i = parser->tokens_i - 1;

    const Ast node = {
        .kind = AST_KIND_ASSIGNMENT,
        .lhs = lhs_handle,
        .main_token_i = main_token_i,
        .rhs = parser_parse_expression(parser, arena),
    };
    return new_ast(&node, arena);
  }

  return lhs_handle;
}
// whileStatement:
//     'while'
//     {NL}
//     '('
//     expression
//     ')'
//     {NL}
//     (controlStructureBody | ';')
static Ast_handle parser_parse_while_statement(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  const u32 main_token_i = parser->tokens_i - 1;
  parser_expect_token(parser, TOKEN_KIND_LEFT_PAREN,
                      "Expect left parenthesis after the while keyword");

  const Ast_handle condition_handle = parser_parse_expression(parser, arena);

  parser_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                      "Expect right parenthesis after the while condition");

  const Ast node = {
      .kind = AST_KIND_WHILE_LOOP,
      .main_token_i = main_token_i,
      .lhs = condition_handle,
  };
  const Ast_handle ast_handle = new_ast(&node, arena);

  ast_handle_to_ptr(ast_handle, *arena)->rhs =
      parser_parse_control_structure_body(parser, arena);

  return ast_handle;
}

static Ast_handle parser_parse_loop_statement(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  if (parser_match_token(parser, TOKEN_KIND_KEYWORD_WHILE))
    return parser_parse_while_statement(parser, arena);

  return ast_handle_nil;
}

// statement:
//     {label | annotation} (declaration | assignment | loopStatement |
//     expression)
static Ast_handle parser_parse_statement(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (ast_handle_is_nil(parser->current_function_handle)) {
    parser_error(parser, parser_peek_token(parser),
                 "code outside of a function body");
  }

  Ast_handle ast_handle = {0};
  if (!ast_handle_is_nil(ast_handle =
                             parser_parse_loop_statement(parser, arena)))
    return ast_handle;

  if (!ast_handle_is_nil(ast_handle = parser_parse_declaration(parser, arena)))
    return ast_handle;

  if (!ast_handle_is_nil(ast_handle = parser_parse_assignment(parser, arena)))
    return ast_handle;

  return parser_parse_expression(parser, arena);
}

// navigationSuffix:
//     memberAccessOperator {NL} (simpleIdentifier | parenthesizedExpression |
//     'class')
static Ast_handle parser_parse_navigation_suffix(Parser *parser,
                                                 u32 *main_token_i,
                                                 Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(main_token_i != NULL);
  pg_assert(arena != NULL);

  if (!parser_match_token(parser, TOKEN_KIND_DOT))
    return ast_handle_nil;

  *main_token_i = parser->tokens_i - 1;

  if (parser_match_token(parser, TOKEN_KIND_IDENTIFIER)) {
    const Ast node = {
        .kind = AST_KIND_NAVIGATION,
        .main_token_i = parser->tokens_i - 1,
    };
    return new_ast(&node, arena);
  }

  if (parser_match_token(parser, TOKEN_KIND_LEFT_PAREN)) {
    const Ast_handle ast_handle = parser_parse_expression(parser, arena);
    parser_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                        "Expected matching right parenthesis after expression");
    return ast_handle;
  }

  pg_assert(0 && "todo"); // TODO: `class`
}

// valueArguments:
//     '(' {NL} [valueArgument {{NL} ',' {NL} valueArgument} [{NL} ','] {NL}]
//     ')'
static Array32(Ast_handle)
    parser_parse_value_arguments(Parser *parser, Arena *arena) {

  Array32(Ast_handle) nodes = array32_make(Ast_handle, 0, 256, arena);

  while (!parser_is_at_end(parser)) {
    Ast_handle argument_i = parser_parse_expression(parser, arena);
    if (ast_handle_is_nil(argument_i)) {
      const Token main_token = parser->lexer->tokens.data[parser->tokens_i];
      parser_error(
          parser, main_token,
          "Expected expression or closing right parenthesis for function "
          "arguments");
      return nodes;
    }
    *array32_push(&nodes, arena) = argument_i;

    parser_match_token(parser, TOKEN_KIND_COMMA);

    if (parser_match_token(parser, TOKEN_KIND_RIGHT_PAREN))
      break;
  }

  if (parser_is_at_end(parser)) {
    parser_error(parser, *array32_last(parser->lexer->tokens),
                 "Expect matching right parenthesis after function call");
  }
  return nodes;
}

// callSuffix:
//     [typeArguments] (([valueArguments] annotatedLambda) | valueArguments)
static Ast_handle parser_parse_call_suffix(Parser *parser, u32 *main_token_i,
                                           Arena *arena) {
  if (!parser_match_token(parser, TOKEN_KIND_LEFT_PAREN))
    return ast_handle_nil;

  *main_token_i = parser->tokens_i - 1;
  Ast node = {
      .kind = AST_KIND_CALL,
      .main_token_i = parser->tokens_i - 1,
  };

  // Calling a function with zero arguments.
  if (parser_match_token(parser, TOKEN_KIND_RIGHT_PAREN)) {
    return new_ast(&node, arena);
  }

  node.nodes = parser_parse_value_arguments(parser, arena);

  return new_ast(&node, arena);
}

// postfixUnarySuffix:
//     postfixUnaryOperator
//     | typeArguments
//     | callSuffix
//     | indexingSuffix
//     | navigationSuffix
static Ast_handle parser_parse_postfix_unary_suffix(Parser *parser,
                                                    u32 *main_token_i,
                                                    Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(main_token_i != NULL);
  pg_assert(arena != NULL);

  if (parser_peek_token(parser).kind == TOKEN_KIND_DOT)
    return parser_parse_navigation_suffix(parser, main_token_i, arena);

  return parser_parse_call_suffix(parser, main_token_i, arena);
}

// postfixUnaryExpression:
//     primaryExpression {postfixUnarySuffix}
static Ast_handle parser_parse_postfix_unary_expression(Parser *parser,
                                                        Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  Ast_handle lhs_handle = parser_parse_primary_expression(parser, arena);

  u32 main_token_i = 0;
  // TODO: multiple suffixes.
  const Ast_handle rhs_handle =
      parser_parse_postfix_unary_suffix(parser, &main_token_i, arena);
  if (ast_handle_is_nil(rhs_handle))
    return lhs_handle;

  ast_handle_to_ptr(rhs_handle, *arena)->lhs = lhs_handle;

  return rhs_handle;
}

// prefixUnaryExpression:
//     {unaryPrefix} postfixUnaryExpression
static Ast_handle parser_parse_prefix_unary_expression(Parser *parser,
                                                       Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (parser_match_token(parser, TOKEN_KIND_NOT) ||
      parser_match_token(parser, TOKEN_KIND_MINUS)) {
    const Ast node = {
        .kind = AST_KIND_UNARY,
        .lhs = parser_parse_prefix_unary_expression(parser, arena),
        .main_token_i = parser->tokens_i - 1,
    };
    return new_ast(&node, arena);
  }

  return parser_parse_postfix_unary_expression(parser, arena);
}

// asExpression:
//     prefixUnaryExpression {{NL} asOperator {NL} type}
static Ast_handle parser_parse_as_expression(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser_parse_prefix_unary_expression(parser, arena);
}

// multiplicativeExpression:
//     asExpression {multiplicativeOperator {NL} asExpression}
static Ast_handle parser_parse_multiplicative_expression(Parser *parser,
                                                         Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const Ast_handle ast_handle = parser_parse_as_expression(parser, arena);
  if (!(parser_match_token(parser, TOKEN_KIND_STAR) ||
        parser_match_token(parser, TOKEN_KIND_SLASH) ||
        parser_match_token(parser, TOKEN_KIND_PERCENT)))
    return ast_handle;

  const Ast node = {
      .kind = AST_KIND_BINARY,
      .lhs = ast_handle,
      .main_token_i = parser->tokens_i - 1,
      .rhs = parser_parse_multiplicative_expression(parser, arena),
  };
  return new_ast(&node, arena);
}

// additiveExpression:
//     multiplicativeExpression {additiveOperator {NL}
//     multiplicativeExpression}
static Ast_handle parser_parse_additive_expression(Parser *parser,
                                                   Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const Ast_handle ast_handle =
      parser_parse_multiplicative_expression(parser, arena);
  if (!(parser_match_token(parser, TOKEN_KIND_PLUS) ||
        parser_match_token(parser, TOKEN_KIND_MINUS)))
    return ast_handle;

  const Ast node = {
      .kind = AST_KIND_BINARY,
      .lhs = ast_handle,
      .main_token_i = parser->tokens_i - 1,
      .rhs = parser_parse_additive_expression(parser, arena),
  };
  return new_ast(&node, arena);
}

// rangeExpression:
//     additiveExpression {'..' {NL} additiveExpression}
static Ast_handle parser_parse_range_expression(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser_parse_additive_expression(parser, arena);
}

// infixFunctionCall:
//     rangeExpression {simpleIdentifier {NL} rangeExpression}
static Ast_handle parser_parse_infix_function_call(Parser *parser,
                                                   Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser_parse_range_expression(parser, arena);
}

// elvisExpression:
//     infixFunctionCall {{NL} elvis {NL} infixFunctionCall}
static Ast_handle parser_parse_elvis_expression(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser_parse_infix_function_call(parser, arena);
}

// infixOperation:
//     elvisExpression {(inOperator {NL} elvisExpression) | (isOperator {NL}
//     type)}
static Ast_handle parser_parse_infix_operation(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser_parse_elvis_expression(parser, arena);
}

// genericCallLikeComparison:
//     infixOperation {callSuffix}
static Ast_handle parser_parse_generic_call_like_comparison(Parser *parser,
                                                            Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser_parse_infix_operation(parser, arena);
}

// comparison:
//     genericCallLikeComparison {comparisonOperator {NL}
//     genericCallLikeComparison}
static Ast_handle parser_parse_comparison(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const Ast_handle ast_handle =
      parser_parse_generic_call_like_comparison(parser, arena);
  if (!(parser_match_token(parser, TOKEN_KIND_LT) ||
        parser_match_token(parser, TOKEN_KIND_GT) ||
        parser_match_token(parser, TOKEN_KIND_LE) ||
        parser_match_token(parser, TOKEN_KIND_GE)))
    return ast_handle;

  const Ast node = {
      .kind = AST_KIND_BINARY,
      .lhs = ast_handle,
      .main_token_i = parser->tokens_i - 1,
      .rhs = parser_parse_comparison(parser, arena),
  };
  return new_ast(&node, arena);
}

// equality:
//     comparison {equalityOperator {NL} comparison}
static Ast_handle parser_parse_equality(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const Ast_handle ast_handle = parser_parse_comparison(parser, arena);
  if (!(parser_match_token(parser, TOKEN_KIND_EQUAL_EQUAL) ||
        parser_match_token(parser, TOKEN_KIND_NOT_EQUAL)))
    return ast_handle;

  const Ast node = {
      .kind = AST_KIND_BINARY,
      .lhs = ast_handle,
      .main_token_i = parser->tokens_i - 1,
      .rhs = parser_parse_equality(parser, arena),
  };
  return new_ast(&node, arena);
}

// conjunction:
//     equality {{NL} '&&' {NL} equality}
static Ast_handle parser_parse_conjunction(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const Ast_handle ast_handle = parser_parse_equality(parser, arena);
  if (!parser_match_token(parser, TOKEN_KIND_AMPERSAND_AMPERSAND))
    return ast_handle;

  const Ast node = {
      .kind = AST_KIND_BINARY,
      .lhs = ast_handle,
      .main_token_i = parser->tokens_i - 1,
      .rhs = parser_parse_conjunction(parser, arena),
  };
  return new_ast(&node, arena);
}

// disjunction:
//     conjunction {{NL} '||' {NL} conjunction}
static Ast_handle parser_parse_disjunction(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  const Ast_handle ast_handle = parser_parse_conjunction(parser, arena);
  if (!parser_match_token(parser, TOKEN_KIND_PIPE_PIPE))
    return ast_handle;

  const Ast node = {
      .kind = AST_KIND_BINARY,
      .lhs = ast_handle,
      .main_token_i = parser->tokens_i - 1,
      .rhs = parser_parse_disjunction(parser, arena),
  };
  return new_ast(&node, arena);
}

// expression:
//     disjunction
static Ast_handle parser_parse_expression(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  return parser_parse_disjunction(parser, arena);
}

// statements:
//     [statement {semis statement}] [semis]
static Ast_handle parser_parse_statements(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (parser_peek_token(parser).kind == TOKEN_KIND_RIGHT_BRACE)
    return ast_handle_nil;

  Ast_handle ast_handle = parser_parse_statement(parser, arena);
  if (ast_handle_is_nil(ast_handle))
    return ast_handle;

  Ast node = {.kind = AST_KIND_LIST};
  *array32_push(&node.nodes, arena) = ast_handle;

  while (!ast_handle_is_nil(ast_handle = parser_parse_statement(parser, arena)))
    *array32_push(&node.nodes, arena) = ast_handle;

  return new_ast(&node, arena);
}

// TODO: Parse more complex types.
// type:
//     [typeModifiers] (functionType | parenthesizedType | nullableType |
//     typeReference | definitelyNonNullableType)
static Ast_handle parser_parse_type(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(arena != NULL);

  parser_expect_token(
      parser, TOKEN_KIND_IDENTIFIER,
      "expected an identifier for the type of the function parameter");

  const Ast node = {
      .kind = AST_KIND_TYPE,
      .main_token_i = parser->tokens_i - 1,
  };

  // userType:
  //     simpleUserType {{NL} '.' {NL} simpleUserType}
  while (parser_peek_token(parser).kind == TOKEN_KIND_DOT &&
         parser_peek_next_token(parser).kind == TOKEN_KIND_IDENTIFIER) {
    parser_advance_token(parser);
    parser_advance_token(parser);
  }

  return new_ast(&node, arena);
}

// parameter:
//     simpleIdentifier
//     {NL}
//     ':'
//     {NL}
//     type
static Ast_handle parser_parse_parameter(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(arena != NULL);

  parser_expect_token(
      parser, TOKEN_KIND_IDENTIFIER,
      "expected an identifier for the name of the function parameter");

  const u32 name_i = parser->tokens_i - 1;

  parser_expect_token(
      parser, TOKEN_KIND_COLON,
      "expected a colon between the function parameter name and type");

  const Ast node = {
      .kind = AST_KIND_FUNCTION_PARAMETER,
      .main_token_i = name_i,
      .lhs = parser_parse_type(parser, arena),
  };
  const Ast_handle ast_handle = new_ast(&node, arena);

  return ast_handle;
}

// functionValueParameter:
//     [parameterModifiers] parameter [{NL} '=' {NL} expression]
static Ast_handle parser_parse_function_value_parameter(Parser *parser,
                                                        Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(arena != NULL);

  return parser_parse_parameter(parser, arena);
}

// functionValueParameters:
//     '('
//     {NL}
//     [functionValueParameter {{NL} ',' {NL} functionValueParameter} [{NL}
//     ',']] {NL}
//     ')'
static Ast_handle parser_parse_function_value_parameters(Parser *parser,
                                                         Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  // No arguments.
  if (parser_match_token(parser, TOKEN_KIND_RIGHT_PAREN))
    return ast_handle_nil;

  Ast node = {.kind = AST_KIND_LIST};

  do {
    *array32_push(&node.nodes, arena) =
        parser_parse_function_value_parameter(parser, arena);
  } while (parser_match_token(parser, TOKEN_KIND_COMMA));

  parser_expect_token(parser, TOKEN_KIND_RIGHT_PAREN,
                      "expected right parenthesis after the arguments");
  return new_ast(&node, arena);
}

// functionBody:
//     block
//     | ('=' {NL} expression)
static Ast_handle parser_parse_function_body(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  return parser_parse_block(parser, arena);
}

// functionDeclaration:
//     [modifiers]
//     'fun'
//     [{NL} typeParameters]
//     [{NL} receiverType {NL} '.']
//     {NL}
//     simpleIdentifier
//     {NL}
//     functionValueParameters
//     [{NL} ':' {NL} type]
//     [{NL} typeConstraints]
//     [{NL} functionBody]
static Ast_handle parser_parse_function_declaration(Parser *parser,
                                                    Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (!parser_match_token(parser, TOKEN_KIND_KEYWORD_FUN))
    return ast_handle_nil;

  parser_expect_token(parser, TOKEN_KIND_IDENTIFIER,
                      "expected function name (identifier)");
  const u32 start_token = parser->tokens_i - 1;

  Ast node = {
      .kind = AST_KIND_FUNCTION_DEFINITION,
      .main_token_i = start_token,
  };

  const Ast_handle fn_i = parser->current_function_handle =
      new_ast(&node, arena);

  parser_expect_token(parser, TOKEN_KIND_LEFT_PAREN,
                      "expected left parenthesis before the arguments");

  ast_handle_to_ptr(parser->current_function_handle, *arena)->lhs =
      parser_parse_function_value_parameters(parser, arena);

  if (parser_match_token(parser, TOKEN_KIND_COLON)) {
    ast_handle_to_ptr(parser->current_function_handle, *arena)
        ->return_type_ast = parser_parse_type(parser, arena);
  }

  ast_handle_to_ptr(parser->current_function_handle, *arena)->rhs =
      parser_parse_function_body(parser, arena);

  parser->current_function_handle = ast_handle_nil;

  return fn_i;
}

static void parser_sync_if_panicked(Parser *parser) {
  pg_assert(parser != NULL);

  if (parser->state != PARSER_STATE_PANIC)
    return; // Nothing to do.

  parser->state = PARSER_STATE_SYNCED;

  while (!parser_is_at_end(parser)) {
    // TODO: sync at newlines?

    switch (parser_peek_token(parser).kind) {
    case TOKEN_KIND_KEYWORD_FUN:
      return;
    default:; // Do nothing.
    }

    parser_advance_token(parser);
  }
}

// propertyDeclaration:
//     [modifiers]
//     ('val' | 'var')
//     [{NL} typeParameters]
//     [{NL} receiverType {NL} '.']
//     ({NL} (multiVariableDeclaration | variableDeclaration))
//     [{NL} typeConstraints]
//     [{NL} (('=' {NL} expression) | propertyDelegate)]
//     [(NL {NL}) ';']
//     {NL}
//     (([getter] [{NL} [semi] setter]) | ([setter] [{NL} [semi] getter]))
static Ast_handle parser_parse_property_declaration(Parser *parser,
                                                    Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(arena != NULL);

  if (parser_match_token(parser, TOKEN_KIND_KEYWORD_VAR))
    return parser_parse_var_declaration(parser, arena);

  return ast_handle_nil;
}

// declaration:
//     classDeclaration
//     | objectDeclaration
//     | functionDeclaration
//     | propertyDeclaration
//     | typeAlias
static Ast_handle parser_parse_declaration(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  Ast_handle new_ast_handle = ast_handle_nil;
  if (!ast_handle_is_nil(new_ast_handle =
                             parser_parse_function_declaration(parser, arena)))
    return new_ast_handle;

  if (!ast_handle_is_nil(new_ast_handle =
                             parser_parse_property_declaration(parser, arena)))
    return new_ast_handle;

  parser_sync_if_panicked(parser);

  return new_ast_handle;
}

// topLevelObject: declaration [semis]
static Ast_handle parser_parse_top_level_object(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(!array32_is_empty(parser->lexer->tokens));

  return parser_parse_declaration(parser, arena);
}

// kotlinFile:
//     [shebangLine]
//     {NL}
//     {fileAnnotation}
//     packageHeader
//     importList
//     {topLevelObject}
//     EOF
static Ast_handle parser_parse_kotlin_file(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(!array32_is_empty(parser->lexer->tokens));

  Ast node = {.kind = AST_KIND_LIST};

  // TODO: package, import, etc.

  Ast_handle ast_handle = ast_handle_nil;
  while (!ast_handle_is_nil(ast_handle =
                                parser_parse_top_level_object(parser, arena))) {
    *array32_push(&node.nodes, arena) = ast_handle;
  }

  if (parser->tokens_i != parser->lexer->tokens.len) {
    parser_error(parser, parser->lexer->tokens.data[parser->tokens_i],
                 "Unexpected trailing code");
  }

  return new_ast(&node, arena);
}

static Ast_handle parser_parse(Parser *parser, Arena *arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);
  pg_assert(!array32_is_empty(parser->lexer->tokens));

  parser->tokens_i = 1; // Skip the dummy token.

  const Ast_handle root_i = parser_parse_kotlin_file(parser, arena);

  return root_i;
}

static void parser_ast_fprint(const Parser *parser, Ast_handle ast_handle,
                              FILE *file, u16 indent, u32 count, Arena arena) {
  pg_assert(parser != NULL);
  pg_assert(parser->lexer != NULL);
  pg_assert(parser->tokens_i <= parser->lexer->tokens.len);

  if (!cli_log_verbose)
    return;

  if (ast_handle_is_nil(ast_handle))
    return;

  const Ast *const node = ast_handle_to_ptr(ast_handle, arena);
  if (node->kind == AST_KIND_NONE)
    return;

  const Str kind_string = ast_kind_to_string[node->kind];
  const Token token = parser->lexer->tokens.data[node->main_token_i];
  u32 line = 0;
  u32 column = 0;
  Str token_string = {0};
  parser_find_token_position(parser, token, &line, &column, &token_string);

  ut_fwrite_indent(file, indent);

  pg_assert(indent < UINT16_MAX - 1); // Avoid overflow.
  switch (node->kind) {
  case AST_KIND_BOOL:
    LOG("[%u] %.*s %.*s at %.*s:%u:%u:%u)", count, (int)kind_string.len,
        kind_string.data, (int)token_string.len, token_string.data,
        (int)parser->lexer->file_path.len, parser->lexer->file_path.data, line,
        column, token.source_offset);
    break;

  case AST_KIND_LIST:
    LOG("[%u] %.*s %.*s at %.*s:%u:%u:%u), %u children", count,
        (int)kind_string.len, kind_string.data, (int)token_string.len,
        token_string.data, (int)parser->lexer->file_path.len,
        parser->lexer->file_path.data, line, column, token.source_offset,
        node->nodes.len);

    for (u64 i = 0; i < node->nodes.len; i++)
      parser_ast_fprint(parser, node->nodes.data[i], file, indent + 2, ++count,
                        arena);

    break;
  case AST_KIND_CALL: {
    LOG("[%u] %.*s %.*s (at %.*s:%u:%u:%u), %u children", count,
        (int)kind_string.len, kind_string.data, (int)token_string.len,
        token_string.data, (int)parser->lexer->file_path.len,
        parser->lexer->file_path.data, line, column, token.source_offset,
        node->nodes.len);

    for (u64 i = 0; i < node->nodes.len; i++)
      parser_ast_fprint(parser, node->nodes.data[i], file, indent + 2, ++count,
                        arena);
    break;
  }
  case AST_KIND_FUNCTION_DEFINITION: {
    LOG("[%u] %.*s %.*s (at %.*s:%u:%u:%u)", count, (int)kind_string.len,
        kind_string.data, (int)token_string.len, token_string.data,
        (int)parser->lexer->file_path.len, parser->lexer->file_path.data, line,
        column, token.source_offset);

    parser_ast_fprint(parser, node->lhs, file, indent + 2, ++count, arena);
    parser_ast_fprint(parser, node->return_type_ast, file, indent + 2, ++count,
                      arena);
    parser_ast_fprint(parser, node->rhs, file, indent + 2, ++count, arena);
    break;
  }
  default:
    LOG("[%u] %.*s %.*s (at %.*s:%u:%u:%u)", count, (int)kind_string.len,
        kind_string.data, (int)token_string.len, token_string.data,
        (int)parser->lexer->file_path.len, parser->lexer->file_path.data, line,
        column, token.source_offset);
    parser_ast_fprint(parser, node->lhs, file, indent + 2, ++count, arena);
    parser_ast_fprint(parser, node->rhs, file, indent + 2, ++count, arena);
    break;
  }
}

// --------------------------------- Typing

// TODO: Caching?
static Type_handle resolver_add_type(Resolver *resolver, Type *type,
                                     Arena *arena) {
  pg_assert(type != NULL);

  if (type->kind == TYPE_INSTANCE) { // Try to lower to a know type.
    if (str_eq_c(type->this_class_name, "java/lang/Boolean"))
      type->kind = TYPE_BOOLEAN;
    else if (str_eq_c(type->this_class_name, "java/lang/Char"))
      type->kind = TYPE_CHAR;
    else if (str_eq_c(type->this_class_name, "java/lang/Byte"))
      type->kind = TYPE_BYTE;
    else if (str_eq_c(type->this_class_name, "java/lang/Short"))
      type->kind = TYPE_SHORT;
    else if (str_eq_c(type->this_class_name, "java/lang/Integer"))
      type->kind = TYPE_INT;
    else if (str_eq_c(type->this_class_name, "java/lang/Float"))
      type->kind = TYPE_FLOAT;
    else if (str_eq_c(type->this_class_name, "java/lang/Long"))
      type->kind = TYPE_LONG;
    else if (str_eq_c(type->this_class_name, "java/lang/Double"))
      type->kind = TYPE_DOUBLE;
    else if (str_eq_c(type->this_class_name, "java/lang/String"))
      type->kind = TYPE_STRING;
  }

  const Type_handle new_type_handle = new_type(type, arena);

  resolver->last_type->list_next = new_type_handle;
  resolver->last_type = type_handle_to_ptr(new_type_handle, *arena);

  return new_type_handle;
}

static Str resolver_function_to_human_string(Type_handle function_i,
                                             Arena *arena);

static bool jvm_method_has_inline_only_annotation(const Class_file *class_file,
                                                  const Jvm_method *method) {

  for (u64 i = 0; i < method->attributes.len; i++) {
    const Jvm_attribute *const attribute = &method->attributes.data[i];
    if (attribute->kind != ATTRIBUTE_KIND_RUNTIME_INVISIBLE_ANNOTATIONS)
      continue;

    for (u64 j = 0; j < attribute->v.runtime_invisible_annotations.len; j++) {
      const Jvm_annotation *const annotation =
          &attribute->v.runtime_invisible_annotations.data[j];

      Str descriptor = jvm_constant_array_get_as_string(
          &class_file->constant_pool, annotation->type_index);

      if (str_eq_c(descriptor, "Lkotlin/internal/InlineOnly;"))
        return true;
    }
  }
  return false;
}

static void resolver_load_methods_from_class_file(
    Resolver *resolver, Type_handle this_class_type_handle,
    const Class_file *class_file, Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  const Type *const this_class_type =
      type_handle_to_ptr(this_class_type_handle, *arena);

  Jvm_constant_pool *constant_pool_clone = NULL;
  for (u64 i = 0; i < class_file->methods.len; i++) {
    const Jvm_method *const method = &class_file->methods.data[i];
    Str descriptor = jvm_constant_array_get_as_string(
        &class_file->constant_pool, method->descriptor);
    Str name = jvm_constant_array_get_as_string(&class_file->constant_pool,
                                                method->name);

    Type type = {
        .this_class_name = this_class_type->this_class_name,
        .package_name = this_class_type->package_name,
    };
    jvm_parse_descriptor(resolver, descriptor, &type, arena);
    pg_assert(type.kind == TYPE_METHOD);

    if (str_eq_c(name, CONSTRUCTOR_JVM_NAME)) {
      type.kind = TYPE_CONSTRUCTOR;
      type.v.method.name = type.this_class_name;
    } else {
      type.v.method.name = name;
    }

    type.v.method.access_flags = method->access_flags;
    type.v.method.this_class_type_handle = this_class_type_handle;
    jvm_get_source_location_of_function(class_file, method,
                                        &type.v.method.source_file_name,
                                        &type.v.method.source_line, arena);

    if (jvm_method_has_inline_only_annotation(class_file, method)) {
      // Do as if the method was public, not private.
      type.v.method.access_flags |= ACCESS_FLAGS_PUBLIC;
      type.v.method.access_flags &= (u16)(~1U << ACCESS_FLAGS_PRIVATE);
      type.flags |= TYPE_FLAG_INLINE_ONLY;

      constant_pool_clone =
          constant_pool_clone == NULL
              ? jvm_constant_array_clone(&class_file->constant_pool, arena)
              : constant_pool_clone;
      type.v.method.constant_pool = constant_pool_clone;

      // Clone code.
      // TODO: Clone exceptions, stack map frames, etc?
      for (u64 i = 0; i < method->attributes.len; i++) {
        const Jvm_attribute *const attribute = &method->attributes.data[i];
        if (attribute->kind == ATTRIBUTE_KIND_CODE) {
          type.v.method.code =
              array32_make_from_slice(u8, attribute->v.code.bytecode.data,
                                      attribute->v.code.bytecode.len, arena);
          break;
        }
      }
      pg_assert(!array32_is_empty(type.v.method.code));
    }

    const Type_handle type_handle = resolver_add_type(resolver, &type, arena);

    if (cli_log_verbose) {
      Arena tmp_arena = *arena;
      Str human_type =
          resolver_function_to_human_string(type_handle, &tmp_arena);
      LOG("Loaded method %s [%lu]: access_flags=%u type=%.*s",
          typechecker_type_kind_string(type_handle, *arena), i,
          method->access_flags, (int)human_type.len, human_type.data);
    }
  }
}

static bool jvm_buf_read_jar_file(Resolver *resolver, Str content, Str path,
                                  Arena scratch_arena, Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(arena != NULL);

  u8 *current = content.data;
  const u64 central_directory_end_size = 22;
  pg_assert(content.len >= 4 + central_directory_end_size);
  pg_assert(buf_read_u8(content, &current) == 0x50);
  pg_assert(buf_read_u8(content, &current) == 0x4b);
  pg_assert(buf_read_u8(content, &current) == 0x03);
  pg_assert(buf_read_u8(content, &current) == 0x04);

  // Assume first no trailing comment.
  u8 *cdre = content.data + content.len - central_directory_end_size;
  if (buf_read_le_u32(content, &cdre) != 0x06054b50) {
    // Need to scan backwards in the presence of a trailing comment to find
    // the magic number.
    cdre -= sizeof(u32);
    while (--cdre > content.data &&
           buf_read_le_u32(content, &cdre) != 0x06054b50) {
      cdre -= sizeof(u32);
    }
    pg_assert(cdre > content.data);
  }

  // disk number
  const u16 disk_number = buf_read_le_u16(content, &cdre);
  pg_unused(disk_number);

  // disk start
  const u16 disk_start = buf_read_le_u16(content, &cdre);

  // records count on this disk
  const u16 disk_records_count = buf_read_le_u16(content, &cdre);
  pg_unused(disk_records_count);

  const u16 records_count = buf_read_le_u16(content, &cdre);

  const u32 central_directory_size = buf_read_le_u32(content, &cdre);
  pg_unused(central_directory_size);

  const u32 central_directory_offset = buf_read_le_u32(content, &cdre);

  pg_assert(central_directory_offset < content.len);

  // Sign of zip64.
  pg_assert(central_directory_offset != (u32)-1);

  u8 *cdfh = content.data + central_directory_offset;
  for (u64 i = 0; i < records_count; i++) {
    pg_assert(buf_read_u8(content, &cdfh) == 0x50);
    pg_assert(buf_read_u8(content, &cdfh) == 0x4b);
    pg_assert(buf_read_u8(content, &cdfh) == 0x01);
    pg_assert(buf_read_u8(content, &cdfh) == 0x02);

    // version made by
    buf_read_le_u16(content, &cdfh);

    // version needed to extract
    buf_read_le_u16(content, &cdfh);

    // general purpose bit flag
    buf_read_le_u16(content, &cdfh);

    const u16 compression_method = buf_read_le_u16(content, &cdfh);
    pg_assert(compression_method == 0 ||
              compression_method == 8); // No compression or DEFLATE.

    // file last modification time
    buf_read_le_u16(content, &cdfh);

    // file last modification date
    buf_read_le_u16(content, &cdfh);

    // crc-32 of uncompressed data
    buf_read_le_u32(content, &cdfh);

    // compressed size
    const u32 compressed_size_according_to_directory_entry =
        buf_read_le_u32(content, &cdfh);

    // uncompressed size
    const u32 uncompressed_size_according_to_directory_entry =
        buf_read_le_u32(content, &cdfh);

    const u16 file_name_length = buf_read_le_u16(content, &cdfh);

    const u16 extra_field_length = buf_read_le_u16(content, &cdfh);

    const u16 file_comment_length = buf_read_le_u16(content, &cdfh);

    // disk number where file starts
    buf_read_le_u16(content, &cdfh);

    // internal file attributes
    buf_read_le_u16(content, &cdfh);

    // external file attributes
    buf_read_le_u32(content, &cdfh);

    const u32 local_file_header_offset = buf_read_le_u32(content, &cdfh);

    // file name
    buf_read_n_u8(content, file_name_length, &cdfh);

    // extra field
    buf_read_n_u8(content, extra_field_length, &cdfh);

    // file comment
    buf_read_n_u8(content, file_comment_length, &cdfh);

    // Read file header.
    {
      u8 *local_file_header =
          content.data + disk_start + local_file_header_offset;
      pg_assert(buf_read_u8(content, &local_file_header) == 0x50);
      pg_assert(buf_read_u8(content, &local_file_header) == 0x4b);
      pg_assert(buf_read_u8(content, &local_file_header) == 0x03);
      pg_assert(buf_read_u8(content, &local_file_header) == 0x04);

      // version to extract
      buf_read_le_u16(content, &local_file_header);

      // general purpose bit flag
      buf_read_le_u16(content, &local_file_header);

      const u16 compression_method =
          buf_read_le_u16(content, &local_file_header);
      pg_assert(compression_method == 0 ||
                compression_method == 8); // No compression or DEFLATE.

      // file last modification time
      buf_read_le_u16(content, &local_file_header);

      // file last modification date
      buf_read_le_u16(content, &local_file_header);

      // crc-32 of uncompressed data
      buf_read_le_u32(content, &local_file_header);

      // compressed size
      buf_read_le_u32(content, &local_file_header);

      // uncompressed size
      buf_read_le_u32(content, &local_file_header);

      const u16 file_name_length = buf_read_le_u16(content, &local_file_header);

      const u16 extra_field_length =
          buf_read_le_u16(content, &local_file_header);

      Str file_name = {.data = local_file_header, .len = file_name_length};
      buf_read_n_u8(content, file_name_length, &local_file_header);

      buf_read_n_u8(content, extra_field_length, &local_file_header);

      Class_file class_file = {
          .class_file_path = file_name,
          .archive_file_path = path,
      };
      // TODO: Read Manifest file?
      if (uncompressed_size_according_to_directory_entry > 0 &&
          compression_method == 0 && str_ends_with_c(file_name, ".class")) {

        jvm_buf_read_class_file(
            str_new(local_file_header,
                    uncompressed_size_according_to_directory_entry),
            &local_file_header, &class_file, &scratch_arena);

        Type type = {.kind = TYPE_INSTANCE};
        type_init_package_and_name(class_file.class_name, &type.package_name,
                                   &type.this_class_name, arena);

        const Type_handle this_class_type_handle =
            resolver_add_type(resolver, &type, arena);

        if (class_file.super_class != 0) {
          const Jvm_constant_pool_entry *const constant_super =
              jvm_constant_array_get(&class_file.constant_pool,
                                     class_file.super_class);

          pg_assert(constant_super->kind == CONSTANT_POOL_KIND_CLASS_INFO);
        }

        resolver_load_methods_from_class_file(resolver, this_class_type_handle,
                                              &class_file, arena);

        resolver->class_file_loaded_count += 1;
        LOG("Loaded class_file_path=%.*s [%lu] archive_file_path=%.*s "
            "kind=uncompressed package_name=%.*s class_name=%.*s",
            (int)class_file.class_file_path.len,
            class_file.class_file_path.data, resolver->class_file_loaded_count,
            (int)class_file.archive_file_path.len,
            class_file.archive_file_path.data, (int)type.package_name.len,
            type.package_name.data, (int)type.this_class_name.len,
            type.this_class_name.data);

      } else if (compressed_size_according_to_directory_entry > 0 &&
                 compression_method == 8 && str_eq_c(file_name, ".class")) {
#if WITH_ZLIB
        Str dst = sb_build(sb_new(
            uncompressed_size_according_to_directory_entry, &scratch_arena));

        z_stream stream = {
            .next_in = (u8 *)local_file_header,
            .avail_in = compressed_size_according_to_directory_entry,
            .next_out = dst.data,
            .avail_out = dst.len,
        };

        // `inflateInit2` is required instead of `inflateInit` because this is a
        // raw compressed stream and not a zlib compressed stream which contains
        // a header.
        int res = inflateInit2(&stream, -8);
        pg_assert(res == Z_OK);

        res = inflate(&stream, Z_SYNC_FLUSH);
        pg_assert(res == Z_STREAM_END);

        u8 *dst_current = dst.data;
        jvm_buf_read_class_file(dst, &dst_current, &class_file, &scratch_arena);

        Type type = {.kind = TYPE_INSTANCE};
        type_init_package_and_name(class_file.class_name, &type.package_name,
                                   &type.this_class_name, arena);

        const u32 this_class_type_handle =
            resolver_add_type(resolver, resolver, &type, arena);

        if (class_file.super_class != 0) {
          const Jvm_constant *const constant_super = jvm_constant_array_get(
              &class_file.constant_pool, class_file.super_class);

          pg_assert(constant_super->kind == CONSTANT_POOL_KIND_CLASS_INFO);
          Str super_class_name = jvm_constant_array_get_as_string(
              &class_file.constant_pool, constant_super->v.string_utf8_i);

          if (!str_eq_c(super_class_name, "java/lang/Object")) {
            type.super_class_name = super_class_name;
          }
        }

        resolver_load_methods_from_class_file(resolver, this_class_type_handle,
                                              &class_file, arena);

        LOG("Loaded class_file_path=%.*s  archive_file_path=%.*s "
            "kind=compressed package_name=%.*s class_name=%.*s",
            (int)class_file.class_file_path.len,
            class_file.class_file_path.data,
            (int)class_file.archive_file_path.len,
            class_file.archive_file_path.data, (int)type.package_name.len,
            type.package_name.data, (int)type.this_class_name.len,
            type.this_class_name.data);

        inflateEnd(&stream);
#else
        pg_assert(0 && "WITH_ZLIB not set, no zlib decompression support");
#endif
      }
    }
  }
  return false;
}
static bool jvm_read_jmod_file(Resolver *resolver, Str path,
                               Arena scratch_arena, Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(arena != NULL);

  char *path_cstr = str_to_c(path, &scratch_arena);
  Read_result read_res =
      // IMPORTANT: We store the content of JMOD files in the *scratch* arena,
      // not the *main* arena. That's because most of the stuff in there is
      // irrelevant. We pick afterwards just the few bits we want to retain and
      // clone them into the main arena.
      ut_read_all_from_file_path(path_cstr, &scratch_arena);
  if (read_res.error) {
    fprintf(stderr, "Failed to read the file %.*s: %s\n", (int)path.len,
            path.data, strerror(read_res.error));
    return false;
  }

  Str content = read_res.content;
  // Check magic number.
  {
    u8 *current = content.data;
    pg_assert(buf_read_u8(content, &current) == 'J');
    pg_assert(buf_read_u8(content, &current) == 'M');
    pg_assert(buf_read_u8(content, &current) == 1);
    pg_assert(buf_read_u8(content, &current) == 0);
  }

  content = str_advance(content, 4);
  return jvm_buf_read_jar_file(resolver, content, path, scratch_arena, arena);
}

static bool jvm_read_jar_file(Resolver *resolver, Str path, Arena scratch_arena,
                              Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(arena != NULL);

  char *path_cstr = str_to_c(path, &scratch_arena);
  Read_result read_res = ut_read_all_from_file_path(path_cstr, &scratch_arena);
  if (read_res.error) {
    fprintf(stderr, "Failed to read the file %.*s: %s\n", (int)path.len,
            path.data, strerror(read_res.error));
    return false;
  }

  return jvm_buf_read_jar_file(resolver, read_res.content, path, scratch_arena,
                               arena);
}

static bool resolver_is_package_imported(const Resolver *resolver,
                                         Str package_name) {
  for (u64 i = 0; i < resolver->imported_package_names.len; i++) {
    if (str_eq(resolver->imported_package_names.data[i], package_name))
      return true;
  }

  return false;
}

static void resolver_collect_callables_with_name(const Resolver *resolver,
                                                 Str function_name,
                                                 Array32(Type_handle) *
                                                     candidate_functions_i,
                                                 Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(candidate_functions_i != NULL);

  for (Type_handle handle = resolver->first_type->list_next;
       !type_handle_handles_nil(handle);
       handle = type_handle_to_ptr(handle, *arena)->list_next) {
    Type *const type = type_handle_to_ptr(handle, *arena);

    if (type->kind == TYPE_METHOD || type->kind == TYPE_CONSTRUCTOR) {
      const Method *const method = &type->v.method;

      if ((method->access_flags & ACCESS_FLAGS_STATIC) == 0)
        continue;

      if (!str_eq(method->name, function_name))
        continue;

      // TODO: Should loaded but not yet imported types reside in a different
      // array to avoid thrashing?
      if (!resolver_is_package_imported(resolver, type->package_name))
        continue;

      *array32_push(candidate_functions_i, arena) = handle;
    }
  }

  // TODO: Collect callable fields as well.
}

// TODO: Add to string: file:line
static Str resolver_function_to_human_string(Type_handle type_handle,
                                             Arena *arena) {

  const Type *const type = type_handle_to_ptr(type_handle, *arena);

  if (!(type->kind == TYPE_METHOD || type->kind == TYPE_CONSTRUCTOR))
    return type_to_human_string(type_handle, arena);

  const Method *const method = &type->v.method;

  const Type *const this_class_type =
      type_handle_to_ptr(method->this_class_type_handle, *arena);

  Str_builder res = sb_new(
      method->name.len + this_class_type->this_class_name.len + 1024, arena);

  if (method->access_flags & ACCESS_FLAGS_PRIVATE)
    res = sb_append_c(res, "private ", arena);

  res = sb_append_c(res, "fun ", arena);

  if (!str_is_empty(type->package_name)) {
    res = sb_append(res, type->package_name, arena);
    res = sb_append_c(res, ".", arena);
  }

  if ((method->access_flags & ACCESS_FLAGS_STATIC) == 0) {
    res = sb_append(res, this_class_type->this_class_name, arena);
    res = sb_append_c(res, ".", arena);
  }

  res = sb_append(res, method->name, arena);
  res = sb_append_c(res, "(", arena);

  const u8 argument_count = (u8)method->argument_type_handles.len;
  for (u8 i = 0; i < argument_count; i++) {
    Str argument_type_string =
        type_to_human_string(method->argument_type_handles.data[i], arena);

    res = sb_append(res, argument_type_string, arena);

    if (i < argument_count - 1)
      res = sb_append_c(res, ", ", arena);
  }

  res = sb_append_c(res, "): ", arena);
  Str return_type_string =
      type_to_human_string(method->return_type_handle, arena);
  res = sb_append(res, return_type_string, arena);

  res = sb_append_c(res, " from ", arena);

  if (str_is_empty(method->source_file_name)) {
    res = sb_append(res, this_class_type->this_class_name, arena);
  } else {
    res = sb_append(res, method->source_file_name, arena);
  }

  if (method->source_line > 0) {
    res = sb_append_c(res, ":", arena);
    res = sb_append_u64(res, (u64)method->source_line, arena);
  }

  return sb_build(res);
}

static void resolver_remove_non_applicable_function_candidates(
    Resolver *resolver, Array32(Type_handle) * candidate_functions_i,
    Array32(Type_handle) call_site_argument_types_i, Arena scratch_arena,
    Arena *arena) {

  u64 i = 0;
  while (i < candidate_functions_i->len) {
    if (!resolver_is_function_candidate_applicable(
            resolver, call_site_argument_types_i,
            candidate_functions_i->data[i], scratch_arena, arena)) {
      array32_remove_at_unordered(candidate_functions_i, i);
    } else {
      i++;
    }
  }
}

typedef enum __attribute__((packed)) {
  APPLICABILITY_LESS = 1,
  APPLICABILITY_SAME = 2,
  APPLICABILITY_MORE = 4,
} Type_applicability;

static Type_applicability resolver_check_applicability_of_candidate_pair(
    Resolver *resolver, Type_handle a_handle, Type_handle b_handle,
    Arena scratch_arena, Arena *arena) {
  const Type *const a = type_handle_to_ptr(a_handle, *arena);
  const Type *const b = type_handle_to_ptr(b_handle, *arena);

  pg_assert(a->kind == TYPE_METHOD || a->kind == TYPE_CONSTRUCTOR);
  pg_assert(a->this_class_name.data != NULL);
  pg_assert(a->this_class_name.len > 0);
  const u8 call_argument_count = (u8)a->v.method.argument_type_handles.len;

  pg_assert(b->kind == TYPE_METHOD || b->kind == TYPE_CONSTRUCTOR);
  pg_assert(b->this_class_name.data != NULL);
  pg_assert(b->this_class_name.len > 0);
  pg_assert(b->v.method.argument_type_handles.len == call_argument_count);

  for (u64 k = 0; k < call_argument_count; k++) {
    if (!resolver_is_type_subtype_of(
            resolver, a->v.method.argument_type_handles.data[k],
            b->v.method.argument_type_handles.data[k], scratch_arena, arena)) {
      return APPLICABILITY_LESS;
    }
  }

  return APPLICABILITY_SAME | APPLICABILITY_MORE;
}

static Type_handle resolver_select_most_specific_candidate_function(
    Resolver *resolver, Array32(Type_handle) candidates, Arena scratch_arena,
    Arena *arena) {

  Array32(bool) tombstones =
      array32_make(bool, candidates.len, candidates.len, &scratch_arena);
  u32 tombstones_count = 0;

  while (tombstones_count < candidates.len - 1) {
    for (u64 i = 0; i < candidates.len; i++) {
      for (u64 j = 0; j < i; j++) {
        const u32 a_index = (u32)i;
        const u32 b_index = (u32)j;
        const Type_handle a_type_handle = candidates.data[a_index];
        const Type_handle b_type_handle = candidates.data[b_index];

        if (tombstones.data[a_index] || tombstones.data[b_index])
          continue;

        const Type_applicability a_b =
            resolver_check_applicability_of_candidate_pair(
                resolver, a_type_handle, b_type_handle, scratch_arena, arena);
        const Type_applicability b_a =
            resolver_check_applicability_of_candidate_pair(
                resolver, b_type_handle, a_type_handle, scratch_arena, arena);

        const bool a_more_applicable_than_b = a_b & APPLICABILITY_MORE;
        const bool b_more_applicable_than_a = b_a & APPLICABILITY_MORE;

        if (cli_log_verbose) {
          Str a_human_type =
              resolver_function_to_human_string(a_type_handle, &scratch_arena);
          Str b_human_type =
              resolver_function_to_human_string(b_type_handle, &scratch_arena);

          LOG("[D001] %.*s vs %.*s: a_b=%u b_a=%u", (int)a_human_type.len,
              a_human_type.data, (int)b_human_type.len, b_human_type.data, a_b,
              b_a);

          if (a_more_applicable_than_b && !b_more_applicable_than_a) {
            LOG("[D002] removing %.*s", (int)b_human_type.len,
                b_human_type.data);
          }
          if (b_more_applicable_than_a && !a_more_applicable_than_b) {
            LOG("[D003] removing %.*s", (int)a_human_type.len,
                a_human_type.data);
          }
        }

        if (a_more_applicable_than_b && !b_more_applicable_than_a) {
          // A clearly more applicable than B, mark B as deleted so that it will
          // be skipped for subsequent checks.
          tombstones.data[b_index] = true;
          tombstones_count += 1;
        } else if (b_more_applicable_than_a && !a_more_applicable_than_b) {
          // B clearly more applicable than A, mark A as deleted so that it will
          // be skipped for subsequent checks.
          tombstones.data[a_index] = true;
          tombstones_count += 1;
        } else {
          // TODO: Need to do more checks.
        }
      }
    }
  }

  for (u64 i = 0; i < tombstones.len; i++) {
    if (!tombstones.data[i])
      return candidates.data[i];
  }

  pg_assert(0 && "unreachable");
}

// TODO: Keep track of imported packages (including those imported by
// default).
static bool
resolver_resolve_free_function(Resolver *resolver, Str method_name,
                               Array32(Type_handle) call_site_argument_types_i,
                               Type_handle *picked_method_type_handle,
                               Array32(Type_handle) * candidate_functions_i,
                               Arena scratch_arena, Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(method_name.len > 0);
  pg_assert(picked_method_type_handle != NULL);

  resolver_collect_callables_with_name(resolver, method_name,
                                       candidate_functions_i, arena);

  const u32 original_candidates_len = candidate_functions_i->len;

  resolver_remove_non_applicable_function_candidates(
      resolver, candidate_functions_i, call_site_argument_types_i,
      scratch_arena, arena);

  if (candidate_functions_i->len == 0) {
    // Restore the original length to display the possible candidates in the
    // error message.
    candidate_functions_i->len = original_candidates_len;
    return false;
  }
  if (candidate_functions_i->len == 1) {
    *picked_method_type_handle = candidate_functions_i->data[0];
    return true;
  }

  *picked_method_type_handle = resolver_select_most_specific_candidate_function(
      resolver, *candidate_functions_i, scratch_arena, arena);

  return true;
}

// TODO: Remove.
static bool typechecker_merge_types(const Resolver *resolver,
                                    Type_handle lhs_handle,
                                    Type_handle rhs_handle,
                                    Type_handle *result_i, Arena arena) {
  pg_assert(resolver != NULL);
  pg_assert(result_i != NULL);

  if (resolver_are_types_equal(resolver, lhs_handle, rhs_handle, arena)) {
    *result_i = lhs_handle;
    return true;
  }

  // Any is compatible with everything.
  if (type_handle_handles_nil(lhs_handle)) {
    *result_i = rhs_handle;
    return true;
  }

  const Type *const lhs_type = type_handle_to_ptr(lhs_handle, arena);

  if (type_handle_handles_nil(rhs_handle)) {
    *result_i = lhs_handle;
    return true;
  }

  const Type *const rhs_type = type_handle_to_ptr(rhs_handle, arena);

  // Any is compatible with everything.
  if (lhs_type->kind == TYPE_ANY) {
    *result_i = rhs_handle;
    return true;
  }

  // Any is compatible with everything.
  if (rhs_type->kind == TYPE_ANY) {
    *result_i = lhs_handle;
    return true;
  }

  // FIXME: Widen.
  if ((lhs_type->kind == TYPE_INT) && (rhs_type->kind == TYPE_BYTE)) {
    *result_i = rhs_handle;
    return true;
  }

  if ((lhs_type->kind == TYPE_BYTE) && (rhs_type->kind == TYPE_INT)) {
    *result_i = lhs_handle;
    return true;
  }

  if ((lhs_type->kind == TYPE_INT) && (rhs_type->kind == TYPE_SHORT)) {
    *result_i = rhs_handle;
    return true;
  }

  if ((lhs_type->kind == TYPE_SHORT) && (rhs_type->kind == TYPE_INT)) {
    *result_i = lhs_handle;
    return true;
  }

  return false;
}

static void resolver_ast_fprint(const Resolver *resolver, Ast_handle ast_handle,
                                FILE *file, u16 indent, u32 count,
                                Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(resolver->parser != NULL);
  pg_assert(resolver->parser->lexer != NULL);
  pg_assert(resolver->parser->tokens_i <= resolver->parser->lexer->tokens.len);

  if (!cli_log_verbose)
    return;

  const Ast *const node = ast_handle_to_ptr(ast_handle, *arena);
  if (node->kind == AST_KIND_NONE)
    return;

  const Str kind_string = ast_kind_to_string[node->kind];
  const Token token = resolver->parser->lexer->tokens.data[node->main_token_i];
  u32 line = 0;
  u32 column = 0;
  Str token_string = {0};
  parser_find_token_position(resolver->parser, token, &line, &column,
                             &token_string);

  ut_fwrite_indent(file, indent);

  const char *const type_kind =
      typechecker_type_kind_string(node->type_handle, *arena);
  Str human_type = type_to_human_string(node->type_handle, arena);

  pg_assert(indent < UINT16_MAX - 1); // Avoid overflow.
  switch (node->kind) {
  case AST_KIND_BOOL:
    LOG("[%u] %.*s %.*s: %.*s (%s) (at %.*s:%u:%u:%u)", count,
        (int)kind_string.len, kind_string.data, (int)token_string.len,
        token_string.data, (int)human_type.len, human_type.data, type_kind,
        (int)resolver->parser->lexer->file_path.len,
        resolver->parser->lexer->file_path.data, line, column,
        token.source_offset);
    break;

  case AST_KIND_LIST:
    LOG("[%u] %.*s %.*s: %.*s %s (at %.*s:%u:%u:%u), %u children", count,
        (int)kind_string.len, kind_string.data, (int)token_string.len,
        token_string.data, (int)human_type.len, human_type.data, type_kind,
        (int)resolver->parser->lexer->file_path.len,
        resolver->parser->lexer->file_path.data, line, column,
        token.source_offset, node->nodes.len);

    for (u64 i = 0; i < node->nodes.len; i++)
      resolver_ast_fprint(resolver, node->nodes.data[i], file, indent + 2,
                          ++count, arena);
    break;
  case AST_KIND_CALL: {

    human_type = resolver_function_to_human_string(node->type_handle, arena);
    LOG("[%u] %.*s %.*s: %.*s %s (at %.*s:%u:%u:%u), %u children", count,
        (int)kind_string.len, kind_string.data, (int)token_string.len,
        token_string.data, (int)human_type.len, human_type.data, type_kind,
        (int)resolver->parser->lexer->file_path.len,
        resolver->parser->lexer->file_path.data, line, column,
        token.source_offset, node->nodes.len);

    for (u64 i = 0; i < node->nodes.len; i++)
      resolver_ast_fprint(resolver, node->nodes.data[i], file, indent + 2,
                          ++count, arena);
    break;
  }
  default:
    LOG("[%u] %.*s %.*s: %.*s %s (at %.*s:%u:%u:%u)", count,
        (int)kind_string.len, kind_string.data, (int)token_string.len,
        token_string.data, (int)human_type.len, human_type.data, type_kind,
        (int)resolver->parser->lexer->file_path.len,
        resolver->parser->lexer->file_path.data, line, column,
        token.source_offset);
    resolver_ast_fprint(resolver, node->lhs, file, indent + 2, ++count, arena);
    resolver_ast_fprint(resolver, node->rhs, file, indent + 2, ++count, arena);
    break;
  }
}

static bool type_fqn_equal_to_package_and_name(Str a_fqn, Str b_package_name,
                                               Str b_class_name,
                                               Arena scratch_arena) {
  pg_assert(!str_contains_element(b_class_name, (u8)'/'));
  pg_assert(!str_contains_element(b_class_name, (u8)'.'));

  Str_builder b_fqn =
      sb_new(b_package_name.len + 1 + b_class_name.len, &scratch_arena);
  if (!str_is_empty(b_package_name)) {
    b_fqn = sb_append(b_fqn, b_package_name, &scratch_arena);
    b_fqn = sb_append_char(b_fqn, '.', &scratch_arena);
  }
  b_fqn = sb_append(b_fqn, b_class_name, &scratch_arena);

  return str_eq(a_fqn, sb_build(b_fqn));
}

static bool resolver_resolve_fully_qualified_name(Resolver *resolver, Str fqn,
                                                  Type_handle *type_handle,
                                                  Arena scratch_arena,
                                                  Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(!str_is_empty(fqn));
  pg_assert(type_handle != NULL);
  pg_assert(arena != NULL);

  // The JVM uses `/` but Java and Kotlin use `.` as separator.
  pg_assert(!str_contains_element(fqn, '/'));

  // TODO: Flag types coming from java as nullable.

  // Check if cached first.
  for (Type_handle handle = resolver->first_type->list_next;
       !type_handle_handles_nil(handle);
       handle = type_handle_to_ptr(handle, *arena)->list_next) {
    const Type *const type = type_handle_to_ptr(handle, *arena);

    if (type->kind == TYPE_METHOD || type->kind == TYPE_CONSTRUCTOR)
      continue;

    if (type->kind == TYPE_INSTANCE &&
        type_fqn_equal_to_package_and_name(
            fqn, type->package_name, type->this_class_name, scratch_arena)) {
      *type_handle = handle;
      return true;
    }
  }

  // Scan the class path entries for `$CLASS_PATH_ENTRY/$CLASS_NAME.class`.
  // E.g.: `/usr/share/java/kotlin-stdlib.jar` -> `/usr/share/java/Fqn.class`.
  for (u64 i = 0; i < resolver->class_path_entries.len; i++) {
    Str entry = resolver->class_path_entries.data[i];
    Str_split_result entry_last_slash_split = str_rsplit(entry, '/');
    Str parent = entry_last_slash_split.left;

    Str final_extension = str_from_c(".class");

    Str_builder tentative_class_file_path_builder =
        sb_new(parent.len + 1 + fqn.len + final_extension.len, arena);

    tentative_class_file_path_builder =
        sb_append(tentative_class_file_path_builder, parent, arena);
    tentative_class_file_path_builder =
        sb_append_char(tentative_class_file_path_builder, '/', arena);

    {
      u64 replace_start = tentative_class_file_path_builder.len;

      // Transform e.g. `/a/b/kotlin.io.ConsoleKt` into
      // `/a/b/kotlin/io/ConsoleKt`.
      tentative_class_file_path_builder =
          sb_append(tentative_class_file_path_builder, fqn, arena);

      tentative_class_file_path_builder = sb_replace_element_starting_at(
          tentative_class_file_path_builder, replace_start, '.', '/');
    }

    tentative_class_file_path_builder =
        sb_append(tentative_class_file_path_builder, final_extension, arena);
    Str tentative_class_file_path = sb_build(tentative_class_file_path_builder);

    {
      // TODO: check if we can read the file content into `scratch_arena`
      char *tentative_class_file_path_cstr =
          str_to_c(tentative_class_file_path, &scratch_arena);
      Read_result read_res = ut_read_all_from_file_path(
          tentative_class_file_path_cstr, &scratch_arena);
      if (read_res.error) // Silently swallow the error and skip this entry.
        continue;

      Class_file class_file = {
          .class_file_path = tentative_class_file_path,
      };
      u8 *current = read_res.content.data;
      jvm_buf_read_class_file(read_res.content, &current, &class_file, arena);

      pg_assert(str_eq(fqn, class_file.class_name));

      Type this_type = {.kind = TYPE_INSTANCE};
      type_init_package_and_name(class_file.class_name, &this_type.package_name,
                                 &this_type.this_class_name, arena);

      *type_handle = resolver_add_type(resolver, &this_type, arena);

      return true;
    }
  }

  // Scan the class path entries for `$CLASS_PATH_ENTRY` which is a jar file
  // that contains
  // `$CLASS_NAME.class`.
  for (u64 i = 0; i < resolver->class_path_entries.len; i++) {
    Str class_path_entry = resolver->class_path_entries.data[i];
    if (!str_ends_with(class_path_entry, str_from_c(".jar")))
      continue;

    jvm_read_jar_file(resolver, class_path_entry, scratch_arena, arena);

    for (Type_handle handle = resolver->first_type->list_next;
         !type_handle_handles_nil(handle);
         handle = type_handle_to_ptr(handle, *arena)->list_next) {
      Type *const type = type_handle_to_ptr(handle, *arena);

      if (type->kind == TYPE_INSTANCE &&
          type_fqn_equal_to_package_and_name(
              fqn, type->package_name, type->this_class_name, scratch_arena)) {
        *type_handle = handle;
        return true;
      }
    }
  }

  return false;
}

// TODO: Check if there is a way not to do it lazily. Not goog to have I/O
// randomly pop up in the middle of type checking.
static bool resolver_resolve_super_lazily(Resolver *resolver,
                                          Type_handle type_handle,
                                          Arena scratch_arena, Arena *arena) {

  // Already done?
  Type *const type = type_handle_to_ptr(type_handle, *arena);

  if (!type_handle_handles_nil(type->super_type_handle))
    return true;

  if (str_eq_c(type->this_class_name, "java/lang/Object"))
    return true; // Reached the top.

  // Since most types inherit from Object, we do not allocate a string for it
  // for optimization purposes.
  if (str_is_empty(type->super_class_name)) {
    return resolver_resolve_fully_qualified_name(
        resolver, str_from_c("java.lang.Object"), &type->super_type_handle,
        scratch_arena, arena);
  }

  return resolver_resolve_fully_qualified_name(resolver, type->super_class_name,
                                               &type->super_type_handle,
                                               scratch_arena, arena);
}

static void resolver_load_standard_types(Resolver *resolver, Str java_home,
                                         Arena scratch_arena, Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(!str_is_empty(java_home));
  pg_assert(arena != NULL);

  Str relative_jmod_path = str_from_c("/jmods/java.base.jmod");
  Str_builder path = sb_new(java_home.len + relative_jmod_path.len, arena);
  path = sb_append(path, java_home, arena);
  path = sb_append(path, relative_jmod_path, arena);

  jvm_read_jmod_file(resolver, sb_build(path), scratch_arena, arena);

  Type_handle dummy = {0};
  Str sanity_check = str_from_c("kotlin.io.ConsoleKt");
  if (!resolver_resolve_fully_qualified_name(resolver, sanity_check, &dummy,
                                             scratch_arena, arena)) {
    fprintf(
        stderr,
        "Could not load the kotlin stdlib classes (failed to load the class "
        "`%.*s` as sanity check for `println` functions). "
        "Please provide the CLI "
        "option manually e.g.: \"-c /usr/share/java/kotlin-stdlib.jar\".\n",
        (int)sanity_check.len, sanity_check.data);
    exit(ENOENT);
  }
}

static void typechecker_begin_scope(Resolver *resolver) {
  pg_assert(resolver != NULL);
  pg_assert(resolver->scope_depth < UINT32_MAX);

  resolver->scope_depth += 1;
}

static void typechecker_end_scope(Resolver *resolver) {
  pg_assert(resolver != NULL);
  pg_assert(resolver->scope_depth > 0);

  for (i64 i = (i64)resolver->variables.len - 1; i >= 0; i--) {
    const Type_variable *const variable = &resolver->variables.data[i];
    if (variable->scope_depth == resolver->scope_depth)
      array32_drop(&resolver->variables, 1);
    else if (variable->scope_depth < resolver->scope_depth)
      break;
    else
      pg_assert(0 && "unreachable");
  }
  resolver->scope_depth -= 1;
}

static u32 typechecker_declare_variable(Resolver *resolver, Str name,
                                        Ast_handle ast_handle, Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(resolver->scope_depth > 0);
  pg_assert(arena != NULL);

  pg_assert(resolver->variables.len < UINT32_MAX);

  const Type_variable variable = {
      .name = name,
      .scope_depth = UINT32_MAX,
      .var_definition_ast_handle = ast_handle,
  };
  *array32_push(&resolver->variables, arena) = variable;
  return (u32)array32_last_index(resolver->variables);
}

static void typechecker_mark_variable_as_initialized(Resolver *resolver,
                                                     u32 variable_i) {
  pg_assert(resolver != NULL);
  pg_assert(resolver->scope_depth > 0);
  pg_assert(variable_i < resolver->variables.len);

  // Should this function be idempotent? In that case, this assert should be
  // removed.
  pg_assert(resolver->variables.data[variable_i].scope_depth == (u32)-1);

  resolver->variables.data[variable_i].scope_depth = resolver->scope_depth;
}

static u32 typechecker_find_variable(Resolver *resolver, u32 token_i) {
  pg_assert(resolver != NULL);
  pg_assert(resolver->scope_depth > 0);

  Str name = parser_token_to_str_view(resolver->parser, token_i);

  for (i64 i = (i64)resolver->variables.len - 1; i >= 0; i--) {
    const Type_variable *const variable = &resolver->variables.data[i];
    if (!str_eq(name, variable->name))
      continue;

    if (variable->scope_depth == (u32)-1) {
      parser_error(resolver->parser,
                   resolver->parser->lexer->tokens.data[token_i],
                   "Cannot read local variable in its own initializer");
      return UINT32_MAX;
    }
    return (u32)i;
  }

  return UINT32_MAX;
}

static Str resolver_get_fqn_from_navigation_chain(const Resolver *resolver,
                                                  Ast_handle ast_handle,
                                                  Arena arena) {
  const Ast *const node = ast_handle_to_ptr(ast_handle, arena);
  pg_assert(node->kind == AST_KIND_NAVIGATION);

  const Token start = resolver->parser->lexer->tokens.data[node->main_token_i];
  pg_assert(start.kind == TOKEN_KIND_IDENTIFIER);

  u32 end_token_excl_i = node->main_token_i + 1;
  while (end_token_excl_i < resolver->parser->lexer->tokens.len) {
    const Token current =
        resolver->parser->lexer->tokens.data[end_token_excl_i];
    if (!(current.kind == TOKEN_KIND_IDENTIFIER ||
          current.kind == TOKEN_KIND_DOT))
      break;

    end_token_excl_i += 1;
  }

  return parser_token_range_to_string(resolver->parser, node->main_token_i,
                                      end_token_excl_i);
}

static bool typechecker_variable_shadows(Resolver *resolver, u32 name_token_i,
                                         Arena arena) {

  const u32 previous_var_i = typechecker_find_variable(resolver, name_token_i);
  if (previous_var_i == (u32)-1)
    return false;

  pg_assert(previous_var_i < resolver->variables.len);
  const Type_variable *const previous_var =
      &resolver->variables.data[previous_var_i];

  const Ast *const previous_var_node =
      ast_handle_to_ptr(previous_var->var_definition_ast_handle, arena);

  const Token previous_var_name_token =
      resolver->parser->lexer->tokens.data[previous_var_node->main_token_i];

  u32 line = 0;
  u32 column = 0;
  Str token_string = {0};
  parser_find_token_position(resolver->parser, previous_var_name_token, &line,
                             &column, &token_string);
  char error[256] = {0};
  snprintf(error, 255, "variable shadowing, already declared at %u:%u", line,
           column);
  parser_error(resolver->parser,
               resolver->parser->lexer->tokens.data[name_token_i], error);
  return false;
}

static Type_handle resolver_resolve_ast(Resolver *resolver,
                                        Ast_handle ast_handle,
                                        Arena scratch_arena, Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(resolver->parser != NULL);

  if (ast_handle_is_nil(ast_handle))
    return type_handle_nil;

  Ast *const node = ast_handle_to_ptr(ast_handle, *arena);
  const Token token = resolver->parser->lexer->tokens.data[node->main_token_i];

  switch (node->kind) {
  case AST_KIND_NONE:
    return node->type_handle =
               resolver_add_type(resolver, &(Type){.kind = TYPE_ANY}, arena);
  case AST_KIND_BOOL:
    return node->type_handle = resolver_add_type(
               resolver, &(Type){.kind = TYPE_BOOLEAN}, arena);

  case AST_KIND_CALL: {
    Arena tmp_arena = scratch_arena;

    const Ast *const lhs = ast_handle_to_ptr(node->lhs, *arena);
    pg_assert(lhs->kind == AST_KIND_UNRESOLVED_NAME);
    Str name = parser_token_to_str_view(resolver->parser, lhs->main_token_i);

    // Resolve arguments.
    Array32(Type_handle) call_site_argument_types_i =
        array32_make(Type_handle, 0, node->nodes.len, &tmp_arena);

    for (u64 i = 0; i < node->nodes.len; i++) {
      const Ast_handle ast_handle = node->nodes.data[i];

      const Type_handle type_handle =
          resolver_resolve_ast(resolver, ast_handle, tmp_arena, arena);
      *array32_push(&call_site_argument_types_i, &tmp_arena) = type_handle;
    }

    Type_handle picked_method_type_handle = type_handle_nil;
    {
      Array32(Type_handle) candidate_functions_i =
          array32_make(Type_handle, 0, 128, &tmp_arena);

      if (!resolver_resolve_free_function(
              resolver, name, call_site_argument_types_i,
              &picked_method_type_handle, &candidate_functions_i, tmp_arena,
              arena)) {

        Str_builder error = sb_new(256, &scratch_arena);
        error = sb_append_c(error, "failed to find matching function", arena);

        if (candidate_functions_i.len == 0) {
          error = sb_append_c(
              error, ", could not find any function with this name: ", arena);
          error = sb_append(error, name, arena);
        } else {
          error = sb_append_c(error, ", possible candidates: ", arena);

          for (u64 i = 0; i < candidate_functions_i.len; i++) {
            const Type_handle candidate_type_handle =
                candidate_functions_i.data[i];

            error = sb_append_c(error, "\n  ", arena);
            error = sb_append(
                error,
                resolver_function_to_human_string(candidate_type_handle, arena),
                arena);
          }
        }
        parser_error(resolver->parser, token, (char *)error.data);
        return type_handle_nil;
      }
    }

    pg_assert(!type_handle_handles_nil(picked_method_type_handle));
    const Type *picked_method_type =
        type_handle_to_ptr(picked_method_type_handle, *arena);
    pg_assert(picked_method_type->kind == TYPE_METHOD ||
              picked_method_type->kind == TYPE_CONSTRUCTOR);

    node->type_handle = picked_method_type_handle;

    return picked_method_type->v.method.return_type_handle;
  }
  case AST_KIND_NUMBER: {
    u8 flag = 0;
    const u64 number = parser_number(resolver->parser, token, &flag);
    if (flag & NODE_NUMBER_FLAGS_OVERFLOW) {
      parser_error(resolver->parser, token,
                   "Integer literal is too big (> 9223372036854775807)");
      return type_handle_nil;
    } else if (flag & NODE_NUMBER_FLAGS_LONG) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_LONG}, arena);
    } else {
      // >  it has an integer literal type containing all the
      // built-in integer types guaranteed to be able to represent this value.

      if (number <= INT32_MAX) {
        node->type_handle =
            resolver_add_type(resolver, &(Type){.kind = TYPE_INT}, arena);
      } else {
        node->type_handle =
            resolver_add_type(resolver, &(Type){.kind = TYPE_LONG}, arena);
      }
    }
    node->extra_data = number;

    return node->type_handle;
  }
  case AST_KIND_UNARY:
    switch (token.kind) {
    case TOKEN_KIND_NOT:
      node->type_handle =
          resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
      const Type *const type = type_handle_to_ptr(node->type_handle, *arena);
      if (type->kind != TYPE_BOOLEAN) {
        Str_builder error = sb_new(256, &scratch_arena);
        error = sb_append_c(error, "incompatible types: got ", arena);
        error = sb_append(error, type_to_human_string(node->type_handle, arena),
                          arena);
        error = sb_append_c(error, ", expected Boolean ", arena);
        parser_error(resolver->parser, token, (char *)error.data);
        return type_handle_nil;
      }

      return node->type_handle;

    case TOKEN_KIND_MINUS:
      return node->type_handle = resolver_resolve_ast(resolver, node->lhs,
                                                      scratch_arena, arena);

    default:
      pg_assert(0 && "todo");
    }
    break;
  case AST_KIND_BINARY: {
    pg_assert(node->main_token_i > 0);

    const Type_handle lhs_handle =
        resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    const Type_handle rhs_handle =
        resolver_resolve_ast(resolver, node->rhs, scratch_arena, arena);

    if (!typechecker_merge_types(resolver, lhs_handle, rhs_handle,
                                 &node->type_handle, *arena)) {
      Str_builder error = sb_new(256, &scratch_arena);
      error = sb_append_c(error, "incompatible types: ", arena);
      error = sb_append(error, type_to_human_string(lhs_handle, arena), arena);
      error = sb_append_c(error, " vs ", arena);
      error = sb_append(error, type_to_human_string(rhs_handle, arena), arena);
      parser_error(resolver->parser, token, (char *)error.data);
    }

    switch (token.kind) {
    case TOKEN_KIND_LT:
    case TOKEN_KIND_LE:
    case TOKEN_KIND_GT:
    case TOKEN_KIND_GE:
    case TOKEN_KIND_NOT_EQUAL:
    case TOKEN_KIND_EQUAL_EQUAL: {
      return node->type_handle = resolver_add_type(
                 resolver, &(Type){.kind = TYPE_BOOLEAN}, arena);
    }
    case TOKEN_KIND_AMPERSAND_AMPERSAND:
    case TOKEN_KIND_PIPE_PIPE: {
      const Type *const lhs_type = type_handle_to_ptr(lhs_handle, *arena);
      if (lhs_type->kind != TYPE_BOOLEAN) {
        Str_builder error = sb_new(256, &scratch_arena);
        error = sb_append_c(
            error, "incompatible types: expected Boolean, got: ", arena);
        error =
            sb_append(error, type_to_human_string(lhs_handle, arena), arena);
        parser_error(resolver->parser, token, (char *)error.data);
      }
      return type_handle_nil;
    }
      return node->type_handle;
    default:
      return node->type_handle;
    }
  }
  case AST_KIND_LIST: {
    for (u64 i = 0; i < node->nodes.len; i++) {
      resolver_resolve_ast(resolver, node->nodes.data[i], scratch_arena, arena);
      // Clean up after each statement.
      resolver->current_type_handle = type_handle_nil;
    }

    return node->type_handle =
               resolver_add_type(resolver, &(Type){.kind = TYPE_UNIT}, arena);
  }
  case AST_KIND_FUNCTION_DEFINITION: {
    // Already resolved by resolver_collect_user_defined_function_signatures().
    pg_assert(!type_handle_handles_nil(node->type_handle));

    typechecker_begin_scope(resolver);
    // Arguments (lhs).
    // Need to re-process them to have the right variables (the function
    // arguments) in the current scope.
    // TODO: We could optimize it by not creating new types at this point.
    resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);

    resolver->current_function_handle = ast_handle;

    // Inspect body (rhs).
    resolver_resolve_ast(resolver, node->rhs, scratch_arena, arena);

    typechecker_end_scope(resolver);

    resolver->current_function_handle = ast_handle_nil;

    return node->type_handle;
  }

  case AST_KIND_VAR_DEFINITION: {
    if (typechecker_variable_shadows(resolver, node->main_token_i, *arena))
      return type_handle_nil;

    const u32 variable_i = typechecker_declare_variable(
        resolver,
        parser_token_to_str_view(resolver->parser, node->main_token_i),
        ast_handle, arena);

    const Type_handle lhs_type_handle =
        resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    const Type_handle rhs_type_handle =
        resolver_resolve_ast(resolver, node->rhs, scratch_arena, arena);

    if (!typechecker_merge_types(resolver, lhs_type_handle, rhs_type_handle,
                                 &node->type_handle, *arena)) {
      Str lhs_type_human = type_to_human_string(lhs_type_handle, arena);
      Str rhs_type_human = type_to_human_string(rhs_type_handle, arena);

      Str_builder error = sb_new(256, &scratch_arena);
      error =
          sb_append_c(error, "incompatible types: declared type is ", arena);
      error = sb_append(error, lhs_type_human, arena);
      error = sb_append_c(error, ", received type is ", arena);
      error = sb_append(error, rhs_type_human, arena);
      parser_error(resolver->parser, token, (char *)error.data);

      // Still assign a type to be able to proceed to catch as many errors
      // as possible.
      node->type_handle = lhs_type_handle;
    }

    typechecker_mark_variable_as_initialized(resolver, variable_i);

    return node->type_handle;
  }
  case AST_KIND_VAR_REFERENCE: {
    return node->type_handle =
               ast_handle_to_ptr(node->lhs, *arena)->type_handle;
  }
  case AST_KIND_IF: {
    const Type_handle type_condition_handle =
        resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    const Type *const type_condition =
        type_handle_to_ptr(type_condition_handle, *arena);

    if (type_condition->kind != TYPE_BOOLEAN) {
      Str_builder error = sb_new(256, &scratch_arena);
      error = sb_append_c(error,
                          "incompatible types, expected Boolean, got: ", arena);

      Str type_inferred_string =
          type_to_human_string(type_condition_handle, arena);
      error = sb_append(error, type_inferred_string, arena);
      parser_error(resolver->parser, token, (char *)error.data);
    }

    return node->type_handle =
               resolver_resolve_ast(resolver, node->rhs, scratch_arena, arena);
  }
  case AST_KIND_WHILE_LOOP: {
    const Type_handle type_condition_handle =
        resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    const Type *const type_condition =
        type_handle_to_ptr(type_condition_handle, *arena);

    if (type_condition->kind != TYPE_BOOLEAN) {
      Str_builder error = sb_new(256, &scratch_arena);
      error = sb_append_c(error,
                          "incompatible types, expect Boolean, got: ", arena);

      Str type_inferred_string =
          type_to_human_string(type_condition_handle, arena);
      error = sb_append(error, type_inferred_string, arena);
      parser_error(resolver->parser, token, (char *)error.data);
    }

    typechecker_begin_scope(resolver);
    resolver_resolve_ast(resolver, node->rhs, scratch_arena, arena);
    typechecker_end_scope(resolver);

    return node->type_handle =
               resolver_add_type(resolver, &(Type){.kind = TYPE_UNIT}, arena);
  }
  case AST_KIND_STRING: {
    return node->type_handle =
               resolver_add_type(resolver, &(Type){.kind = TYPE_STRING}, arena);
  }

  case AST_KIND_CLASS_REFERENCE: {
    pg_assert(0 && "todo");
  }

  case AST_KIND_NAVIGATION: { // e.g.: `foo.bar.baz`
    // IDEA:
    // If the first element `foo` is a known variable in scope: resolve that
    // recursively.
    // Else: try to load the package `foo.bar` and find the class
    // `baz`, or the function `public static (WhateverKt).baz`. Update the node
    // kind to `CLASS_REFERENCE` or `CALL` (or `FUNCTION_REFERENCE` ?).
    // Else: error.
    // TODO: static fields/companion objects.

    const u32 variable_i =
        typechecker_find_variable(resolver, node->main_token_i);

    if (variable_i == (u32)-1) {
      Str fqn =
          resolver_get_fqn_from_navigation_chain(resolver, ast_handle, *arena);

      if (resolver_resolve_fully_qualified_name(
              resolver, fqn, &node->type_handle, scratch_arena, arena)) {
        pg_assert(0 && "todo");
      } else {
        const Token main_token =
            resolver->parser->lexer->tokens.data[node->main_token_i];
        Str_builder error = sb_new(256, &scratch_arena);
        error = sb_append_c(error,
                            "Unknown reference to a name, neither a variable "
                            "in scope or an external identifier: ",
                            arena);
        error = sb_append(error, fqn, arena);
        parser_error(resolver->parser, main_token, (char *)error.data);
        return type_handle_nil;
      }
    } else {
      pg_assert(0 && "todo");
      // FIXME: wrong
      //      const Ast *const variable =
      //      &resolver->parser->nodes.data[variable_i];
      //    node->type_handle = variable->type_handle;

      return resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    }
    break;
  }

  case AST_KIND_FUNCTION_PARAMETER: {
    const u32 variable_i = typechecker_declare_variable(
        resolver,
        parser_token_to_str_view(resolver->parser, node->main_token_i),
        ast_handle, arena);
    node->type_handle =
        resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    typechecker_mark_variable_as_initialized(resolver, variable_i);

    return node->type_handle;
  }

  case AST_KIND_TYPE: {
    Str type_literal_string =
        parser_token_to_str_view(resolver->parser, node->main_token_i);

    if (str_eq_c(type_literal_string, "Any") ||
        str_eq_c(type_literal_string, "kotlin.Any")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_ANY}, arena);
    } else if (str_eq_c(type_literal_string, "Unit") ||
               str_eq_c(type_literal_string, "kotlin.Unit")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_UNIT}, arena);
    } else if (str_eq_c(type_literal_string, "Int") ||
               str_eq_c(type_literal_string, "kotlin.Int")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_INT}, arena);
    } else if (str_eq_c(type_literal_string, "Boolean") ||
               str_eq_c(type_literal_string, "kotlin.Boolean")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_BOOLEAN}, arena);
    } else if (str_eq_c(type_literal_string, "Byte") ||
               str_eq_c(type_literal_string, "kotlin.Byte")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_BYTE}, arena);
    } else if (str_eq_c(type_literal_string, "Char") ||
               str_eq_c(type_literal_string, "kotlin.Char")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_CHAR}, arena);
    } else if (str_eq_c(type_literal_string, "Short") ||
               str_eq_c(type_literal_string, "kotlin.Short")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_SHORT}, arena);
    } else if (str_eq_c(type_literal_string, "Float") ||
               str_eq_c(type_literal_string, "kotlin.Float")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_FLOAT}, arena);
    } else if (str_eq_c(type_literal_string, "Double") ||
               str_eq_c(type_literal_string, "kotlin.Double")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_DOUBLE}, arena);
    } else if (str_eq_c(type_literal_string, "Long") ||
               str_eq_c(type_literal_string, "kotlin.Long")) {
      node->type_handle =
          resolver_add_type(resolver, &(Type){.kind = TYPE_LONG}, arena);
    } else {
      const bool found = resolver_resolve_fully_qualified_name(
          resolver, type_literal_string, &node->type_handle, scratch_arena,
          arena);
      if (!found) {
        Str_builder error = sb_new(256, &scratch_arena);
        error = sb_append_c(error, "unknown type: ", arena);
        error = sb_append(error, type_literal_string, arena);

        parser_error(resolver->parser, token, (char *)error.data);
        return type_handle_nil;
      }
    }

    return node->type_handle;
  }

  case AST_KIND_UNRESOLVED_NAME: {
    const u32 variable_i =
        typechecker_find_variable(resolver, node->main_token_i);

    if (variable_i == (u32)-1) {
      parser_error(resolver->parser,
                   resolver->parser->lexer->tokens.data[node->main_token_i],
                   "unknown reference to variable");
      return type_handle_nil;
    }

    node->kind = AST_KIND_VAR_REFERENCE;
    node->lhs = resolver->variables.data[variable_i].var_definition_ast_handle;

    return resolver_resolve_ast(resolver, ast_handle, scratch_arena, arena);

    break;
  }

  case AST_KIND_THEN_ELSE: {
    typechecker_begin_scope(resolver);
    const Type_handle lhs_type_handle =
        resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    typechecker_end_scope(resolver);

    typechecker_begin_scope(resolver);
    const Type_handle rhs_type_handle =
        resolver_resolve_ast(resolver, node->rhs, scratch_arena, arena);
    typechecker_end_scope(resolver);

    if (!typechecker_merge_types(resolver, lhs_type_handle, rhs_type_handle,
                                 &node->type_handle, *arena)) {
      Str_builder error = sb_new(256, &scratch_arena);
      error = sb_append_c(error, "incompatible types: ", arena);
      error =
          sb_append(error, type_to_human_string(lhs_type_handle, arena), arena);
      error = sb_append_c(error, " vs ", arena);
      error =
          sb_append(error, type_to_human_string(rhs_type_handle, arena), arena);
      parser_error(resolver->parser, token, (char *)error.data);
    }
    return node->type_handle;

    break;
  }
  case AST_KIND_ASSIGNMENT:
    resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);

    if (!parser_is_lvalue(resolver->parser, node->lhs, *arena)) {
      parser_error(resolver->parser,
                   resolver->parser->lexer->tokens.data[node->main_token_i],
                   "The assignment target is not a lvalue (such as a local "
                   "variable)");
    }

    return node->type_handle =
               resolver_resolve_ast(resolver, node->rhs, scratch_arena, arena);

  case AST_KIND_RETURN: {
    node->type_handle =
        resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    const Ast *const current_function =
        ast_handle_to_ptr(resolver->current_function_handle, *arena);
    const Type *const function_type =
        type_handle_to_ptr(current_function->type_handle, *arena);

    pg_assert(function_type->kind == TYPE_METHOD ||
              function_type->kind == TYPE_CONSTRUCTOR);
    const Type_handle return_type_handle =
        function_type->v.method.return_type_handle;

    if (!resolver_are_types_equal(resolver, node->type_handle,
                                  return_type_handle, *arena)) {
      Str_builder error = sb_new(256, &scratch_arena);
      error =
          sb_append_c(error, "incompatible return type in function `", arena);
      error = sb_append(error,
                        parser_token_to_str_view(
                            resolver->parser, current_function->main_token_i),
                        arena);
      error = sb_append_c(error, "` of type ", arena);
      error = sb_append(
          error, type_to_human_string(current_function->type_handle, arena),
          arena);
      error = sb_append_c(error, ": got ", arena);

      error = sb_append(error, type_to_human_string(node->type_handle, arena),
                        arena);
      error = sb_append_c(error, ", expected ", arena);
      error = sb_append(error, type_to_human_string(return_type_handle, arena),
                        arena);
      parser_error(resolver->parser, token, (char *)error.data);
    }

    return node->type_handle;
  }

  case AST_KIND_MAX:
    pg_assert(0 && "unreachable");
  }
  pg_assert(0 && "unreachable");
}

// First pass to resolve all the function signatures so that they can be called
// before their definition in the source order.
static void resolver_user_defined_function_signatures(Resolver *resolver,
                                                      Ast_handle ast_handle,
                                                      Arena scratch_arena,
                                                      Arena *arena) {

  if (ast_handle_is_nil(ast_handle))
    return;

  Ast *const node = ast_handle_to_ptr(ast_handle, *arena);
  switch (node->kind) {
  case AST_KIND_LIST:
    for (u64 i = 0; i < node->nodes.len; i++)
      resolver_user_defined_function_signatures(resolver, node->nodes.data[i],
                                                scratch_arena, arena);

    break;

  case AST_KIND_FUNCTION_DEFINITION: {
    typechecker_begin_scope(resolver);
    resolver->current_function_handle = ast_handle;

    // Arguments (lhs).
    resolver_resolve_ast(resolver, node->lhs, scratch_arena, arena);
    // Return type, if present.
    Type_handle return_type_handle =
        resolver_add_type(resolver, &(Type){.kind = TYPE_UNIT}, arena);
    if (!ast_handle_is_nil(node->return_type_ast)) {
      return_type_handle = resolver_resolve_ast(resolver, node->return_type_ast,
                                                scratch_arena, arena);
    }

    const Token name_token =
        resolver->parser->lexer->tokens.data[node->main_token_i];
    Type type = {
        .kind = TYPE_METHOD,
        .package_name = resolver->parser->current_package,
        .this_class_name = resolver->this_class_name,
        .v.method =
            {
                .return_type_handle = return_type_handle,
                .source_file_name = resolver->parser->lexer->file_path,
                .access_flags = ACCESS_FLAGS_PUBLIC | ACCESS_FLAGS_STATIC,
            },
    };
    u32 column = 0;
    u32 line = 0;
    parser_find_token_position(resolver->parser, name_token, &line, &column,
                               &type.v.method.name);
    pg_assert(line <= UINT16_MAX);
    type.v.method.source_line = (u16)line;

    if (!ast_handle_is_nil(node->lhs)) {
      const Ast *const lhs = ast_handle_to_ptr(node->lhs, *arena);
      pg_assert(lhs->kind == AST_KIND_LIST);

      type.v.method.argument_type_handles =
          array32_make(Type_handle, 0, lhs->nodes.len, arena);
      for (u64 i = 0; i < lhs->nodes.len; i++) {
        const Ast_handle ast_handle = lhs->nodes.data[i];
        const Type_handle type_handle =
            ast_handle_to_ptr(ast_handle, *arena)->type_handle;
        *array32_push(&type.v.method.argument_type_handles, arena) =
            type_handle;
      }
    }

    node->type_handle = resolver_add_type(resolver, &type, arena);

    // NOTE: Skip function body by nature.
    // But: Once we allow return type inference based on body, we need to also
    // inspect the body.

    resolver->current_function_handle = ast_handle_nil;
    typechecker_end_scope(resolver);
  } break;
  default:
    resolver_user_defined_function_signatures(resolver, node->lhs,
                                              scratch_arena, arena);
    resolver_user_defined_function_signatures(resolver, node->rhs,
                                              scratch_arena, arena);
    break;
  }
}

// --------------------------------- Code generation

typedef struct {
  Jvm_variable variable;
  u32 scope_id;
} Codegen_scope_variable;
Array32_struct(Codegen_scope_variable);

typedef struct {
  Resolver *resolver;
  Jvm_attribute_code *code;
  codegen_frame *frame;
  Array32(Codegen_scope_variable) locals;
  Array32(Stack_map_frame) stack_map_frames;
  u32 scope_id;
  pg_pad(4);
} codegen_generator;

// FIXME: Probably should not behave like a FIFO and rather like an array.
static void codegen_frame_locals_push(codegen_generator *gen,
                                      const Jvm_variable *variable,
                                      u16 *logical_local_index,
                                      u16 *physical_local_index, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(variable != NULL);
  pg_assert(arena != NULL);
  pg_assert(logical_local_index != NULL);
  pg_assert(physical_local_index != NULL);

  pg_assert(gen->frame->locals_physical_count + 1 < UINT16_MAX);

  *array32_push(&gen->frame->locals, arena) = *variable;

  const u16 word_count =
      jvm_verification_info_kind_word_count(variable->verification_info.kind);

  *logical_local_index = (u16)array32_last_index(gen->frame->locals);
  *physical_local_index = gen->frame->locals_physical_count;
  gen->frame->locals_physical_count += word_count;
  gen->frame->max_physical_locals = pg_max(gen->frame->max_physical_locals,
                                           gen->frame->locals_physical_count);

  Codegen_scope_variable scope_variable = {.variable = *variable,
                                           .scope_id = gen->scope_id};
  *array32_push(&gen->locals, arena) = scope_variable;
}

static u16 codegen_import_constant(Jvm_constant_pool *dst,
                                   const Jvm_constant_pool *src, u16 constant_i,
                                   Arena *arena) {
  const Jvm_constant_pool_entry *const constant =
      jvm_constant_array_get(src, constant_i);

  switch (constant->kind) {
  case CONSTANT_POOL_KIND_FIELD_REF: {
    const Jvm_constant_field_ref field_ref = constant->v.field_ref;

    Jvm_constant_pool_entry constant_gen = {
        .kind = constant->kind,
        .v =
            {
                .field_ref =
                    {
                        .descriptor = codegen_import_constant(
                            dst, src, field_ref.descriptor, arena),
                        .name = codegen_import_constant(dst, src,
                                                        field_ref.name, arena),
                    },
            },
    };
    return jvm_constant_array_push(dst, &constant_gen, arena);
  }
  case CONSTANT_POOL_KIND_METHOD_REF: {
    const Jvm_constant_method_ref method_ref = constant->v.method_ref;

    Jvm_constant_pool_entry constant_gen = {
        .kind = constant->kind,
        .v =
            {
                .method_ref =
                    {
                        .class = codegen_import_constant(
                            dst, src, method_ref.class, arena),
                        .name_and_type = codegen_import_constant(
                            dst, src, method_ref.name_and_type, arena),
                    },
            },
    };
    return jvm_constant_array_push(dst, &constant_gen, arena);
  }

  case CONSTANT_POOL_KIND_NAME_AND_TYPE: {
    const Jvm_constant_name_and_type name_and_type = constant->v.name_and_type;
    Jvm_constant_pool_entry constant_gen = {
        .kind = constant->kind,
        .v =
            {
                .name_and_type =
                    {
                        .name = codegen_import_constant(
                            dst, src, name_and_type.name, arena),
                        .descriptor = codegen_import_constant(
                            dst, src, name_and_type.descriptor, arena),
                    },
            },
    };
    return jvm_constant_array_push(dst, &constant_gen, arena);
  }

  case CONSTANT_POOL_KIND_INT:
  case CONSTANT_POOL_KIND_UTF8: {
    return jvm_constant_array_push(dst, constant, arena);
  }

  case CONSTANT_POOL_KIND_CLASS_INFO: {
    Jvm_constant_pool_entry constant_gen = {
        .kind = constant->kind,
        .v =
            {
                .java_class_name = codegen_import_constant(
                    dst, src, constant->v.java_class_name, arena),
            },
    };
    return jvm_constant_array_push(dst, &constant_gen, arena);
  }
  default:

    pg_assert(0 && "unimplemented");
  }
}

static u16 codegen_emit_jump_conditionally(codegen_generator *gen,
                                           u8 jump_opcode, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  jvm_code_push_u8(&gen->code->bytecode, jump_opcode, arena);
  const u16 jump_from_i = (u16)gen->code->bytecode.len;
  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IMPDEP1, arena);
  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IMPDEP2, arena);

  switch (jump_opcode) {
  case BYTECODE_IF_ICMPEQ:
  case BYTECODE_IF_ICMPNE:
  case BYTECODE_IF_ICMPLT:
  case BYTECODE_IF_ICMPGE:
  case BYTECODE_IF_ICMPGT:
  case BYTECODE_IF_ICMPLE:
    codegen_frame_stack_pop(gen->frame);
    codegen_frame_stack_pop(gen->frame);
    break;
  case BYTECODE_IFEQ:
  case BYTECODE_IFNE:
    codegen_frame_stack_pop(gen->frame);
    break;
  default:
    pg_assert(0 && "unreachable/unimplemented");
  }

  return jump_from_i;
}

static u16 codegen_emit_jump(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_GOTO, arena);
  const u16 from_location = (u16)gen->code->bytecode.len;
  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IMPDEP1, arena);
  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IMPDEP2, arena);

  return from_location;
}

static void codegen_emit_pop(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_POP, arena);

  codegen_frame_stack_pop(gen->frame);
}

static void codegen_emit_store_variable_int(codegen_generator *gen, u8 var_i,
                                            Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len > 0);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  pg_assert(var_i < gen->frame->locals_physical_count);
  pg_assert(array32_last(gen->frame->stack)->kind == VERIFICATION_INFO_INT);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_ISTORE, arena);
  jvm_code_push_u8(&gen->code->bytecode, var_i, arena);

  codegen_frame_stack_pop(gen->frame);
}

static void codegen_emit_store_variable_object(codegen_generator *gen, u8 var_i,
                                               Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len > 0);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  pg_assert(var_i < gen->frame->locals_physical_count);
  pg_assert(array32_last(gen->frame->stack)->kind == VERIFICATION_INFO_OBJECT);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_ASTORE, arena);
  jvm_code_push_u8(&gen->code->bytecode, var_i, arena);

  codegen_frame_stack_pop(gen->frame);
}

static void codegen_emit_store_variable_long(codegen_generator *gen, u8 var_i,
                                             Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  pg_assert(var_i < gen->frame->locals_physical_count);
  pg_assert(array32_last(gen->frame->stack)->kind == VERIFICATION_INFO_LONG);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LSTORE, arena);
  jvm_code_push_u8(&gen->code->bytecode, var_i, arena);

  codegen_frame_stack_pop(gen->frame);
}

static void codegen_emit_store_variable(codegen_generator *gen, u8 var_i,
                                        Arena *arena) {
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  pg_assert(var_i < gen->frame->locals_physical_count);
  const Jvm_verification_info_kind kind = array32_last(gen->frame->stack)->kind;

  switch (kind) {
  case VERIFICATION_INFO_INT:
    codegen_emit_store_variable_int(gen, var_i, arena);
    break;
  case VERIFICATION_INFO_OBJECT:
    codegen_emit_store_variable_object(gen, var_i, arena);
    break;
  case VERIFICATION_INFO_LONG:
    codegen_emit_store_variable_long(gen, var_i, arena);
    break;
  default:
    pg_assert(0 && "unimplemented");
  }
}

static void codegen_emit_load_variable_int(codegen_generator *gen, u8 var_i,
                                           Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len < UINT16_MAX);
  pg_assert(var_i < gen->frame->locals_physical_count);
  pg_assert(gen->frame->locals.len > 0);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_ILOAD, arena);
  jvm_code_push_u8(&gen->code->bytecode, var_i, arena);

  codegen_frame_stack_push(
      gen->frame, (Jvm_verification_info){.kind = VERIFICATION_INFO_INT},
      arena);
}

static void codegen_emit_load_variable_object(codegen_generator *gen, u8 var_i,
                                              Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len < UINT16_MAX);
  pg_assert(var_i < gen->frame->locals_physical_count);
  pg_assert(gen->frame->locals.len > 0);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_ALOAD, arena);
  jvm_code_push_u8(&gen->code->bytecode, var_i, arena);

  codegen_frame_stack_push(gen->frame,
                           (Jvm_verification_info){
                               .kind = VERIFICATION_INFO_OBJECT,
                               .extra_data = 0, // FIXME
                           },
                           arena);
}

static void codegen_emit_ldc(codegen_generator *gen,
                             const Jvm_constant_pool *constant_pool,
                             u16 constant_i, Arena *arena) {

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LDC_W, arena);

  const Jvm_constant_pool_entry *const constant =
      jvm_constant_array_get(constant_pool, constant_i);
  switch (constant->kind) {
  case CONSTANT_POOL_KIND_INT:
    jvm_code_array_push_u16(&gen->code->bytecode, constant_i, arena);
    codegen_frame_stack_push(
        gen->frame, (Jvm_verification_info){.kind = VERIFICATION_INFO_INT},
        arena);
    break;
  default:
    pg_assert(0 && "unimplemented");
  }
}

static void codegen_emit_load_variable_long(codegen_generator *gen, u8 var_i,
                                            Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len < UINT16_MAX);
  pg_assert(var_i < gen->frame->locals_physical_count);
  pg_assert(gen->frame->locals.len > 0);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LLOAD, arena);
  jvm_code_push_u8(&gen->code->bytecode, var_i, arena);

  codegen_frame_stack_push(
      gen->frame, (Jvm_verification_info){.kind = VERIFICATION_INFO_LONG},
      arena);
}

static void codegen_emit_get_static(codegen_generator *gen, u16 field_i,
                                    u16 class_i, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(field_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);
  pg_assert(arena != NULL);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_GET_STATIC, arena);
  jvm_code_array_push_u16(&gen->code->bytecode, field_i, arena);

  pg_assert(gen->frame->stack.len < UINT16_MAX);

  const Jvm_verification_info verification_info = {
      .kind = VERIFICATION_INFO_OBJECT,
      .extra_data = class_i,
  };
  codegen_frame_stack_push(gen->frame, verification_info, arena);
}

static void codegen_emit_invoke_virtual(codegen_generator *gen,
                                        u16 method_ref_i,
                                        const Method *method_type,
                                        Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_INVOKE_VIRTUAL, arena);
  jvm_code_array_push_u16(&gen->code->bytecode, method_ref_i, arena);

  for (u8 i = 0; i < 1 + method_type->argument_type_handles.len; i++)
    codegen_frame_stack_pop(gen->frame);

  const Type *const return_type =
      type_handle_to_ptr(method_type->return_type_handle, *arena);

  if (return_type->kind == TYPE_UNIT)
    return;

  const Jvm_verification_info verification_info =
      codegen_type_to_verification_info(
          resolver_eval_type(method_type->return_type_handle, *arena));

  codegen_frame_stack_push(gen->frame, verification_info, arena);
}

static void codegen_emit_invoke_static(codegen_generator *gen, u16 method_ref_i,
                                       const Method *method_type,
                                       Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_INVOKE_STATIC, arena);
  jvm_code_array_push_u16(&gen->code->bytecode, method_ref_i, arena);

  for (u8 i = 0; i < method_type->argument_type_handles.len; i++)
    codegen_frame_stack_pop(gen->frame);

  const Type *const return_type =
      type_handle_to_ptr(method_type->return_type_handle, *arena);

  if (return_type->kind == TYPE_UNIT)
    return;

  const Jvm_verification_info verification_info =
      codegen_type_to_verification_info(
          resolver_eval_type(method_type->return_type_handle, *arena));

  codegen_frame_stack_push(gen->frame, verification_info, arena);
}

static void codegen_emit_invoke_special(codegen_generator *gen,
                                        u16 method_ref_i,
                                        const Method *method_type,
                                        Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(method_ref_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_INVOKE_SPECIAL, arena);
  jvm_code_array_push_u16(&gen->code->bytecode, method_ref_i, arena);

  for (u8 i = 0; i < method_type->argument_type_handles.len; i++)
    codegen_frame_stack_pop(gen->frame);

  const Type *const return_type =
      type_handle_to_ptr(method_type->return_type_handle, *arena);

  pg_assert(return_type->kind != TYPE_UNIT);

  const Jvm_verification_info verification_info =
      codegen_type_to_verification_info(
          resolver_eval_type(method_type->return_type_handle, *arena));

  codegen_frame_stack_push(gen->frame, verification_info, arena);
}

static Type_handle
codegen_make_type_from_method_descriptor(codegen_generator *gen,
                                         Class_file *class_file, u16 constant_i,
                                         Arena *arena) {
  const Jvm_constant_pool_entry *const constant =
      jvm_constant_array_get(&class_file->constant_pool, constant_i);
  pg_assert(constant->kind == CONSTANT_POOL_KIND_METHOD_REF);

  const Jvm_constant_pool_entry *const name_and_type = jvm_constant_array_get(
      &class_file->constant_pool, constant->v.method_ref.name_and_type);
  pg_assert(name_and_type->kind == CONSTANT_POOL_KIND_NAME_AND_TYPE);

  Str descriptor = jvm_constant_array_get_as_string(
      &class_file->constant_pool, name_and_type->v.name_and_type.descriptor);

  Type new_type = {0};
  jvm_parse_descriptor(gen->resolver, descriptor, &new_type, arena);

  return resolver_add_type(gen->resolver, &new_type, arena);
}

static void codegen_emit_inlined_method_call(codegen_generator *gen,
                                             Class_file *class_file,
                                             const Type *method_type,
                                             u16 locals_offset, Arena *arena) {
  pg_assert(method_type->kind == TYPE_METHOD);
  pg_assert(method_type->flags & TYPE_FLAG_INLINE_ONLY);

  const Method *const method = &method_type->v.method;
  pg_assert(!array32_is_empty(method->code));
  pg_assert(method->constant_pool != NULL);

  const u32 code_size = method->code.len;
  Array32(u8) code = method->code;
  u8 *current = code.data;

  u64 stack_size_before_inline_snippet = gen->frame->stack.len;

  while (current < array32_last(code)) {
    const u8 opcode = buf_read_u8(str_new(code.data, code_size), &current);

    switch (opcode) {
    case BYTECODE_GET_STATIC: {
      const u16 field_ref_i =
          buf_read_be_u16(str_new(code.data, code_size), &current);
      const u16 field_ref_gen_i =
          codegen_import_constant(&class_file->constant_pool,
                                  method->constant_pool, field_ref_i, arena);

      const Jvm_constant_pool_entry *const field_ref_gen =
          jvm_constant_array_get(&class_file->constant_pool, field_ref_gen_i);
      pg_assert(field_ref_gen->kind == CONSTANT_POOL_KIND_FIELD_REF);

      codegen_emit_get_static(gen, field_ref_gen_i,
                              field_ref_gen->v.field_ref.name, arena);

      break;
    }
    case BYTECODE_INVOKE_VIRTUAL: {
      const u16 method_ref_i =
          buf_read_be_u16(str_new(code.data, code_size), &current);
      const u16 method_ref_gen_i =
          codegen_import_constant(&class_file->constant_pool,
                                  method->constant_pool, method_ref_i, arena);

      const Type_handle invoked_type_handle =
          codegen_make_type_from_method_descriptor(gen, class_file,
                                                   method_ref_gen_i, arena);
      const Type *const invoked_type =
          type_handle_to_ptr(invoked_type_handle, *arena);
      pg_assert(invoked_type->kind == TYPE_METHOD);

      codegen_emit_invoke_virtual(gen, method_ref_gen_i,
                                  &invoked_type->v.method, arena);

      break;
    }

    case BYTECODE_ISTORE_1: {
      u16 physical_local_index = locals_offset + 1;
      if (physical_local_index >=
          gen->frame->locals_physical_count) { // Need to add the variable.
        const Jvm_variable variable = {
            .scope_depth = gen->frame->scope_depth,
            .verification_info = {.kind = VERIFICATION_INFO_INT},
        };

        u16 logical_local_index = 0;
        codegen_frame_locals_push(gen, &variable, &logical_local_index,
                                  &physical_local_index, arena);
      }
      // Not sure about that one.
      pg_assert(physical_local_index <= UINT8_MAX);
      codegen_emit_store_variable_int(gen, (u8)physical_local_index, arena);

      break;
    }

    case BYTECODE_ISTORE_2: {
      u16 physical_local_index = locals_offset + 2;
      if (physical_local_index >=
          gen->frame->locals_physical_count) { // Need to add the variable.
        const Jvm_variable variable = {
            .scope_depth = gen->frame->scope_depth,
            .verification_info = {.kind = VERIFICATION_INFO_INT},
        };

        u16 logical_local_index = 0;
        codegen_frame_locals_push(gen, &variable, &logical_local_index,
                                  &physical_local_index, arena);
      }
      // Not sure about that one.
      pg_assert(physical_local_index <= UINT8_MAX);
      codegen_emit_store_variable_int(gen, (u8)physical_local_index, arena);

      break;
    }

    case BYTECODE_ILOAD_0:
      codegen_emit_load_variable_int(gen, (u8)locals_offset, arena);
      break;

    case BYTECODE_LLOAD_0:
      codegen_emit_load_variable_long(gen, (u8)locals_offset, arena);
      break;
    case BYTECODE_RETURN:
      // No-op by nature.
      break;

    case BYTECODE_LDC: {
      const u16 constant_i =
          (u16)buf_read_u8(str_new(code.data, code_size), &current);
      const u16 constant_gen_i = codegen_import_constant(
          &class_file->constant_pool, method->constant_pool, constant_i, arena);

      codegen_emit_ldc(gen, &class_file->constant_pool, constant_gen_i, arena);

      break;
    }

    case BYTECODE_ALOAD_0: {
      codegen_emit_load_variable_object(gen, (u8)locals_offset, arena);
      break;
    }
    case BYTECODE_INVOKE_STATIC: {
      const u16 method_ref_i =
          buf_read_be_u16(str_new(code.data, code_size), &current);
      const u16 method_ref_gen_i =
          codegen_import_constant(&class_file->constant_pool,
                                  method->constant_pool, method_ref_i, arena);

      const Type_handle invoked_type_handle =
          codegen_make_type_from_method_descriptor(gen, class_file,
                                                   method_ref_gen_i, arena);
      const Type *const invoked_type =
          type_handle_to_ptr(invoked_type_handle, *arena);
      pg_assert(invoked_type->kind == TYPE_METHOD);

      codegen_emit_invoke_static(gen, method_ref_gen_i, &invoked_type->v.method,
                                 arena);

      break;
    }

    default:
      pg_assert(0 && "unimplemented");
    }
  }
  u64 stack_size_after_inline_snippet = gen->frame->stack.len;

  // Not conceptually required but we do not support inlining snippets that
  // enlarge/shrink the stack right now.
  pg_assert(stack_size_before_inline_snippet ==
            stack_size_after_inline_snippet);
}

static void codegen_emit_add(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IADD, arena);
    break;
  case VERIFICATION_INFO_LONG:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LADD, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  codegen_frame_stack_pop(gen->frame);
}

static void codegen_emit_neg(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);
  const Jvm_verification_info_kind kind = array32_last(gen->frame->stack)->kind;

  switch (kind) {
  case VERIFICATION_INFO_INT:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_INEG, arena);
    break;
  case VERIFICATION_INFO_LONG:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LNEG, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void codegen_emit_lcmp(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(arena != NULL);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LCMP, arena);

  codegen_frame_stack_pop(gen->frame);
  codegen_frame_stack_pop(gen->frame);

  codegen_frame_stack_push(
      gen->frame, (Jvm_verification_info){.kind = VERIFICATION_INFO_INT},
      arena);
}

static void codegen_emit_bipush(codegen_generator *gen, u8 value,
                                Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(arena != NULL);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_BIPUSH, arena);
  jvm_code_push_u8(&gen->code->bytecode, value, arena);

  codegen_frame_stack_push(
      gen->frame, (Jvm_verification_info){.kind = VERIFICATION_INFO_INT},
      arena);
}

static void codegen_emit_ixor(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len >= 2);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);
  pg_assert(array32_last(gen->frame->stack)->kind == VERIFICATION_INFO_INT);
  pg_assert(array32_penultimate(gen->frame->stack)->kind ==
            VERIFICATION_INFO_INT);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IXOR, arena);

  codegen_frame_stack_pop(gen->frame);
}

static void codegen_emit_mul(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;
  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IMUL, arena);
    break;
  case VERIFICATION_INFO_LONG:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LMUL, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  codegen_frame_stack_pop(gen->frame);
}

static void codegen_emit_div(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IDIV, arena);
    break;
  case VERIFICATION_INFO_LONG:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LDIV, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  codegen_frame_stack_pop(gen->frame);
}

static void codegen_emit_rem(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IREM, arena);
    break;
  case VERIFICATION_INFO_LONG:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LREM, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }

  codegen_frame_stack_pop(gen->frame);
}

static void
codegen_emit_load_constant_single_word(codegen_generator *gen, u16 constant_i,
                                       Jvm_verification_info verification_info,
                                       Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(constant_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len < UINT16_MAX);
  pg_assert(jvm_verification_info_kind_word_count(verification_info.kind) == 1);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LDC_W, arena);
  jvm_code_array_push_u16(&gen->code->bytecode, constant_i, arena);

  pg_assert(gen->frame->stack.len < UINT16_MAX);

  codegen_frame_stack_push(gen->frame, verification_info, arena);
}

static void
codegen_emit_load_constant_double_word(codegen_generator *gen, u16 constant_i,
                                       Jvm_verification_info verification_info,
                                       Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(constant_i > 0);
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len < UINT16_MAX);
  pg_assert(jvm_verification_info_kind_word_count(verification_info.kind) == 2);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LDC2_W, arena);
  jvm_code_array_push_u16(&gen->code->bytecode, constant_i, arena);

  pg_assert(gen->frame->stack.len < UINT16_MAX);

  codegen_frame_stack_push(gen->frame, verification_info, arena);
}

static void codegen_emit_return_nothing(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(arena != NULL);

  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_RETURN, arena);
}

static void codegen_emit_return_value(codegen_generator *gen, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(arena != NULL);

  pg_assert(gen->frame->stack.len >= 1);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);
  const Jvm_verification_info_kind kind = array32_last(gen->frame->stack)->kind;

  switch (kind) {
  case VERIFICATION_INFO_INT:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IRETURN, arena);
    break;
  case VERIFICATION_INFO_LONG:
    jvm_code_push_u8(&gen->code->bytecode, BYTECODE_LRETURN, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void codegen_begin_scope(codegen_generator *gen) {
  pg_assert(gen->frame);
  pg_assert(gen->frame->scope_depth < UINT32_MAX);

  gen->frame->scope_depth += 1;
  gen->scope_id += 1;
}

static void stack_map_record_frame_at_pc(const codegen_frame *frame,
                                         Array32(Stack_map_frame) *
                                             stack_map_frames,
                                         u16 pc, Arena *arena) {
  pg_assert(frame != NULL);
  pg_assert(arena != NULL);

  const Stack_map_frame stack_map_frame = {
      .frame = codegen_frame_clone(frame, arena),
      .pc = pc,
  };
  *array32_push(stack_map_frames, arena) = stack_map_frame;
}

static void codegen_frame_drop_current_scope_variables(codegen_frame *frame) {
  pg_assert(frame != NULL);

  u32 to_drop = 0;
  for (i64 i = (i64)frame->locals.len - 1; i >= 0; i--) {
    const Jvm_variable *const variable = &frame->locals.data[i];
    if (variable->scope_depth < frame->scope_depth)
      break;

    pg_assert(variable->scope_depth == frame->scope_depth);

    pg_assert(to_drop < UINT32_MAX);
    to_drop += 1;
  }

  array32_drop(&frame->locals, to_drop);
}

static void codegen_end_scope(codegen_generator *gen) {
  pg_assert(gen);
  pg_assert(gen->frame);
  pg_assert(gen->frame->scope_depth > 0);

  codegen_frame_drop_current_scope_variables(gen->frame);

  gen->frame->scope_depth -= 1;
}

// TODO: Should the AST_KIND_VAR_DEFINITION node simply store the variable
// slot number? Or use a lookup table?
static bool jvm_find_variable(const codegen_frame *frame, Ast_handle ast_handle,
                              u16 *logical_local_index,
                              u16 *physical_local_index) {
  pg_assert(frame != NULL);
  pg_assert(!ast_handle_is_nil(ast_handle));
  pg_assert(logical_local_index != NULL);
  pg_assert(physical_local_index != NULL);

  *physical_local_index = frame->locals_physical_count;
  for (i64 i = frame->locals.len - 1; i >= 0; i--) {
    const Jvm_variable *const variable = &frame->locals.data[i];
    *physical_local_index -=
        jvm_verification_info_kind_word_count(variable->verification_info.kind);
    if (variable->ast_handle.value != ast_handle.value)
      continue;

    pg_assert(*physical_local_index < frame->locals_physical_count);
    *logical_local_index = (u16)i;
    return true;
  }

  return false;
}

static void codegen_emit_node(codegen_generator *gen, Class_file *class_file,
                              Ast_handle ast_handle, Arena *arena);

static void codegen_patch_jump_at(codegen_generator *gen, u16 at, u16 target) {
  pg_assert(gen != NULL);
  pg_assert(gen->code != NULL);
  pg_assert(at > 0);
  pg_assert(target > 0);

  const i16 jump_offset = (i16)target - (i16)(at - 1);
  gen->code->bytecode.data[at + 0] = (u8)(((u16)(jump_offset & 0xff00)) >> 8);
  gen->code->bytecode.data[at + 1] = (u8)(((u16)(jump_offset & 0x00ff)) >> 0);
}

// TODO: Make a primitive emerge to use here and in codegen_emit_if_then_else.
static void codegen_emit_synthetic_if_then_else(codegen_generator *gen,
                                                u8 conditional_jump_opcode,
                                                Arena *arena) {
  // Assume the condition is already on the stack

  jvm_code_push_u8(&gen->code->bytecode, conditional_jump_opcode, arena);
  jvm_code_push_u8(&gen->code->bytecode, 0, arena);
  jvm_code_push_u8(&gen->code->bytecode, 3 + 2 + 3, arena);

  switch (conditional_jump_opcode) {
  case BYTECODE_IF_ICMPEQ:
  case BYTECODE_IF_ICMPNE:
  case BYTECODE_IF_ICMPLT:
  case BYTECODE_IF_ICMPGE:
  case BYTECODE_IF_ICMPGT:
  case BYTECODE_IF_ICMPLE:
    codegen_frame_stack_pop(gen->frame);
    codegen_frame_stack_pop(gen->frame);
    break;
  case BYTECODE_IFEQ:
  case BYTECODE_IFNE:
    codegen_frame_stack_pop(gen->frame);
    break;
  default:
    pg_assert(0 && "unreachable/unimplemented");
  }

  const codegen_frame *const frame_before_then_else =
      codegen_frame_clone(gen->frame, arena);

  codegen_emit_bipush(gen, true, arena); // Then.
  jvm_code_push_u8(&gen->code->bytecode, BYTECODE_GOTO, arena);
  jvm_code_push_u8(&gen->code->bytecode, 0, arena);
  jvm_code_push_u8(&gen->code->bytecode, 3 + 2, arena);

  const codegen_frame *const frame_after_then =
      codegen_frame_clone(gen->frame, arena);

  gen->frame = codegen_frame_clone(frame_before_then_else, arena);

  const u16 conditional_jump_target_absolute = (u16)gen->code->bytecode.len;
  codegen_emit_bipush(gen, false, arena); // Else.

  const u16 unconditional_jump_target_absolute = (u16)gen->code->bytecode.len;

  stack_map_record_frame_at_pc(frame_before_then_else, &gen->stack_map_frames,
                               conditional_jump_target_absolute, arena);
  stack_map_record_frame_at_pc(frame_after_then, &gen->stack_map_frames,
                               unconditional_jump_target_absolute, arena);
}

static void codegen_emit_gt(codegen_generator *gen, Arena *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPLE, arena);
    break;
  case VERIFICATION_INFO_LONG:
    codegen_emit_lcmp(gen, arena);
    codegen_emit_bipush(gen, 1, arena);
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPNE, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void codegen_emit_ne(codegen_generator *gen, Arena *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPEQ, arena);
    break;
  case VERIFICATION_INFO_LONG:
    codegen_emit_lcmp(gen, arena);
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IFEQ, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void codegen_emit_eq(codegen_generator *gen, Arena *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPNE, arena);
    break;
  case VERIFICATION_INFO_LONG:
    codegen_emit_lcmp(gen, arena);
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IFNE, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void codegen_emit_ge(codegen_generator *gen, Arena *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPLT, arena);
    break;
  case VERIFICATION_INFO_LONG:
    codegen_emit_lcmp(gen, arena);
    codegen_emit_bipush(gen, UINT8_MAX, arena);
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPEQ, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void codegen_emit_le(codegen_generator *gen, Arena *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPGT, arena);
    break;
  case VERIFICATION_INFO_LONG:
    codegen_emit_lcmp(gen, arena);
    codegen_emit_bipush(gen, 1, arena);
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPEQ, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void codegen_emit_lt(codegen_generator *gen, Arena *arena) {
  pg_assert(gen->frame != NULL);
  pg_assert(gen->frame->stack.len <= UINT16_MAX);

  const Jvm_verification_info_kind kind_a =
      array32_last(gen->frame->stack)->kind;

  const Jvm_verification_info_kind kind_b =
      array32_penultimate(gen->frame->stack)->kind;

  pg_assert(kind_a == kind_b);

  switch (kind_a) {
  case VERIFICATION_INFO_INT:
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPGE, arena);
    break;
  case VERIFICATION_INFO_LONG:
    codegen_emit_lcmp(gen, arena);
    codegen_emit_bipush(gen, UINT8_MAX, arena);
    codegen_emit_synthetic_if_then_else(gen, BYTECODE_IF_ICMPNE, arena);
    break;
  default:
    pg_assert(0 && "todo");
  }
}

static void codegen_emit_if_then_else(codegen_generator *gen,
                                      Class_file *class_file,
                                      Ast_handle ast_handle, Arena *arena) {
  // clang-format off
//
//               IF 
//              /  \
//    condition     THEN_ELSE
//                 /      \
//             then        else
//
//                 <condition expression>
//      x     ---- jump_conditionally (IFEQ,  etc)
//      x     |    jump_conditionally_offset1
//      x     |    jump_conditionally_offset2
//      x     |    <then branch>
//  +   x  ...|... jump
//  +   x  .  |    jump_offset1 
//  +   x  .  |    jump_offset2
//  +   x  .  |--> <else branch> 
//  +      ......> ...          
//
  // clang-format on

  pg_assert(gen != NULL);
  pg_assert(gen->resolver->parser != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);
  pg_assert(gen->frame != NULL);

  const Ast *const node = ast_handle_to_ptr(ast_handle, *arena);
  pg_assert(!type_handle_handles_nil(node->type_handle));

  // Emit condition.
  codegen_emit_node(gen, class_file, node->lhs, arena);

  const u16 jump_conditionally_from_i =
      codegen_emit_jump_conditionally(gen, BYTECODE_IFEQ, arena);

  const Ast *const rhs = ast_handle_to_ptr(node->rhs, *arena);
  pg_assert(rhs->kind == AST_KIND_THEN_ELSE);

  // Emit `then` branch.
  // Save a clone of the frame before the `then` branch since we need it
  // later.
  const codegen_frame *const frame_before_then_else =
      codegen_frame_clone(gen->frame, arena);

  codegen_emit_node(gen, class_file, rhs->lhs, arena);
  const u16 jump_from_i =
      ast_handle_is_nil(rhs->rhs) ? 0 : codegen_emit_jump(gen, arena);
  const u16 conditional_jump_target_absolute = (u16)gen->code->bytecode.len;

  // Save a clone of the frame after the `then` branch executed so that we
  // can generate a stack map frame later.
  const codegen_frame *const frame_after_then =
      codegen_frame_clone(gen->frame, arena);

  // Emit `else` branch.
  // Restore the frame as if the `then` branch never executed.
  gen->frame = codegen_frame_clone(frame_before_then_else, arena);

  codegen_emit_node(gen, class_file, rhs->rhs, arena);
  const u16 unconditional_jump_target_absolute = (u16)gen->code->bytecode.len;

  gen->frame->max_physical_stack = pg_max(frame_after_then->max_physical_stack,
                                          gen->frame->max_physical_stack);
  gen->frame->max_physical_locals = pg_max(
      frame_after_then->max_physical_locals, gen->frame->max_physical_locals);
  // TODO: assert that the stack/locals count is the same?

  // Patch first, conditional, jump.
  {
    codegen_patch_jump_at(gen, jump_conditionally_from_i,
                          conditional_jump_target_absolute);
    stack_map_record_frame_at_pc(frame_before_then_else, &gen->stack_map_frames,
                                 conditional_jump_target_absolute, arena);
  }
  // Patch second, unconditional, jump.
  {
    if (!ast_handle_is_nil(rhs->rhs)) {
      codegen_patch_jump_at(gen, jump_from_i,
                            unconditional_jump_target_absolute);

      stack_map_record_frame_at_pc(frame_after_then, &gen->stack_map_frames,
                                   unconditional_jump_target_absolute, arena);
    }
  }
}

static int stack_map_frame_sort(const void *a, const void *b) {
  pg_assert(a != NULL);
  pg_assert(b != NULL);

  const Stack_map_frame *const smp_a = a;
  const Stack_map_frame *const smp_b = b;

  return (int)smp_a->pc - (int)smp_b->pc;
}

static void stack_map_resolve_frames(const codegen_frame *first_method_frame,
                                     Array32(Stack_map_frame) stack_map_frames,
                                     Arena *arena) {
  pg_assert(first_method_frame != NULL);
  pg_assert(arena != NULL);

  if (array32_is_empty(stack_map_frames))
    return;

  // TODO: Better sort.
  qsort(stack_map_frames.data, stack_map_frames.len, sizeof(Stack_map_frame),
        stack_map_frame_sort);

  for (u64 i = 0; i < stack_map_frames.len; i++) {
    Stack_map_frame *const stack_map_frame = &stack_map_frames.data[i];
    codegen_frame *const frame = stack_map_frame->frame;

    const codegen_frame *const previous_frame =
        i > 0 ? stack_map_frames.data[i - 1].frame : first_method_frame;

    i16 locals_delta = (i16)frame->locals.len - (i16)previous_frame->locals.len;

    i32 offset_delta =
        i == 0 ? stack_map_frame->pc
               : (stack_map_frame->pc - stack_map_frames.data[i - 1].pc - 1);

    if (offset_delta == -1) // Duplicate jump target, already has a valid
                            // stack map frame, skip.
    {
      stack_map_frame->tombstone = true;
      continue;
    }

    pg_assert(offset_delta >= 0);
    pg_assert(offset_delta <= UINT16_MAX);

    if (frame->stack_physical_count == 0 && locals_delta == 0 &&
        offset_delta <= 63) {
      stack_map_frame->kind = (u8)offset_delta;
      stack_map_frame->offset_delta = (u16)offset_delta;
    } else if (frame->stack_physical_count == 0 && locals_delta == 0 &&
               offset_delta > 63) {
      pg_assert(0 && "todo"); // same_frame_extended
    } else if (frame->stack_physical_count == 1 && locals_delta == 0 &&
               offset_delta <= 63) {
      stack_map_frame->kind = (u8)offset_delta + 64;
      stack_map_frame->offset_delta = (u16)offset_delta;

      pg_assert(stack_map_frame->kind >= 64);
      pg_assert(stack_map_frame->kind <= 127);
    } else if (frame->stack_physical_count == 1 && locals_delta == 0 &&
               offset_delta <= 63) {
      pg_assert(0 && "todo"); // same_locals_1_stack_item_frame_extended
    } else if (frame->stack_physical_count == 0 &&
               (1 <= locals_delta && locals_delta <= 3)) { // append_frame
      stack_map_frame->kind = (u8)251 + (u8)locals_delta;
      stack_map_frame->offset_delta = (u16)offset_delta;
    } else if (frame->stack_physical_count == 0 &&
               (locals_delta == -1 || locals_delta == -2 ||
                locals_delta == -3) &&
               offset_delta <= 3) {
      pg_assert(0 && "todo"); // chop_frame
    } else {
      stack_map_frame->kind = 255;
      stack_map_frame->offset_delta = (u16)offset_delta;
    }
  }
}

__attribute__((unused)) static u16
codegen_add_class_name_in_constant_pool(Class_file *class_file, Str class_name,
                                        Arena *arena) {
  const u16 class_name_i =
      jvm_add_constant_string(&class_file->constant_pool, class_name, arena);
  const Jvm_constant_pool_entry out_class = {
      .kind = CONSTANT_POOL_KIND_CLASS_INFO,
      .v = {.java_class_name = class_name_i}};
  const u16 class_i =
      jvm_constant_array_push(&class_file->constant_pool, &out_class, arena);

  return class_i;
}

static void codegen_emit_node(codegen_generator *gen, Class_file *class_file,
                              Ast_handle ast_handle, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->resolver->parser != NULL);
  pg_assert(gen->resolver->parser->lexer != NULL);
  pg_assert(gen->resolver->parser->tokens_i <=
            gen->resolver->parser->lexer->tokens.len);
  pg_assert(class_file != NULL);

  if (ast_handle_is_nil(ast_handle))
    return;

  const Ast *const node = ast_handle_to_ptr(ast_handle, *arena);
  const Token token =
      gen->resolver->parser->lexer->tokens.data[node->main_token_i];
  const Type *const type = type_handle_to_ptr(node->type_handle, *arena);

  switch (node->kind) {
  case AST_KIND_NONE:
    return;
  case AST_KIND_BOOL: {
    pg_assert(node->main_token_i < gen->resolver->parser->lexer->tokens.len);
    const Jvm_constant_pool_entry constant = {
        .kind = CONSTANT_POOL_KIND_INT, .v = {.number = node->extra_data}};
    const u16 number_i =
        jvm_constant_array_push(&class_file->constant_pool, &constant, arena);

    pg_assert(gen->code != NULL);
    pg_assert(gen->frame != NULL);

    const Jvm_verification_info verification_info = {.kind =
                                                         VERIFICATION_INFO_INT};
    codegen_emit_load_constant_single_word(gen, number_i, verification_info,
                                           arena);
    break;
  }
  case AST_KIND_NUMBER: {
    pg_assert(node->main_token_i < gen->resolver->parser->lexer->tokens.len);

    Jvm_constant_pool_kind pool_kind = CONSTANT_POOL_KIND_INT;
    Jvm_verification_info_kind verification_info_kind = VERIFICATION_INFO_INT;
    if (type->kind == TYPE_LONG) {
      pool_kind = CONSTANT_POOL_KIND_LONG;
      verification_info_kind = VERIFICATION_INFO_LONG;
    }
    // TODO: Float, Double, etc.

    const u64 number = node->extra_data;
    const Jvm_constant_pool_entry constant = {.kind = pool_kind,
                                              .v = {.number = number}};
    const u16 number_i =
        jvm_constant_array_push(&class_file->constant_pool, &constant, arena);
    if (pool_kind == CONSTANT_POOL_KIND_LONG ||
        pool_kind == CONSTANT_POOL_KIND_DOUBLE) {
      const Jvm_constant_pool_entry dummy = {0};
      jvm_constant_array_push(&class_file->constant_pool, &dummy, arena);

      codegen_emit_load_constant_double_word(
          gen, number_i,
          (Jvm_verification_info){.kind = verification_info_kind}, arena);
    } else {
      codegen_emit_load_constant_single_word(
          gen, number_i,
          (Jvm_verification_info){.kind = verification_info_kind}, arena);
    }
    break;
  }
  case AST_KIND_CALL: {
    pg_assert(type->this_class_name.data != NULL);
    pg_assert(type->this_class_name.len > 0);
    pg_assert(type->kind == TYPE_METHOD || type->kind == TYPE_CONSTRUCTOR);

    for (u64 i = 0; i < node->nodes.len; i++) {
      codegen_emit_node(gen, class_file, node->nodes.data[i], arena);
    }

    if (type->flags & TYPE_FLAG_INLINE_ONLY) {
      const u16 initial_locals_physical_count =
          gen->frame->locals_physical_count;

      u64 stack_index = array32_last_index(gen->frame->stack);

      for (u64 i = 0; i < node->nodes.len; i++) {
        const Ast_handle argument_i = node->nodes.data[i];
        const Ast *const argument = ast_handle_to_ptr(argument_i, *arena);

        // Each argument `a, b, c` is now on the stack in order: `[..] [this] a
        // b c` with the corresponding verification info.
        const Jvm_verification_info verification_info =
            gen->frame->stack.data[stack_index];
        const Jvm_variable variable = {
            .ast_handle = argument_i,
            .type_handle = argument->type_handle,
            .scope_depth = gen->frame->scope_depth,
            .verification_info = verification_info,
        };

        u16 logical_local_index = 0;
        u16 physical_local_index = 0;
        codegen_frame_locals_push(gen, &variable, &logical_local_index,
                                  &physical_local_index, arena);

        codegen_emit_store_variable(gen, (u8)physical_local_index, arena);

        stack_index -=
            jvm_verification_info_kind_word_count(verification_info.kind);
      }
      codegen_emit_inlined_method_call(gen, class_file, type,
                                       initial_locals_physical_count, arena);

    } else {
      // TODO: Support non static calls.
      pg_assert(type->v.method.access_flags & ACCESS_FLAGS_STATIC);

      const Jvm_constant_pool_entry class_name = {
          .kind = CONSTANT_POOL_KIND_UTF8,
          .v = {.s = gen->resolver->this_class_name}};
      const u16 class_name_i = jvm_constant_array_push(
          &class_file->constant_pool, &class_name, arena);

      const Jvm_constant_pool_entry class = {
          .kind = CONSTANT_POOL_KIND_CLASS_INFO,
          .v = {.java_class_name = class_name_i}};
      const u16 class_i =
          jvm_constant_array_push(&class_file->constant_pool, &class, arena);

      const Jvm_constant_pool_entry name = {
          .kind = CONSTANT_POOL_KIND_UTF8,
          .v = {
              .s = type->kind == TYPE_METHOD ? type->v.method.name
                                             : str_from_c(CONSTRUCTOR_JVM_NAME),
          }};
      const u16 name_i =
          jvm_constant_array_push(&class_file->constant_pool, &name, arena);

      Str_builder descriptor_s = sb_new(256, arena);
      descriptor_s =
          jvm_fill_descriptor_string(descriptor_s, node->type_handle, arena);
      const Jvm_constant_pool_entry descriptor = {
          .kind = CONSTANT_POOL_KIND_UTF8, .v = {.s = sb_build(descriptor_s)}};
      const u16 descriptor_i = jvm_constant_array_push(
          &class_file->constant_pool, &descriptor, arena);

      const Jvm_constant_pool_entry name_and_type = {
          .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
          .v = {.name_and_type = {.name = name_i, .descriptor = descriptor_i}}};
      const u16 name_and_type_handle = jvm_constant_array_push(
          &class_file->constant_pool, &name_and_type, arena);

      Jvm_constant_pool_entry method_ref = {
          .kind = CONSTANT_POOL_KIND_METHOD_REF,
          .v = {.method_ref = {.class = class_i,
                               .name_and_type = name_and_type_handle}}};
      const u16 method_ref_i = jvm_constant_array_push(
          &class_file->constant_pool, &method_ref, arena);

      if (type->kind == TYPE_METHOD)
        codegen_emit_invoke_static(gen, method_ref_i, &type->v.method, arena);
      else if (type->kind == TYPE_CONSTRUCTOR)
        codegen_emit_invoke_special(gen, method_ref_i, &type->v.method, arena);
    }

    break;
  }
  case AST_KIND_FUNCTION_DEFINITION: {
    array32_clear(&gen->locals);

    const u32 token_name_i = node->main_token_i;
    pg_assert(token_name_i < gen->resolver->parser->lexer->tokens.len);
    const Token token_name =
        gen->resolver->parser->lexer->tokens.data[token_name_i];
    pg_assert(token_name.kind == TOKEN_KIND_IDENTIFIER);

    Str method_name = {
        .len = lex_identifier_length(gen->resolver->parser->buf,
                                     token_name.source_offset),
        .data = &gen->resolver->parser->buf.data[token_name.source_offset],
    };
    const u16 method_name_i =
        jvm_add_constant_string(&class_file->constant_pool, method_name, arena);

    Str_builder descriptor = sb_new(64, arena);
    descriptor =
        jvm_fill_descriptor_string(descriptor, node->type_handle, arena);
    const u16 descriptor_i = jvm_add_constant_string(
        &class_file->constant_pool, sb_build(descriptor), arena);

    Jvm_method method = {
        .access_flags = ACCESS_FLAGS_STATIC | ACCESS_FLAGS_PUBLIC,
        .name = method_name_i,
        .descriptor = descriptor_i,
    };
    method.attributes = array32_make(Jvm_attribute, 0, 1, arena);

    Jvm_attribute_code code = {0};
    gen->code = &code;
    codegen_frame frame = {0};
    codegen_frame_init(&frame, arena);

    gen->frame = &frame;

    // `lhs` is the arguments, `rhs` is the body.

    codegen_begin_scope(gen);
    // Emit parameters i.e. locals.
    codegen_emit_node(gen, class_file, node->lhs, arena);
    // The firt frame implicitly encompasses arguments as locals.
    codegen_frame *const first_method_frame =
        codegen_frame_clone(gen->frame, arena);
    // Emit the body.
    codegen_emit_node(gen, class_file, node->rhs, arena);

    { // Add return if there is none e.g. the function body is empty or the
      // return type is Unit.
      // TODO: Should it be in the lowering phase instead?

      if (ast_handle_is_nil(node->rhs)) { // Empty body
        codegen_emit_return_nothing(gen, arena);
      } else {
        const Ast *const rhs = ast_handle_to_ptr(node->rhs, *arena);
        pg_assert(rhs->kind == AST_KIND_LIST);

        if (rhs->nodes.len == 0) {
          codegen_emit_return_nothing(gen, arena);
        } else {
          const Ast_handle last_ast_handle = *array32_last(rhs->nodes);
          const Ast *const last_node =
              ast_handle_to_ptr(last_ast_handle, *arena);

          if (last_node->kind != AST_KIND_RETURN) {
            codegen_emit_return_nothing(gen, arena);
          }
        }
      }
    }

    codegen_end_scope(gen);

    gen->code->max_physical_stack = gen->frame->max_physical_stack;
    gen->code->max_physical_locals = gen->frame->max_physical_locals;

    stack_map_resolve_frames(first_method_frame, gen->stack_map_frames, arena);

    Jvm_attribute attribute_stack_map_frames = {
        .kind = ATTRIBUTE_KIND_STACK_MAP_TABLE,
        .name = jvm_add_constant_cstring(&class_file->constant_pool,
                                         "StackMapTable", arena),
        .v.stack_map_table =
            array32_make(Stack_map_frame, 0, gen->stack_map_frames.len, arena),
    };

    for (u64 i = 0; i < gen->stack_map_frames.len; i++) {
      if (!gen->stack_map_frames.data[i].tombstone)
        *array32_push(&attribute_stack_map_frames.v.stack_map_table, arena) =
            gen->stack_map_frames.data[i];
    }

    *array32_push(&code.attributes, arena) = attribute_stack_map_frames;

    const Jvm_attribute attribute_code = {
        .kind = ATTRIBUTE_KIND_CODE,
        .name =
            jvm_add_constant_cstring(&class_file->constant_pool, "Code", arena),
        .v = {.code = code}};
    *array32_push(&method.attributes, arena) = attribute_code;

    *array32_push(&class_file->methods, arena) = method;

    gen->code = NULL;
    gen->frame = NULL;
    array32_clear(&gen->stack_map_frames);
    break;
  }
  case AST_KIND_UNARY: {

    switch (token.kind) {
    case TOKEN_KIND_NOT:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_bipush(gen, 1, arena);
      codegen_emit_ixor(gen, arena);
      break;

    case TOKEN_KIND_MINUS:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_neg(gen, arena);
      break;

    default:
      pg_assert(0 && "unimplemented");
    }
    break;
  }
  case AST_KIND_BINARY: {
    pg_assert(gen->frame != NULL);

    switch (token.kind) {
    case TOKEN_KIND_NONE:
      break; // Nothing to do.

    case TOKEN_KIND_PLUS:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_add(gen, arena);
      break;

    case TOKEN_KIND_MINUS:
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_neg(gen, arena);
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_add(gen, arena);
      break;

    case TOKEN_KIND_STAR:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_mul(gen, arena);
      break;

    case TOKEN_KIND_SLASH:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_div(gen, arena);
      break;

    case TOKEN_KIND_PERCENT:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_rem(gen, arena);
      break;

    case TOKEN_KIND_AMPERSAND_AMPERSAND: {
      // Since the if_xxx opcodes always pop the condition off the stack,
      // there is no simple way to push 0 on the stack if `lhs` is falsey.
      // We have to use this contrived way, short of advanced CFG analysis.
      // :(
      //
      // clang-format off
      //
      // a && b
      // 
      // <=>
      // 
      // if (a) {
      //   if (b) {
      //     push 1 
      //     goto end
      //   }  
      // } else {
      //   push 0
      // }
      // end:
      //
      //                 lhs
      //      x     ---- jump_conditionally (IFEQ,  etc)
      //      x     |    jump_conditionally_offset1 
      //      x     |    jump_conditionally_offset2
      //      x     |    rhs
      //  +   x  ...|... jump
      //  +   x  .  |    jump_offset1 
      //  +   x  .  |    jump_offset2
      //  +   x  .  |--> bipush 0
      //  +      ......> ...           
      //
      // clang-format on
      codegen_emit_node(gen, class_file, node->lhs, arena);

      jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IFEQ, arena);
      const u16 conditional_jump_location = (u16)gen->code->bytecode.len;
      jvm_code_array_push_u16(&gen->code->bytecode, 0, arena);
      codegen_frame_stack_pop(gen->frame);

      const codegen_frame *const frame_before_rhs =
          codegen_frame_clone(gen->frame, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);

      const codegen_frame *const frame_after_rhs =
          codegen_frame_clone(gen->frame, arena);
      const u16 unconditional_jump_location = codegen_emit_jump(gen, arena);

      {
        const u16 pc_end = (u16)gen->code->bytecode.len;
        codegen_patch_jump_at(gen, conditional_jump_location, pc_end);
        stack_map_record_frame_at_pc(frame_before_rhs, &gen->stack_map_frames,
                                     pc_end, arena);
      }

      // Restore the frame as if the `rhs` branch never executed.
      gen->frame = codegen_frame_clone(frame_before_rhs, arena);
      codegen_emit_bipush(gen, false, arena);

      {
        const u16 pc_end = (u16)gen->code->bytecode.len;
        codegen_patch_jump_at(gen, unconditional_jump_location, pc_end);
        stack_map_record_frame_at_pc(frame_after_rhs, &gen->stack_map_frames,
                                     pc_end, arena);
      }

      break;
    }

    case TOKEN_KIND_PIPE_PIPE: {
      // Since the if_xxx opcodes always pop the condition off the stack,
      // there is no simple way to push 0 on the stack if `lhs` is falsey.
      // We have to use this contrived way, short of advanced CFG analysis.
      // :(
      //
      // clang-format off
      //
      // a || b
      // 
      // <=>
      // 
      // if (a) {
      //   push 1
      // } else {
      //   if (b) {
      //     push 1 
      //     goto end
      //   }
      //   push 0
      // }
      // end:
      //
      //                 lhs
      //      x     ---- jump_conditionally (IFNE)
      //      x     |    jump_conditionally_offset1 
      //      x     |    jump_conditionally_offset2
      //      x     |    rhs
      //  +   x  ...|... jump
      //  +   x  .  |    jump_offset1 
      //  +   x  .  |    jump_offset2
      //  +   x  .  |--> bipush 1
      //  +      ......> ...           
      //
      // clang-format on
      codegen_emit_node(gen, class_file, node->lhs, arena);

      jvm_code_push_u8(&gen->code->bytecode, BYTECODE_IFNE, arena);
      const u16 conditional_jump_location = (u16)gen->code->bytecode.len;
      jvm_code_array_push_u16(&gen->code->bytecode, 0, arena);
      codegen_frame_stack_pop(gen->frame);

      const codegen_frame *const frame_before_rhs =
          codegen_frame_clone(gen->frame, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);

      const codegen_frame *const frame_after_rhs =
          codegen_frame_clone(gen->frame, arena);
      const u16 unconditional_jump_location = codegen_emit_jump(gen, arena);

      {
        const u16 pc_end = (u16)gen->code->bytecode.len;
        codegen_patch_jump_at(gen, conditional_jump_location, pc_end);
        stack_map_record_frame_at_pc(frame_before_rhs, &gen->stack_map_frames,
                                     pc_end, arena);
      }

      // Restore the frame as if the `rhs` branch never executed.
      gen->frame = codegen_frame_clone(frame_before_rhs, arena);
      codegen_emit_bipush(gen, true, arena);

      {
        const u16 pc_end = (u16)gen->code->bytecode.len;
        codegen_patch_jump_at(gen, unconditional_jump_location, pc_end);
        stack_map_record_frame_at_pc(frame_after_rhs, &gen->stack_map_frames,
                                     pc_end, arena);
      }

      break;
    }

    case TOKEN_KIND_EQUAL_EQUAL:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_eq(gen, arena);
      break;

    case TOKEN_KIND_LE:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_le(gen, arena);
      break;

    case TOKEN_KIND_LT:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_lt(gen, arena);
      break;

    case TOKEN_KIND_GT:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_gt(gen, arena);
      break;

    case TOKEN_KIND_GE:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_ge(gen, arena);
      break;

    case TOKEN_KIND_NOT_EQUAL:
      codegen_emit_node(gen, class_file, node->lhs, arena);
      codegen_emit_node(gen, class_file, node->rhs, arena);
      codegen_emit_ne(gen, arena);
      break;

    default:
      pg_assert(0 && "todo");
    }
    break;
  }
  case AST_KIND_LIST: {
    if (gen->code != NULL) {
      pg_assert(gen->frame != NULL);
    }

    for (u64 i = 0; i < node->nodes.len; i++) {
      const Ast_handle child_i = node->nodes.data[i];

      if (gen->frame != NULL) {
        pg_assert(array32_is_empty(gen->frame->stack));
      }
      codegen_emit_node(gen, class_file, child_i, arena);

      // If the 'statement' was in fact an expression, we need to pop it
      // out.
      // IMPROVEMENT: If we emit the pop earlier, some stack map frames
      // don't have to be a full_frame but can be something smaller e.g.
      // append_frame.
      const Ast *const child = ast_handle_to_ptr(child_i, *arena);
      if (child->kind != AST_KIND_RETURN && // Avoid: `return; pop;`
          gen->frame != NULL) {
        while (!array32_is_empty(gen->frame->stack))
          codegen_emit_pop(gen, arena);
      }
    }

    break;
  }
  case AST_KIND_VAR_DEFINITION: {
    pg_assert(gen->frame != NULL);
    pg_assert(!type_handle_handles_nil(node->type_handle));

    codegen_emit_node(gen, class_file, node->lhs, arena);
    codegen_emit_node(gen, class_file, node->rhs, arena);

    const Jvm_verification_info verification_info =
        codegen_type_to_verification_info(
            resolver_eval_type(node->type_handle, *arena));
    const Jvm_variable variable = {
        .ast_handle = ast_handle,
        .type_handle = node->type_handle,
        .scope_depth = gen->frame->scope_depth,
        .verification_info = verification_info,
    };

    u16 logical_local_index = 0;
    u16 physical_local_index = 0;
    codegen_frame_locals_push(gen, &variable, &logical_local_index,
                              &physical_local_index, arena);

    codegen_emit_store_variable(gen, (u8)physical_local_index, arena);
    break;
  }
  case AST_KIND_VAR_REFERENCE: {
    pg_assert(gen->frame != NULL);
    pg_assert(!type_handle_handles_nil(node->type_handle));

    pg_assert(ast_handle_to_ptr(node->lhs, *arena)->kind ==
                  AST_KIND_VAR_DEFINITION ||
              ast_handle_to_ptr(node->lhs, *arena)->kind ==
                  AST_KIND_FUNCTION_PARAMETER);

    u16 logical_local_index = 0;
    u16 physical_local_index = 0;
    pg_assert(jvm_find_variable(gen->frame, node->lhs, &logical_local_index,
                                &physical_local_index));

    const Jvm_verification_info verification_info =
        gen->frame->locals.data[logical_local_index].verification_info;
    if (verification_info.kind == VERIFICATION_INFO_INT)
      codegen_emit_load_variable_int(gen, (u8)physical_local_index, arena);
    else if (verification_info.kind == VERIFICATION_INFO_LONG)
      codegen_emit_load_variable_long(gen, (u8)physical_local_index, arena);
    else
      pg_assert(0 && "todo");

    break;
  }
  case AST_KIND_IF: {
    codegen_emit_if_then_else(gen, class_file, ast_handle, arena);
    break;
  }
  case AST_KIND_WHILE_LOOP: {
    const u16 pc_start = (u16)gen->code->bytecode.len;
    const codegen_frame *const frame_before_loop =
        codegen_frame_clone(gen->frame, arena);

    codegen_emit_node(gen, class_file, node->lhs, arena); // Condition.
    const u16 conditional_jump =
        codegen_emit_jump_conditionally(gen, BYTECODE_IFEQ, arena);
    codegen_emit_node(gen, class_file, node->rhs, arena); // Body.
    const u16 unconditional_jump = codegen_emit_jump(gen, arena);

    const i16 unconditional_jump_delta =
        (i16) - ((i16)unconditional_jump - (i16)1 - (i16)pc_start);
    gen->code->bytecode.data[unconditional_jump + 0] =
        (u8)(((u16)(unconditional_jump_delta & 0xff00)) >> 8);
    gen->code->bytecode.data[unconditional_jump + 1] =
        (u8)(((u16)(unconditional_jump_delta & 0x00ff)) >> 0);

    const u16 pc_end = (u16)gen->code->bytecode.len;

    // This stack map frame covers the unconditional jump.
    stack_map_record_frame_at_pc(frame_before_loop, &gen->stack_map_frames,
                                 pc_start, arena);

    // Patch first, conditional, jump.
    {
      codegen_patch_jump_at(gen, conditional_jump, pc_end);
      stack_map_record_frame_at_pc(frame_before_loop, &gen->stack_map_frames,
                                   pc_end, arena);
    }

    break;
  }
  case AST_KIND_STRING: {
    const u32 length =
        lex_string_length(gen->resolver->parser->buf, token.source_offset);
    Str s = {
        .data = gen->resolver->parser->buf.data + token.source_offset,
        .len = length,
    };
    const u16 string_i =
        jvm_add_constant_string(&class_file->constant_pool, s, arena);
    const u16 jstring_i =
        jvm_add_constant_jstring(&class_file->constant_pool, string_i, arena);

    // TODO: Deduplicate.
    const Jvm_constant_pool_entry string_class_info = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {
            .java_class_name =
                jvm_add_constant_string(&class_file->constant_pool,
                                        str_from_c("java/lang/String"), arena),
        }};

    const Jvm_verification_info verification_info = {
        .kind = VERIFICATION_INFO_OBJECT,
        .extra_data = jvm_constant_array_push(&class_file->constant_pool,
                                              &string_class_info, arena),
    };
    codegen_emit_load_constant_single_word(gen, jstring_i, verification_info,
                                           arena);

    break;
  }
  case AST_KIND_CLASS_REFERENCE: {
    pg_assert(0 && "todo");
    break;
  }
  case AST_KIND_NAVIGATION: {
    pg_assert(0 && "todo");
    break;
  }
  case AST_KIND_FUNCTION_PARAMETER: {
    const Jvm_verification_info verification_info =
        codegen_type_to_verification_info(
            resolver_eval_type(node->type_handle, *arena));
    const Jvm_variable argument = {
        .ast_handle = ast_handle,
        .type_handle = node->type_handle,
        .scope_depth = gen->frame->scope_depth,
        .verification_info = verification_info,
    };
    u16 logical_local_index = 0;
    u16 physical_local_index = 0;
    codegen_frame_locals_push(gen, &argument, &logical_local_index,
                              &physical_local_index, arena);
    break;
  }

  case AST_KIND_TYPE:
    // No-op. Although at some point we might need to generate RTTI or such.
    return;

  case AST_KIND_THEN_ELSE:
  case AST_KIND_UNRESOLVED_NAME:
    pg_assert(0 && "unreachable");

  case AST_KIND_ASSIGNMENT: {
    const Ast *const lhs = ast_handle_to_ptr(node->lhs, *arena);
    pg_assert(lhs->kind == AST_KIND_VAR_REFERENCE);

    codegen_emit_node(gen, class_file, node->rhs, arena);

    u16 logical_local_index = 0;
    u16 physical_local_index = 0;
    pg_assert(jvm_find_variable(gen->frame, lhs->lhs, &logical_local_index,
                                &physical_local_index));

    codegen_emit_store_variable(gen, (u8)physical_local_index, arena);
    break;
  }

  case AST_KIND_RETURN:
    codegen_emit_node(gen, class_file, node->lhs, arena);
    type->kind == TYPE_UNIT ? codegen_emit_return_nothing(gen, arena)
                            : codegen_emit_return_value(gen, arena);
    break;

  case AST_KIND_MAX:
    pg_assert(0 && "unreachable");
  }
}

static Str codegen_make_class_name_from_path(Str path, Arena *arena) {

  Str_split_result slash_split = str_rsplit(path, '/');
  pg_assert(!str_is_empty(slash_split.right));

  Str_split_result dot_split = str_rsplit(slash_split.right, '.');
  pg_assert(dot_split.found);
  pg_assert(!str_is_empty(dot_split.left));

  Str_builder res = sb_clone(dot_split.left, arena);
  res = sb_capitalize_at(res, 0);
  return sb_build(res);
}

static void codegen_emit_synthetic_class(codegen_generator *gen,
                                         Class_file *class_file, Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->resolver != NULL);
  pg_assert(gen->resolver->parser != NULL);
  pg_assert(gen->resolver->parser->lexer != NULL);
  pg_assert(gen->resolver->parser->tokens_i <=
            gen->resolver->parser->lexer->tokens.len);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);
  pg_assert(!str_is_empty(gen->resolver->this_class_name));

  { // This class
    const u16 this_class_name_i = jvm_add_constant_string(
        &class_file->constant_pool, gen->resolver->this_class_name, arena);

    const Jvm_constant_pool_entry this_class_info = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {
            .java_class_name = this_class_name_i,
        }};
    class_file->this_class = jvm_constant_array_push(&class_file->constant_pool,
                                                     &this_class_info, arena);
  }

  { // Super class
    const u16 constant_java_lang_object_string_i = jvm_add_constant_cstring(
        &class_file->constant_pool, "java/lang/Object", arena);

    const Jvm_constant_pool_entry super_class_info = {
        .kind = CONSTANT_POOL_KIND_CLASS_INFO,
        .v = {
            .java_class_name = constant_java_lang_object_string_i,
        }};

    class_file->super_class = jvm_constant_array_push(
        &class_file->constant_pool, &super_class_info, arena);
  }
}

static u16 codegen_add_method(Class_file *class_file, u16 access_flags,
                              u16 name, u16 descriptor,
                              Array32(Jvm_attribute) attributes, Arena *arena) {
  pg_assert(class_file != NULL);

  Jvm_method method = {
      .access_flags = access_flags,
      .attributes = attributes,
      .descriptor = descriptor,
      .name = name,
  };
  *array32_push(&class_file->methods, arena) = method;
  return (u16)array32_last_index(class_file->methods);
}

static void codegen_supplement_entrypoint_if_exists(codegen_generator *gen,
                                                    Class_file *class_file,
                                                    Arena *arena) {
  pg_assert(gen != NULL);
  pg_assert(gen->resolver->parser != NULL);
  pg_assert(class_file != NULL);

  i32 method_i = -1;
  Str source_descriptor_str = str_from_c("([Ljava/lang/String;)V");

  for (u16 i = 0; i < class_file->methods.len; i++) {
    const Jvm_method *const method = &class_file->methods.data[i];

    if ((method->access_flags & (ACCESS_FLAGS_PUBLIC | ACCESS_FLAGS_STATIC)) ==
        0)
      continue;

    // A function not named `main`, skip.
    Str name = jvm_constant_array_get_as_string(&class_file->constant_pool,
                                                method->name);
    if (!str_eq_c(name, "main"))
      continue;

    Str descriptor = jvm_constant_array_get_as_string(
        &class_file->constant_pool, method->descriptor);

    // The entrypoint already exists as the JVM expects it, nothing to do.
    if (str_eq(descriptor, source_descriptor_str))
      return;

    // A function named `main` but with a different signature e.g. `fun
    // main(x: Int){}`, skip.
    if (!str_eq_c(descriptor, "()V"))
      continue;

    // At this point, the function is `fun main(){}` and we need to add an
    // JVM entrypoint i.e. `fun main(args: Array<String){ main() }`. Record
    // its index but keep going, in case a later function is already a
    // suitable JVM entrypoint, to avoid duplication.

    pg_assert(method_i == -1);
    method_i = i;
  }
  if (method_i == -1)
    return; // Nothing to do.

  pg_assert((u16)method_i < class_file->methods.len);
  const Jvm_method *const target_method = &class_file->methods.data[method_i];

  Array32(Jvm_attribute) attributes = array32_make(Jvm_attribute, 0, 1, arena);

  // Generate code section for the new method.
  {

    Str target_descriptor_string = jvm_constant_array_get_as_string(
        &class_file->constant_pool, target_method->descriptor);
    const Jvm_constant_pool_entry target_descriptor = {
        .kind = CONSTANT_POOL_KIND_UTF8,
        .v = {.s = target_descriptor_string},
    };
    const u16 target_descriptor_i = jvm_constant_array_push(
        &class_file->constant_pool, &target_descriptor, arena);

    const Jvm_constant_pool_entry target_name_and_type = {
        .kind = CONSTANT_POOL_KIND_NAME_AND_TYPE,
        .v = {.name_and_type = {.name = target_method->name,
                                .descriptor = target_descriptor_i}},
    };
    const u16 target_name_and_type_handle = jvm_constant_array_push(
        &class_file->constant_pool, &target_name_and_type, arena);
    const Jvm_constant_pool_entry target_method_ref = {
        .kind = CONSTANT_POOL_KIND_METHOD_REF,
        .v = {.method_ref = {.class = class_file->this_class,
                             .name_and_type = target_name_and_type_handle}}};
    const u16 target_method_ref_i = jvm_constant_array_push(
        &class_file->constant_pool, &target_method_ref, arena);

    const Method target_method_type = {
        .return_type_handle =
            resolver_add_type(gen->resolver, &(Type){.kind = TYPE_UNIT}, arena),
    };

    Jvm_attribute_code code = {0};
    code.bytecode = array32_make(u8, 0, 4, arena);

    gen->code = &code;
    gen->frame =
        arena_alloc(arena, sizeof(codegen_frame), _Alignof(codegen_frame), 1);
    codegen_frame_init(gen->frame, arena);

    // Fill locals (method arguments).
    {
      Type string_type = {
          .kind = TYPE_INSTANCE,
          .this_class_name = str_from_c("java/lang/String"),
      };

      const Type_handle string_type_handle =
          resolver_add_type(gen->resolver, &string_type, arena);

      Type source_method_argument_types = {
          .kind = TYPE_ARRAY,
          .this_class_name = str_from_c("FIXME"),
          .v = {.array_type_handle = string_type_handle},
      };

      const Type_handle source_argument_types_i = resolver_add_type(
          gen->resolver, &source_method_argument_types, arena);
      const u16 source_method_arg0_string = jvm_add_constant_cstring(
          &class_file->constant_pool, "[Ljava/lang/String;", arena);

      const Jvm_constant_pool_entry source_method_arg0_class = {
          .kind = CONSTANT_POOL_KIND_CLASS_INFO,
          .v = {
              .java_class_name = source_method_arg0_string,
          }};
      const u16 source_method_arg0_class_i = jvm_constant_array_push(
          &class_file->constant_pool, &source_method_arg0_class, arena);

      const Jvm_variable arg0 = {
          .type_handle = source_argument_types_i,
          .scope_depth = gen->frame->scope_depth,
          .verification_info =
              {
                  .kind = VERIFICATION_INFO_OBJECT,
                  .extra_data = source_method_arg0_class_i,
              },
      };
      u16 logical_local_index = 0;
      u16 physical_local_index = 0;
      codegen_frame_locals_push(gen, &arg0, &logical_local_index,
                                &physical_local_index, arena);
    }

    codegen_emit_invoke_static(gen, target_method_ref_i, &target_method_type,
                               arena);
    codegen_emit_return_nothing(gen, arena);

    gen->code->max_physical_stack = gen->frame->max_physical_stack;
    gen->code->max_physical_locals = gen->frame->max_physical_locals;
    gen->code = NULL;
    gen->frame = NULL;

    Jvm_attribute attribute_code = {
        .kind = ATTRIBUTE_KIND_CODE,
        .name =
            jvm_add_constant_cstring(&class_file->constant_pool, "Code", arena),
        .v = {.code = code}};
    *array32_push(&attributes, arena) = attribute_code;
  }

  // Add new method.
  {
    const Jvm_constant_pool_entry source_descriptor = {
        .kind = CONSTANT_POOL_KIND_UTF8,
        .v = {.s = source_descriptor_str},
    };
    const u16 source_descriptor_i = jvm_constant_array_push(
        &class_file->constant_pool, &source_descriptor, arena);
    codegen_add_method(class_file, ACCESS_FLAGS_PUBLIC | ACCESS_FLAGS_STATIC,
                       target_method->name, source_descriptor_i, attributes,
                       arena);
  }
}

static void codegen_emit(Resolver *resolver, Class_file *class_file,
                         Ast_handle root_handle, Arena *arena) {
  pg_assert(resolver != NULL);
  pg_assert(class_file != NULL);
  pg_assert(arena != NULL);

  codegen_generator gen = {
      .resolver = resolver,
      .stack_map_frames = array32_make(Stack_map_frame, 0, 64, arena),
      .locals = array32_make(Codegen_scope_variable, 0, 1 << 12, arena),
  };

  codegen_emit_synthetic_class(&gen, class_file, arena);

  codegen_emit_node(&gen, class_file, root_handle, arena);

  codegen_supplement_entrypoint_if_exists(&gen, class_file, arena);
}
