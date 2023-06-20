#include "class_file.h"

int main() {
  arena_t arena = {0};
  arena_init(&arena, 1 << 26);

  cf_t class_file = {
      .magic = cf_MAGIC_NUMBER,
      .minor_version = cf_MINOR_VERSION,
      .major_version = cf_MAJOR_VERSION_6,
      .access_flags = CAF_ACC_SUPER | CAF_ACC_PUBLIC,
  };

  cf_init(&class_file, &arena);

  const u16 constant_java_lang_object_string_i =
      cf_add_constant_cstring(&class_file.constant_pool, "java/lang/Object");

  const u16 constant_void_method_descriptor_string_i =
      cf_add_constant_cstring(&class_file.constant_pool, "()V");

  const u16 constant_class_object_name_and_type_name_i =
      cf_add_constant_cstring(&class_file.constant_pool, "<init>");

  const cf_constant_t constant_class_object = {
      .kind = CIK_CLASS_INFO,
      .v = {.class_name = constant_java_lang_object_string_i}};
  const u16 constant_class_object_i =
      cf_constant_array_push(&class_file.constant_pool, &constant_class_object);
  class_file.super_class = constant_class_object_i;

  const cf_constant_t constant_class_object_name_and_type = {
      .kind = CIK_NAME_AND_TYPE,
      .v = {.name_and_type = {
                .name = constant_class_object_name_and_type_name_i,
                .type_descriptor = constant_void_method_descriptor_string_i}}};
  const u16 constant_class_object_name_and_type_i = cf_constant_array_push(
      &class_file.constant_pool, &constant_class_object_name_and_type);

  const cf_constant_t constant_object_method_ref_constructor = {
      .kind = CIK_METHOD_REF,
      .v = {.method_ref = {.class = constant_class_object_i,
                           .name_and_type =
                               constant_class_object_name_and_type_i}}};
  const u16 constant_object_method_ref_constructor_i = cf_constant_array_push(
      &class_file.constant_pool, &constant_object_method_ref_constructor);

  const u16 constant_this_class_name_i =
      cf_add_constant_cstring(&class_file.constant_pool, "PgMain");
  const cf_constant_t constant_this_class = {
      .kind = CIK_CLASS_INFO, .v = {.class_name = constant_this_class_name_i}};
  const u16 constant_this_class_i =
      cf_constant_array_push(&class_file.constant_pool, &constant_this_class);
  class_file.this_class = constant_this_class_i;

  const u16 constant_string_code_i =
      cf_add_constant_cstring(&class_file.constant_pool, "Code");

//  const u16 constant_string_line_number_table_i =
//      cf_add_constant_cstring(&class_file.constant_pool, "LineNumberTable");

  const u16 constant_string_main_i =
      cf_add_constant_cstring(&class_file.constant_pool, "main");

  const u16 constant_string_main_type_descriptor_i = cf_add_constant_cstring(
      &class_file.constant_pool, "([Ljava/lang/String;)V");

  const u16 constant_string_source_file_i =
      cf_add_constant_cstring(&class_file.constant_pool, "SourceFile");

  const u16 constant_string_file_i =
      cf_add_constant_cstring(&class_file.constant_pool, "PgMain.java");

  const u16 constant_string_java_lang_system_class_i =
      cf_add_constant_cstring(&class_file.constant_pool, "java/lang/System");
  const cf_constant_t constant_java_lang_system_class_info = {
      .kind = CIK_CLASS_INFO,
      .v = {.class_name = constant_string_java_lang_system_class_i}};
  const u16 constant_java_lang_system_class_info_i = cf_constant_array_push(
      &class_file.constant_pool, &constant_java_lang_system_class_info);

  const u16 constant_string_out_i =
      cf_add_constant_cstring(&class_file.constant_pool, "out");

  const u16 constant_string_java_io_printstream_i =
      cf_add_constant_cstring(&class_file.constant_pool, "java/io/PrintStream");

  const cf_constant_t constant_string_java_io_printstream_class = {
      .kind = CIK_CLASS_INFO,
      .v = {.class_name = constant_string_java_io_printstream_i}};
  const u16 constant_string_java_io_printstream_class_i =
      cf_constant_array_push(&class_file.constant_pool,
                             &constant_string_java_io_printstream_class);

  const u16 constant_string_java_io_printstream_descriptor_i =
      cf_add_constant_cstring(&class_file.constant_pool,
                              "Ljava/io/PrintStream;");

  const cf_constant_t constant_out_name_and_type = {
      .kind = CIK_NAME_AND_TYPE,
      .v = {.name_and_type = {
                .name = constant_string_out_i,
                .type_descriptor =
                    constant_string_java_io_printstream_descriptor_i}}};
  const u16 constant_out_name_and_type_i = cf_constant_array_push(
      &class_file.constant_pool, &constant_out_name_and_type);

  const cf_constant_t constant_out_fieldref = {
      .kind = CIK_FIELD_REF,
      .v = {.field_ref = {.name = constant_java_lang_system_class_info_i,
                          .type_descriptor = constant_out_name_and_type_i}}};
  const u16 constant_out_fieldref_i =
      cf_constant_array_push(&class_file.constant_pool, &constant_out_fieldref);

  const cf_attribute_t source_file_attribute = {
      .kind = CAK_SOURCE_FILE,
      .name = constant_string_source_file_i,
      .v = {.source_file = {.source_file = constant_string_file_i}}};
  cf_attribute_array_push(&class_file.attributes, &source_file_attribute);

  const u16 constant_string_hello_i =
      cf_add_constant_cstring(&class_file.constant_pool, "Hello, world!");
  const u16 constant_jstring_hello_i = cf_add_constant_jstring(
      &class_file.constant_pool, constant_string_hello_i);

  const u16 constant_string_println_i =
      cf_add_constant_cstring(&class_file.constant_pool, "println");
  const u16 constant_println_method_descriptor_string_i =
      cf_add_constant_cstring(&class_file.constant_pool,
                              "(Ljava/lang/String;)V");
  const cf_constant_t constant_println_name_and_type = {
      .kind = CIK_NAME_AND_TYPE,
      .v = {
          .name_and_type = {.name = constant_string_println_i,
                            .type_descriptor =
                                constant_println_method_descriptor_string_i}}};
  const u16 constant_println_name_and_type_i = cf_constant_array_push(
      &class_file.constant_pool, &constant_println_name_and_type);
  const cf_constant_t constant_println_method_ref = {
      .kind = CIK_METHOD_REF,
      .v = {.method_ref = {.class = constant_string_java_io_printstream_class_i,
                           .name_and_type = constant_println_name_and_type_i}}};
  const u16 constant_println_method_ref_i = cf_constant_array_push(
      &class_file.constant_pool, &constant_println_method_ref);

  // This's class Constructor

  {
    cf_attribute_code_t constructor_code = {.max_stack = 1, .max_locals = 1};
    cf_attribute_code_init(&constructor_code, &arena);
    cf_code_array_push_u8(&constructor_code.code, CFO_ALOAD_0);
    cf_code_array_push_u8(&constructor_code.code, CFO_INVOKE_SPECIAL);
    cf_code_array_push_u16(&constructor_code.code,
                           constant_object_method_ref_constructor_i);
    cf_code_array_push_u8(&constructor_code.code, CFO_RETURN);

    cf_method_t constructor = {
        .access_flags = CAF_ACC_PUBLIC,
        .name = constant_class_object_name_and_type_name_i,
        .descriptor = constant_void_method_descriptor_string_i,
    };
    cf_method_init(&constructor, &arena);
    cf_attribute_t constructor_attribute_code = {
        .kind = CAK_CODE,
        .name = constant_string_code_i,
        .v = {.code = constructor_code}};
    cf_attribute_array_push(&constructor.attributes,
                            &constructor_attribute_code);

    cf_method_array_push(&class_file.methods, &constructor);
  }
  // This's class main
  {
    cf_attribute_code_t main_code = {.max_stack = 2, .max_locals = 1};
    cf_attribute_code_init(&main_code, &arena);

    cf_code_array_push_u8(&main_code.code, CFO_GET_STATIC);
    cf_code_array_push_u16(&main_code.code, constant_out_fieldref_i);

    cf_code_array_push_u8(&main_code.code, CFO_LDC);
    cf_code_array_push_u8(&main_code.code, constant_jstring_hello_i);

    cf_code_array_push_u8(&main_code.code, CFO_INVOKE_VIRTUAL);
    cf_code_array_push_u16(&main_code.code, constant_println_method_ref_i);

    cf_code_array_push_u8(&main_code.code, CFO_RETURN);

    cf_method_t main = {
        .name = constant_string_main_i,
        .access_flags = CAF_ACC_PUBLIC | CAF_ACC_STATIC,
        .descriptor = constant_string_main_type_descriptor_i,
    };
    cf_method_init(&main, &arena);
    cf_attribute_t main_attribute_code = {.kind = CAK_CODE,
                                          .name = constant_string_code_i,
                                          .v = {.code = main_code}};
    cf_attribute_array_push(&main.attributes, &main_attribute_code);

    cf_method_array_push(&class_file.methods, &main);
  }

  FILE *file = fopen("PgMain.class", "w");
  assert(file != NULL);
  cf_write(&class_file, file);
}
