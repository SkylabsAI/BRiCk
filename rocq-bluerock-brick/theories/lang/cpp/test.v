Require Import bedrock.prelude.list.
Require Import bedrock.lang.cpp.syntax.
Require bedrock.lang.cpp.foo_cpp.

Definition type_names :=
  NM.elements foo_cpp.module.(types).
Definition symbol_names :=
  NM.elements foo_cpp.module.(symbols).

Arguments Atype {_ _ _} _%_cpp_type.

Optimize Heap.
Instructions
Definition s : list name :=
["__gnu_cxx::__alloc_traits<std::allocator<int>, int>::rebind<int>";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::rebind<char>";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::rebind<wchar_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::rebind<char16_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::rebind<char32_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::rebind<std::_List_node<std::vector<int, std::allocator<int>>>>";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::rebind<std::vector<int, std::allocator<int>>>";
        "__gnu_cxx::_Char_types<char>"; "__gnu_cxx::_Char_types<wchar_t>";
        "__gnu_cxx::__add_unsigned<signed char>"; "__gnu_cxx::__add_unsigned<short>";
        "__gnu_cxx::__add_unsigned<int>"; "__gnu_cxx::__add_unsigned<long>";
        "__gnu_cxx::__add_unsigned<long long>"; "__gnu_cxx::__add_unsigned<char>";
        "__gnu_cxx::__add_unsigned<wchar_t>"; "__gnu_cxx::__add_unsigned<bool>";
        "__gnu_cxx::__aligned_membuf<std::vector<int, std::allocator<int>>>";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>"; "__gnu_cxx::__alloc_traits<std::allocator<char>, char>";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>"]%cpp_name.

Import foo_cpp.


Optimize Heap.
Instructions
Definition t : list name :=
["__gnu_cxx::__alloc_traits<std::allocator<int>, int>::rebind<int>";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::rebind<char>";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::rebind<wchar_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::rebind<char16_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::rebind<char32_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::rebind<std::_List_node<std::vector<int, std::allocator<int>>>>";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::rebind<std::vector<int, std::allocator<int>>>";
        "__gnu_cxx::_Char_types<char>"; "__gnu_cxx::_Char_types<wchar_t>";
        "__gnu_cxx::__add_unsigned<signed char>"; "__gnu_cxx::__add_unsigned<short>";
        "__gnu_cxx::__add_unsigned<int>"; "__gnu_cxx::__add_unsigned<long>";
        "__gnu_cxx::__add_unsigned<long long>"; "__gnu_cxx::__add_unsigned<char>";
        "__gnu_cxx::__add_unsigned<wchar_t>"; "__gnu_cxx::__add_unsigned<bool>";
        "__gnu_cxx::__aligned_membuf<std::vector<int, std::allocator<int>>>";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>"; "__gnu_cxx::__alloc_traits<std::allocator<char>, char>";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>"]%cpp_name.



(* MORE NAMES
        Ninst "std::__and_"
          [Apack
             [Atype "std::is_convertible<const char32_t* const&, std::basic_string_view<char32_t, std::char_traits<char32_t>>>";
              Atype
                "std::__not_<std::is_convertible<const char32_t* const*, const std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>*>>";
              Atype "std::__not_<std::is_convertible<const char32_t* const&, const char32_t*>>"]];
        Ninst "std::__and_"
          [Apack
             [Atype "std::is_convertible<const int&, std::basic_string_view<char, std::char_traits<char>>>";
              Atype
                "std::__not_<std::is_convertible<const int*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>>";
              Atype "std::__not_<std::is_convertible<const int&, const char*>>"]];
        Ninst "std::__and_"
          [Apack
             [Atype "std::is_convertible<const char&, std::basic_string_view<char, std::char_traits<char>>>";
              Atype
                "std::__not_<std::is_convertible<const char*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>>";
              Atype "std::__not_<std::is_convertible<const char&, const char*>>"]];
        Ninst "std::__and_"
          [Apack
             [Atype
                "std::is_convertible<const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&, std::basic_string_view<char, std::char_traits<char>>>";
              Atype
                "std::__not_<std::is_convertible<const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>>";
              Atype
                "std::__not_<std::is_convertible<const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&, const char*>>"]];
        Ninst "std::__and_" [Apack [Atype "std::is_same<int*, int*>"; Atype "std::__not_<std::is_pointer<int*>>"]];
        Ninst "std::__and_"
          [Apack
             [Atype
                "std::is_same<std::_List_node<std::vector<int, std::allocator<int>>>*, std::_List_node<std::vector<int, std::allocator<int>>>*>"]];
        Ninst "std::__and_"
          [Apack
             [Atype
                "std::is_same<std::_List_node<std::vector<int, std::allocator<int>>>*, std::vector<int, std::allocator<int>>*>";
              Atype "std::__not_<std::is_pointer<std::vector<int, std::allocator<int>>*>>"]];
        "std::__are_same<float, float>"; "std::__are_same<float, double>"; "std::__are_same<double, float>";
        "std::__are_same<double, double>"; "std::__are_same<long double, float>";
        "std::__are_same<long double, double>"; "std::__byte_operand<signed char>";
        "std::__byte_operand<unsigned char>"; "std::__byte_operand<short>";
        "std::__byte_operand<unsigned short>"; "std::__byte_operand<int>"; "std::__byte_operand<unsigned int>";
        "std::__byte_operand<long>"; "std::__byte_operand<unsigned long>"; "std::__byte_operand<long long>";
        "std::__byte_operand<unsigned long long>"; "std::__byte_operand<int128_t>";
        "std::__byte_operand<uint128_t>"; "std::__byte_operand<char>"; "std::__byte_operand<wchar_t>";
        "std::__byte_operand<char16_t>"; "std::__byte_operand<char32_t>"; "std::__byte_operand<bool>";
        Ninst "std::__combine_tuples" [Apack []]; Ninst "std::__conditional" [Avalue (Eint 0 "bool")];
        Ninst "std::__copy_move" [Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool"); Atype "std::random_access_iterator_tag"];
        Ninst "std::__copy_move" [Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool"); Atype "std::random_access_iterator_tag"];
        Ninst "std::__copy_move" [Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool"); Atype "std::random_access_iterator_tag"];
        Ninst "std::__copy_move_backward"
          [Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool"); Atype "std::random_access_iterator_tag"];
        Ninst "std::__copy_move_backward"
          [Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool"); Atype "std::random_access_iterator_tag"];
        "std::__ctype_abstract_base<wchar_t>";
        Ninst "std::__cv_selector" [Atype "short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__cv_selector" [Atype "unsigned short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__cv_selector" [Atype "int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__cv_selector" [Atype "unsigned int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__equal" [Avalue (Eint 1 "bool")]; "std::__hash_base<unsigned long, signed char>";
        "std::__hash_base<unsigned long, unsigned char>"; "std::__hash_base<unsigned long, short>";
        "std::__hash_base<unsigned long, unsigned short>"; "std::__hash_base<unsigned long, int>";
        "std::__hash_base<unsigned long, unsigned int>"; "std::__hash_base<unsigned long, long>";
        "std::__hash_base<unsigned long, unsigned long>"; "std::__hash_base<unsigned long, long long>";
        "std::__hash_base<unsigned long, unsigned long long>"; "std::__hash_base<unsigned long, int128_t>";
        "std::__hash_base<unsigned long, uint128_t>"; "std::__hash_base<unsigned long, char>";
        "std::__hash_base<unsigned long, wchar_t>"; "std::__hash_base<unsigned long, char16_t>";
        "std::__hash_base<unsigned long, char32_t>";
        "std::__hash_base<unsigned long, std::basic_string_view<char, std::char_traits<char>>>";
        "std::__hash_base<unsigned long, std::basic_string_view<wchar_t, std::char_traits<wchar_t>>>";
        "std::__hash_base<unsigned long, std::basic_string_view<char16_t, std::char_traits<char16_t>>>";
        "std::__hash_base<unsigned long, std::basic_string_view<char32_t, std::char_traits<char32_t>>>";
        "std::__hash_base<unsigned long, std::error_code>"; "std::__hash_base<unsigned long, std::error_condition>";
        "std::__hash_base<unsigned long, bool>"; "std::__hash_base<unsigned long, float>";
        "std::__hash_base<unsigned long, double>"; "std::__hash_base<unsigned long, long double>";
        "std::__hash_base<unsigned long, nullptr_t>"; "std::__is_allocator<std::allocator<char>, void>";
        "std::__is_allocator<std::allocator<wchar_t>, void>"; "std::__is_allocator<std::allocator<char16_t>, void>";
        "std::__is_allocator<std::allocator<char32_t>, void>"; "std::__is_array_unknown_bounds<int*>";
        "std::__is_array_unknown_bounds<const int*>"; "std::__is_array_unknown_bounds<int>";
        "std::__is_array_unknown_bounds<std::allocator<int>>"; "std::__is_array_unknown_bounds<std::allocator<char>>";
        "std::__is_array_unknown_bounds<std::allocator<wchar_t>>";
        "std::__is_array_unknown_bounds<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
        "std::__is_array_unknown_bounds<std::vector<int, std::allocator<int>>>";
        "std::__is_bitwise_relocatable<int, void>"; "std::__is_byte<signed char>";
        "std::__is_byte<unsigned char>"; "std::__is_byte<char>"; "std::__is_byte<enum std::byte>";
        "std::__is_char<char>"; "std::__is_char<wchar_t>";
        Ninst "std::__is_destructible_safe" [Atype "int"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")];
        "std::__is_fast_hash<std::hash<std::basic_string_view<char, std::char_traits<char>>>>";
        "std::__is_fast_hash<std::hash<std::basic_string_view<wchar_t, std::char_traits<wchar_t>>>>";
        "std::__is_fast_hash<std::hash<std::basic_string_view<char16_t, std::char_traits<char16_t>>>>";
        "std::__is_fast_hash<std::hash<std::basic_string_view<char32_t, std::char_traits<char32_t>>>>";
        "std::__is_fast_hash<std::hash<std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>>";
        "std::__is_fast_hash<std::hash<std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>>";
        "std::__is_fast_hash<std::hash<std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>>";
        "std::__is_fast_hash<std::hash<std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>>";
        "std::__is_fast_hash<std::hash<long double>>"; "std::__is_floating<float>";
        "std::__is_floating<double>"; "std::__is_floating<long double>";
        "std::__is_floating_point_helper<std::vector<int, std::allocator<int>>>";
        "std::__is_floating_point_helper<float>"; "std::__is_floating_point_helper<double>";
        "std::__is_floating_point_helper<long double>"; "std::__is_floating_point_helper<float128>";
        "std::__is_integer<signed char>"; "std::__is_integer<unsigned char>"; "std::__is_integer<short>";
        "std::__is_integer<unsigned short>"; "std::__is_integer<int>"; "std::__is_integer<unsigned int>";
        "std::__is_integer<long>"; "std::__is_integer<unsigned long>"; "std::__is_integer<long long>";
        "std::__is_integer<unsigned long long>"; "std::__is_integer<int128_t>"; "std::__is_integer<uint128_t>";
        "std::__is_integer<char>"; "std::__is_integer<wchar_t>"; "std::__is_integer<char16_t>";
        "std::__is_integer<char32_t>"; "std::__is_integer<bool>"; "std::__is_integer<float>";
        "std::__is_integer<double>"; "std::__is_integer<long double>";
        "std::__is_integral_helper<signed char>"; "std::__is_integral_helper<unsigned char>";
        "std::__is_integral_helper<short>"; "std::__is_integral_helper<unsigned short>";
        "std::__is_integral_helper<int>"; "std::__is_integral_helper<unsigned int>";
        "std::__is_integral_helper<long>"; "std::__is_integral_helper<unsigned long>";
        "std::__is_integral_helper<long long>"; "std::__is_integral_helper<unsigned long long>";
        "std::__is_integral_helper<int128_t>"; "std::__is_integral_helper<uint128_t>";
        "std::__is_integral_helper<char>"; "std::__is_integral_helper<wchar_t>";
        "std::__is_integral_helper<char16_t>"; "std::__is_integral_helper<char32_t>";
        "std::__is_integral_helper<std::vector<int, std::allocator<int>>>"; "std::__is_integral_helper<bool>";
        Ninst "std::__is_memcmp_ordered_with" [Atype "enum std::byte"; Atype "enum std::byte"; Avalue (Eint 1 "bool")];
        "std::__is_move_insertable<std::allocator<int>>";
        "std::__is_move_iterator<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>>";
        "std::__is_nonvolatile_trivially_copyable<int>";
        "std::__is_nt_destructible_impl<std::vector<int, std::allocator<int>>>";
        Ninst "std::__is_nt_destructible_safe"
          [Atype "std::vector<int, std::allocator<int>>"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        "std::__is_pointer_helper<int*>"; "std::__is_pointer_helper<std::vector<int, std::allocator<int>>>";
        "std::__is_void<void>";
        "std::__iterator_traits<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, void>";
        "std::__iterator_traits<std::_Bit_const_iterator, void>"; "std::__iterator_traits<std::_Bit_iterator, void>";
        "std::__lc_rai<std::random_access_iterator_tag, std::random_access_iterator_tag>";
        Ninst "std::__lexicographical_compare" [Avalue (Eint 1 "bool")]; Ninst "std::__make_1st_indices" [Apack []];
        "std::__make_signed<unsigned char>"; "std::__make_signed<unsigned short>";
        "std::__make_signed<unsigned int>"; "std::__make_signed<unsigned long>";
        "std::__make_signed<unsigned long long>"; "std::__make_signed<uint128_t>"; "std::__make_signed<char>";
        "std::__make_signed<wchar_t>"; "std::__make_signed<char16_t>"; "std::__make_signed<char32_t>";
        Ninst "std::__make_signed_selector" [Atype "unsigned short"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__make_signed_selector" [Atype "unsigned int"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__make_signed_selector" [Atype "wchar_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")];
        Ninst "std::__make_signed_selector" [Atype "char16_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")];
        Ninst "std::__make_signed_selector" [Atype "char32_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")];
        "std::__make_unsigned<signed char>"; "std::__make_unsigned<short>"; "std::__make_unsigned<int>";
        "std::__make_unsigned<long>"; "std::__make_unsigned<long long>"; "std::__make_unsigned<int128_t>";
        "std::__make_unsigned<char>"; "std::__make_unsigned<wchar_t>"; "std::__make_unsigned<char16_t>";
        "std::__make_unsigned<char32_t>";
        Ninst "std::__make_unsigned_selector" [Atype "wchar_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")];
        Ninst "std::__make_unsigned_selector" [Atype "wchar_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__make_unsigned_selector" [Atype "char16_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")];
        Ninst "std::__make_unsigned_selector" [Atype "char16_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__make_unsigned_selector" [Atype "char32_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")];
        Ninst "std::__make_unsigned_selector" [Atype "char32_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__match_cv_qualifiers"
          [Atype "unsigned short"; Atype "short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__match_cv_qualifiers"
          [Atype "unsigned int"; Atype "int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__match_cv_qualifiers"
          [Atype "wchar_t"; Atype "unsigned int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__match_cv_qualifiers"
          [Atype "char16_t"; Atype "unsigned short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        Ninst "std::__match_cv_qualifiers"
          [Atype "char32_t"; Atype "unsigned int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")];
        "std::__memcpyable<int*, const int*>"; "std::__new_allocator<int>"; "std::__new_allocator<char>";
        "std::__new_allocator<wchar_t>"; "std::__new_allocator<char16_t>"; "std::__new_allocator<char32_t>";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>";
        "std::__not_<std::is_convertible<char* const*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>>";
        "std::__not_<std::is_convertible<const char* const*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>>";
        "std::__not_<std::is_convertible<const char* const*, const std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>*>>";
        "std::__not_<std::is_convertible<const wchar_t* const*, const std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>*>>";
        "std::__not_<std::is_convertible<const char16_t* const*, const std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>*>>";
        "std::__not_<std::is_convertible<const char32_t* const*, const std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>*>>";
        "std::__not_<std::is_convertible<const int*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>>";
        "std::__not_<std::is_convertible<const char*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>>";
        "std::__not_<std::is_convertible<const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>>";
        "std::__not_<std::is_convertible<char* const&, const char*>>";
        "std::__not_<std::is_convertible<const char* const&, const char*>>";
        "std::__not_<std::is_convertible<const char* const&, const wchar_t*>>";
        "std::__not_<std::is_convertible<const wchar_t* const&, const wchar_t*>>";
        "std::__not_<std::is_convertible<const char16_t* const&, const char16_t*>>";
        "std::__not_<std::is_convertible<const char32_t* const&, const char32_t*>>";
        "std::__not_<std::is_convertible<const int&, const char*>>";
        "std::__not_<std::is_convertible<const char&, const char*>>";
        "std::__not_<std::is_convertible<const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&, const char*>>";
        "std::__not_<std::is_pointer<int*>>"; "std::__not_<std::is_pointer<std::vector<int, std::allocator<int>>*>>";
        "std::__not_<std::is_same<std::basic_ostream<char, std::char_traits<char>>&, std::ios_base>>";
        "std::__numpunct_cache<char>"; "std::__numpunct_cache<wchar_t>";
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_arithmetic<int>"; Atype "std::is_enum<int>"; Atype "std::is_pointer<int>";
              Atype "std::is_member_pointer<int>"; Atype "std::is_null_pointer<int>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_arithmetic<std::vector<int, std::allocator<int>>>";
              Atype "std::is_enum<std::vector<int, std::allocator<int>>>";
              Atype "std::is_pointer<std::vector<int, std::allocator<int>>>";
              Atype "std::is_member_pointer<std::vector<int, std::allocator<int>>>";
              Atype "std::is_null_pointer<std::vector<int, std::allocator<int>>>"]];
        Ninst "std::__or_" [Apack [Atype "std::is_integral<int>"; Atype "std::is_floating_point<int>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_integral<std::vector<int, std::allocator<int>>>";
              Atype "std::is_floating_point<std::vector<int, std::allocator<int>>>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<int*>"; Atype "std::is_function<int*>"; Atype "std::is_void<int*>";
              Atype "std::__is_array_unknown_bounds<int*>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<const int*>"; Atype "std::is_function<const int*>";
              Atype "std::is_void<const int*>"; Atype "std::__is_array_unknown_bounds<const int*>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<int>"; Atype "std::is_function<int>"; Atype "std::is_void<int>";
              Atype "std::__is_array_unknown_bounds<int>"]];
        Ninst "std::__or_" [Apack [Atype "std::is_reference<int>"; Atype "std::is_scalar<int>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<std::allocator<int>>"; Atype "std::is_function<std::allocator<int>>";
              Atype "std::is_void<std::allocator<int>>"; Atype "std::__is_array_unknown_bounds<std::allocator<int>>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<std::allocator<char>>"; Atype "std::is_function<std::allocator<char>>";
              Atype "std::is_void<std::allocator<char>>"; Atype "std::__is_array_unknown_bounds<std::allocator<char>>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<std::allocator<wchar_t>>"; Atype "std::is_function<std::allocator<wchar_t>>";
              Atype "std::is_void<std::allocator<wchar_t>>";
              Atype "std::__is_array_unknown_bounds<std::allocator<wchar_t>>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
              Atype "std::is_function<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
              Atype "std::is_void<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
              Atype "std::__is_array_unknown_bounds<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<std::vector<int, std::allocator<int>>>";
              Atype "std::is_function<std::vector<int, std::allocator<int>>>";
              Atype "std::is_void<std::vector<int, std::allocator<int>>>";
              Atype "std::__is_array_unknown_bounds<std::vector<int, std::allocator<int>>>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_reference<std::vector<int, std::allocator<int>>>";
              Atype "std::is_scalar<std::vector<int, std::allocator<int>>>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_void<int>"; Atype "std::__is_array_unknown_bounds<int>";
              Atype "std::is_function<int>"]];
        Ninst "std::__or_"
          [Apack
             [Atype "std::is_void<std::vector<int, std::allocator<int>>>";
              Atype "std::__is_array_unknown_bounds<std::vector<int, std::allocator<int>>>";
              Atype "std::is_function<std::vector<int, std::allocator<int>>>"]];
        "std::__pair_get<0ul>"; "std::__pair_get<1ul>";
        Ninst "std::__ptr_traits_ptr_to" [Atype "int*"; Atype "int"; Avalue (Eint 0 "bool")];
        Ninst "std::__ptr_traits_ptr_to" [Atype "char*"; Atype "char"; Avalue (Eint 0 "bool")];
        Ninst "std::__ptr_traits_ptr_to" [Atype "wchar_t*"; Atype "wchar_t"; Avalue (Eint 0 "bool")];
        Ninst "std::__ptr_traits_ptr_to" [Atype "char16_t*"; Atype "char16_t"; Avalue (Eint 0 "bool")];
        Ninst "std::__ptr_traits_ptr_to" [Atype "char32_t*"; Atype "char32_t"; Avalue (Eint 0 "bool")];
        Ninst "std::__ptr_traits_ptr_to" [Atype "const char*"; Atype "const char"; Avalue (Eint 0 "bool")];
        Ninst "std::__ptr_traits_ptr_to" [Atype "const wchar_t*"; Atype "const wchar_t"; Avalue (Eint 0 "bool")];
        Ninst "std::__ptr_traits_ptr_to" [Atype "const char16_t*"; Atype "const char16_t"; Avalue (Eint 0 "bool")];
        Ninst "std::__ptr_traits_ptr_to" [Atype "const char32_t*"; Atype "const char32_t"; Avalue (Eint 0 "bool")];
        Ninst "std::__truth_type" [Avalue (Eint 1 "bool")]; "std::__type_identity<int*>";
        "std::__type_identity<const int*>"; "std::__type_identity<int>";
        "std::__type_identity<std::allocator<int>>"; "std::__type_identity<std::allocator<char>>";
        "std::__type_identity<std::allocator<wchar_t>>";
        "std::__type_identity<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
        "std::__type_identity<std::allocator<std::vector<int, std::allocator<int>>>>";
        "std::__type_identity<std::vector<int, std::allocator<int>>>";
        Ninst "std::__uninitialized_copy" [Avalue (Eint 1 "bool")]; Ninst "std::__uninitialized_default_1" [Avalue (Eint 1 "bool")];
        Ninst "std::__uninitialized_default_n_1" [Avalue (Eint 1 "bool")];
        Ninst "std::__uninitialized_default_novalue_1" [Avalue (Eint 1 "bool")];
        Ninst "std::__uninitialized_default_novalue_n_1" [Avalue (Eint 1 "bool")];
        Ninst "std::__uninitialized_fill" [Avalue (Eint 1 "bool")]; Ninst "std::__uninitialized_fill_n" [Avalue (Eint 1 "bool")];
        "std::add_pointer<std::basic_ostream<char, std::char_traits<char>>&>"; "std::allocator<int>";
        "std::allocator<char>"; "std::allocator<wchar_t>"; "std::allocator<char16_t>";
        "std::allocator<char32_t>"; "std::allocator<void>";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>";
        "std::allocator<std::vector<int, std::allocator<int>>>"; "std::allocator_traits<std::allocator<int>>";
        "std::allocator_traits<std::allocator<char>>"; "std::allocator_traits<std::allocator<wchar_t>>";
        "std::allocator_traits<std::allocator<char16_t>>"; "std::allocator_traits<std::allocator<char32_t>>";
        "std::allocator_traits<std::allocator<void>>";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>";
        "std::basic_filebuf<char, std::char_traits<char>>"; "std::basic_filebuf<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_fstream<char, std::char_traits<char>>"; "std::basic_fstream<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_ifstream<char, std::char_traits<char>>"; "std::basic_ifstream<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_ios<char, std::char_traits<char>>"; "std::basic_ios<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_iostream<char, std::char_traits<char>>"; "std::basic_iostream<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_istream<char, std::char_traits<char>>"; "std::basic_istream<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_ofstream<char, std::char_traits<char>>"; "std::basic_ofstream<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_ostream<char, std::char_traits<char>>"; "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_streambuf<char, std::char_traits<char>>";
        "std::basic_streambuf<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_string_view<char, std::char_traits<char>>";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>";
        "std::binary_function<const volatile void*, const volatile void*, bool>";
        "std::binary_function<const std::_V2::error_category*, const std::_V2::error_category*, bool>";
        "std::bit_and<void>"; "std::bit_not<void>"; "std::bit_or<void>"; "std::bit_xor<void>";
        "std::char_traits<char>"; "std::char_traits<wchar_t>"; "std::char_traits<char16_t>";
        "std::char_traits<char32_t>"; "std::codecvt<char, char, __mbstate_t>";
        "std::codecvt<wchar_t, char, __mbstate_t>"; "std::codecvt<char16_t, char, __mbstate_t>";
        "std::codecvt<char32_t, char, __mbstate_t>"; Ninst "std::common_type" [Apack []]; Ninst "std::conjunction" [Apack []];
        "std::ctype<char>"; "std::ctype<wchar_t>"; "std::ctype_byname<char>";
        "std::ctype_byname<wchar_t>"; Ninst "std::disjunction" [Apack []]; "std::divides<void>";
        Ninst "std::enable_if"
          [Avalue (Eint 0 "bool"); Atype "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&"];
        Ninst "std::enable_if" [Avalue (Eint 0 "bool"); Atype "void"];
        Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "int*"];
        Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "void"];
        Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "std::allocator<char>"];
        Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "std::allocator<wchar_t>"];
        Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "std::allocator<char16_t>"];
        Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "std::allocator<char32_t>"]; "std::equal_to<void>";
        "std::fpos<__mbstate_t>"; "std::greater<const volatile void*>"; "std::greater<void>";
        "std::greater_equal<const volatile void*>"; "std::greater_equal<void>"; "std::hash<signed char>";
        "std::hash<unsigned char>"; "std::hash<short>"; "std::hash<unsigned short>"; "std::hash<int>";
        "std::hash<unsigned int>"; "std::hash<long>"; "std::hash<unsigned long>";
        "std::hash<long long>"; "std::hash<unsigned long long>"; "std::hash<int128_t>";
        "std::hash<uint128_t>"; "std::hash<char>"; "std::hash<wchar_t>"; "std::hash<char16_t>";
        "std::hash<char32_t>"; "std::hash<std::basic_string_view<char, std::char_traits<char>>>";
        "std::hash<std::basic_string_view<wchar_t, std::char_traits<wchar_t>>>";
        "std::hash<std::basic_string_view<char16_t, std::char_traits<char16_t>>>";
        "std::hash<std::basic_string_view<char32_t, std::char_traits<char32_t>>>";
        "std::hash<std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>";
        "std::hash<std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>";
        "std::hash<std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>";
        "std::hash<std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>";
        "std::hash<std::error_code>"; "std::hash<std::error_condition>"; "std::hash<bool>";
        "std::hash<float>"; "std::hash<double>"; "std::hash<long double>"; "std::hash<nullptr_t>";
        "std::initializer_list<int>"; "std::initializer_list<char>"; "std::initializer_list<wchar_t>";
        "std::initializer_list<char16_t>"; "std::initializer_list<char32_t>";
        "std::initializer_list<std::vector<int, std::allocator<int>>>"; "std::initializer_list<bool>";
        "std::integral_constant<unsigned long, 0ul>"; "std::integral_constant<unsigned long, 2ul>";
        Ninst "std::integral_constant" [Atype "bool"; Avalue (Eint 0 "bool")];
        Ninst "std::integral_constant" [Atype "bool"; Avalue (Eint 1 "bool")]; "std::is_arithmetic<int>";
        "std::is_arithmetic<std::vector<int, std::allocator<int>>>";
        "std::is_class<std::basic_ostream<char, std::char_traits<char>>&>"; "std::is_const<unsigned short>";
        "std::is_const<unsigned int>"; "std::is_const<wchar_t>"; "std::is_const<char16_t>";
        "std::is_const<char32_t>"; Ninst "std::is_constructible" [Atype "int"; Apack [Atype "const int&"]];
        "std::is_convertible<std::basic_ostream<char, std::char_traits<char>>*, std::ios_base*>";
        "std::is_convertible<char* const*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>";
        "std::is_convertible<const char* const*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>";
        "std::is_convertible<const char* const*, const std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>*>";
        "std::is_convertible<const wchar_t* const*, const std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>*>";
        "std::is_convertible<const char16_t* const*, const std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>*>";
        "std::is_convertible<const char32_t* const*, const std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>*>";
        "std::is_convertible<const int*, const int*>";
        "std::is_convertible<const int*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>";
        "std::is_convertible<const char*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>";
        "std::is_convertible<const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>*>";
        "std::is_convertible<char* const&, const char*>";
        "std::is_convertible<char* const&, std::basic_string_view<char, std::char_traits<char>>>";
        "std::is_convertible<const char* const&, const char*>";
        "std::is_convertible<const char* const&, const wchar_t*>";
        "std::is_convertible<const char* const&, std::basic_string_view<char, std::char_traits<char>>>";
        "std::is_convertible<const char* const&, std::basic_string_view<wchar_t, std::char_traits<wchar_t>>>";
        "std::is_convertible<const wchar_t* const&, const wchar_t*>";
        "std::is_convertible<const wchar_t* const&, std::basic_string_view<wchar_t, std::char_traits<wchar_t>>>";
        "std::is_convertible<const char16_t* const&, const char16_t*>";
        "std::is_convertible<const char16_t* const&, std::basic_string_view<char16_t, std::char_traits<char16_t>>>";
        "std::is_convertible<const char32_t* const&, const char32_t*>";
        "std::is_convertible<const char32_t* const&, std::basic_string_view<char32_t, std::char_traits<char32_t>>>";
        "std::is_convertible<const int&, const char*>";
        "std::is_convertible<const int&, std::basic_string_view<char, std::char_traits<char>>>";
        "std::is_convertible<const char&, const char*>";
        "std::is_convertible<const char&, std::basic_string_view<char, std::char_traits<char>>>";
        "std::is_convertible<const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&, const char*>";
        "std::is_convertible<const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&, std::basic_string_view<char, std::char_traits<char>>>";
        "std::is_convertible<std::random_access_iterator_tag, std::input_iterator_tag>"; "std::is_destructible<int>";
        "std::is_enum<int>"; "std::is_enum<std::vector<int, std::allocator<int>>>";
        "std::is_error_code_enum<int>";
        "std::is_error_code_enum<__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>>";
        "std::is_error_code_enum<std::_Bit_iterator>"; "std::is_error_code_enum<std::_Bit_iterator_base>";
        "std::is_error_code_enum<std::error_code>"; "std::is_error_code_enum<std::error_condition>";
        "std::is_error_code_enum<std::_V2::error_category>"; "std::is_error_code_enum<enum std::io_errc>";
        "std::is_error_condition_enum<__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>>";
        "std::is_error_condition_enum<std::_Bit_iterator>"; "std::is_error_condition_enum<std::_Bit_iterator_base>";
        "std::is_error_condition_enum<std::error_code>"; "std::is_error_condition_enum<std::_V2::error_category>";
        "std::is_error_condition_enum<enum std::errc>"; "std::is_floating_point<int>";
        "std::is_floating_point<std::vector<int, std::allocator<int>>>"; "std::is_function<int*>";
        "std::is_function<const int*>"; "std::is_function<int>"; "std::is_function<std::allocator<int>>";
        "std::is_function<std::allocator<char>>"; "std::is_function<std::allocator<wchar_t>>";
        "std::is_function<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
        "std::is_function<std::vector<int, std::allocator<int>>>"; "std::is_integral<unsigned short>";
        "std::is_integral<int>"; "std::is_integral<unsigned int>"; "std::is_integral<wchar_t>";
        "std::is_integral<char16_t>"; "std::is_integral<char32_t>";
        "std::is_integral<std::vector<int, std::allocator<int>>>"; "std::is_member_pointer<int>";
        "std::is_member_pointer<std::vector<int, std::allocator<int>>>"; "std::is_move_constructible<int>";
        Ninst "std::is_nothrow_constructible" [Atype "int"; Apack [Atype "int"]];
        Ninst "std::is_nothrow_constructible"
          [Atype "std::vector<int, std::allocator<int>>"; Apack [Atype "const std::vector<int, std::allocator<int>>&"]];
        "std::is_nothrow_copy_constructible<int*>"; "std::is_nothrow_copy_constructible<const int*>";
        "std::is_nothrow_default_constructible<std::allocator<int>>";
        "std::is_nothrow_default_constructible<std::allocator<char>>";
        "std::is_nothrow_default_constructible<std::allocator<wchar_t>>";
        "std::is_nothrow_default_constructible<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
        "std::is_nothrow_destructible<std::vector<int, std::allocator<int>>>"; "std::is_null_pointer<int>";
        "std::is_null_pointer<std::vector<int, std::allocator<int>>>"; "std::is_null_pointer<const volatile nullptr_t>";
        "std::is_null_pointer<const nullptr_t>"; "std::is_null_pointer<volatile nullptr_t>";
        "std::is_null_pointer<nullptr_t>"; "std::is_pointer<int*>";
        "std::is_pointer<std::vector<int, std::allocator<int>>*>"; "std::is_pointer<int>";
        "std::is_pointer<std::vector<int, std::allocator<int>>>"; "std::is_reference<int*>";
        "std::is_reference<const int*>"; "std::is_reference<int>"; "std::is_reference<std::allocator<int>>";
        "std::is_reference<std::allocator<char>>"; "std::is_reference<std::allocator<wchar_t>>";
        "std::is_reference<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
        "std::is_reference<std::vector<int, std::allocator<int>>>"; "std::is_same<int*, int*>";
        "std::is_same<std::_List_node<std::vector<int, std::allocator<int>>>*, std::_List_node<std::vector<int, std::allocator<int>>>*>";
        "std::is_same<std::_List_node<std::vector<int, std::allocator<int>>>*, std::vector<int, std::allocator<int>>*>";
        "std::is_same<std::basic_ostream<char, std::char_traits<char>>&, std::ios_base>"; "std::is_same<int, int>";
        "std::is_same<long, int>"; "std::is_same<unsigned long, int>"; "std::is_same<long long, int>";
        "std::is_same<unsigned long long, int>";
        "std::is_same<std::vector<int, std::allocator<int>>, std::vector<int, std::allocator<int>>>";
        "std::is_same<float, int>"; "std::is_same<double, int>"; "std::is_same<long double, int>";
        "std::is_scalar<int>"; "std::is_scalar<std::vector<int, std::allocator<int>>>"; "std::is_trivial<int>";
        "std::is_void<int*>"; "std::is_void<const int*>"; "std::is_void<int>"; "std::is_void<char>";
        "std::is_void<wchar_t>"; "std::is_void<char16_t>"; "std::is_void<char32_t>";
        "std::is_void<void>"; "std::is_void<std::allocator<int>>"; "std::is_void<std::allocator<char>>";
        "std::is_void<std::allocator<wchar_t>>";
        "std::is_void<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>";
        "std::is_void<std::vector<int, std::allocator<int>>>"; "std::is_void<const volatile void>";
        "std::is_void<const char>"; "std::is_void<const wchar_t>"; "std::is_void<const char16_t>";
        "std::is_void<const char32_t>"; "std::is_void<const void>"; "std::is_void<volatile void>";
        "std::is_volatile<unsigned short>"; "std::is_volatile<unsigned int>"; "std::is_volatile<wchar_t>";
        "std::is_volatile<char16_t>"; "std::is_volatile<char32_t>";
        "std::istreambuf_iterator<char, std::char_traits<char>>";
        "std::istreambuf_iterator<wchar_t, std::char_traits<wchar_t>>";
        "std::iterator<std::output_iterator_tag, void, void, void, void>";
        "std::iterator<std::random_access_iterator_tag, bool, long, std::_Bit_reference*, std::_Bit_reference>";
        "std::iterator<std::random_access_iterator_tag, bool, long, bool*, bool&>";
        "std::iterator<std::random_access_iterator_tag, bool, long, const bool*, bool>"; "std::iterator_traits<int*>";
        "std::iterator_traits<char*>"; "std::iterator_traits<wchar_t*>"; "std::iterator_traits<char16_t*>";
        "std::iterator_traits<char32_t*>"; "std::iterator_traits<const int*>";
        "std::iterator_traits<const char*>"; "std::iterator_traits<const wchar_t*>";
        "std::iterator_traits<const char16_t*>"; "std::iterator_traits<const char32_t*>";
        "std::iterator_traits<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>>";
        "std::iterator_traits<std::_Bit_const_iterator>"; "std::iterator_traits<std::_Bit_iterator>";
        "std::less<const volatile void*>"; "std::less<const std::_V2::error_category*>"; "std::less<void>";
        "std::less_equal<const volatile void*>"; "std::less_equal<void>"; "std::logical_and<void>";
        "std::logical_not<void>"; "std::logical_or<void>"; "std::make_signed<bool>";
        "std::make_signed<const volatile bool>"; "std::make_signed<const bool>";
        "std::make_signed<volatile bool>"; "std::make_unsigned<bool>";
        "std::make_unsigned<const volatile bool>"; "std::make_unsigned<const bool>";
        "std::make_unsigned<volatile bool>"; "std::minus<void>"; "std::modulus<void>";
        "std::multiplies<void>"; "std::negate<void>"; "std::not_equal_to<void>";
        "std::num_get<char, std::istreambuf_iterator<char, std::char_traits<char>>>";
        "std::num_get<wchar_t, std::istreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>";
        "std::num_put<char, std::ostreambuf_iterator<char, std::char_traits<char>>>";
        "std::num_put<wchar_t, std::ostreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>";
        "std::ostreambuf_iterator<char, std::char_traits<char>>";
        "std::ostreambuf_iterator<wchar_t, std::char_traits<wchar_t>>"; "std::plus<void>";
        "std::pointer_traits<int*>"; "std::pointer_traits<char*>"; "std::pointer_traits<wchar_t*>";
        "std::pointer_traits<char16_t*>"; "std::pointer_traits<char32_t*>"; "std::pointer_traits<const char*>";
        "std::pointer_traits<const wchar_t*>"; "std::pointer_traits<const char16_t*>";
        "std::pointer_traits<const char32_t*>"; "std::remove_all_extents<std::vector<int, std::allocator<int>>>";
        "std::remove_cv<int*>"; "std::remove_cv<unsigned short>"; "std::remove_cv<int>";
        "std::remove_cv<unsigned int>"; "std::remove_cv<wchar_t>"; "std::remove_cv<char16_t>";
        "std::remove_cv<char32_t>"; "std::remove_cv<std::vector<int, std::allocator<int>>>";
        "std::remove_reference<int&>"; "std::remove_reference<std::allocator<char>&>";
        "std::remove_reference<std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&>";
        "std::remove_reference<std::__cxx11::to_string(int)::@0&>";
        "std::remove_reference<std::__cxx11::to_string(unsigned int)::@0&>";
        "std::remove_reference<std::__cxx11::to_string(long)::@0&>";
        "std::remove_reference<std::__cxx11::to_string(unsigned long)::@0&>";
        "std::remove_reference<std::__cxx11::to_string(long long)::@0&>";
        "std::remove_reference<std::__cxx11::to_string(unsigned long long)::@0&>";
        "std::remove_reference<const std::vector<int, std::allocator<int>>&>"; "std::remove_reference<int>";
        "std::reverse_iterator<const char*>"; "std::reverse_iterator<const wchar_t*>";
        "std::reverse_iterator<const char16_t*>"; "std::reverse_iterator<const char32_t*>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<const char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<const wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<const char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>>";
        "std::reverse_iterator<__gnu_cxx::__normal_iterator<const char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>>";
        "std::reverse_iterator<std::_List_const_iterator<std::vector<int, std::allocator<int>>>>";
        "std::reverse_iterator<std::_List_iterator<std::vector<int, std::allocator<int>>>>";
        "std::reverse_iterator<std::_Bit_const_iterator>"; "std::reverse_iterator<std::_Bit_iterator>";
        "std::time_put<char, std::ostreambuf_iterator<char, std::char_traits<char>>>";
        "std::time_put<wchar_t, std::ostreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>"; Ninst "std::tuple" [Apack []];
        "std::vector<int, std::allocator<int>>";
        "std::__cxx11::_List_base<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>";
        "std::__cxx11::basic_istringstream<char, std::char_traits<char>, std::allocator<char>>";
        "std::__cxx11::basic_istringstream<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>";
        "std::__cxx11::basic_ostringstream<char, std::char_traits<char>, std::allocator<char>>";
        "std::__cxx11::basic_ostringstream<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::pmr::polymorphic_allocator<char>>";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::pmr::polymorphic_allocator<wchar_t>>";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::pmr::polymorphic_allocator<char16_t>>";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::pmr::polymorphic_allocator<char32_t>>";
        "std::__cxx11::basic_stringbuf<char, std::char_traits<char>, std::allocator<char>>";
        "std::__cxx11::basic_stringbuf<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>";
        "std::__cxx11::basic_stringstream<char, std::char_traits<char>, std::allocator<char>>";
        "std::__cxx11::basic_stringstream<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>";
        "std::__cxx11::collate<char>"; "std::__cxx11::collate<wchar_t>"; "std::__cxx11::collate_byname<char>";
        "std::__cxx11::collate_byname<wchar_t>";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>";
        "std::__cxx11::messages<char>"; "std::__cxx11::messages<wchar_t>";
        "std::__cxx11::money_get<char, std::istreambuf_iterator<char, std::char_traits<char>>>";
        "std::__cxx11::money_get<wchar_t, std::istreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>";
        "std::__cxx11::money_put<char, std::ostreambuf_iterator<char, std::char_traits<char>>>";
        "std::__cxx11::money_put<wchar_t, std::ostreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>";
        Ninst "std::__cxx11::moneypunct" [Atype "char"; Avalue (Eint 0 "bool")];
        Ninst "std::__cxx11::moneypunct" [Atype "char"; Avalue (Eint 1 "bool")];
        Ninst "std::__cxx11::moneypunct" [Atype "wchar_t"; Avalue (Eint 0 "bool")];
        Ninst "std::__cxx11::moneypunct" [Atype "wchar_t"; Avalue (Eint 1 "bool")]; "std::__cxx11::numpunct<char>";
        "std::__cxx11::numpunct<wchar_t>"; "std::__cxx11::numpunct_byname<char>";
        "std::__cxx11::numpunct_byname<wchar_t>";
        "std::__cxx11::time_get<char, std::istreambuf_iterator<char, std::char_traits<char>>>";
        "std::__cxx11::time_get<wchar_t, std::istreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>";
        Ninst "std::__make_unsigned_selector_base::_List" [Apack []];
        Ninst "std::__make_unsigned_selector_base::_List"
          [Apack
             [Atype "unsigned char"; Atype "unsigned short"; Atype "unsigned int";
              Atype "unsigned long"; Atype "unsigned long long"]];
        Ninst "std::__make_unsigned_selector_base::_List"
          [Apack
             [Atype "unsigned short"; Atype "unsigned int"; Atype "unsigned long";
              Atype "unsigned long long"]];
        Ninst "std::__make_unsigned_selector_base::_List"
          [Apack [Atype "unsigned int"; Atype "unsigned long"; Atype "unsigned long long"]];
        Ninst "std::__make_unsigned_selector_base::_List" [Apack [Atype "unsigned long"; Atype "unsigned long long"]];
        Ninst "std::__make_unsigned_selector_base::_List" [Apack [Atype "unsigned long long"]];
        Ninst "std::__make_unsigned_selector_base::__select"
          [Avalue (Eint 2 "unsigned long");
           Atype
             (Tnamed
                (Ninst "std::__make_unsigned_selector_base::_List"
                   [Apack
                      [Atype "unsigned char"; Atype "unsigned short"; Atype "unsigned int";
                       Atype "unsigned long"; Atype "unsigned long long"]]));
           Avalue (Eint 0 "bool")];
        Ninst "std::__make_unsigned_selector_base::__select"
          [Avalue (Eint 2 "unsigned long");
           Atype
             (Tnamed
                (Ninst "std::__make_unsigned_selector_base::_List"
                   [Apack
                      [Atype "unsigned short"; Atype "unsigned int"; Atype "unsigned long";
                       Atype "unsigned long long"]]));
           Avalue (Eint 1 "bool")];
        Ninst "std::__make_unsigned_selector_base::__select"
          [Avalue (Eint 4 "unsigned long");
           Atype
             (Tnamed
                (Ninst "std::__make_unsigned_selector_base::_List"
                   [Apack
                      [Atype "unsigned char"; Atype "unsigned short"; Atype "unsigned int";
                       Atype "unsigned long"; Atype "unsigned long long"]]));
           Avalue (Eint 0 "bool")];
        Ninst "std::__make_unsigned_selector_base::__select"
          [Avalue (Eint 4 "unsigned long");
           Atype
             (Tnamed
                (Ninst "std::__make_unsigned_selector_base::_List"
                   [Apack
                      [Atype "unsigned short"; Atype "unsigned int"; Atype "unsigned long";
                       Atype "unsigned long long"]]));
           Avalue (Eint 0 "bool")];
        Ninst "std::__make_unsigned_selector_base::__select"
          [Avalue (Eint 4 "unsigned long");
           Atype
             (Tnamed
                (Ninst "std::__make_unsigned_selector_base::_List"
                   [Apack [Atype "unsigned int"; Atype "unsigned long"; Atype "unsigned long long"]]));
           Avalue (Eint 1 "bool")];
        "std::pmr::polymorphic_allocator<char>"; "std::pmr::polymorphic_allocator<wchar_t>";
        "std::pmr::polymorphic_allocator<char16_t>"; "std::pmr::polymorphic_allocator<char32_t>"; "FILE";
        "_Atomic_word"; "_Float32"; "_Float32x"; "_Float64"; "_Float64x";
        "_G_fpos64_t"; "_G_fpos_t"; "_IO_FILE"; "_IO_codecvt"; "_IO_cookie_io_functions_t";
        "_IO_lock_t"; "_IO_marker"; "_IO_wide_data"; "__FILE"; "__NSConstantString";
        "__atomic_wide_counter"; "__blkcnt64_t"; "__blkcnt_t"; "__blksize_t";
        "__builtin_ms_va_list"; "__builtin_va_list"; "__caddr_t"; "__cancel_jmp_buf_tag";
        "__clock_t"; "__clockid_t"; "__compar_d_fn_t"; "__compar_fn_t"; "__cpu_mask";
        "__daddr_t"; "__dev_t"; "__fd_mask"; "__fpos64_t"; "__fpos_t";
        "__fsblkcnt64_t"; "__fsblkcnt_t"; "__fsfilcnt64_t"; "__fsfilcnt_t"; "__fsid_t";
        "__fsword_t"; "__gid_t"; "__gnuc_va_list"; "__gthread_cond_t"; "__gthread_key_t";
        "__gthread_mutex_t"; "__gthread_once_t"; "__gthread_recursive_mutex_t"; "__gthread_t";
        "__gthread_time_t"; "__id_t"; "__ino64_t"; "__ino_t"; "__int128_t";
        "__int16_t"; "__int32_t"; "__int64_t"; "__int8_t"; "__int_least16_t";
        "__int_least32_t"; "__int_least64_t"; "__int_least8_t"; "__intmax_t"; "__intptr_t";
        "__jmp_buf"; "__jmp_buf_tag"; "__key_t"; "__locale_data"; "__locale_struct";
        "__locale_t"; "__loff_t"; "__mbstate_t"; "__mode_t"; "__nlink_t";
        "__off64_t"; "__off_t"; "__once_flag"; "__pid_t"; "__pthread_cleanup_class";
        "__pthread_cleanup_frame"; "__pthread_cond_s"; "__pthread_internal_list";
        "__pthread_internal_slist"; "__pthread_list_t"; "__pthread_mutex_s";
        "__pthread_rwlock_arch_t"; "__pthread_slist_t"; "__pthread_unwind_buf_t"; "__quad_t";
        "__rlim64_t"; "__rlim_t"; "__sig_atomic_t"; "__sigset_t"; "__socklen_t";
        "__ssize_t"; "__suseconds64_t"; "__suseconds_t"; "__syscall_slong_t";
        "__syscall_ulong_t"; "__thrd_t"; "__time_t"; "__timer_t"; "__tss_t";
        "__u_char"; "__u_int"; "__u_long"; "__u_quad_t"; "__u_short"; "__uid_t";
        "__uint128_t"; "__uint16_t"; "__uint32_t"; "__uint64_t"; "__uint8_t";
        "__uint_least16_t"; "__uint_least32_t"; "__uint_least64_t"; "__uint_least8_t";
        "__uintmax_t"; "__useconds_t"; "_pthread_cleanup_buffer"; "blkcnt64_t"; "blkcnt_t";
        "blksize_t"; "caddr_t"; "clock_t"; "clockid_t"; "comparison_fn_t";
        "cookie_close_function_t"; "cookie_io_functions_t"; "cookie_read_function_t";
        "cookie_seek_function_t"; "cookie_write_function_t"; "cpu_set_t"; "daddr_t"; "dev_t";
        "div_t"; "drand48_data"; "error_t"; "fd_mask"; "fd_set"; "fpos64_t";
        "fpos_t"; "fsblkcnt64_t"; "fsblkcnt_t"; "fsfilcnt64_t"; "fsfilcnt_t";
        "fsid_t"; "gid_t"; "id_t"; "ino64_t"; "ino_t"; "int16_t";
        "int32_t"; "int64_t"; "int8_t"; "itimerspec"; "key_t"; "lconv";
        "ldiv_t"; "lldiv_t"; "locale_t"; "loff_t"; "max_align_t"; "mbstate_t";
        "mode_t"; "nlink_t"; "obstack"; "off64_t"; "off_t"; "pid_t";
        "pthread_attr_t"; "pthread_barrier_t"; "pthread_barrierattr_t"; "pthread_cond_t";
        "pthread_condattr_t"; "pthread_key_t"; "pthread_mutex_t"; "pthread_mutexattr_t";
        "pthread_once_t"; "pthread_rwlock_t"; "pthread_rwlockattr_t"; "pthread_spinlock_t";
        "pthread_t"; "ptrdiff_t"; "quad_t"; "random_data"; "register_t";
        "sched_param"; "sigevent"; "sigset_t"; "size_t"; "ssize_t"; "suseconds_t";
        "time_t"; "timer_t"; "timespec"; "timeval"; "timex"; "tm";
        "u_char"; "u_int"; "u_int16_t"; "u_int32_t"; "u_int64_t"; "u_int8_t";
        "u_long"; "u_quad_t"; "u_short"; "uid_t"; "uint"; "ulong";
        "useconds_t"; "ushort"; "va_list"; "wctrans_t"; "wctype_t"; "wint_t";
        ".PTHREAD_CANCEL_DEFERRED"; ".PTHREAD_CANCEL_ENABLE"; ".PTHREAD_CREATE_JOINABLE";
        ".PTHREAD_INHERIT_SCHED"; ".PTHREAD_MUTEX_STALLED"; ".PTHREAD_MUTEX_TIMED_NP";
        ".PTHREAD_PRIO_NONE"; ".PTHREAD_PROCESS_PRIVATE"; ".PTHREAD_RWLOCK_PREFER_READER_NP";
        ".PTHREAD_SCOPE_SYSTEM"; "._ISupper"; ".__ISwupper";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::rebind<int>::other";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::rebind<char>::other";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::rebind<wchar_t>::other";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::rebind<char16_t>::other";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::rebind<char32_t>::other";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::rebind<std::_List_node<std::vector<int, std::allocator<int>>>>::other";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::rebind<std::vector<int, std::allocator<int>>>::other";
        Nscoped (Ninst "std::vector<int, std::allocator<int>>::_M_realloc_append(int&&)" [Apack [Atype "int"]]) (Nid "_Guard");
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::_M_construct<char*>(char*, char*, std::forward_iterator_tag)::_Guard";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::_M_construct<const char*>(const char*, const char*, std::forward_iterator_tag)::_Guard";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__resize_and_overwrite<std::__cxx11::to_string(int)::@0>(unsigned long, std::__cxx11::to_string(int)::@0)::_Terminator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__resize_and_overwrite<std::__cxx11::to_string(unsigned int)::@0>(unsigned long, std::__cxx11::to_string(unsigned int)::@0)::_Terminator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__resize_and_overwrite<std::__cxx11::to_string(long)::@0>(unsigned long, std::__cxx11::to_string(long)::@0)::_Terminator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__resize_and_overwrite<std::__cxx11::to_string(unsigned long)::@0>(unsigned long, std::__cxx11::to_string(unsigned long)::@0)::_Terminator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__resize_and_overwrite<std::__cxx11::to_string(long long)::@0>(unsigned long, std::__cxx11::to_string(long long)::@0)::_Terminator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__resize_and_overwrite<std::__cxx11::to_string(unsigned long long)::@0>(unsigned long, std::__cxx11::to_string(unsigned long long)::@0)::_Terminator";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::_M_construct<const char*>(const char*, const char*, std::forward_iterator_tag)::_Guard";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::_M_construct<const wchar_t*>(const wchar_t*, const wchar_t*, std::forward_iterator_tag)::_Guard";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::_M_construct<const char16_t*>(const char16_t*, const char16_t*, std::forward_iterator_tag)::_Guard";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::_M_construct<const char32_t*>(const char32_t*, const char32_t*, std::forward_iterator_tag)::_Guard";
        "__gnu_cxx::_Char_types<char>::int_type"; "__gnu_cxx::_Char_types<char>::off_type";
        "__gnu_cxx::_Char_types<char>::pos_type"; "__gnu_cxx::_Char_types<char>::state_type";
        "__gnu_cxx::_Char_types<wchar_t>::int_type"; "__gnu_cxx::_Char_types<wchar_t>::off_type";
        "__gnu_cxx::_Char_types<wchar_t>::pos_type"; "__gnu_cxx::_Char_types<wchar_t>::state_type";
        "__gnu_cxx::__add_unsigned<signed char>::__type"; "__gnu_cxx::__add_unsigned<short>::__type";
        "__gnu_cxx::__add_unsigned<int>::__type"; "__gnu_cxx::__add_unsigned<long>::__type";
        "__gnu_cxx::__add_unsigned<long long>::__type"; "__gnu_cxx::__add_unsigned<char>::__type";
        "__gnu_cxx::__aligned_membuf<std::vector<int, std::allocator<int>>>::_Tp2";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::_Base_type";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::allocator_type";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::const_pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::const_reference";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::difference_type";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::reference";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::size_type";
        "__gnu_cxx::__alloc_traits<std::allocator<int>, int>::value_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::_Base_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::allocator_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::const_pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::const_reference";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::difference_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::reference";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::size_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char>, char>::value_type";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::_Base_type";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::allocator_type";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::const_pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::const_reference";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::difference_type";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::reference";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::size_type";
        "__gnu_cxx::__alloc_traits<std::allocator<wchar_t>, wchar_t>::value_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::_Base_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::allocator_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::const_pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::const_reference";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::difference_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::reference";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::size_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char16_t>, char16_t>::value_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::_Base_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::allocator_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::const_pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::const_reference";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::difference_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::reference";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::size_type";
        "__gnu_cxx::__alloc_traits<std::allocator<char32_t>, char32_t>::value_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::_Base_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::allocator_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::const_pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::const_reference";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::difference_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::reference";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::size_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>, std::_List_node<std::vector<int, std::allocator<int>>>>::value_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::_Base_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::allocator_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::const_pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::const_reference";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::difference_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::pointer";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::reference";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::size_type";
        "__gnu_cxx::__alloc_traits<std::allocator<std::vector<int, std::allocator<int>>>, std::vector<int, std::allocator<int>>>::value_type";
        Nscoped
          (Ninst "__gnu_cxx::__conditional_type"
             [Avalue (Eint 1 "bool"); Atype "unsigned long"; Atype "unsigned long long"])
          (Nid "__type");
        "__gnu_cxx::__is_integer_nonstrict<short>::.__width"; "__gnu_cxx::__is_integer_nonstrict<int>::.__width";
        "__gnu_cxx::__is_integer_nonstrict<unsigned int>::.__width";
        "__gnu_cxx::__is_integer_nonstrict<long>::.__width";
        "__gnu_cxx::__is_integer_nonstrict<unsigned long>::.__width";
        "__gnu_cxx::__is_integer_nonstrict<unsigned long long>::.__width";
        "__gnu_cxx::__is_integer_nonstrict<char>::.__width";
        "__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>::difference_type";
        "__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>::pointer";
        "__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>::reference";
        "__gnu_cxx::__normal_iterator<int*, std::vector<int, std::allocator<int>>>::value_type";
        "__gnu_cxx::__normal_iterator<char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::difference_type";
        "__gnu_cxx::__normal_iterator<char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::pointer";
        "__gnu_cxx::__normal_iterator<char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::reference";
        "__gnu_cxx::__normal_iterator<char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::value_type";
        "__gnu_cxx::__normal_iterator<wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::difference_type";
        "__gnu_cxx::__normal_iterator<wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::pointer";
        "__gnu_cxx::__normal_iterator<wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::reference";
        "__gnu_cxx::__normal_iterator<wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::value_type";
        "__gnu_cxx::__normal_iterator<char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::difference_type";
        "__gnu_cxx::__normal_iterator<char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::pointer";
        "__gnu_cxx::__normal_iterator<char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::reference";
        "__gnu_cxx::__normal_iterator<char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::value_type";
        "__gnu_cxx::__normal_iterator<char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::difference_type";
        "__gnu_cxx::__normal_iterator<char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::pointer";
        "__gnu_cxx::__normal_iterator<char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::reference";
        "__gnu_cxx::__normal_iterator<char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::value_type";
        "__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>::difference_type";
        "__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>::pointer";
        "__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>::reference";
        "__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>::value_type";
        "__gnu_cxx::__normal_iterator<const char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<const char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::difference_type";
        "__gnu_cxx::__normal_iterator<const char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<const char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<const char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::pointer";
        "__gnu_cxx::__normal_iterator<const char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::reference";
        "__gnu_cxx::__normal_iterator<const char*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>::value_type";
        "__gnu_cxx::__normal_iterator<const wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<const wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::difference_type";
        "__gnu_cxx::__normal_iterator<const wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<const wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<const wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::pointer";
        "__gnu_cxx::__normal_iterator<const wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::reference";
        "__gnu_cxx::__normal_iterator<const wchar_t*, std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>>::value_type";
        "__gnu_cxx::__normal_iterator<const char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<const char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::difference_type";
        "__gnu_cxx::__normal_iterator<const char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<const char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<const char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::pointer";
        "__gnu_cxx::__normal_iterator<const char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::reference";
        "__gnu_cxx::__normal_iterator<const char16_t*, std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>>::value_type";
        "__gnu_cxx::__normal_iterator<const char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::__traits_type";
        "__gnu_cxx::__normal_iterator<const char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::difference_type";
        "__gnu_cxx::__normal_iterator<const char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::iterator_category";
        "__gnu_cxx::__normal_iterator<const char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::iterator_type";
        "__gnu_cxx::__normal_iterator<const char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::pointer";
        "__gnu_cxx::__normal_iterator<const char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::reference";
        "__gnu_cxx::__normal_iterator<const char32_t*, std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>>::value_type";
        Nscoped (Ninst "__gnu_cxx::__promote" [Atype "float"; Avalue (Eint 0 "bool")]) (Nid "__type");
        Nscoped (Ninst "__gnu_cxx::__promote" [Atype "double"; Avalue (Eint 0 "bool")]) (Nid "__type");
        Nscoped (Ninst "__gnu_cxx::__promote" [Atype "long double"; Avalue (Eint 0 "bool")]) (Nid "__type");
        "__gnu_cxx::__remove_unsigned<unsigned char>::__type"; "__gnu_cxx::__remove_unsigned<unsigned short>::__type";
        "__gnu_cxx::__remove_unsigned<unsigned int>::__type"; "__gnu_cxx::__remove_unsigned<unsigned long>::__type";
        "__gnu_cxx::__remove_unsigned<unsigned long long>::__type"; "__gnu_cxx::__remove_unsigned<char>::__type";
        "__gnu_cxx::char_traits<char>::char_type"; "__gnu_cxx::char_traits<char>::int_type";
        "__gnu_cxx::char_traits<char>::off_type"; "__gnu_cxx::char_traits<char>::pos_type";
        "__gnu_cxx::char_traits<char>::state_type"; "__gnu_cxx::char_traits<wchar_t>::char_type";
        "__gnu_cxx::char_traits<wchar_t>::int_type"; "__gnu_cxx::char_traits<wchar_t>::off_type";
        "__gnu_cxx::char_traits<wchar_t>::pos_type"; "__gnu_cxx::char_traits<wchar_t>::state_type";
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "long"; Atype "int"; Atype "char"; Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "long"; Atype "int"; Atype "char"; Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "long"; Atype "long"; Atype "char"; Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "long"; Atype "long"; Atype "char"; Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "long"; Atype "int"; Atype "wchar_t"; Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "long"; Atype "int"; Atype "wchar_t"; Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "long"; Atype "long"; Atype "wchar_t"; Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "long"; Atype "long"; Atype "wchar_t"; Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(unsigned long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "unsigned long"; Atype "unsigned long"; Atype "char"; Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(unsigned long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "unsigned long"; Atype "unsigned long"; Atype "char"; Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(unsigned long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "unsigned long"; Atype "unsigned long"; Atype "wchar_t"; Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(unsigned long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "unsigned long"; Atype "unsigned long"; Atype "wchar_t"; Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "long long"; Atype "long long"; Atype "char"; Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "long long"; Atype "long long"; Atype "char"; Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "long long"; Atype "long long"; Atype "wchar_t"; Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "long long"; Atype "long long"; Atype "wchar_t"; Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(unsigned long long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "unsigned long long"; Atype "unsigned long long"; Atype "char";
              Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(unsigned long long(* )(const char*,char**,int), const char*, const char*, unsigned long*, int)"
             [Atype "unsigned long long"; Atype "unsigned long long"; Atype "char";
              Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst
             "__gnu_cxx::__stoa(unsigned long long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "unsigned long long"; Atype "unsigned long long"; Atype "wchar_t";
              Apack [Atype "int"]])
          (Nid "_Range_chk");
        Nscoped
          (Ninst
             "__gnu_cxx::__stoa(unsigned long long(* )(const wchar_t*,wchar_t**,int), const char*, const wchar_t*, unsigned long*, int)"
             [Atype "unsigned long long"; Atype "unsigned long long"; Atype "wchar_t";
              Apack [Atype "int"]])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(float(* )(const char*,char** ), const char*, const char*, unsigned long* )"
             [Atype "float"; Atype "float"; Atype "char"; Apack []])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(float(* )(const char*,char** ), const char*, const char*, unsigned long* )"
             [Atype "float"; Atype "float"; Atype "char"; Apack []])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(float(* )(const wchar_t*,wchar_t** ), const char*, const wchar_t*, unsigned long* )"
             [Atype "float"; Atype "float"; Atype "wchar_t"; Apack []])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(float(* )(const wchar_t*,wchar_t** ), const char*, const wchar_t*, unsigned long* )"
             [Atype "float"; Atype "float"; Atype "wchar_t"; Apack []])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(double(* )(const char*,char** ), const char*, const char*, unsigned long* )"
             [Atype "double"; Atype "double"; Atype "char"; Apack []])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(double(* )(const char*,char** ), const char*, const char*, unsigned long* )"
             [Atype "double"; Atype "double"; Atype "char"; Apack []])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(double(* )(const wchar_t*,wchar_t** ), const char*, const wchar_t*, unsigned long* )"
             [Atype "double"; Atype "double"; Atype "wchar_t"; Apack []])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(double(* )(const wchar_t*,wchar_t** ), const char*, const wchar_t*, unsigned long* )"
             [Atype "double"; Atype "double"; Atype "wchar_t"; Apack []])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long double(* )(const char*,char** ), const char*, const char*, unsigned long* )"
             [Atype "long double"; Atype "long double"; Atype "char"; Apack []])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long double(* )(const char*,char** ), const char*, const char*, unsigned long* )"
             [Atype "long double"; Atype "long double"; Atype "char"; Apack []])
          (Nid "_Save_errno");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long double(* )(const wchar_t*,wchar_t** ), const char*, const wchar_t*, unsigned long* )"
             [Atype "long double"; Atype "long double"; Atype "wchar_t"; Apack []])
          (Nid "_Range_chk");
        Nscoped
          (Ninst "__gnu_cxx::__stoa(long double(* )(const wchar_t*,wchar_t** ), const char*, const wchar_t*, unsigned long* )"
             [Atype "long double"; Atype "long double"; Atype "wchar_t"; Apack []])
          (Nid "_Save_errno");
        "std::_List_iterator<std::vector<int, std::allocator<int>>>::_Node";
        "std::_List_iterator<std::vector<int, std::allocator<int>>>::_Self";
        "std::_List_iterator<std::vector<int, std::allocator<int>>>::difference_type";
        "std::_List_iterator<std::vector<int, std::allocator<int>>>::iterator_category";
        "std::_List_iterator<std::vector<int, std::allocator<int>>>::pointer";
        "std::_List_iterator<std::vector<int, std::allocator<int>>>::reference";
        "std::_List_iterator<std::vector<int, std::allocator<int>>>::value_type";
        "std::_Vector_base<int, std::allocator<int>>::_Tp_alloc_type";
        "std::_Vector_base<int, std::allocator<int>>::_Vector_impl";
        "std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data";
        "std::_Vector_base<int, std::allocator<int>>::allocator_type";
        "std::_Vector_base<int, std::allocator<int>>::pointer";
        "std::__add_lvalue_reference_helper<int* const, void>::type";
        "std::__add_lvalue_reference_helper<const int* const, void>::type";
        "std::__add_rvalue_reference_helper<int, void>::type";
        "std::__allocated_ptr<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::pointer";
        "std::__allocated_ptr<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::value_type";
        "std::__are_same<float, float>::__type"; "std::__are_same<float, float>::.__value";
        "std::__are_same<float, double>::__type"; "std::__are_same<float, double>::.__value";
        "std::__are_same<double, float>::__type"; "std::__are_same<double, float>::.__value";
        "std::__are_same<double, double>::__type"; "std::__are_same<double, double>::.__value";
        "std::__are_same<long double, float>::__type"; "std::__are_same<long double, float>::.__value";
        "std::__are_same<long double, double>::__type"; "std::__are_same<long double, double>::.__value";
        "std::__byte_operand<signed char>::__type"; "std::__byte_operand<unsigned char>::__type";
        "std::__byte_operand<short>::__type"; "std::__byte_operand<unsigned short>::__type";
        "std::__byte_operand<int>::__type"; "std::__byte_operand<unsigned int>::__type";
        "std::__byte_operand<long>::__type"; "std::__byte_operand<unsigned long>::__type";
        "std::__byte_operand<long long>::__type"; "std::__byte_operand<unsigned long long>::__type";
        "std::__byte_operand<int128_t>::__type"; "std::__byte_operand<uint128_t>::__type";
        "std::__byte_operand<char>::__type"; "std::__byte_operand<wchar_t>::__type";
        "std::__byte_operand<char16_t>::__type"; "std::__byte_operand<char32_t>::__type";
        "std::__byte_operand<bool>::__type"; Nscoped (Ninst "std::__combine_tuples" [Apack []]) (Nid "__type");
        "std::__ctype_abstract_base<wchar_t>::char_type";
        Nscoped (Ninst "std::__cv_selector" [Atype "short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")]) (Nid "__type");
        Nscoped (Ninst "std::__cv_selector" [Atype "unsigned short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__cv_selector" [Atype "int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")]) (Nid "__type");
        Nscoped (Ninst "std::__cv_selector" [Atype "unsigned int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        "std::__hash_base<unsigned long, signed char>::argument_type";
        "std::__hash_base<unsigned long, signed char>::result_type";
        "std::__hash_base<unsigned long, unsigned char>::argument_type";
        "std::__hash_base<unsigned long, unsigned char>::result_type";
        "std::__hash_base<unsigned long, short>::argument_type";
        "std::__hash_base<unsigned long, short>::result_type";
        "std::__hash_base<unsigned long, unsigned short>::argument_type";
        "std::__hash_base<unsigned long, unsigned short>::result_type";
        "std::__hash_base<unsigned long, int>::argument_type"; "std::__hash_base<unsigned long, int>::result_type";
        "std::__hash_base<unsigned long, unsigned int>::argument_type";
        "std::__hash_base<unsigned long, unsigned int>::result_type";
        "std::__hash_base<unsigned long, long>::argument_type"; "std::__hash_base<unsigned long, long>::result_type";
        "std::__hash_base<unsigned long, unsigned long>::argument_type";
        "std::__hash_base<unsigned long, unsigned long>::result_type";
        "std::__hash_base<unsigned long, long long>::argument_type";
        "std::__hash_base<unsigned long, long long>::result_type";
        "std::__hash_base<unsigned long, unsigned long long>::argument_type";
        "std::__hash_base<unsigned long, unsigned long long>::result_type";
        "std::__hash_base<unsigned long, int128_t>::argument_type";
        "std::__hash_base<unsigned long, int128_t>::result_type";
        "std::__hash_base<unsigned long, uint128_t>::argument_type";
        "std::__hash_base<unsigned long, uint128_t>::result_type";
        "std::__hash_base<unsigned long, char>::argument_type"; "std::__hash_base<unsigned long, char>::result_type";
        "std::__hash_base<unsigned long, wchar_t>::argument_type";
        "std::__hash_base<unsigned long, wchar_t>::result_type";
        "std::__hash_base<unsigned long, char16_t>::argument_type";
        "std::__hash_base<unsigned long, char16_t>::result_type";
        "std::__hash_base<unsigned long, char32_t>::argument_type";
        "std::__hash_base<unsigned long, char32_t>::result_type";
        "std::__hash_base<unsigned long, std::basic_string_view<char, std::char_traits<char>>>::argument_type";
        "std::__hash_base<unsigned long, std::basic_string_view<char, std::char_traits<char>>>::result_type";
        "std::__hash_base<unsigned long, std::basic_string_view<wchar_t, std::char_traits<wchar_t>>>::argument_type";
        "std::__hash_base<unsigned long, std::basic_string_view<wchar_t, std::char_traits<wchar_t>>>::result_type";
        "std::__hash_base<unsigned long, std::basic_string_view<char16_t, std::char_traits<char16_t>>>::argument_type";
        "std::__hash_base<unsigned long, std::basic_string_view<char16_t, std::char_traits<char16_t>>>::result_type";
        "std::__hash_base<unsigned long, std::basic_string_view<char32_t, std::char_traits<char32_t>>>::argument_type";
        "std::__hash_base<unsigned long, std::basic_string_view<char32_t, std::char_traits<char32_t>>>::result_type";
        "std::__hash_base<unsigned long, std::error_code>::argument_type";
        "std::__hash_base<unsigned long, std::error_code>::result_type";
        "std::__hash_base<unsigned long, std::error_condition>::argument_type";
        "std::__hash_base<unsigned long, std::error_condition>::result_type";
        "std::__hash_base<unsigned long, bool>::argument_type"; "std::__hash_base<unsigned long, bool>::result_type";
        "std::__hash_base<unsigned long, float>::argument_type";
        "std::__hash_base<unsigned long, float>::result_type";
        "std::__hash_base<unsigned long, double>::argument_type";
        "std::__hash_base<unsigned long, double>::result_type";
        "std::__hash_base<unsigned long, long double>::argument_type";
        "std::__hash_base<unsigned long, long double>::result_type";
        "std::__hash_base<unsigned long, nullptr_t>::argument_type";
        "std::__hash_base<unsigned long, nullptr_t>::result_type"; "std::__is_byte<signed char>::__type";
        "std::__is_byte<signed char>::.__value"; "std::__is_byte<unsigned char>::__type";
        "std::__is_byte<unsigned char>::.__value"; "std::__is_byte<char>::__type";
        "std::__is_byte<char>::.__value"; "std::__is_byte<enum std::byte>::__type";
        "std::__is_byte<enum std::byte>::.__value"; "std::__is_char<char>::__type";
        "std::__is_char<char>::.__value"; "std::__is_char<wchar_t>::__type";
        "std::__is_char<wchar_t>::.__value"; "std::__is_floating<float>::__type";
        "std::__is_floating<float>::.__value"; "std::__is_floating<double>::__type";
        "std::__is_floating<double>::.__value"; "std::__is_floating<long double>::__type";
        "std::__is_floating<long double>::.__value"; "std::__is_integer<signed char>::__type";
        "std::__is_integer<signed char>::.__value"; "std::__is_integer<unsigned char>::__type";
        "std::__is_integer<unsigned char>::.__value"; "std::__is_integer<short>::__type";
        "std::__is_integer<short>::.__value"; "std::__is_integer<unsigned short>::__type";
        "std::__is_integer<unsigned short>::.__value"; "std::__is_integer<int>::__type";
        "std::__is_integer<int>::.__value"; "std::__is_integer<unsigned int>::__type";
        "std::__is_integer<unsigned int>::.__value"; "std::__is_integer<long>::__type";
        "std::__is_integer<long>::.__value"; "std::__is_integer<unsigned long>::__type";
        "std::__is_integer<unsigned long>::.__value"; "std::__is_integer<long long>::__type";
        "std::__is_integer<long long>::.__value"; "std::__is_integer<unsigned long long>::__type";
        "std::__is_integer<unsigned long long>::.__value"; "std::__is_integer<int128_t>::__type";
        "std::__is_integer<int128_t>::.__value"; "std::__is_integer<uint128_t>::__type";
        "std::__is_integer<uint128_t>::.__value"; "std::__is_integer<char>::__type";
        "std::__is_integer<char>::.__value"; "std::__is_integer<wchar_t>::__type";
        "std::__is_integer<wchar_t>::.__value"; "std::__is_integer<char16_t>::__type";
        "std::__is_integer<char16_t>::.__value"; "std::__is_integer<char32_t>::__type";
        "std::__is_integer<char32_t>::.__value"; "std::__is_integer<bool>::__type";
        "std::__is_integer<bool>::.__value"; "std::__is_integer<float>::__type";
        "std::__is_integer<float>::.__value"; "std::__is_integer<double>::__type";
        "std::__is_integer<double>::.__value"; "std::__is_integer<long double>::__type";
        "std::__is_integer<long double>::.__value";
        "std::__is_move_iterator<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>>::__type";
        "std::__is_move_iterator<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>>::.__value";
        "std::__is_nonvolatile_trivially_copyable<int>::.__value";
        "std::__is_nt_destructible_impl<std::vector<int, std::allocator<int>>>::type"; "std::__is_void<void>::__type";
        "std::__is_void<void>::.__value";
        "std::__iterator_traits<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, void>::difference_type";
        "std::__iterator_traits<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, void>::iterator_category";
        "std::__iterator_traits<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, void>::pointer";
        "std::__iterator_traits<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, void>::reference";
        "std::__iterator_traits<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, void>::value_type";
        "std::__iterator_traits<std::_Bit_const_iterator, void>::difference_type";
        "std::__iterator_traits<std::_Bit_const_iterator, void>::iterator_category";
        "std::__iterator_traits<std::_Bit_const_iterator, void>::pointer";
        "std::__iterator_traits<std::_Bit_const_iterator, void>::reference";
        "std::__iterator_traits<std::_Bit_const_iterator, void>::value_type";
        "std::__iterator_traits<std::_Bit_iterator, void>::difference_type";
        "std::__iterator_traits<std::_Bit_iterator, void>::iterator_category";
        "std::__iterator_traits<std::_Bit_iterator, void>::pointer";
        "std::__iterator_traits<std::_Bit_iterator, void>::reference";
        "std::__iterator_traits<std::_Bit_iterator, void>::value_type";
        Nscoped (Ninst "std::__make_1st_indices" [Apack []]) (Nid "__type"); "std::__make_signed<unsigned char>::__type";
        "std::__make_signed<unsigned short>::__type"; "std::__make_signed<unsigned int>::__type";
        "std::__make_signed<unsigned long>::__type"; "std::__make_signed<unsigned long long>::__type";
        "std::__make_signed<uint128_t>::__type"; "std::__make_signed<char>::__type";
        "std::__make_signed<wchar_t>::__type"; "std::__make_signed<char16_t>::__type";
        "std::__make_signed<char32_t>::__type";
        Nscoped (Ninst "std::__make_signed_selector" [Atype "unsigned short"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__signed_type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "unsigned short"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "unsigned int"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__signed_type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "unsigned int"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "wchar_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "wchar_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__unsigned_type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "char16_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "char16_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__unsigned_type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "char32_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_signed_selector" [Atype "char32_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__unsigned_type");
        "std::__make_unsigned<signed char>::__type"; "std::__make_unsigned<short>::__type";
        "std::__make_unsigned<int>::__type"; "std::__make_unsigned<long>::__type";
        "std::__make_unsigned<long long>::__type"; "std::__make_unsigned<int128_t>::__type";
        "std::__make_unsigned<char>::__type"; "std::__make_unsigned<wchar_t>::__type";
        "std::__make_unsigned<char16_t>::__type"; "std::__make_unsigned<char32_t>::__type";
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "wchar_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "_UInts");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "wchar_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "wchar_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__unsigned_type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "wchar_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "wchar_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__unsigned_type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char16_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "_UInts");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char16_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char16_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__unsigned_type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char16_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char16_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__unsigned_type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char32_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "_UInts");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char32_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char32_t"; Avalue (Eint 0 "bool"); Avalue (Eint 1 "bool")])
          (Nid "__unsigned_type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char32_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped (Ninst "std::__make_unsigned_selector" [Atype "char32_t"; Avalue (Eint 1 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__unsigned_type");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "unsigned short"; Atype "short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__match");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "unsigned short"; Atype "short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "unsigned int"; Atype "int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__match");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "unsigned int"; Atype "int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "wchar_t"; Atype "unsigned int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__match");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "wchar_t"; Atype "unsigned int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "char16_t"; Atype "unsigned short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__match");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "char16_t"; Atype "unsigned short"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "char32_t"; Atype "unsigned int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__match");
        Nscoped
          (Ninst "std::__match_cv_qualifiers"
             [Atype "char32_t"; Atype "unsigned int"; Avalue (Eint 0 "bool"); Avalue (Eint 0 "bool")])
          (Nid "__type");
        "std::__new_allocator<int>::const_pointer"; "std::__new_allocator<int>::const_reference";
        "std::__new_allocator<int>::difference_type"; "std::__new_allocator<int>::pointer";
        "std::__new_allocator<int>::propagate_on_container_move_assignment"; "std::__new_allocator<int>::reference";
        "std::__new_allocator<int>::size_type"; "std::__new_allocator<int>::value_type";
        "std::__new_allocator<char>::const_pointer"; "std::__new_allocator<char>::const_reference";
        "std::__new_allocator<char>::difference_type"; "std::__new_allocator<char>::pointer";
        "std::__new_allocator<char>::propagate_on_container_move_assignment"; "std::__new_allocator<char>::reference";
        "std::__new_allocator<char>::size_type"; "std::__new_allocator<char>::value_type";
        "std::__new_allocator<wchar_t>::const_pointer"; "std::__new_allocator<wchar_t>::const_reference";
        "std::__new_allocator<wchar_t>::difference_type"; "std::__new_allocator<wchar_t>::pointer";
        "std::__new_allocator<wchar_t>::propagate_on_container_move_assignment";
        "std::__new_allocator<wchar_t>::reference"; "std::__new_allocator<wchar_t>::size_type";
        "std::__new_allocator<wchar_t>::value_type"; "std::__new_allocator<char16_t>::const_pointer";
        "std::__new_allocator<char16_t>::const_reference"; "std::__new_allocator<char16_t>::difference_type";
        "std::__new_allocator<char16_t>::pointer";
        "std::__new_allocator<char16_t>::propagate_on_container_move_assignment";
        "std::__new_allocator<char16_t>::reference"; "std::__new_allocator<char16_t>::size_type";
        "std::__new_allocator<char16_t>::value_type"; "std::__new_allocator<char32_t>::const_pointer";
        "std::__new_allocator<char32_t>::const_reference"; "std::__new_allocator<char32_t>::difference_type";
        "std::__new_allocator<char32_t>::pointer";
        "std::__new_allocator<char32_t>::propagate_on_container_move_assignment";
        "std::__new_allocator<char32_t>::reference"; "std::__new_allocator<char32_t>::size_type";
        "std::__new_allocator<char32_t>::value_type";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::const_pointer";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::const_reference";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::difference_type";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::pointer";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::propagate_on_container_move_assignment";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::reference";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::size_type";
        "std::__new_allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::value_type";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>::const_pointer";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>::const_reference";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>::difference_type";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>::pointer";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>::propagate_on_container_move_assignment";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>::reference";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>::size_type";
        "std::__new_allocator<std::vector<int, std::allocator<int>>>::value_type";
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "int*"; Atype "int"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "int*"; Atype "int"; Avalue (Eint 0 "bool")]) (Nid "pointer");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "char*"; Atype "char"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "char*"; Atype "char"; Avalue (Eint 0 "bool")]) (Nid "pointer");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "wchar_t*"; Atype "wchar_t"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "wchar_t*"; Atype "wchar_t"; Avalue (Eint 0 "bool")])
          (Nid "pointer");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "char16_t*"; Atype "char16_t"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "char16_t*"; Atype "char16_t"; Avalue (Eint 0 "bool")])
          (Nid "pointer");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "char32_t*"; Atype "char32_t"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "char32_t*"; Atype "char32_t"; Avalue (Eint 0 "bool")])
          (Nid "pointer");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "const char*"; Atype "const char"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped (Ninst "std::__ptr_traits_ptr_to" [Atype "const char*"; Atype "const char"; Avalue (Eint 0 "bool")])
          (Nid "pointer");
        Nscoped
          (Ninst "std::__ptr_traits_ptr_to" [Atype "const wchar_t*"; Atype "const wchar_t"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped
          (Ninst "std::__ptr_traits_ptr_to" [Atype "const wchar_t*"; Atype "const wchar_t"; Avalue (Eint 0 "bool")])
          (Nid "pointer");
        Nscoped
          (Ninst "std::__ptr_traits_ptr_to" [Atype "const char16_t*"; Atype "const char16_t"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped
          (Ninst "std::__ptr_traits_ptr_to" [Atype "const char16_t*"; Atype "const char16_t"; Avalue (Eint 0 "bool")])
          (Nid "pointer");
        Nscoped
          (Ninst "std::__ptr_traits_ptr_to" [Atype "const char32_t*"; Atype "const char32_t"; Avalue (Eint 0 "bool")])
          (Nid "element_type");
        Nscoped
          (Ninst "std::__ptr_traits_ptr_to" [Atype "const char32_t*"; Atype "const char32_t"; Avalue (Eint 0 "bool")])
          (Nid "pointer");
        Nscoped (Ninst "std::__truth_type" [Avalue (Eint 1 "bool")]) (Nid "__type"); "std::__type_identity<int*>::type";
        "std::__type_identity<const int*>::type"; "std::__type_identity<int>::type";
        "std::__type_identity<std::allocator<int>>::type"; "std::__type_identity<std::allocator<char>>::type";
        "std::__type_identity<std::allocator<wchar_t>>::type";
        "std::__type_identity<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::type";
        "std::__type_identity<std::allocator<std::vector<int, std::allocator<int>>>>::type";
        "std::__type_identity<std::vector<int, std::allocator<int>>>::type";
        "std::add_pointer<std::basic_ostream<char, std::char_traits<char>>&>::type";
        "std::allocator<int>::const_pointer"; "std::allocator<int>::const_reference";
        "std::allocator<int>::difference_type"; "std::allocator<int>::is_always_equal";
        "std::allocator<int>::pointer"; "std::allocator<int>::propagate_on_container_move_assignment";
        "std::allocator<int>::reference"; "std::allocator<int>::size_type";
        "std::allocator<int>::value_type"; "std::allocator<char>::const_pointer";
        "std::allocator<char>::const_reference"; "std::allocator<char>::difference_type";
        "std::allocator<char>::is_always_equal"; "std::allocator<char>::pointer";
        "std::allocator<char>::propagate_on_container_move_assignment"; "std::allocator<char>::reference";
        "std::allocator<char>::size_type"; "std::allocator<char>::value_type";
        "std::allocator<wchar_t>::const_pointer"; "std::allocator<wchar_t>::const_reference";
        "std::allocator<wchar_t>::difference_type"; "std::allocator<wchar_t>::is_always_equal";
        "std::allocator<wchar_t>::pointer"; "std::allocator<wchar_t>::propagate_on_container_move_assignment";
        "std::allocator<wchar_t>::reference"; "std::allocator<wchar_t>::size_type";
        "std::allocator<wchar_t>::value_type"; "std::allocator<char16_t>::const_pointer";
        "std::allocator<char16_t>::const_reference"; "std::allocator<char16_t>::difference_type";
        "std::allocator<char16_t>::is_always_equal"; "std::allocator<char16_t>::pointer";
        "std::allocator<char16_t>::propagate_on_container_move_assignment"; "std::allocator<char16_t>::reference";
        "std::allocator<char16_t>::size_type"; "std::allocator<char16_t>::value_type";
        "std::allocator<char32_t>::const_pointer"; "std::allocator<char32_t>::const_reference";
        "std::allocator<char32_t>::difference_type"; "std::allocator<char32_t>::is_always_equal";
        "std::allocator<char32_t>::pointer"; "std::allocator<char32_t>::propagate_on_container_move_assignment";
        "std::allocator<char32_t>::reference"; "std::allocator<char32_t>::size_type";
        "std::allocator<char32_t>::value_type"; "std::allocator<void>::const_pointer";
        "std::allocator<void>::difference_type"; "std::allocator<void>::is_always_equal";
        "std::allocator<void>::pointer"; "std::allocator<void>::propagate_on_container_move_assignment";
        "std::allocator<void>::size_type"; "std::allocator<void>::value_type";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::const_pointer";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::const_reference";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::difference_type";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::is_always_equal";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::pointer";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::propagate_on_container_move_assignment";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::reference";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::size_type";
        "std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>::value_type";
        "std::allocator<std::vector<int, std::allocator<int>>>::const_pointer";
        "std::allocator<std::vector<int, std::allocator<int>>>::const_reference";
        "std::allocator<std::vector<int, std::allocator<int>>>::difference_type";
        "std::allocator<std::vector<int, std::allocator<int>>>::is_always_equal";
        "std::allocator<std::vector<int, std::allocator<int>>>::pointer";
        "std::allocator<std::vector<int, std::allocator<int>>>::propagate_on_container_move_assignment";
        "std::allocator<std::vector<int, std::allocator<int>>>::reference";
        "std::allocator<std::vector<int, std::allocator<int>>>::size_type";
        "std::allocator<std::vector<int, std::allocator<int>>>::value_type";
        "std::allocator_traits<std::allocator<int>>::allocator_type";
        "std::allocator_traits<std::allocator<int>>::const_pointer";
        "std::allocator_traits<std::allocator<int>>::const_void_pointer";
        "std::allocator_traits<std::allocator<int>>::difference_type";
        "std::allocator_traits<std::allocator<int>>::is_always_equal";
        "std::allocator_traits<std::allocator<int>>::pointer";
        "std::allocator_traits<std::allocator<int>>::propagate_on_container_copy_assignment";
        "std::allocator_traits<std::allocator<int>>::propagate_on_container_move_assignment";
        "std::allocator_traits<std::allocator<int>>::propagate_on_container_swap";
        "std::allocator_traits<std::allocator<int>>::size_type";
        "std::allocator_traits<std::allocator<int>>::value_type";
        "std::allocator_traits<std::allocator<int>>::void_pointer";
        "std::allocator_traits<std::allocator<char>>::allocator_type";
        "std::allocator_traits<std::allocator<char>>::const_pointer";
        "std::allocator_traits<std::allocator<char>>::const_void_pointer";
        "std::allocator_traits<std::allocator<char>>::difference_type";
        "std::allocator_traits<std::allocator<char>>::is_always_equal";
        "std::allocator_traits<std::allocator<char>>::pointer";
        "std::allocator_traits<std::allocator<char>>::propagate_on_container_copy_assignment";
        "std::allocator_traits<std::allocator<char>>::propagate_on_container_move_assignment";
        "std::allocator_traits<std::allocator<char>>::propagate_on_container_swap";
        "std::allocator_traits<std::allocator<char>>::size_type";
        "std::allocator_traits<std::allocator<char>>::value_type";
        "std::allocator_traits<std::allocator<char>>::void_pointer";
        "std::allocator_traits<std::allocator<wchar_t>>::allocator_type";
        "std::allocator_traits<std::allocator<wchar_t>>::const_pointer";
        "std::allocator_traits<std::allocator<wchar_t>>::const_void_pointer";
        "std::allocator_traits<std::allocator<wchar_t>>::difference_type";
        "std::allocator_traits<std::allocator<wchar_t>>::is_always_equal";
        "std::allocator_traits<std::allocator<wchar_t>>::pointer";
        "std::allocator_traits<std::allocator<wchar_t>>::propagate_on_container_copy_assignment";
        "std::allocator_traits<std::allocator<wchar_t>>::propagate_on_container_move_assignment";
        "std::allocator_traits<std::allocator<wchar_t>>::propagate_on_container_swap";
        "std::allocator_traits<std::allocator<wchar_t>>::size_type";
        "std::allocator_traits<std::allocator<wchar_t>>::value_type";
        "std::allocator_traits<std::allocator<wchar_t>>::void_pointer";
        "std::allocator_traits<std::allocator<char16_t>>::allocator_type";
        "std::allocator_traits<std::allocator<char16_t>>::const_pointer";
        "std::allocator_traits<std::allocator<char16_t>>::const_void_pointer";
        "std::allocator_traits<std::allocator<char16_t>>::difference_type";
        "std::allocator_traits<std::allocator<char16_t>>::is_always_equal";
        "std::allocator_traits<std::allocator<char16_t>>::pointer";
        "std::allocator_traits<std::allocator<char16_t>>::propagate_on_container_copy_assignment";
        "std::allocator_traits<std::allocator<char16_t>>::propagate_on_container_move_assignment";
        "std::allocator_traits<std::allocator<char16_t>>::propagate_on_container_swap";
        "std::allocator_traits<std::allocator<char16_t>>::size_type";
        "std::allocator_traits<std::allocator<char16_t>>::value_type";
        "std::allocator_traits<std::allocator<char16_t>>::void_pointer";
        "std::allocator_traits<std::allocator<char32_t>>::allocator_type";
        "std::allocator_traits<std::allocator<char32_t>>::const_pointer";
        "std::allocator_traits<std::allocator<char32_t>>::const_void_pointer";
        "std::allocator_traits<std::allocator<char32_t>>::difference_type";
        "std::allocator_traits<std::allocator<char32_t>>::is_always_equal";
        "std::allocator_traits<std::allocator<char32_t>>::pointer";
        "std::allocator_traits<std::allocator<char32_t>>::propagate_on_container_copy_assignment";
        "std::allocator_traits<std::allocator<char32_t>>::propagate_on_container_move_assignment";
        "std::allocator_traits<std::allocator<char32_t>>::propagate_on_container_swap";
        "std::allocator_traits<std::allocator<char32_t>>::size_type";
        "std::allocator_traits<std::allocator<char32_t>>::value_type";
        "std::allocator_traits<std::allocator<char32_t>>::void_pointer";
        "std::allocator_traits<std::allocator<void>>::allocator_type";
        "std::allocator_traits<std::allocator<void>>::const_pointer";
        "std::allocator_traits<std::allocator<void>>::const_void_pointer";
        "std::allocator_traits<std::allocator<void>>::difference_type";
        "std::allocator_traits<std::allocator<void>>::is_always_equal";
        "std::allocator_traits<std::allocator<void>>::pointer";
        "std::allocator_traits<std::allocator<void>>::propagate_on_container_copy_assignment";
        "std::allocator_traits<std::allocator<void>>::propagate_on_container_move_assignment";
        "std::allocator_traits<std::allocator<void>>::propagate_on_container_swap";
        "std::allocator_traits<std::allocator<void>>::size_type";
        "std::allocator_traits<std::allocator<void>>::value_type";
        "std::allocator_traits<std::allocator<void>>::void_pointer";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::allocator_type";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::const_pointer";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::const_void_pointer";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::difference_type";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::is_always_equal";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::pointer";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::propagate_on_container_copy_assignment";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::propagate_on_container_move_assignment";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::propagate_on_container_swap";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::size_type";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::value_type";
        "std::allocator_traits<std::allocator<std::_List_node<std::vector<int, std::allocator<int>>>>>::void_pointer";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::allocator_type";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::const_pointer";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::const_void_pointer";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::difference_type";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::is_always_equal";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::pointer";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::propagate_on_container_copy_assignment";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::propagate_on_container_move_assignment";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::propagate_on_container_swap";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::size_type";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::value_type";
        "std::allocator_traits<std::allocator<std::vector<int, std::allocator<int>>>>::void_pointer";
        "std::basic_ios<char, std::char_traits<char>>::__ctype_type";
        "std::basic_ios<char, std::char_traits<char>>::__num_get_type";
        "std::basic_ios<char, std::char_traits<char>>::__num_put_type";
        "std::basic_ios<char, std::char_traits<char>>::char_type";
        "std::basic_ios<char, std::char_traits<char>>::int_type";
        "std::basic_ios<char, std::char_traits<char>>::off_type";
        "std::basic_ios<char, std::char_traits<char>>::pos_type";
        "std::basic_ios<char, std::char_traits<char>>::traits_type";
        "std::basic_ios<wchar_t, std::char_traits<wchar_t>>::__ctype_type";
        "std::basic_ios<wchar_t, std::char_traits<wchar_t>>::__num_get_type";
        "std::basic_ios<wchar_t, std::char_traits<wchar_t>>::__num_put_type";
        "std::basic_ios<wchar_t, std::char_traits<wchar_t>>::char_type";
        "std::basic_ios<wchar_t, std::char_traits<wchar_t>>::int_type";
        "std::basic_ios<wchar_t, std::char_traits<wchar_t>>::off_type";
        "std::basic_ios<wchar_t, std::char_traits<wchar_t>>::pos_type";
        "std::basic_ios<wchar_t, std::char_traits<wchar_t>>::traits_type";
        "std::basic_iostream<char, std::char_traits<char>>::__istream_type";
        "std::basic_iostream<char, std::char_traits<char>>::__ostream_type";
        "std::basic_iostream<char, std::char_traits<char>>::char_type";
        "std::basic_iostream<char, std::char_traits<char>>::int_type";
        "std::basic_iostream<char, std::char_traits<char>>::off_type";
        "std::basic_iostream<char, std::char_traits<char>>::pos_type";
        "std::basic_iostream<char, std::char_traits<char>>::traits_type";
        "std::basic_iostream<wchar_t, std::char_traits<wchar_t>>::__istream_type";
        "std::basic_iostream<wchar_t, std::char_traits<wchar_t>>::__ostream_type";
        "std::basic_iostream<wchar_t, std::char_traits<wchar_t>>::char_type";
        "std::basic_iostream<wchar_t, std::char_traits<wchar_t>>::int_type";
        "std::basic_iostream<wchar_t, std::char_traits<wchar_t>>::off_type";
        "std::basic_iostream<wchar_t, std::char_traits<wchar_t>>::pos_type";
        "std::basic_iostream<wchar_t, std::char_traits<wchar_t>>::traits_type";
        "std::basic_istream<char, std::char_traits<char>>::__ctype_type";
        "std::basic_istream<char, std::char_traits<char>>::__ios_type";
        "std::basic_istream<char, std::char_traits<char>>::__istream_type";
        "std::basic_istream<char, std::char_traits<char>>::__num_get_type";
        "std::basic_istream<char, std::char_traits<char>>::__streambuf_type";
        "std::basic_istream<char, std::char_traits<char>>::char_type";
        "std::basic_istream<char, std::char_traits<char>>::int_type";
        "std::basic_istream<char, std::char_traits<char>>::off_type";
        "std::basic_istream<char, std::char_traits<char>>::pos_type";
        "std::basic_istream<char, std::char_traits<char>>::sentry";
        "std::basic_istream<char, std::char_traits<char>>::traits_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::__ctype_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::__ios_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::__istream_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::__num_get_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::__streambuf_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::char_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::int_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::off_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::pos_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::sentry";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::traits_type";
        "std::basic_ostream<char, std::char_traits<char>>::__ctype_type";
        "std::basic_ostream<char, std::char_traits<char>>::__ios_type";
        "std::basic_ostream<char, std::char_traits<char>>::__num_put_type";
        "std::basic_ostream<char, std::char_traits<char>>::__ostream_type";
        "std::basic_ostream<char, std::char_traits<char>>::__streambuf_type";
        "std::basic_ostream<char, std::char_traits<char>>::char_type";
        "std::basic_ostream<char, std::char_traits<char>>::int_type";
        "std::basic_ostream<char, std::char_traits<char>>::off_type";
        "std::basic_ostream<char, std::char_traits<char>>::pos_type";
        "std::basic_ostream<char, std::char_traits<char>>::sentry";
        "std::basic_ostream<char, std::char_traits<char>>::traits_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::__ctype_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::__ios_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::__num_put_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::__ostream_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::__streambuf_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::char_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::int_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::off_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::pos_type";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::sentry";
        "std::basic_ostream<wchar_t, std::char_traits<wchar_t>>::traits_type";
        "std::basic_streambuf<char, std::char_traits<char>>::__streambuf_type";
        "std::basic_streambuf<char, std::char_traits<char>>::char_type";
        "std::basic_streambuf<char, std::char_traits<char>>::int_type";
        "std::basic_streambuf<char, std::char_traits<char>>::off_type";
        "std::basic_streambuf<char, std::char_traits<char>>::pos_type";
        "std::basic_streambuf<char, std::char_traits<char>>::traits_type";
        "std::basic_streambuf<wchar_t, std::char_traits<wchar_t>>::__streambuf_type";
        "std::basic_streambuf<wchar_t, std::char_traits<wchar_t>>::char_type";
        "std::basic_streambuf<wchar_t, std::char_traits<wchar_t>>::int_type";
        "std::basic_streambuf<wchar_t, std::char_traits<wchar_t>>::off_type";
        "std::basic_streambuf<wchar_t, std::char_traits<wchar_t>>::pos_type";
        "std::basic_streambuf<wchar_t, std::char_traits<wchar_t>>::traits_type";
        "std::basic_string_view<char, std::char_traits<char>>::const_iterator";
        "std::basic_string_view<char, std::char_traits<char>>::const_pointer";
        "std::basic_string_view<char, std::char_traits<char>>::const_reference";
        "std::basic_string_view<char, std::char_traits<char>>::const_reverse_iterator";
        "std::basic_string_view<char, std::char_traits<char>>::difference_type";
        "std::basic_string_view<char, std::char_traits<char>>::iterator";
        "std::basic_string_view<char, std::char_traits<char>>::pointer";
        "std::basic_string_view<char, std::char_traits<char>>::reference";
        "std::basic_string_view<char, std::char_traits<char>>::reverse_iterator";
        "std::basic_string_view<char, std::char_traits<char>>::size_type";
        "std::basic_string_view<char, std::char_traits<char>>::traits_type";
        "std::basic_string_view<char, std::char_traits<char>>::value_type";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::const_iterator";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::const_pointer";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::const_reference";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::const_reverse_iterator";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::difference_type";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::iterator";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::pointer";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::reference";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::reverse_iterator";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::size_type";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::traits_type";
        "std::basic_string_view<wchar_t, std::char_traits<wchar_t>>::value_type";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::const_iterator";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::const_pointer";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::const_reference";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::const_reverse_iterator";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::difference_type";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::iterator";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::pointer";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::reference";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::reverse_iterator";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::size_type";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::traits_type";
        "std::basic_string_view<char16_t, std::char_traits<char16_t>>::value_type";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::const_iterator";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::const_pointer";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::const_reference";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::const_reverse_iterator";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::difference_type";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::iterator";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::pointer";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::reference";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::reverse_iterator";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::size_type";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::traits_type";
        "std::basic_string_view<char32_t, std::char_traits<char32_t>>::value_type";
        "std::binary_function<const volatile void*, const volatile void*, bool>::first_argument_type";
        "std::binary_function<const volatile void*, const volatile void*, bool>::result_type";
        "std::binary_function<const volatile void*, const volatile void*, bool>::second_argument_type";
        "std::binary_function<const std::_V2::error_category*, const std::_V2::error_category*, bool>::first_argument_type";
        "std::binary_function<const std::_V2::error_category*, const std::_V2::error_category*, bool>::result_type";
        "std::binary_function<const std::_V2::error_category*, const std::_V2::error_category*, bool>::second_argument_type";
        "std::bit_and<void>::is_transparent"; "std::bit_not<void>::is_transparent";
        "std::bit_or<void>::is_transparent"; "std::bit_xor<void>::is_transparent";
        "std::char_traits<char>::char_type"; "std::char_traits<char>::int_type";
        "std::char_traits<char>::off_type"; "std::char_traits<char>::pos_type";
        "std::char_traits<char>::state_type"; "std::char_traits<wchar_t>::char_type";
        "std::char_traits<wchar_t>::int_type"; "std::char_traits<wchar_t>::off_type";
        "std::char_traits<wchar_t>::pos_type"; "std::char_traits<wchar_t>::state_type";
        "std::char_traits<char16_t>::char_type"; "std::char_traits<char16_t>::int_type";
        "std::char_traits<char16_t>::off_type"; "std::char_traits<char16_t>::pos_type";
        "std::char_traits<char16_t>::state_type"; "std::char_traits<char32_t>::char_type";
        "std::char_traits<char32_t>::int_type"; "std::char_traits<char32_t>::off_type";
        "std::char_traits<char32_t>::pos_type"; "std::char_traits<char32_t>::state_type";
        "std::ctype<char>::char_type"; "std::ctype<wchar_t>::__wmask_type";
        "std::ctype<wchar_t>::char_type"; "std::divides<void>::is_transparent";
        Nscoped (Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "int*"]) (Nid "type");
        Nscoped (Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "void"]) (Nid "type");
        Nscoped (Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "std::allocator<char>"]) (Nid "type");
        Nscoped (Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "std::allocator<wchar_t>"]) (Nid "type");
        Nscoped (Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "std::allocator<char16_t>"]) (Nid "type");
        Nscoped (Ninst "std::enable_if" [Avalue (Eint 1 "bool"); Atype "std::allocator<char32_t>"]) (Nid "type");
        "std::equal_to<void>::is_transparent"; "std::greater<void>::is_transparent";
        "std::greater_equal<void>::is_transparent"; "std::initializer_list<int>::const_iterator";
        "std::initializer_list<int>::const_reference"; "std::initializer_list<int>::iterator";
        "std::initializer_list<int>::reference"; "std::initializer_list<int>::size_type";
        "std::initializer_list<int>::value_type"; "std::initializer_list<char>::const_iterator";
        "std::initializer_list<char>::const_reference"; "std::initializer_list<char>::iterator";
        "std::initializer_list<char>::reference"; "std::initializer_list<char>::size_type";
        "std::initializer_list<char>::value_type"; "std::initializer_list<wchar_t>::const_iterator";
        "std::initializer_list<wchar_t>::const_reference"; "std::initializer_list<wchar_t>::iterator";
        "std::initializer_list<wchar_t>::reference"; "std::initializer_list<wchar_t>::size_type";
        "std::initializer_list<wchar_t>::value_type"; "std::initializer_list<char16_t>::const_iterator";
        "std::initializer_list<char16_t>::const_reference"; "std::initializer_list<char16_t>::iterator";
        "std::initializer_list<char16_t>::reference"; "std::initializer_list<char16_t>::size_type";
        "std::initializer_list<char16_t>::value_type"; "std::initializer_list<char32_t>::const_iterator";
        "std::initializer_list<char32_t>::const_reference"; "std::initializer_list<char32_t>::iterator";
        "std::initializer_list<char32_t>::reference"; "std::initializer_list<char32_t>::size_type";
        "std::initializer_list<char32_t>::value_type"; "std::initializer_list<bool>::const_iterator";
        "std::initializer_list<bool>::const_reference"; "std::initializer_list<bool>::iterator";
        "std::initializer_list<bool>::reference"; "std::initializer_list<bool>::size_type";
        "std::initializer_list<bool>::value_type"; "std::integral_constant<unsigned long, 0ul>::type";
        "std::integral_constant<unsigned long, 0ul>::value_type"; "std::integral_constant<unsigned long, 2ul>::type";
        "std::integral_constant<unsigned long, 2ul>::value_type";
        Nscoped (Ninst "std::integral_constant" [Atype "bool"; Avalue (Eint 0 "bool")]) (Nid "type");
        Nscoped (Ninst "std::integral_constant" [Atype "bool"; Avalue (Eint 0 "bool")]) (Nid "value_type");
        Nscoped (Ninst "std::integral_constant" [Atype "bool"; Avalue (Eint 1 "bool")]) (Nid "type");
        Nscoped (Ninst "std::integral_constant" [Atype "bool"; Avalue (Eint 1 "bool")]) (Nid "value_type");
        "std::iterator<std::output_iterator_tag, void, void, void, void>::difference_type";
        "std::iterator<std::output_iterator_tag, void, void, void, void>::iterator_category";
        "std::iterator<std::output_iterator_tag, void, void, void, void>::pointer";
        "std::iterator<std::output_iterator_tag, void, void, void, void>::reference";
        "std::iterator<std::output_iterator_tag, void, void, void, void>::value_type";
        "std::iterator<std::random_access_iterator_tag, bool, long, std::_Bit_reference*, std::_Bit_reference>::difference_type";
        "std::iterator<std::random_access_iterator_tag, bool, long, std::_Bit_reference*, std::_Bit_reference>::iterator_category";
        "std::iterator<std::random_access_iterator_tag, bool, long, std::_Bit_reference*, std::_Bit_reference>::pointer";
        "std::iterator<std::random_access_iterator_tag, bool, long, std::_Bit_reference*, std::_Bit_reference>::reference";
        "std::iterator<std::random_access_iterator_tag, bool, long, std::_Bit_reference*, std::_Bit_reference>::value_type";
        "std::iterator<std::random_access_iterator_tag, bool, long, bool*, bool&>::difference_type";
        "std::iterator<std::random_access_iterator_tag, bool, long, bool*, bool&>::iterator_category";
        "std::iterator<std::random_access_iterator_tag, bool, long, bool*, bool&>::pointer";
        "std::iterator<std::random_access_iterator_tag, bool, long, bool*, bool&>::reference";
        "std::iterator<std::random_access_iterator_tag, bool, long, bool*, bool&>::value_type";
        "std::iterator<std::random_access_iterator_tag, bool, long, const bool*, bool>::difference_type";
        "std::iterator<std::random_access_iterator_tag, bool, long, const bool*, bool>::iterator_category";
        "std::iterator<std::random_access_iterator_tag, bool, long, const bool*, bool>::pointer";
        "std::iterator<std::random_access_iterator_tag, bool, long, const bool*, bool>::reference";
        "std::iterator<std::random_access_iterator_tag, bool, long, const bool*, bool>::value_type";
        "std::iterator_traits<int*>::difference_type"; "std::iterator_traits<int*>::iterator_category";
        "std::iterator_traits<int*>::pointer"; "std::iterator_traits<int*>::reference";
        "std::iterator_traits<int*>::value_type"; "std::iterator_traits<char*>::difference_type";
        "std::iterator_traits<char*>::iterator_category"; "std::iterator_traits<char*>::pointer";
        "std::iterator_traits<char*>::reference"; "std::iterator_traits<char*>::value_type";
        "std::iterator_traits<wchar_t*>::difference_type"; "std::iterator_traits<wchar_t*>::iterator_category";
        "std::iterator_traits<wchar_t*>::pointer"; "std::iterator_traits<wchar_t*>::reference";
        "std::iterator_traits<wchar_t*>::value_type"; "std::iterator_traits<char16_t*>::difference_type";
        "std::iterator_traits<char16_t*>::iterator_category"; "std::iterator_traits<char16_t*>::pointer";
        "std::iterator_traits<char16_t*>::reference"; "std::iterator_traits<char16_t*>::value_type";
        "std::iterator_traits<char32_t*>::difference_type"; "std::iterator_traits<char32_t*>::iterator_category";
        "std::iterator_traits<char32_t*>::pointer"; "std::iterator_traits<char32_t*>::reference";
        "std::iterator_traits<char32_t*>::value_type"; "std::iterator_traits<const int*>::difference_type";
        "std::iterator_traits<const int*>::iterator_category"; "std::iterator_traits<const int*>::pointer";
        "std::iterator_traits<const int*>::reference"; "std::iterator_traits<const int*>::value_type";
        "std::iterator_traits<const char*>::difference_type"; "std::iterator_traits<const char*>::iterator_category";
        "std::iterator_traits<const char*>::pointer"; "std::iterator_traits<const char*>::reference";
        "std::iterator_traits<const char*>::value_type"; "std::iterator_traits<const wchar_t*>::difference_type";
        "std::iterator_traits<const wchar_t*>::iterator_category"; "std::iterator_traits<const wchar_t*>::pointer";
        "std::iterator_traits<const wchar_t*>::reference"; "std::iterator_traits<const wchar_t*>::value_type";
        "std::iterator_traits<const char16_t*>::difference_type";
        "std::iterator_traits<const char16_t*>::iterator_category"; "std::iterator_traits<const char16_t*>::pointer";
        "std::iterator_traits<const char16_t*>::reference"; "std::iterator_traits<const char16_t*>::value_type";
        "std::iterator_traits<const char32_t*>::difference_type";
        "std::iterator_traits<const char32_t*>::iterator_category"; "std::iterator_traits<const char32_t*>::pointer";
        "std::iterator_traits<const char32_t*>::reference"; "std::iterator_traits<const char32_t*>::value_type";
        "std::less<void>::is_transparent"; "std::less_equal<void>::is_transparent";
        "std::logical_and<void>::is_transparent"; "std::logical_not<void>::is_transparent";
        "std::logical_or<void>::is_transparent"; "std::minus<void>::is_transparent";
        "std::modulus<void>::is_transparent"; "std::multiplies<void>::is_transparent";
        "std::negate<void>::is_transparent"; "std::not_equal_to<void>::is_transparent";
        "std::num_get<char, std::istreambuf_iterator<char, std::char_traits<char>>>::char_type";
        "std::num_get<char, std::istreambuf_iterator<char, std::char_traits<char>>>::iter_type";
        "std::num_get<wchar_t, std::istreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>::char_type";
        "std::num_get<wchar_t, std::istreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>::iter_type";
        "std::num_put<char, std::ostreambuf_iterator<char, std::char_traits<char>>>::char_type";
        "std::num_put<char, std::ostreambuf_iterator<char, std::char_traits<char>>>::iter_type";
        "std::num_put<wchar_t, std::ostreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>::char_type";
        "std::num_put<wchar_t, std::ostreambuf_iterator<wchar_t, std::char_traits<wchar_t>>>::iter_type";
        "std::plus<void>::is_transparent"; "std::pointer_traits<int*>::difference_type";
        "std::pointer_traits<int*>::element_type"; "std::pointer_traits<int*>::pointer";
        "std::pointer_traits<char*>::difference_type"; "std::pointer_traits<char*>::element_type";
        "std::pointer_traits<char*>::pointer"; "std::pointer_traits<wchar_t*>::difference_type";
        "std::pointer_traits<wchar_t*>::element_type"; "std::pointer_traits<wchar_t*>::pointer";
        "std::pointer_traits<char16_t*>::difference_type"; "std::pointer_traits<char16_t*>::element_type";
        "std::pointer_traits<char16_t*>::pointer"; "std::pointer_traits<char32_t*>::difference_type";
        "std::pointer_traits<char32_t*>::element_type"; "std::pointer_traits<char32_t*>::pointer";
        "std::pointer_traits<const char*>::difference_type"; "std::pointer_traits<const char*>::element_type";
        "std::pointer_traits<const char*>::pointer"; "std::pointer_traits<const wchar_t*>::difference_type";
        "std::pointer_traits<const wchar_t*>::element_type"; "std::pointer_traits<const wchar_t*>::pointer";
        "std::pointer_traits<const char16_t*>::difference_type"; "std::pointer_traits<const char16_t*>::element_type";
        "std::pointer_traits<const char16_t*>::pointer"; "std::pointer_traits<const char32_t*>::difference_type";
        "std::pointer_traits<const char32_t*>::element_type"; "std::pointer_traits<const char32_t*>::pointer";
        "std::remove_all_extents<std::vector<int, std::allocator<int>>>::type"; "std::remove_cv<int*>::type";
        "std::remove_cv<unsigned short>::type"; "std::remove_cv<int>::type";
        "std::remove_cv<unsigned int>::type"; "std::remove_cv<wchar_t>::type";
        "std::remove_cv<char16_t>::type"; "std::remove_cv<char32_t>::type";
        "std::remove_cv<std::vector<int, std::allocator<int>>>::type"; "std::remove_reference<int&>::type";
        "std::remove_reference<std::allocator<char>&>::type";
        "std::remove_reference<std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&>::type";
        "std::remove_reference<std::__cxx11::to_string(int)::@0&>::type";
        "std::remove_reference<std::__cxx11::to_string(unsigned int)::@0&>::type";
        "std::remove_reference<std::__cxx11::to_string(long)::@0&>::type";
        "std::remove_reference<std::__cxx11::to_string(unsigned long)::@0&>::type";
        "std::remove_reference<std::__cxx11::to_string(long long)::@0&>::type";
        "std::remove_reference<std::__cxx11::to_string(unsigned long long)::@0&>::type";
        "std::remove_reference<const std::vector<int, std::allocator<int>>&>::type";
        "std::remove_reference<int>::type"; "std::reverse_iterator<std::_Bit_const_iterator>::__traits_type";
        "std::reverse_iterator<std::_Bit_const_iterator>::difference_type";
        "std::reverse_iterator<std::_Bit_const_iterator>::iterator_type";
        "std::reverse_iterator<std::_Bit_const_iterator>::pointer";
        "std::reverse_iterator<std::_Bit_const_iterator>::reference";
        "std::reverse_iterator<std::_Bit_iterator>::__traits_type";
        "std::reverse_iterator<std::_Bit_iterator>::difference_type";
        "std::reverse_iterator<std::_Bit_iterator>::iterator_type";
        "std::reverse_iterator<std::_Bit_iterator>::pointer"; "std::reverse_iterator<std::_Bit_iterator>::reference";
        "std::vector<int, std::allocator<int>>::_Alloc_traits"; "std::vector<int, std::allocator<int>>::_Base";
        "std::vector<int, std::allocator<int>>::_Temporary_value";
        "std::vector<int, std::allocator<int>>::_Tp_alloc_type";
        "std::vector<int, std::allocator<int>>::allocator_type";
        "std::vector<int, std::allocator<int>>::const_iterator";
        "std::vector<int, std::allocator<int>>::const_pointer";
        "std::vector<int, std::allocator<int>>::const_reference";
        "std::vector<int, std::allocator<int>>::const_reverse_iterator";
        "std::vector<int, std::allocator<int>>::difference_type"; "std::vector<int, std::allocator<int>>::iterator";
        "std::vector<int, std::allocator<int>>::pointer"; "std::vector<int, std::allocator<int>>::reference";
        "std::vector<int, std::allocator<int>>::reverse_iterator"; "std::vector<int, std::allocator<int>>::size_type";
        "std::vector<int, std::allocator<int>>::value_type"; "std::_Destroy<int*>(int*, int* )::_Value_type";
        Nscoped
          (Ninst "std::__copy_move_a2(const int*, const int*, int* )"
             [Avalue (Eint 0 "bool"); Atype "const int*"; Atype "int*"])
          (Nid "_Category");
        "std::uninitialized_copy<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, int*>(__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, __gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, int* )::_From";
        "std::uninitialized_copy<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, int*>(__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, __gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, int* )::_ValueType1";
        "std::uninitialized_copy<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, int*>(__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, __gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>, int* )::_ValueType2";
        "std::__cxx11::_List_base<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_List_impl";
        "std::__cxx11::_List_base<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Node_alloc_traits";
        "std::__cxx11::_List_base<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Node_alloc_type";
        "std::__cxx11::_List_base<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Tp_alloc_traits";
        "std::__cxx11::_List_base<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Tp_alloc_type";
        "std::__cxx11::_List_base<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::allocator_type";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::_Alloc_hider";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::_Alloc_traits";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::_Char_alloc_type";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__const_iterator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__sv_type";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::__sv_wrapper";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::allocator_type";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::const_iterator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::const_pointer";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::const_reference";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::const_reverse_iterator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::difference_type";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::iterator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::pointer";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::reference";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::reverse_iterator";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::size_type";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::traits_type";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::value_type";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::._M_local_buf";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::._S_local_capacity";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::_Alloc_hider";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::_Alloc_traits";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::_Char_alloc_type";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::__const_iterator";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::__sv_type";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::__sv_wrapper";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::allocator_type";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::const_iterator";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::const_pointer";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::const_reference";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::const_reverse_iterator";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::difference_type";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::iterator";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::pointer";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::reference";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::reverse_iterator";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::size_type";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::traits_type";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::value_type";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::._M_local_buf";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::._S_local_capacity";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::_Alloc_hider";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::_Alloc_traits";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::_Char_alloc_type";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::__const_iterator";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::__sv_type";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::__sv_wrapper";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::allocator_type";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::const_iterator";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::const_pointer";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::const_reference";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::const_reverse_iterator";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::difference_type";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::iterator";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::pointer";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::reference";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::reverse_iterator";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::size_type";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::traits_type";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::value_type";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::._M_local_buf";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::._S_local_capacity";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::_Alloc_hider";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::_Alloc_traits";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::_Char_alloc_type";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::__const_iterator";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::__sv_type";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::__sv_wrapper";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::allocator_type";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::const_iterator";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::const_pointer";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::const_reference";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::const_reverse_iterator";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::difference_type";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::iterator";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::pointer";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::reference";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::reverse_iterator";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::size_type";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::traits_type";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::value_type";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::._M_local_buf";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::._S_local_capacity";
        "std::__cxx11::collate<char>::char_type"; "std::__cxx11::collate<char>::string_type";
        "std::__cxx11::collate<wchar_t>::char_type"; "std::__cxx11::collate<wchar_t>::string_type";
        "std::__cxx11::collate_byname<char>::char_type"; "std::__cxx11::collate_byname<char>::string_type";
        "std::__cxx11::collate_byname<wchar_t>::char_type"; "std::__cxx11::collate_byname<wchar_t>::string_type";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Base";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Finalize_merge";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Node";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Node_alloc_traits";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Node_alloc_type";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Tp_alloc_traits";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_Tp_alloc_type";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::__remove_return_type";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::allocator_type";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::const_iterator";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::const_pointer";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::const_reference";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::const_reverse_iterator";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::difference_type";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::iterator";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::pointer";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::reference";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::reverse_iterator";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::size_type";
        "std::__cxx11::list<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::value_type";
        "std::__cxx11::numpunct<char>::__cache_type"; "std::__cxx11::numpunct<char>::char_type";
        "std::__cxx11::numpunct<char>::string_type"; "std::__cxx11::numpunct<wchar_t>::__cache_type";
        "std::__cxx11::numpunct<wchar_t>::char_type"; "std::__cxx11::numpunct<wchar_t>::string_type";
        "std::__cxx11::numpunct_byname<char>::char_type"; "std::__cxx11::numpunct_byname<char>::string_type";
        "std::__cxx11::numpunct_byname<wchar_t>::char_type"; "std::__cxx11::numpunct_byname<wchar_t>::string_type";
        Nscoped
          (Ninst "std::__make_unsigned_selector_base::__select"
             [Avalue (Eint 2 "unsigned long");
              Atype
                (Tnamed
                   (Ninst "std::__make_unsigned_selector_base::_List"
                      [Apack
                         [Atype "unsigned short"; Atype "unsigned int"; Atype "unsigned long";
                          Atype "unsigned long long"]]));
              Avalue (Eint 1 "bool")])
          (Nid "__type");
        Nscoped
          (Ninst "std::__make_unsigned_selector_base::__select"
             [Avalue (Eint 4 "unsigned long");
              Atype
                (Tnamed
                   (Ninst "std::__make_unsigned_selector_base::_List"
                      [Apack [Atype "unsigned int"; Atype "unsigned long"; Atype "unsigned long long"]]));
              Avalue (Eint 1 "bool")])
          (Nid "__type");
        "__atomic_wide_counter::@__value32"; "__cxxabiv1::__class_type_info";
        "__cxxabiv1::__cxa_refcounted_exception"; "__cxxabiv1::__forced_unwind"; "__mbstate_t::@__value";
        "std::_Bit_const_iterator"; "std::_Bit_iterator"; "std::_Bit_iterator_base";
        "std::_Bit_reference"; "std::_Bit_type"; "std::_Fnv_hash_impl"; "std::_Hash_impl";
        "std::_Ios_Fmtflags"; "std::_Ios_Iostate"; "std::_Ios_Openmode"; "std::_Ios_Seekdir";
        "std::_Swallow_assign"; "std::__allocator_traits_base"; "std::__c_locale";
        "std::__cow_string"; "std::__do_common_type_impl"; "std::__do_is_destructible_impl";
        "std::__do_is_implicitly_default_constructible_impl"; "std::__do_is_nt_destructible_impl";
        "std::__erased_type"; "std::__failure_type"; "std::__false_type";
        "std::__invoke_memfun_deref"; "std::__invoke_memfun_ref"; "std::__invoke_memobj_deref";
        "std::__invoke_memobj_ref"; "std::__invoke_other"; "std::__is_transparent";
        "std::__make_unsigned_selector_base"; "std::__nonesuch"; "std::__nonesuchbase";
        "std::__num_base"; "std::__result_of_memfun_deref_impl"; "std::__result_of_memfun_ref_impl";
        "std::__result_of_memobj_deref_impl"; "std::__result_of_memobj_ref_impl";
        "std::__result_of_other_impl"; "std::__sso_string"; "std::__true_type";
        "std::__undefined"; "std::__uses_alloc0"; "std::__uses_alloc_base"; "std::align_val_t";
        "std::allocator_arg_t"; "std::bad_alloc"; "std::bad_array_new_length"; "std::bad_cast";
        "std::bad_exception"; "std::bad_typeid"; "std::bidirectional_iterator_tag"; "std::byte";
        "std::codecvt_base"; "std::ctype_base"; "std::domain_error"; "std::errc";
        "std::error_code"; "std::error_condition"; "std::exception"; "std::false_type";
        "std::filebuf"; "std::forward_iterator_tag"; "std::fstream"; "std::ifstream";
        "std::in_place_t"; "std::input_iterator_tag"; "std::invalid_argument"; "std::io_errc";
        "std::ios"; "std::ios_base"; "std::iostream"; "std::istream";
        "std::istringstream"; "std::length_error"; "std::locale"; "std::logic_error";
        "std::messages_base"; "std::money_base"; "std::nested_exception"; "std::new_handler";
        "std::nothrow_t"; "std::nullptr_t"; "std::ofstream"; "std::ostream";
        "std::ostringstream"; "std::out_of_range"; "std::output_iterator_tag";
        "std::overflow_error"; "std::piecewise_construct_t"; "std::ptrdiff_t";
        "std::random_access_iterator_tag"; "std::range_error"; "std::runtime_error";
        "std::size_t"; "std::streambuf"; "std::streamoff"; "std::streampos";
        "std::streamsize"; "std::string"; "std::string_view"; "std::stringbuf";
        "std::stringstream"; "std::system_error"; "std::terminate_handler"; "std::time_base";
        "std::true_type"; "std::type_info"; "std::u16streampos"; "std::u16string";
        "std::u16string_view"; "std::u32streampos"; "std::u32string"; "std::u32string_view";
        "std::underflow_error"; "std::unexpected_handler"; "std::wfilebuf"; "std::wfstream";
        "std::wifstream"; "std::wios"; "std::wiostream"; "std::wistream";
        "std::wistringstream"; "std::wofstream"; "std::wostream"; "std::wostringstream";
        "std::wstreambuf"; "std::wstreampos"; "std::wstring"; "std::wstring_view";
        "std::wstringbuf"; "std::wstringstream"; "std::._S_word_bit";
        ".PTHREAD_CANCEL_DEFERRED::PTHREAD_CANCEL_ASYNCHRONOUS"; ".PTHREAD_CANCEL_DEFERRED::PTHREAD_CANCEL_DEFERRED";
        ".PTHREAD_CANCEL_ENABLE::PTHREAD_CANCEL_DISABLE"; ".PTHREAD_CANCEL_ENABLE::PTHREAD_CANCEL_ENABLE";
        ".PTHREAD_CREATE_JOINABLE::PTHREAD_CREATE_DETACHED"; ".PTHREAD_CREATE_JOINABLE::PTHREAD_CREATE_JOINABLE";
        ".PTHREAD_INHERIT_SCHED::PTHREAD_EXPLICIT_SCHED"; ".PTHREAD_INHERIT_SCHED::PTHREAD_INHERIT_SCHED";
        ".PTHREAD_MUTEX_STALLED::PTHREAD_MUTEX_ROBUST"; ".PTHREAD_MUTEX_STALLED::PTHREAD_MUTEX_ROBUST_NP";
        ".PTHREAD_MUTEX_STALLED::PTHREAD_MUTEX_STALLED"; ".PTHREAD_MUTEX_STALLED::PTHREAD_MUTEX_STALLED_NP";
        ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_ADAPTIVE_NP"; ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_DEFAULT";
        ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_ERRORCHECK"; ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_ERRORCHECK_NP";
        ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_FAST_NP"; ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_NORMAL";
        ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_RECURSIVE"; ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_RECURSIVE_NP";
        ".PTHREAD_MUTEX_TIMED_NP::PTHREAD_MUTEX_TIMED_NP"; ".PTHREAD_PRIO_NONE::PTHREAD_PRIO_INHERIT";
        ".PTHREAD_PRIO_NONE::PTHREAD_PRIO_NONE"; ".PTHREAD_PRIO_NONE::PTHREAD_PRIO_PROTECT";
        ".PTHREAD_PROCESS_PRIVATE::PTHREAD_PROCESS_PRIVATE"; ".PTHREAD_PROCESS_PRIVATE::PTHREAD_PROCESS_SHARED";
        ".PTHREAD_RWLOCK_PREFER_READER_NP::PTHREAD_RWLOCK_DEFAULT_NP";
        ".PTHREAD_RWLOCK_PREFER_READER_NP::PTHREAD_RWLOCK_PREFER_READER_NP";
        ".PTHREAD_RWLOCK_PREFER_READER_NP::PTHREAD_RWLOCK_PREFER_WRITER_NONRECURSIVE_NP";
        ".PTHREAD_RWLOCK_PREFER_READER_NP::PTHREAD_RWLOCK_PREFER_WRITER_NP";
        ".PTHREAD_SCOPE_SYSTEM::PTHREAD_SCOPE_PROCESS"; ".PTHREAD_SCOPE_SYSTEM::PTHREAD_SCOPE_SYSTEM";
        "._ISupper::_ISalnum"; "._ISupper::_ISalpha"; "._ISupper::_ISblank";
        "._ISupper::_IScntrl"; "._ISupper::_ISdigit"; "._ISupper::_ISgraph";
        "._ISupper::_ISlower"; "._ISupper::_ISprint"; "._ISupper::_ISpunct";
        "._ISupper::_ISspace"; "._ISupper::_ISupper"; "._ISupper::_ISxdigit";
        ".__ISwupper::_ISwalnum"; ".__ISwupper::_ISwalpha"; ".__ISwupper::_ISwblank";
        ".__ISwupper::_ISwcntrl"; ".__ISwupper::_ISwdigit"; ".__ISwupper::_ISwgraph";
        ".__ISwupper::_ISwlower"; ".__ISwupper::_ISwprint"; ".__ISwupper::_ISwpunct";
        ".__ISwupper::_ISwspace"; ".__ISwupper::_ISwupper"; ".__ISwupper::_ISwxdigit";
        ".__ISwupper::__ISwalnum"; ".__ISwupper::__ISwalpha"; ".__ISwupper::__ISwblank";
        ".__ISwupper::__ISwcntrl"; ".__ISwupper::__ISwdigit"; ".__ISwupper::__ISwgraph";
        ".__ISwupper::__ISwlower"; ".__ISwupper::__ISwprint"; ".__ISwupper::__ISwpunct";
        ".__ISwupper::__ISwspace"; ".__ISwupper::__ISwupper"; ".__ISwupper::__ISwxdigit";
        "__gnu_cxx::__is_integer_nonstrict<short>::.__width::__width";
        "__gnu_cxx::__is_integer_nonstrict<int>::.__width::__width";
        "__gnu_cxx::__is_integer_nonstrict<unsigned int>::.__width::__width";
        "__gnu_cxx::__is_integer_nonstrict<long>::.__width::__width";
        "__gnu_cxx::__is_integer_nonstrict<unsigned long>::.__width::__width";
        "__gnu_cxx::__is_integer_nonstrict<unsigned long long>::.__width::__width";
        "__gnu_cxx::__is_integer_nonstrict<char>::.__width::__width";
        "std::_Vector_base<int, std::allocator<int>>::_M_allocate(unsigned long)::_Tr";
        "std::_Vector_base<int, std::allocator<int>>::_M_deallocate(int*, unsigned long)::_Tr";
        "std::__are_same<float, float>::.__value::__value"; "std::__are_same<float, double>::.__value::__value";
        "std::__are_same<double, float>::.__value::__value"; "std::__are_same<double, double>::.__value::__value";
        "std::__are_same<long double, float>::.__value::__value";
        "std::__are_same<long double, double>::.__value::__value"; "std::__is_byte<signed char>::.__value::__value";
        "std::__is_byte<unsigned char>::.__value::__value"; "std::__is_byte<char>::.__value::__value";
        "std::__is_byte<enum std::byte>::.__value::__value"; "std::__is_char<char>::.__value::__value";
        "std::__is_char<wchar_t>::.__value::__value"; "std::__is_floating<float>::.__value::__value";
        "std::__is_floating<double>::.__value::__value"; "std::__is_floating<long double>::.__value::__value";
        "std::__is_integer<signed char>::.__value::__value"; "std::__is_integer<unsigned char>::.__value::__value";
        "std::__is_integer<short>::.__value::__value"; "std::__is_integer<unsigned short>::.__value::__value";
        "std::__is_integer<int>::.__value::__value"; "std::__is_integer<unsigned int>::.__value::__value";
        "std::__is_integer<long>::.__value::__value"; "std::__is_integer<unsigned long>::.__value::__value";
        "std::__is_integer<long long>::.__value::__value"; "std::__is_integer<unsigned long long>::.__value::__value";
        "std::__is_integer<int128_t>::.__value::__value"; "std::__is_integer<uint128_t>::.__value::__value";
        "std::__is_integer<char>::.__value::__value"; "std::__is_integer<wchar_t>::.__value::__value";
        "std::__is_integer<char16_t>::.__value::__value"; "std::__is_integer<char32_t>::.__value::__value";
        "std::__is_integer<bool>::.__value::__value"; "std::__is_integer<float>::.__value::__value";
        "std::__is_integer<double>::.__value::__value"; "std::__is_integer<long double>::.__value::__value";
        "std::__is_move_iterator<__gnu_cxx::__normal_iterator<const int*, std::vector<int, std::allocator<int>>>>::.__value::__value";
        "std::__is_nonvolatile_trivially_copyable<int>::.__value::__value"; "std::__is_void<void>::.__value::__value";
        "std::basic_istream<char, std::char_traits<char>>::sentry::__ctype_type";
        "std::basic_istream<char, std::char_traits<char>>::sentry::__int_type";
        "std::basic_istream<char, std::char_traits<char>>::sentry::__istream_type";
        "std::basic_istream<char, std::char_traits<char>>::sentry::__streambuf_type";
        "std::basic_istream<char, std::char_traits<char>>::sentry::traits_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::sentry::__ctype_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::sentry::__int_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::sentry::__istream_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::sentry::__streambuf_type";
        "std::basic_istream<wchar_t, std::char_traits<wchar_t>>::sentry::traits_type";
        "std::__cxx11::_List_base<std::vector<int, std::allocator<int>>, std::allocator<std::vector<int, std::allocator<int>>>>::_M_clear()::_Node";
        "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::._S_local_capacity::_S_local_capacity";
        "std::__cxx11::basic_string<wchar_t, std::char_traits<wchar_t>, std::allocator<wchar_t>>::._S_local_capacity::_S_local_capacity";
        "std::__cxx11::basic_string<char16_t, std::char_traits<char16_t>, std::allocator<char16_t>>::._S_local_capacity::_S_local_capacity";
        "std::__cxx11::basic_string<char32_t, std::char_traits<char32_t>, std::allocator<char32_t>>::._S_local_capacity::_S_local_capacity";
        "__gnu_cxx::__ops::_Iter_equal_to_iter"; "__gnu_cxx::__ops::_Iter_equal_to_val";
        "__gnu_cxx::__ops::_Iter_less_iter"; "__gnu_cxx::__ops::_Iter_less_val";
        "__gnu_cxx::__ops::_Val_less_iter"; "std::_Bit_const_iterator::const_iterator";
        "std::_Bit_const_iterator::const_reference"; "std::_Bit_const_iterator::pointer";
        "std::_Bit_const_iterator::reference"; "std::_Bit_iterator::iterator";
        "std::_Bit_iterator::pointer"; "std::_Bit_iterator::reference";
        "std::_Ios_Fmtflags::_S_adjustfield"; "std::_Ios_Fmtflags::_S_basefield";
        "std::_Ios_Fmtflags::_S_boolalpha"; "std::_Ios_Fmtflags::_S_dec"; "std::_Ios_Fmtflags::_S_fixed";
        "std::_Ios_Fmtflags::_S_floatfield"; "std::_Ios_Fmtflags::_S_hex";
        "std::_Ios_Fmtflags::_S_internal"; "std::_Ios_Fmtflags::_S_ios_fmtflags_end";
        "std::_Ios_Fmtflags::_S_ios_fmtflags_max"; "std::_Ios_Fmtflags::_S_ios_fmtflags_min";
        "std::_Ios_Fmtflags::_S_left"; "std::_Ios_Fmtflags::_S_oct"; "std::_Ios_Fmtflags::_S_right";
        "std::_Ios_Fmtflags::_S_scientific"; "std::_Ios_Fmtflags::_S_showbase";
        "std::_Ios_Fmtflags::_S_showpoint"; "std::_Ios_Fmtflags::_S_showpos";
        "std::_Ios_Fmtflags::_S_skipws"; "std::_Ios_Fmtflags::_S_unitbuf";
        "std::_Ios_Fmtflags::_S_uppercase"; "std::_Ios_Iostate::_S_badbit"; "std::_Ios_Iostate::_S_eofbit";
        "std::_Ios_Iostate::_S_failbit"; "std::_Ios_Iostate::_S_goodbit";
        "std::_Ios_Iostate::_S_ios_iostate_end"; "std::_Ios_Iostate::_S_ios_iostate_max";
        "std::_Ios_Iostate::_S_ios_iostate_min"; "std::_Ios_Openmode::_S_app"; "std::_Ios_Openmode::_S_ate";
        "std::_Ios_Openmode::_S_bin"; "std::_Ios_Openmode::_S_in";
        "std::_Ios_Openmode::_S_ios_openmode_end"; "std::_Ios_Openmode::_S_ios_openmode_max";
        "std::_Ios_Openmode::_S_ios_openmode_min"; "std::_Ios_Openmode::_S_noreplace";
        "std::_Ios_Openmode::_S_out"; "std::_Ios_Openmode::_S_trunc"; "std::_Ios_Seekdir::_S_beg";
        "std::_Ios_Seekdir::_S_cur"; "std::_Ios_Seekdir::_S_end"; "std::_Ios_Seekdir::_S_ios_seekdir_end";
        "std::_V2::error_category"; "std::__cow_string::._M_p"; "std::__detail::_List_node_base";
        "std::__detail::_List_node_header"; "std::__detail::_Scratch_list";
        "std::__exception_ptr::exception_ptr"; "std::__num_base::._S_iminus"; "std::__num_base::._S_ominus";
        "std::__swappable_details::__do_is_nothrow_swappable_impl";
        "std::__swappable_details::__do_is_swappable_impl";
        "std::__swappable_with_details::__do_is_nothrow_swappable_with_impl";
        "std::__swappable_with_details::__do_is_swappable_with_impl"; "std::__uses_alloc0::_Sink";
        "std::ctype_base::__to_type"; "std::ctype_base::mask"; "std::errc::address_family_not_supported";
        "std::errc::address_in_use"; "std::errc::address_not_available"; "std::errc::already_connected";
        "std::errc::argument_list_too_long"; "std::errc::argument_out_of_domain"; "std::errc::bad_address";
        "std::errc::bad_file_descriptor"; "std::errc::bad_message"; "std::errc::broken_pipe";
        "std::errc::connection_aborted"; "std::errc::connection_already_in_progress";
        "std::errc::connection_refused"; "std::errc::connection_reset"; "std::errc::cross_device_link";
        "std::errc::destination_address_required"; "std::errc::device_or_resource_busy";
        "std::errc::directory_not_empty"; "std::errc::executable_format_error"; "std::errc::file_exists";
        "std::errc::file_too_large"; "std::errc::filename_too_long"; "std::errc::function_not_supported";
        "std::errc::host_unreachable"; "std::errc::identifier_removed"; "std::errc::illegal_byte_sequence";
        "std::errc::inappropriate_io_control_operation"; "std::errc::interrupted";
        "std::errc::invalid_argument"; "std::errc::invalid_seek"; "std::errc::io_error";
        "std::errc::is_a_directory"; "std::errc::message_size"; "std::errc::network_down";
        "std::errc::network_reset"; "std::errc::network_unreachable"; "std::errc::no_buffer_space";
        "std::errc::no_child_process"; "std::errc::no_link"; "std::errc::no_lock_available";
        "std::errc::no_message"; "std::errc::no_message_available"; "std::errc::no_protocol_option";
        "std::errc::no_space_on_device"; "std::errc::no_stream_resources"; "std::errc::no_such_device";
        "std::errc::no_such_device_or_address"; "std::errc::no_such_file_or_directory";
        "std::errc::no_such_process"; "std::errc::not_a_directory"; "std::errc::not_a_socket";
        "std::errc::not_a_stream"; "std::errc::not_connected"; "std::errc::not_enough_memory";
        "std::errc::not_supported"; "std::errc::operation_canceled"; "std::errc::operation_in_progress";
        "std::errc::operation_not_permitted"; "std::errc::operation_not_supported";
        "std::errc::operation_would_block"; "std::errc::owner_dead"; "std::errc::permission_denied";
        "std::errc::protocol_error"; "std::errc::protocol_not_supported";
        "std::errc::read_only_file_system"; "std::errc::resource_deadlock_would_occur";
        "std::errc::resource_unavailable_try_again"; "std::errc::result_out_of_range";
        "std::errc::state_not_recoverable"; "std::errc::stream_timeout"; "std::errc::text_file_busy";
        "std::errc::timed_out"; "std::errc::too_many_files_open";
        "std::errc::too_many_files_open_in_system"; "std::errc::too_many_links";
        "std::errc::too_many_symbolic_link_levels"; "std::errc::value_too_large";
        "std::errc::wrong_protocol_type"; "std::io_errc::stream"; "std::ios_base::Init";
        "std::ios_base::_Callback_list"; "std::ios_base::_Words"; "std::ios_base::event";
        "std::ios_base::event_callback"; "std::ios_base::failure"; "std::ios_base::fmtflags";
        "std::ios_base::iostate"; "std::ios_base::openmode"; "std::ios_base::seekdir";
        "std::ios_base::._S_local_word_size"; "std::locale::_Impl"; "std::locale::category";
        "std::locale::facet"; "std::locale::id"; "std::locale::._S_categories_size";
        "std::pmr::memory_resource"; "std::pmr::string"; "std::pmr::u16string";
        "std::pmr::u32string"; "std::pmr::wstring"; "std::._S_word_bit::_S_word_bit";
        "std::__cxx11::__to_wstring_numeric(std::basic_string_view<char, std::char_traits<char>>)::@0";
        "std::__cxx11::to_string(int)::@0"; "std::__cxx11::to_string(unsigned int)::@0";
        "std::__cxx11::to_string(long)::@0"; "std::__cxx11::to_string(unsigned long)::@0";
        "std::__cxx11::to_string(long long)::@0"; "std::__cxx11::to_string(unsigned long long)::@0";
        "std::__num_base::._S_iminus::_S_iE"; "std::__num_base::._S_iminus::_S_iX";
        "std::__num_base::._S_iminus::_S_ie"; "std::__num_base::._S_iminus::_S_iend";
        "std::__num_base::._S_iminus::_S_iminus"; "std::__num_base::._S_iminus::_S_iplus";
        "std::__num_base::._S_iminus::_S_ix"; "std::__num_base::._S_iminus::_S_izero";
        "std::__num_base::._S_ominus::_S_oE"; "std::__num_base::._S_ominus::_S_oX";
        "std::__num_base::._S_ominus::_S_odigits"; "std::__num_base::._S_ominus::_S_odigits_end";
        "std::__num_base::._S_ominus::_S_oe"; "std::__num_base::._S_ominus::_S_oend";
        "std::__num_base::._S_ominus::_S_ominus"; "std::__num_base::._S_ominus::_S_oplus";
        "std::__num_base::._S_ominus::_S_oudigits"; "std::__num_base::._S_ominus::_S_oudigits_end";
        "std::__num_base::._S_ominus::_S_ox"; "std::ios_base::event::copyfmt_event";
        "std::ios_base::event::erase_event"; "std::ios_base::event::imbue_event";
        "std::ios_base::._S_local_word_size::_S_local_word_size"; "std::locale::facet::__shim";
*)
