#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "cryptominisat5" for configuration "Release"
set_property(TARGET cryptominisat5 APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(cryptominisat5 PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "CXX"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libcryptominisat5.a"
  )

list(APPEND _IMPORT_CHECK_TARGETS cryptominisat5 )
list(APPEND _IMPORT_CHECK_FILES_FOR_cryptominisat5 "${_IMPORT_PREFIX}/lib/libcryptominisat5.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
