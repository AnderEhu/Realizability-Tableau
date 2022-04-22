#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "minisat" for configuration "Release"
set_property(TARGET minisat APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(minisat PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "CXX"
  IMPORTED_LINK_INTERFACE_LIBRARIES_RELEASE "/usr/lib/x86_64-linux-gnu/libz.so"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libminisat.a"
  )

list(APPEND _IMPORT_CHECK_TARGETS minisat )
list(APPEND _IMPORT_CHECK_FILES_FOR_minisat "${_IMPORT_PREFIX}/lib/libminisat.a" )

# Import target "minisat_core" for configuration "Release"
set_property(TARGET minisat_core APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(minisat_core PROPERTIES
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/bin/minisat_core"
  )

list(APPEND _IMPORT_CHECK_TARGETS minisat_core )
list(APPEND _IMPORT_CHECK_FILES_FOR_minisat_core "${_IMPORT_PREFIX}/bin/minisat_core" )

# Import target "minisat_simp" for configuration "Release"
set_property(TARGET minisat_simp APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(minisat_simp PROPERTIES
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/bin/minisat"
  )

list(APPEND _IMPORT_CHECK_TARGETS minisat_simp )
list(APPEND _IMPORT_CHECK_FILES_FOR_minisat_simp "${_IMPORT_PREFIX}/bin/minisat" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
