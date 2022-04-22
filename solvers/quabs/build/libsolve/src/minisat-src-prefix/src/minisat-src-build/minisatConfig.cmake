# Config file for the Build-tree cryptominisat Package
# It defines the following variables
#  MINISAT_INCLUDE_DIRS - include directories for minisat
#  MINISAT_LIBRARIES    - libraries to link against
#  MINISAT_EXECUTABLE   - the cryptominisat executable

# Compute paths
get_filename_component(MINISAT_CMAKE_DIR "${CMAKE_CURRENT_LIST_FILE}" PATH)
set(MINISAT_INCLUDE_DIRS "/home/alephnoell/quabs/build/libsolve/src/minisat-src-prefix/src/minisat-src/")

# Our library dependencies (contains definitions for IMPORTED targets)
include("${MINISAT_CMAKE_DIR}/minisatTargets.cmake")

# These are IMPORTED targets created by minisatTargets.cmake
set(MINISAT_LIBRARIES minisat)
set(MINISAT_VERSION_MAJOR )
set(MINISAT_VERSION_MINOR )
set(MINISAT_EXECUTABLE minisat)
