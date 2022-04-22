# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.20

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /snap/cmake/870/bin/cmake

# The command to remove a file.
RM = /snap/cmake/870/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/alephnoell/quabs

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/alephnoell/quabs/build

# Include any dependencies generated for this target.
include libsolve/src/CMakeFiles/solve.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include libsolve/src/CMakeFiles/solve.dir/compiler_depend.make

# Include the progress variables for this target.
include libsolve/src/CMakeFiles/solve.dir/progress.make

# Include the compile flags for this target's objects.
include libsolve/src/CMakeFiles/solve.dir/flags.make

libsolve/src/CMakeFiles/solve.dir/bit_vector.c.o: libsolve/src/CMakeFiles/solve.dir/flags.make
libsolve/src/CMakeFiles/solve.dir/bit_vector.c.o: ../libsolve/src/bit_vector.c
libsolve/src/CMakeFiles/solve.dir/bit_vector.c.o: libsolve/src/CMakeFiles/solve.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object libsolve/src/CMakeFiles/solve.dir/bit_vector.c.o"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -MD -MT libsolve/src/CMakeFiles/solve.dir/bit_vector.c.o -MF CMakeFiles/solve.dir/bit_vector.c.o.d -o CMakeFiles/solve.dir/bit_vector.c.o -c /home/alephnoell/quabs/libsolve/src/bit_vector.c

libsolve/src/CMakeFiles/solve.dir/bit_vector.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/solve.dir/bit_vector.c.i"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/alephnoell/quabs/libsolve/src/bit_vector.c > CMakeFiles/solve.dir/bit_vector.c.i

libsolve/src/CMakeFiles/solve.dir/bit_vector.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/solve.dir/bit_vector.c.s"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/alephnoell/quabs/libsolve/src/bit_vector.c -o CMakeFiles/solve.dir/bit_vector.c.s

libsolve/src/CMakeFiles/solve.dir/map.c.o: libsolve/src/CMakeFiles/solve.dir/flags.make
libsolve/src/CMakeFiles/solve.dir/map.c.o: ../libsolve/src/map.c
libsolve/src/CMakeFiles/solve.dir/map.c.o: libsolve/src/CMakeFiles/solve.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building C object libsolve/src/CMakeFiles/solve.dir/map.c.o"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -MD -MT libsolve/src/CMakeFiles/solve.dir/map.c.o -MF CMakeFiles/solve.dir/map.c.o.d -o CMakeFiles/solve.dir/map.c.o -c /home/alephnoell/quabs/libsolve/src/map.c

libsolve/src/CMakeFiles/solve.dir/map.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/solve.dir/map.c.i"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/alephnoell/quabs/libsolve/src/map.c > CMakeFiles/solve.dir/map.c.i

libsolve/src/CMakeFiles/solve.dir/map.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/solve.dir/map.c.s"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/alephnoell/quabs/libsolve/src/map.c -o CMakeFiles/solve.dir/map.c.s

libsolve/src/CMakeFiles/solve.dir/queue.c.o: libsolve/src/CMakeFiles/solve.dir/flags.make
libsolve/src/CMakeFiles/solve.dir/queue.c.o: ../libsolve/src/queue.c
libsolve/src/CMakeFiles/solve.dir/queue.c.o: libsolve/src/CMakeFiles/solve.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building C object libsolve/src/CMakeFiles/solve.dir/queue.c.o"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -MD -MT libsolve/src/CMakeFiles/solve.dir/queue.c.o -MF CMakeFiles/solve.dir/queue.c.o.d -o CMakeFiles/solve.dir/queue.c.o -c /home/alephnoell/quabs/libsolve/src/queue.c

libsolve/src/CMakeFiles/solve.dir/queue.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/solve.dir/queue.c.i"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/alephnoell/quabs/libsolve/src/queue.c > CMakeFiles/solve.dir/queue.c.i

libsolve/src/CMakeFiles/solve.dir/queue.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/solve.dir/queue.c.s"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/alephnoell/quabs/libsolve/src/queue.c -o CMakeFiles/solve.dir/queue.c.s

libsolve/src/CMakeFiles/solve.dir/vector.c.o: libsolve/src/CMakeFiles/solve.dir/flags.make
libsolve/src/CMakeFiles/solve.dir/vector.c.o: ../libsolve/src/vector.c
libsolve/src/CMakeFiles/solve.dir/vector.c.o: libsolve/src/CMakeFiles/solve.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building C object libsolve/src/CMakeFiles/solve.dir/vector.c.o"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -MD -MT libsolve/src/CMakeFiles/solve.dir/vector.c.o -MF CMakeFiles/solve.dir/vector.c.o.d -o CMakeFiles/solve.dir/vector.c.o -c /home/alephnoell/quabs/libsolve/src/vector.c

libsolve/src/CMakeFiles/solve.dir/vector.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/solve.dir/vector.c.i"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/alephnoell/quabs/libsolve/src/vector.c > CMakeFiles/solve.dir/vector.c.i

libsolve/src/CMakeFiles/solve.dir/vector.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/solve.dir/vector.c.s"
	cd /home/alephnoell/quabs/build/libsolve/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/alephnoell/quabs/libsolve/src/vector.c -o CMakeFiles/solve.dir/vector.c.s

# Object files for target solve
solve_OBJECTS = \
"CMakeFiles/solve.dir/bit_vector.c.o" \
"CMakeFiles/solve.dir/map.c.o" \
"CMakeFiles/solve.dir/queue.c.o" \
"CMakeFiles/solve.dir/vector.c.o"

# External object files for target solve
solve_EXTERNAL_OBJECTS =

libsolve/src/libsolve.a: libsolve/src/CMakeFiles/solve.dir/bit_vector.c.o
libsolve/src/libsolve.a: libsolve/src/CMakeFiles/solve.dir/map.c.o
libsolve/src/libsolve.a: libsolve/src/CMakeFiles/solve.dir/queue.c.o
libsolve/src/libsolve.a: libsolve/src/CMakeFiles/solve.dir/vector.c.o
libsolve/src/libsolve.a: libsolve/src/CMakeFiles/solve.dir/build.make
libsolve/src/libsolve.a: libsolve/src/CMakeFiles/solve.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Linking C static library libsolve.a"
	cd /home/alephnoell/quabs/build/libsolve/src && $(CMAKE_COMMAND) -P CMakeFiles/solve.dir/cmake_clean_target.cmake
	cd /home/alephnoell/quabs/build/libsolve/src && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/solve.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
libsolve/src/CMakeFiles/solve.dir/build: libsolve/src/libsolve.a
.PHONY : libsolve/src/CMakeFiles/solve.dir/build

libsolve/src/CMakeFiles/solve.dir/clean:
	cd /home/alephnoell/quabs/build/libsolve/src && $(CMAKE_COMMAND) -P CMakeFiles/solve.dir/cmake_clean.cmake
.PHONY : libsolve/src/CMakeFiles/solve.dir/clean

libsolve/src/CMakeFiles/solve.dir/depend:
	cd /home/alephnoell/quabs/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/alephnoell/quabs /home/alephnoell/quabs/libsolve/src /home/alephnoell/quabs/build /home/alephnoell/quabs/build/libsolve/src /home/alephnoell/quabs/build/libsolve/src/CMakeFiles/solve.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : libsolve/src/CMakeFiles/solve.dir/depend
