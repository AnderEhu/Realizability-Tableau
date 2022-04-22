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

# Utility rule file for picosat-src.

# Include any custom commands dependencies for this target.
include libsolve/src/CMakeFiles/picosat-src.dir/compiler_depend.make

# Include the progress variables for this target.
include libsolve/src/CMakeFiles/picosat-src.dir/progress.make

libsolve/src/CMakeFiles/picosat-src: libsolve/src/CMakeFiles/picosat-src-complete

libsolve/src/CMakeFiles/picosat-src-complete: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-install
libsolve/src/CMakeFiles/picosat-src-complete: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-mkdir
libsolve/src/CMakeFiles/picosat-src-complete: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-download
libsolve/src/CMakeFiles/picosat-src-complete: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-update
libsolve/src/CMakeFiles/picosat-src-complete: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-patch
libsolve/src/CMakeFiles/picosat-src-complete: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-configure
libsolve/src/CMakeFiles/picosat-src-complete: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-build
libsolve/src/CMakeFiles/picosat-src-complete: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-install
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Completed 'picosat-src'"
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/CMakeFiles
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/CMakeFiles/picosat-src-complete
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-done

libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-build: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-configure
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Performing build step for 'picosat-src'"
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src && make libpicosat.a
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-build

libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-configure: libsolve/src/picosat-src-prefix/tmp/picosat-src-cfgcmd.txt
libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-configure: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-patch
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Performing configure step for 'picosat-src'"
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src && ./configure.sh
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-configure

libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-download: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-urlinfo.txt
libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-download: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-mkdir
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Performing download step (download, verify and extract) for 'picosat-src'"
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src && /snap/cmake/870/bin/cmake -P /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/download-picosat-src.cmake
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src && /snap/cmake/870/bin/cmake -P /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/verify-picosat-src.cmake
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src && /snap/cmake/870/bin/cmake -P /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/extract-picosat-src.cmake
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-download

libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-install: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-build
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "No install step for 'picosat-src'"
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src && /snap/cmake/870/bin/cmake -E echo_append
	cd /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-install

libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-mkdir:
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "Creating directories for 'picosat-src'"
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/tmp
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-mkdir

libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-patch: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-update
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "No patch step for 'picosat-src'"
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E echo_append
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-patch

libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-update: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-download
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "No update step for 'picosat-src'"
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E echo_append
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-update

picosat-src: libsolve/src/CMakeFiles/picosat-src
picosat-src: libsolve/src/CMakeFiles/picosat-src-complete
picosat-src: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-build
picosat-src: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-configure
picosat-src: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-download
picosat-src: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-install
picosat-src: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-mkdir
picosat-src: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-patch
picosat-src: libsolve/src/picosat-src-prefix/src/picosat-src-stamp/picosat-src-update
picosat-src: libsolve/src/CMakeFiles/picosat-src.dir/build.make
.PHONY : picosat-src

# Rule to build all files generated by this target.
libsolve/src/CMakeFiles/picosat-src.dir/build: picosat-src
.PHONY : libsolve/src/CMakeFiles/picosat-src.dir/build

libsolve/src/CMakeFiles/picosat-src.dir/clean:
	cd /home/alephnoell/quabs/build/libsolve/src && $(CMAKE_COMMAND) -P CMakeFiles/picosat-src.dir/cmake_clean.cmake
.PHONY : libsolve/src/CMakeFiles/picosat-src.dir/clean

libsolve/src/CMakeFiles/picosat-src.dir/depend:
	cd /home/alephnoell/quabs/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/alephnoell/quabs /home/alephnoell/quabs/libsolve/src /home/alephnoell/quabs/build /home/alephnoell/quabs/build/libsolve/src /home/alephnoell/quabs/build/libsolve/src/CMakeFiles/picosat-src.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : libsolve/src/CMakeFiles/picosat-src.dir/depend
