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

# Utility rule file for lingeling-src.

# Include any custom commands dependencies for this target.
include libsolve/src/CMakeFiles/lingeling-src.dir/compiler_depend.make

# Include the progress variables for this target.
include libsolve/src/CMakeFiles/lingeling-src.dir/progress.make

libsolve/src/CMakeFiles/lingeling-src: libsolve/src/CMakeFiles/lingeling-src-complete

libsolve/src/CMakeFiles/lingeling-src-complete: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-install
libsolve/src/CMakeFiles/lingeling-src-complete: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-mkdir
libsolve/src/CMakeFiles/lingeling-src-complete: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-download
libsolve/src/CMakeFiles/lingeling-src-complete: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-update
libsolve/src/CMakeFiles/lingeling-src-complete: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-patch
libsolve/src/CMakeFiles/lingeling-src-complete: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-configure
libsolve/src/CMakeFiles/lingeling-src-complete: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-build
libsolve/src/CMakeFiles/lingeling-src-complete: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-install
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Completed 'lingeling-src'"
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/CMakeFiles
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/CMakeFiles/lingeling-src-complete
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-done

libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-build: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-configure
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Performing build step for 'lingeling-src'"
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src && make liblgl.a
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-build

libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-configure: libsolve/src/lingeling-src-prefix/tmp/lingeling-src-cfgcmd.txt
libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-configure: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-patch
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Performing configure step for 'lingeling-src'"
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src && ./configure.sh
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-configure

libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-download: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-urlinfo.txt
libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-download: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-mkdir
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Performing download step (download, verify and extract) for 'lingeling-src'"
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src && /snap/cmake/870/bin/cmake -P /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/download-lingeling-src.cmake
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src && /snap/cmake/870/bin/cmake -P /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/verify-lingeling-src.cmake
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src && /snap/cmake/870/bin/cmake -P /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/extract-lingeling-src.cmake
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-download

libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-install: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-build
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "No install step for 'lingeling-src'"
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src && /snap/cmake/870/bin/cmake -E echo_append
	cd /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-install

libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-mkdir:
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "Creating directories for 'lingeling-src'"
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/tmp
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E make_directory /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-mkdir

libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-patch: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-update
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "No patch step for 'lingeling-src'"
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E echo_append
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-patch

libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-update: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-download
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/alephnoell/quabs/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "No update step for 'lingeling-src'"
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E echo_append
	cd /home/alephnoell/quabs/build/libsolve/src && /snap/cmake/870/bin/cmake -E touch /home/alephnoell/quabs/build/libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-update

lingeling-src: libsolve/src/CMakeFiles/lingeling-src
lingeling-src: libsolve/src/CMakeFiles/lingeling-src-complete
lingeling-src: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-build
lingeling-src: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-configure
lingeling-src: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-download
lingeling-src: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-install
lingeling-src: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-mkdir
lingeling-src: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-patch
lingeling-src: libsolve/src/lingeling-src-prefix/src/lingeling-src-stamp/lingeling-src-update
lingeling-src: libsolve/src/CMakeFiles/lingeling-src.dir/build.make
.PHONY : lingeling-src

# Rule to build all files generated by this target.
libsolve/src/CMakeFiles/lingeling-src.dir/build: lingeling-src
.PHONY : libsolve/src/CMakeFiles/lingeling-src.dir/build

libsolve/src/CMakeFiles/lingeling-src.dir/clean:
	cd /home/alephnoell/quabs/build/libsolve/src && $(CMAKE_COMMAND) -P CMakeFiles/lingeling-src.dir/cmake_clean.cmake
.PHONY : libsolve/src/CMakeFiles/lingeling-src.dir/clean

libsolve/src/CMakeFiles/lingeling-src.dir/depend:
	cd /home/alephnoell/quabs/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/alephnoell/quabs /home/alephnoell/quabs/libsolve/src /home/alephnoell/quabs/build /home/alephnoell/quabs/build/libsolve/src /home/alephnoell/quabs/build/libsolve/src/CMakeFiles/lingeling-src.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : libsolve/src/CMakeFiles/lingeling-src.dir/depend

