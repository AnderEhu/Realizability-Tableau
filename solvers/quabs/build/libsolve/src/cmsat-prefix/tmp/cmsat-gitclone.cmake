
if(NOT "/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat-stamp/cmsat-gitinfo.txt" IS_NEWER_THAN "/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat-stamp/cmsat-gitclone-lastrun.txt")
  message(STATUS "Avoiding repeated git clone, stamp file is up to date: '/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat-stamp/cmsat-gitclone-lastrun.txt'")
  return()
endif()

execute_process(
  COMMAND ${CMAKE_COMMAND} -E rm -rf "/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat"
  RESULT_VARIABLE error_code
  )
if(error_code)
  message(FATAL_ERROR "Failed to remove directory: '/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat'")
endif()

# try the clone 3 times in case there is an odd git clone issue
set(error_code 1)
set(number_of_tries 0)
while(error_code AND number_of_tries LESS 3)
  execute_process(
    COMMAND "/usr/bin/git"  clone --no-checkout --config "advice.detachedHead=false" "https://github.com/msoos/cryptominisat.git" "cmsat"
    WORKING_DIRECTORY "/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src"
    RESULT_VARIABLE error_code
    )
  math(EXPR number_of_tries "${number_of_tries} + 1")
endwhile()
if(number_of_tries GREATER 1)
  message(STATUS "Had to git clone more than once:
          ${number_of_tries} times.")
endif()
if(error_code)
  message(FATAL_ERROR "Failed to clone repository: 'https://github.com/msoos/cryptominisat.git'")
endif()

execute_process(
  COMMAND "/usr/bin/git"  checkout 5.6.8 --
  WORKING_DIRECTORY "/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat"
  RESULT_VARIABLE error_code
  )
if(error_code)
  message(FATAL_ERROR "Failed to checkout tag: '5.6.8'")
endif()

set(init_submodules TRUE)
if(init_submodules)
  execute_process(
    COMMAND "/usr/bin/git"  submodule update --recursive --init 
    WORKING_DIRECTORY "/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat"
    RESULT_VARIABLE error_code
    )
endif()
if(error_code)
  message(FATAL_ERROR "Failed to update submodules in: '/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat'")
endif()

# Complete success, update the script-last-run stamp file:
#
execute_process(
  COMMAND ${CMAKE_COMMAND} -E copy
    "/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat-stamp/cmsat-gitinfo.txt"
    "/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat-stamp/cmsat-gitclone-lastrun.txt"
  RESULT_VARIABLE error_code
  )
if(error_code)
  message(FATAL_ERROR "Failed to copy script-last-run stamp file: '/home/alephnoell/quabs/build/libsolve/src/cmsat-prefix/src/cmsat-stamp/cmsat-gitclone-lastrun.txt'")
endif()

