include(configure.cmake)

set_source_group(CONFIGURATION_FILES "Configuration Files" configure.cmake config.h.in.cmake ${CMAKE_CURRENT_BINARY_DIR}/config.h)

#set_source_group(SIMPLE_READER_SOURCES "Source Files" simplereader.c)
#
#add_executable(simplereader ${SIMPLE_READER_SOURCES} ${SIMPLE_READER_HEADERS} ${CONFIGURATION_FILES})
#
#set_folder(simplereader dwarfexample)
#
#target_compile_definitions(simplereader PRIVATE CONFPREFIX={CMAKE_INSTALL_PREFIX}/lib)
#
#target_link_libraries(simplereader PRIVATE ${dwarf-target} ${dwfzlib})
#
#set_source_group(FRAME1_SOURCES "Source Files" frame1.c)
#
#add_executable(frame1 ${FRAME1_SOURCES} ${FRAME1_HEADERS} ${CONFIGURATION_FILES})
#
#set_folder(frame1 dwarfexample)
#
#target_compile_definitions(frame1 PRIVATE CONFPREFIX={CMAKE_INSTALL_PREFIX}/lib)
#
#target_link_libraries(frame1 PRIVATE ${dwarf-target} ${dwfzlib})


set_source_group(MASK_REGISTERS_SOURCES "Source Files" maskregisters.c)

add_executable(maskregisters ${MASK_REGISTERS_SOURCES} ${MASK_REGISTERS_HEADERS} ${CONFIGURATION_FILES})

set_folder(maskregisters dwarfdatarandohelper)

target_compile_definitions(maskregisters PRIVATE CONFPREFIX={CMAKE_INSTALL_PREFIX}/lib)

target_link_libraries(maskregisters PRIVATE ${dwarf-target} ${dwfzlib})
