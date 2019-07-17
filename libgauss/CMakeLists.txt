add_executable(whatever-bin
    EGaussian.cpp
    packedrow.cpp
    test.cpp
    model_counting.cpp
    propagator.cpp
    utility.cpp
)
set_target_properties(whatever-bin PROPERTIES
    OUTPUT_NAME whatever
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
    INSTALL_RPATH_USE_LINK_PATH TRUE)
target_link_libraries(whatever-bin
    PRIVATE libclingo
)
set_target_properties(whatever-bin
    PROPERTIES FOLDER "exe"
)
# install(TARGETS whatever-bin
#     RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
# )
