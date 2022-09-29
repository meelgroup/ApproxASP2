add_executable(approxasp-bin
    EGaussian.cpp
    packedrow.cpp
    test.cpp
    model_counting.cpp
    propagator.cpp
    utility.cpp
)
set_target_properties(approxasp-bin PROPERTIES
    OUTPUT_NAME approxasp
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
    INSTALL_RPATH_USE_LINK_PATH TRUE)

target_link_libraries(approxasp-bin
    PRIVATE libclingo
)

set_target_properties(approxasp-bin
    PROPERTIES FOLDER "exe"
)

# install(TARGETS approxasp-bin
#     RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
# )
