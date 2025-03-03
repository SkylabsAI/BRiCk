set(PACKAGE_VERSION "16.0")

# LLVM is API-compatible only with matching major.minor versions
# and patch versions not less than that requested.
if("{PACKAGE_VERSION}" VERSION_EQUAL
    "${PACKAGE_FIND_VERSION_MAJOR}.${PACKAGE_FIND_VERSION_MINOR}")
  set(PACKAGE_VERSION_COMPATIBLE 1)
endif()

