set (CHROMIUM_BASE ${PROJECT_SOURCE_DIR}/third_party/chromium_base)

set (BASE_COMMON_SOURCES
	${CHROMIUM_BASE}/base/time.cc
	${CHROMIUM_BASE}/base/time_posix.cc

	${CHROMIUM_BASE}/base/string_util.cc
	${CHROMIUM_BASE}/base/string16.cc
	${CHROMIUM_BASE}/base/string_piece.cc
	${CHROMIUM_BASE}/base/utf_string_conversions.cc
)

add_library(chromium_base STATIC
  ${BASE_COMMON_SOURCES}
)
