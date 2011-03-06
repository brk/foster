set (CHROMIUM_BASE ${PROJECT_SOURCE_DIR}/third_party/chromium_base)

set (CHROMIUM_BASE_ARCH x86)

set (BASE_SOURCES
	${CHROMIUM_BASE}/base/at_exit.cc
	${CHROMIUM_BASE}/base/lazy_instance.cc
	${CHROMIUM_BASE}/base/lock.cc
	${CHROMIUM_BASE}/base/logging.cc
	${CHROMIUM_BASE}/base/debug/debugger.cc
	${CHROMIUM_BASE}/base/string_util.cc
	${CHROMIUM_BASE}/base/string16.cc
	${CHROMIUM_BASE}/base/string_number_conversions.cc
	${CHROMIUM_BASE}/base/string_split.cc
	${CHROMIUM_BASE}/base/string_piece.cc
	${CHROMIUM_BASE}/base/stringprintf.cc
	${CHROMIUM_BASE}/base/time.cc
	${CHROMIUM_BASE}/base/thread_restrictions.cc
	${CHROMIUM_BASE}/base/utf_string_conversions.cc
	${CHROMIUM_BASE}/base/utf_string_conversion_utils.cc
	${CHROMIUM_BASE}/base/vlog.cc
	${CHROMIUM_BASE}/base/third_party/icu/icu_utf.cc
	${CHROMIUM_BASE}/base/third_party/dmg_fp/g_fmt.cc
	${CHROMIUM_BASE}/base/third_party/dmg_fp/dtoa.cc
)

#####################################################################

if (${APPLE})
set(BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/time_mac.cc
	${CHROMIUM_BASE}/base/platform_thread_mac.mm
	${CHROMIUM_BASE}/base/sys_string_conversions_mac.mm
)
endif (${APPLE})

#####################################################################

if ("${UNIX}" AND NOT "${APPLE}")
  set (BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/sys_string_conversions_linux.cc
	${CHROMIUM_BASE}/base/time_posix.cc
  )
endif ("${UNIX}" AND NOT "${APPLE}")

#####################################################################

if (${CHROMIUM_BASE_ARCH} STREQUAL "x86")
  set (BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/atomicops_internals_x86_gcc.cc
  )
endif (${CHROMIUM_BASE_ARCH} STREQUAL "x86")

#####################################################################

if (${UNIX})
  set (BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/lock_impl_posix.cc
	${CHROMIUM_BASE}/base/safe_strerror_posix.cc
	${CHROMIUM_BASE}/base/platform_thread_posix.cc
	${CHROMIUM_BASE}/base/thread_local_posix.cc
	${CHROMIUM_BASE}/base/debug/debugger_posix.cc
  )
endif (${UNIX})

#####################################################################

if (${WIN32})
  set (BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/time_win.cc
	${CHROMIUM_BASE}/base/lock_impl_win.cc
	${CHROMIUM_BASE}/base/logging_win.cc
	${CHROMIUM_BASE}/base/platform_thread_win.cc
	${CHROMIUM_BASE}/base/debug/debugger_win.cc
	${CHROMIUM_BASE}/base/thread_local_win.cc
	${CHROMIUM_BASE}/base/sys_string_conversions_win.cc
  )
endif (${WIN32})

add_library(chromium_base SHARED
  ${BASE_SOURCES}
)

if (${APPLE})
  target_link_libraries(chromium_base "-framework Cocoa")
endif (${APPLE})
