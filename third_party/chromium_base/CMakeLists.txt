set (CHROMIUM_BASE ${PROJECT_SOURCE_DIR}/third_party/chromium_base)

set (CHROMIUM_BASE_ARCH x86)

set (BASE_SOURCES
	${CHROMIUM_BASE}/base/at_exit.cc
        ${CHROMIUM_BASE}/base/callback_internal.cc
        ${CHROMIUM_BASE}/base/command_line.cc
        ${CHROMIUM_BASE}/base/base_switches.cc
	${CHROMIUM_BASE}/base/environment.cc
	${CHROMIUM_BASE}/base/lazy_instance.cc
	${CHROMIUM_BASE}/base/file_path.cc
	${CHROMIUM_BASE}/base/file_util.cc
	${CHROMIUM_BASE}/base/synchronization/lock.cc
	${CHROMIUM_BASE}/base/location.cc
	${CHROMIUM_BASE}/base/logging.cc
	${CHROMIUM_BASE}/base/debug/alias.cc
	${CHROMIUM_BASE}/base/debug/debugger.cc
	${CHROMIUM_BASE}/base/debug/stack_trace.cc
        #${CHROMIUM_BASE}/base/json/json_file_value_serializer.cc
        ${CHROMIUM_BASE}/base/json/json_string_value_serializer.cc
        ${CHROMIUM_BASE}/base/json/json_reader.cc
        ${CHROMIUM_BASE}/base/json/json_parser.cc
        ${CHROMIUM_BASE}/base/json/json_writer.cc
        ${CHROMIUM_BASE}/base/json/string_escape.cc
	${CHROMIUM_BASE}/base/metrics/bucket_ranges.cc
	${CHROMIUM_BASE}/base/metrics/histogram_base.cc
	${CHROMIUM_BASE}/base/metrics/histogram.cc
	${CHROMIUM_BASE}/base/metrics/histogram_samples.cc
	${CHROMIUM_BASE}/base/metrics/sample_vector.cc
	${CHROMIUM_BASE}/base/metrics/sample_map.cc
	${CHROMIUM_BASE}/base/metrics/sparse_histogram.cc
	${CHROMIUM_BASE}/base/metrics/stats_counters.cc
	${CHROMIUM_BASE}/base/metrics/stats_table.cc
	${CHROMIUM_BASE}/base/metrics/statistics_recorder.cc
        ${CHROMIUM_BASE}/base/memory/aligned_memory.cc
        ${CHROMIUM_BASE}/base/memory/weak_ptr.cc
        ${CHROMIUM_BASE}/base/threading/thread_checker_impl.cc
	${CHROMIUM_BASE}/base/sys_info.cc
	${CHROMIUM_BASE}/base/string_util.cc
	${CHROMIUM_BASE}/base/string16.cc
	${CHROMIUM_BASE}/base/strings/string_number_conversions.cc
	${CHROMIUM_BASE}/base/strings/utf_string_conversion_utils.cc
	${CHROMIUM_BASE}/base/strings/string_split.cc
	${CHROMIUM_BASE}/base/string_piece.cc
	${CHROMIUM_BASE}/base/stringprintf.cc
	${CHROMIUM_BASE}/base/base_paths.cc
	${CHROMIUM_BASE}/base/path_service.cc
	${CHROMIUM_BASE}/base/pickle.cc
	${CHROMIUM_BASE}/base/platform_file.cc
	${CHROMIUM_BASE}/base/process_util.cc
	${CHROMIUM_BASE}/base/profiler/alternate_timer.cc
	${CHROMIUM_BASE}/base/profiler/tracked_time.cc
	${CHROMIUM_BASE}/base/time.cc
        ${CHROMIUM_BASE}/base/tracking_info.cc
        ${CHROMIUM_BASE}/base/tracked_objects.cc
	${CHROMIUM_BASE}/base/memory/ref_counted.cc
        ${CHROMIUM_BASE}/base/memory/singleton.cc
	${CHROMIUM_BASE}/base/threading/thread_restrictions.cc
	${CHROMIUM_BASE}/base/threading/thread_collision_warner.cc
	${CHROMIUM_BASE}/base/threading/thread_id_name_manager.cc
	${CHROMIUM_BASE}/base/threading/simple_thread.cc
	${CHROMIUM_BASE}/base/utf_string_conversions.cc
	${CHROMIUM_BASE}/base/values.cc
	${CHROMIUM_BASE}/base/vlog.cc
	${CHROMIUM_BASE}/base/third_party/icu/icu_utf.cc
	${CHROMIUM_BASE}/base/third_party/dmg_fp/g_fmt.cc
	${CHROMIUM_BASE}/base/third_party/dmg_fp/dtoa.cc
	${CHROMIUM_BASE}/base/third_party/nspr/prtime.cc
        #${CHROMIUM_BASE}/base/third_party/dynamic_annotations/dynamic_annotations.c
)

#####################################################################

if (${APPLE})
set(BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/base_paths_mac.mm
	${CHROMIUM_BASE}/base/time_mac.cc
	${CHROMIUM_BASE}/base/process_util_mac.mm
	${CHROMIUM_BASE}/base/file_util_mac.mm
	${CHROMIUM_BASE}/base/sys_info_mac.cc
	${CHROMIUM_BASE}/base/mac/mac_util.mm
	${CHROMIUM_BASE}/base/mac/scoped_mach_port.cc
	${CHROMIUM_BASE}/base/mac/foundation_util.mm
	${CHROMIUM_BASE}/base/mac/bundle_locations.mm
	${CHROMIUM_BASE}/base/mac/mac_logging.cc
	${CHROMIUM_BASE}/base/threading/platform_thread_mac.mm
	${CHROMIUM_BASE}/base/strings/sys_string_conversions_mac.mm
)
endif (${APPLE})

#####################################################################

# TODO differentiate Linux from *BSD etc
if ("${UNIX}" AND NOT "${APPLE}")
  set (BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/strings/sys_string_conversions_posix.cc
	${CHROMIUM_BASE}/base/process_util_linux.cc
  )

  execute_process(COMMAND pkg-config --cflags glib-2.0
    OUTPUT_VARIABLE PKG_CONFIG_GLIB_CFLAGS
  )
  add_definitions(${PKG_CONFIG_GLIB_CFLAGS})
  # scripts/run_test.py is careful to link with glib-2.0 on Linux...
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
	${CHROMIUM_BASE}/base/file_util_posix.cc
	${CHROMIUM_BASE}/base/base_paths_posix.cc
	${CHROMIUM_BASE}/base/synchronization/lock_impl_posix.cc
	${CHROMIUM_BASE}/base/safe_strerror_posix.cc
	${CHROMIUM_BASE}/base/shared_memory_posix.cc
	${CHROMIUM_BASE}/base/platform_file_posix.cc
	${CHROMIUM_BASE}/base/process_util_posix.cc
	${CHROMIUM_BASE}/base/posix/file_descriptor_shuffle.cc
	${CHROMIUM_BASE}/base/threading/platform_thread_posix.cc
	${CHROMIUM_BASE}/base/threading/thread_local_posix.cc
	${CHROMIUM_BASE}/base/threading/thread_local_storage_posix.cc
	${CHROMIUM_BASE}/base/debug/debugger_posix.cc
	${CHROMIUM_BASE}/base/time_posix.cc
	${CHROMIUM_BASE}/base/sys_info_posix.cc
	${CHROMIUM_BASE}/base/process_posix.cc
	${CHROMIUM_BASE}/base/debug/stack_trace_posix.cc
        ${CHROMIUM_BASE}/base/synchronization/waitable_event_posix.cc
        ${CHROMIUM_BASE}/base/synchronization/condition_variable_posix.cc
	${CHROMIUM_BASE}/base/nix/xdg_util.cc
	${CHROMIUM_BASE}/base/third_party/xdg_user_dirs/xdg_user_dir_lookup.cc
  )
endif (${UNIX})

#####################################################################

if (${WIN32})
  set (BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/base_paths_win.cc
	${CHROMIUM_BASE}/base/time_win.cc
	${CHROMIUM_BASE}/base/process_win.cc
	${CHROMIUM_BASE}/base/synchronization/lock_impl_win.cc
	${CHROMIUM_BASE}/base/logging_win.cc
	${CHROMIUM_BASE}/base/file_util_win.cc
	${CHROMIUM_BASE}/base/process_util_win.cc
	${CHROMIUM_BASE}/base/shared_memory_win.cc
	${CHROMIUM_BASE}/base/debug/debugger_win.cc
	${CHROMIUM_BASE}/base/threading/platform_thread_win.cc
	${CHROMIUM_BASE}/base/threading/thread_local_win.cc
	${CHROMIUM_BASE}/base/threading/thread_local_storage_win.cc
	${CHROMIUM_BASE}/base/strings/sys_string_conversions_win.cc
	${CHROMIUM_BASE}/base/sys_info_win.cc
	${CHROMIUM_BASE}/base/platform_file_win.cc
	${CHROMIUM_BASE}/base/debug/stack_trace_win.cc
        ${CHROMIUM_BASE}/base/synchronization/waitable_event_win.cc
        ${CHROMIUM_BASE}/base/synchronization/condition_variable_win.cc
  )
endif (${WIN32})


set(CMAKE_MACOSX_RPATH 1)

add_library(chromium_base SHARED
  ${BASE_SOURCES}
)

if (${APPLE})
  target_link_libraries(chromium_base "-framework Cocoa -framework IOKit")
endif (${APPLE})

if ("${UNIX}" AND NOT "${APPLE}")
  target_link_libraries(chromium_base "-lrt")
endif ("${UNIX}" AND NOT "${APPLE}")
