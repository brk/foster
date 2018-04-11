set (CHROMIUM_BASE ${PROJECT_SOURCE_DIR}/third_party/chromium_base)

set (CHROMIUM_BASE_ARCH x86)

set (BASE_SOURCES
        ${CHROMIUM_BASE}/base/at_exit.cc
        ${CHROMIUM_BASE}/base/callback_internal.cc
        ${CHROMIUM_BASE}/base/command_line.cc
        ${CHROMIUM_BASE}/base/base_switches.cc
        ${CHROMIUM_BASE}/base/lazy_instance.cc
        ${CHROMIUM_BASE}/base/files/file_enumerator.cc
        ${CHROMIUM_BASE}/base/files/file_path.cc
        ${CHROMIUM_BASE}/base/files/file_util.cc
        ${CHROMIUM_BASE}/base/files/file.cc
        ${CHROMIUM_BASE}/base/files/scoped_file.cc
        ${CHROMIUM_BASE}/base/files/file_path_constants.cc
        ${CHROMIUM_BASE}/base/files/memory_mapped_file.cc
        ${CHROMIUM_BASE}/base/logging.cc
        ${CHROMIUM_BASE}/base/debug/alias.cc
        #${CHROMIUM_BASE}/base/debug/debugger.cc
        #${CHROMIUM_BASE}/base/debug/stack_trace.cc
        ##${CHROMIUM_BASE}/base/json/json_file_value_serializer.cc
        ${CHROMIUM_BASE}/base/json/json_string_value_serializer.cc
        ${CHROMIUM_BASE}/base/json/json_reader.cc
        ${CHROMIUM_BASE}/base/json/json_parser.cc
        ${CHROMIUM_BASE}/base/json/json_writer.cc
        ${CHROMIUM_BASE}/base/json/string_escape.cc
        ${CHROMIUM_BASE}/base/values.cc
	${CHROMIUM_BASE}/base/metrics/metrics_hashes.cc
	${CHROMIUM_BASE}/base/metrics/bucket_ranges.cc
	${CHROMIUM_BASE}/base/metrics/histogram_base.cc
	${CHROMIUM_BASE}/base/metrics/histogram.cc
	${CHROMIUM_BASE}/base/metrics/histogram_samples.cc
        ${CHROMIUM_BASE}/base/metrics/persistent_histogram_allocator.cc
	${CHROMIUM_BASE}/base/metrics/persistent_memory_allocator.cc
	${CHROMIUM_BASE}/base/metrics/persistent_sample_map.cc
	${CHROMIUM_BASE}/base/metrics/sample_vector.cc
	${CHROMIUM_BASE}/base/metrics/sample_map.cc
	${CHROMIUM_BASE}/base/metrics/sparse_histogram.cc
        #${CHROMIUM_BASE}/base/metrics/stats_counters.cc
        #${CHROMIUM_BASE}/base/metrics/stats_table.cc
        ${CHROMIUM_BASE}/base/metrics/statistics_recorder.cc
        ${CHROMIUM_BASE}/base/md5.cc # needed by metrics_hashes.cc
        ${CHROMIUM_BASE}/base/synchronization/lock.cc
        #${CHROMIUM_BASE}/base/memory/aligned_memory.cc
        #${CHROMIUM_BASE}/base/memory/weak_ptr.cc
        #${CHROMIUM_BASE}/base/memory/ref_counted_memory.cc
        #${CHROMIUM_BASE}/base/threading/thread_checker_impl.cc
        #${CHROMIUM_BASE}/base/threading/thread_local_storage.cc
        #${CHROMIUM_BASE}/base/threading/thread_task_runner_handle.cc
        #${CHROMIUM_BASE}/base/threading/worker_pool.cc
        ${CHROMIUM_BASE}/base/sys_info.cc
        ${CHROMIUM_BASE}/base/strings/string_util.cc
        ${CHROMIUM_BASE}/base/strings/string_util_constants.cc
        ${CHROMIUM_BASE}/base/strings/string16.cc
        ${CHROMIUM_BASE}/base/strings/string_number_conversions.cc
        ${CHROMIUM_BASE}/base/strings/utf_string_conversion_utils.cc
        ${CHROMIUM_BASE}/base/strings/string_split.cc
        ${CHROMIUM_BASE}/base/strings/string_piece.cc
        ${CHROMIUM_BASE}/base/strings/stringprintf.cc
        #${CHROMIUM_BASE}/base/base_paths.cc
        #${CHROMIUM_BASE}/base/path_service.cc
        ${CHROMIUM_BASE}/base/pickle.cc # required for histograms
        #${CHROMIUM_BASE}/base/timer/elapsed_timer.cc
        #${CHROMIUM_BASE}/base/platform_file.cc
        #${CHROMIUM_BASE}/base/process/process_info.cc
        #${CHROMIUM_BASE}/base/profiler/alternate_timer.cc
        #${CHROMIUM_BASE}/base/profiler/tracked_time.cc
        ${CHROMIUM_BASE}/base/time/time.cc
        #${CHROMIUM_BASE}/base/tracking_info.cc # from SequencedWorkerPool
        #${CHROMIUM_BASE}/base/tracked_objects.cc
        ${CHROMIUM_BASE}/base/memory/ref_counted.cc
        ${CHROMIUM_BASE}/base/memory/singleton.cc
        #${CHROMIUM_BASE}/base/sequence_checker_impl.cc # needed by weak_ptr.cc
        #${CHROMIUM_BASE}/base/sequenced_task_runner.cc # needed by sequenced_worker_pool.cc
        ${CHROMIUM_BASE}/base/threading/thread_restrictions.cc
        #${CHROMIUM_BASE}/base/threading/thread_collision_warner.cc
        ${CHROMIUM_BASE}/base/threading/thread_id_name_manager.cc
        #${CHROMIUM_BASE}/base/threading/simple_thread.cc
        #${CHROMIUM_BASE}/base/threading/sequenced_worker_pool.cc # needed by sequence_checker
        #${CHROMIUM_BASE}/base/task_runner.cc
        ${CHROMIUM_BASE}/base/strings/utf_string_conversions.cc
        #${CHROMIUM_BASE}/base/vlog.cc
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
	${CHROMIUM_BASE}/base/time/time_mac.cc
        #${CHROMIUM_BASE}/base/base_paths_mac.mm
        #${CHROMIUM_BASE}/base/process/process_info_mac.cc
	${CHROMIUM_BASE}/base/process/process_handle_mac.cc
	${CHROMIUM_BASE}/base/files/file_util_mac.mm
        ${CHROMIUM_BASE}/base/sys_info_mac.mm
	#${CHROMIUM_BASE}/base/mac/mac_util.mm
	${CHROMIUM_BASE}/base/mac/scoped_mach_port.cc
	${CHROMIUM_BASE}/base/mac/scoped_nsautorelease_pool.mm
	${CHROMIUM_BASE}/base/mac/foundation_util.mm
	${CHROMIUM_BASE}/base/mac/bundle_locations.mm
        ${CHROMIUM_BASE}/base/mac/mach_logging.cc
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
        #${CHROMIUM_BASE}/base/process/process_info_linux.cc
        #${CHROMIUM_BASE}/base/process/process_linux.cc
        ${CHROMIUM_BASE}/base/sys_info_linux.cc
        ${CHROMIUM_BASE}/base/threading/platform_thread_linux.cc
	${CHROMIUM_BASE}/base/threading/platform_thread_internal_posix.cc
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
    #${CHROMIUM_BASE}/base/atomicops_internals_x86_gcc.cc
  )
endif (${CHROMIUM_BASE_ARCH} STREQUAL "x86")

#####################################################################

if (${UNIX})
  set (BASE_SOURCES
    ${BASE_SOURCES}
        ${CHROMIUM_BASE}/base/files/file_util_posix.cc
        ${CHROMIUM_BASE}/base/files/file_posix.cc
        ${CHROMIUM_BASE}/base/files/file_enumerator_posix.cc
        ${CHROMIUM_BASE}/base/files/memory_mapped_file_posix.cc
	#${CHROMIUM_BASE}/base/base_paths_posix.cc
	${CHROMIUM_BASE}/base/synchronization/lock_impl_posix.cc
        ${CHROMIUM_BASE}/base/posix/safe_strerror.cc
        #${CHROMIUM_BASE}/base/memory/shared_memory_posix.cc
        ##${CHROMIUM_BASE}/base/platform_file_posix.cc
	#${CHROMIUM_BASE}/base/posix/file_descriptor_shuffle.cc
	${CHROMIUM_BASE}/base/threading/platform_thread_posix.cc
	${CHROMIUM_BASE}/base/threading/thread_local_posix.cc
        #${CHROMIUM_BASE}/base/threading/thread_local_storage_posix.cc
        #${CHROMIUM_BASE}/base/threading/worker_pool_posix.cc
	${CHROMIUM_BASE}/base/debug/debugger_posix.cc
	${CHROMIUM_BASE}/base/time/time_posix.cc
        ${CHROMIUM_BASE}/base/sys_info_posix.cc
	#${CHROMIUM_BASE}/base/process/process_posix.cc
        ${CHROMIUM_BASE}/base/process/process_handle_posix.cc
        #${CHROMIUM_BASE}/base/debug/stack_trace_posix.cc
        #${CHROMIUM_BASE}/base/synchronization/waitable_event_posix.cc
        #${CHROMIUM_BASE}/base/synchronization/condition_variable_posix.cc
	#${CHROMIUM_BASE}/base/nix/xdg_util.cc
	#${CHROMIUM_BASE}/base/third_party/xdg_user_dirs/xdg_user_dir_lookup.cc
  )
endif (${UNIX})

#####################################################################

if (${WIN32})
  set (BASE_SOURCES
    ${BASE_SOURCES}
	${CHROMIUM_BASE}/base/base_paths_win.cc
	${CHROMIUM_BASE}/base/time/time_win.cc
	${CHROMIUM_BASE}/base/process/process_win.cc
	${CHROMIUM_BASE}/base/process/process_handle_win.cc
        ${CHROMIUM_BASE}/base/process/process_info_win.cc
	${CHROMIUM_BASE}/base/synchronization/lock_impl_win.cc
	${CHROMIUM_BASE}/base/logging_win.cc
        ${CHROMIUM_BASE}/base/files/file_win.cc
	${CHROMIUM_BASE}/base/files/file_util_win.cc
	${CHROMIUM_BASE}/base/files/file_enumerator_win.cc
        ${CHROMIUM_BASE}/base/files/memory_mapped_file_win.cc
        #${CHROMIUM_BASE}/base/memory/shared_memory_win.cc
	${CHROMIUM_BASE}/base/debug/debugger_win.cc
	${CHROMIUM_BASE}/base/threading/platform_thread_win.cc
	${CHROMIUM_BASE}/base/threading/thread_local_win.cc
        #${CHROMIUM_BASE}/base/threading/thread_local_storage_win.cc
        #${CHROMIUM_BASE}/base/threading/worker_pool_win.cc
	${CHROMIUM_BASE}/base/strings/sys_string_conversions_win.cc
	${CHROMIUM_BASE}/base/sys_info_win.cc
        #${CHROMIUM_BASE}/base/platform_file_win.cc
        #${CHROMIUM_BASE}/base/debug/stack_trace_win.cc
        #${CHROMIUM_BASE}/base/synchronization/waitable_event_win.cc
        #${CHROMIUM_BASE}/base/synchronization/condition_variable_win.cc
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

set_target_properties(chromium_base PROPERTIES
  COMPILE_FLAGS -Wno-mismatched-tags
  COMPILE_FLAGS -Wno-gnu-statement-expression
  COMPILE_FALGS -Wno-non-virtual-dtor
  COMPILE_FLAGS -Wno-gnu-zero-variadic-macro-arguments
)
