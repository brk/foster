set (hdrhist_ROOT ${PROJECT_SOURCE_DIR}/third_party/HdrHistogram_c/)

set (hdrhist_SRCS
  ${hdrhist_ROOT}/src/hdr_encoding.c
  ${hdrhist_ROOT}/src/hdr_histogram.c
  ${hdrhist_ROOT}/src/hdr_histogram_log.c
  ${hdrhist_ROOT}/src/hdr_interval_recorder.c
  ${hdrhist_ROOT}/src/hdr_thread.c
  ${hdrhist_ROOT}/src/hdr_time.c
  ${hdrhist_ROOT}/src/hdr_writer_reader_phaser.c
)

include_directories(${hdrhist_ROOT}/src)

