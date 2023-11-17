// Copyright (c) 2014 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "build/build_config.h" // from Chromium, for OS_* defintions.

#include "libfoster.h"

#include <cstdio> // for fread(), etc.
#include <cerrno>
#include <climits> // for SSIZE_MAX
#include <unistd.h> // for read(), write(), access()
#include <cstring> // for strerror_r

#ifdef OS_LINUX
#include <fcntl.h> // for O_RDWR
// <cstring> provides strncpy and memset
#include <sys/ioctl.h>
#include <net/if.h> // for ifreq

#include <linux/if_tun.h> // for IFF_TUN
#elif defined(OS_MACOSX)
#include <fcntl.h> // for O_RDWR
#endif

// Definitions of functions which are meant to be exposed to Foster code
// (at least for bootstrapping/utility purposes) rather than an implementation
// of runtime services themselves.

extern "C" {

int64_t foster_stdin_read_bytes(foster_bytes* to, int32_t* status) {
  size_t nread = fread(to->bytes, 1, uint32_t(to->cap), stdin);
  if (feof(stdin) != 0) {
    *status = 0; // DONE
  } else if (ferror(stdin) != 0) {
    if (errno == EAGAIN) {
      *status = 2; // LATER
    } else {
      *status = 3; // ERROR
    }
  } else {
    *status = 1; // MORE
  }
  return int64_t(nread);
}

int64_t foster_posix_read_bytes(int64_t       fd,
                                foster_bytes* to,
                                int64_t       bytes_offset,
                                int64_t       trailing_pad,
                                int32_t*      status) {
  foster__assert(bytes_offset >= 0 && bytes_offset < to->cap, "byte offset out of range");
  int64_t len = (to->cap - bytes_offset) - trailing_pad;
  foster__assert(len <= SIZE_MAX, "can't read that many bytes!");

  ssize_t nread = read(int(fd), &to->bytes[bytes_offset], size_t(len));

  if (nread == 0) {
    *status = 0; // DONE
  } else if (nread == -1) {
    if (errno == EAGAIN) {
      *status = 2; // LATER
    } else {
      *status = 3; // ERROR
    }
  } else {
    *status = 1; // MORE
  }
  return int64_t(nread);
}

int64_t foster_posix_write_bytes(int64_t       fd,
                                 foster_bytes* from,
                                 int64_t       bytes_offset,
                                 int64_t       len,
                                 int32_t*      status) {
  foster__assert(bytes_offset >= 0 && bytes_offset < from->cap, "byte offset out of range");
  int64_t maxlen = from->cap - bytes_offset;
  foster__assert(len >= 0 && len <= maxlen && maxlen <= SSIZE_MAX, "can't write that many bytes!");

  ssize_t nwrote = write(int(fd), &from->bytes[bytes_offset], size_t(len));

  if (nwrote > 0) {
    *status = (nwrote == len) ? 0 : 1; // DONE : MORE
  } else {
    if (errno == EAGAIN) {
      *status = 2; // LATER
    } else {
      *status = 3; // ERROR
    }
  }
  return int64_t(nwrote);
}

int64_t foster_posix_write_bytes_to_file(
                                 foster_bytes* name,
                                 foster_bytes* from,
                                 int64_t       bytes_offset,
                                 int64_t       len,
                                 int32_t*      status) {
  foster__assert(bytes_offset >= 0 && bytes_offset < from->cap, "byte offset out of range");
  int64_t maxlen = from->cap - bytes_offset;
  foster__assert(len >= 0 && len <= maxlen && maxlen <= SSIZE_MAX, "can't write that many bytes!");

  FILE* f = fopen((const char*) &name->bytes[0], "w");
  if (!f) {
    *status = 3;
    return 0;
  }
  int64_t nwrote = 0;
  do {
    nwrote += foster_posix_write_bytes(fileno(f), from, bytes_offset + nwrote, len - nwrote, status);
  } while (*status == 1 && nwrote < len);

  if (nwrote == len) { *status = 0; }

  fclose(f);
  return nwrote;
}

// noreturn
void foster__perror(const char* msg) {
  perror(msg);
  foster__assert(false, msg);
}

// See the comments in the root README.txt file about tuntap.
int64_t foster_posix_get_tuntap_fd() {
  int fd;

#ifdef OS_LINUX
  fd = open("/dev/net/tun", O_RDWR);
  if (fd < 0) {
    foster__perror("foster_posix_get_tuntap_fd failed to open /dev/net/tun");
  }

  struct ifreq ifr; memset(&ifr, 0, sizeof(ifr));
  ifr.ifr_flags = IFF_TUN | IFF_NO_PI;
  strncpy(ifr.ifr_name, "tun8", IFNAMSIZ);

  int err = ioctl(fd, TUNSETIFF, (void*) &ifr);
  if (err < 0) {
    close(fd);
    foster__perror("foster_posix_get_tuntap_fd failed to connect to tun8");
  }
#elif defined(OS_MAC)
  fd = open("/dev/tun8", O_RDWR);
  if (fd < 0) {
    foster__perror("foster_posix_get_tuntap_fd failed to open /dev/tun8");
  }
#else
#error Haven't yet coded support for tun/tap on this platform...
#endif

  return int64_t(fd);
}

int32_t foster_posix_access__autowrap(foster_bytes* path, int32_t mode) {
  return int32_t(access((const char*) &path->bytes[0], mode));
}

int32_t foster_posix_open3__autowrap(foster_bytes* path, int32_t flags, int32_t mode) {
  return int32_t(open((const char*) &path->bytes[0], flags, mode));
}

int32_t foster_posix_getErrno() { return errno; }

int32_t foster_posix_strError__autowrap(foster_bytes* b, int32_t errnum) {
  char* msg = strerror(errnum);
  strncpy((char*)&b->bytes[0], msg, (int)b->cap);
  return strlen((char*)&b->bytes[0]);
}

}
