// Copyright (c) 2014 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "libfoster.h"

#include <cstdio> // for fread(), etc.
#include <cerrno>
#include <climits> // for SSIZE_MAX
#include <unistd.h> // for read(), write()

#ifdef OS_LINUX
#include <fcntl.h> // for O_RDWR
#include <cstring> // for strncpy and memset
#include <sys/ioctl.h>
#include <net/if.h> // for ifreq

#include <linux/if_tun.h> // for IFF_TUN
#endif

// Definitions of functions which are meant to be exposed to Foster code
// (at least for bootstrapping/utility purposes) rather than an implementation
// of runtime services themselves.

extern "C" void foster__assert(bool ok, const char* msg);

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
                                int32_t*      status) {
  foster__assert(bytes_offset >= 0 && bytes_offset < to->cap, "byte offset out of range");
  int64_t len = to->cap - bytes_offset;
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

  if (nwrote == 0) {
    *status = 0; // DONE
  } else if (nwrote == -1) {
    if (errno == EAGAIN) {
      *status = 2; // LATER
    } else {
      *status = 3; // ERROR
    }
  } else {
    *status = 1; // MORE
  }
  return int64_t(nwrote);
}

// noreturn
void foster__perror(const char* msg) {
  perror(msg);
  foster__assert(false, msg);
}

// See the comments in the root README.txt file about tuntap.
int64_t foster_posix_get_tuntap_fd() {
  int fd;

#ifdef OS_MACOSX
#error TODO set up tuntap code for OS X
#else
  fd = open("/dev/net/tun", O_RDWR);
  if (fd < 0) {
    foster__perror("foster_posix_get_tuntap_fd failed to open /dev/net/tun");
  }

  struct ifreq ifr; memset(&ifr, 0, sizeof(ifr));
  ifr.ifr_flags = IFF_TUN | IFF_NO_PI;
  strncpy(ifr.ifr_name, "tun1", IFNAMSIZ);

  int err = ioctl(fd, TUNSETIFF, (void*) &ifr);
  if (err < 0) {
    close(fd);
    foster__perror("foster_posix_get_tuntap_fd failed to connect to tun1");
  }
#endif

  return int64_t(fd);
}

}