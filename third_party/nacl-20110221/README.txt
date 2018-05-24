URL: https://nacl.cr.yp.to/
Version: 20110221
Description: Cryptography library
License: public domain
License File: none
Local Modifications:
  Customized build script to:
    * Use "foster" instead of machine name
    * Not generate C++ wrappers

TODO: randombytes can block;
      randombytes is used by crypto_box and crypto_sign.
