echo replacing gtest includes
find base -type f | xargs perl -pi -e 's@^\#include "base/gtest_prod_util.h"@//#include "base/gtest_prod_util.h"@g'
echo replacing FRIEND_TESTs...
find base -type f | xargs perl -pi -e 's@ FRIEND_TEST_@ //FRIEND_TEST_@g'
