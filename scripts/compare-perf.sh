#1/bin/bash

# Script by Eric Anholt <http://anholt.net/compare-perf/>
# Tweaked by Ben Karel to remove bias.

i=0

rm -f before after

while true; do
	$2 $1 >> before
	$3 $1 >> after

	# Sometimes it's nice to see the numbers too, so uncomment
	# that.

	# cat before after

	# nuke the data from the first run.  We usually don't want the
	# first run, because that's when we're loading disk cache,
	# warming up the GPU, etc.
	if test $i = 0; then
		rm -f before after
	fi

	# once we've got 3 points each, start running ministat.
	if test $i -gt 3; then
		ministat before after
	fi

        sleep 0.1

	i=$(($i + 1))
done
