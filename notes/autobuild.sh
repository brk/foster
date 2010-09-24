FOSTER_SRC_ROOT=..
FILES=`ls *.rst conf.py`
echo "Watching files: " ${FILES}
python ${FOSTER_SRC_ROOT}/scripts/watch.py ${FILES} - 'make html'
