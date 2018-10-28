FOSTER_SRC_ROOT=..
FILES=`ls *.rst conf.py`
echo "Watching files: " ${FILES}
make html
python ${FOSTER_SRC_ROOT}/scripts/watch.py ${FILES} - 'make html'
