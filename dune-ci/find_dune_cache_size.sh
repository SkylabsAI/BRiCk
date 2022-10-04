#! /bin/bash

# This script should be executed inside dune cache
# directory to fetch the cache size for specified time

# Usage: $0 time_option(atime/mtime/ctime) time_amount
# time_amount is for instance "7" (7 days)

log_file="dune_time.log"
tmp_file="/tmp/dune_find_temp.log"

time_cat=$1
fi_date=$2

usage()
{
    echo "Usage: $0 time_option(atime/mtime/ctime) time_amount"
    echo -e "\n example:"
    echo -e "$0 -mtime -7 \t - Compute size for modified-files in last 7 days"
    echo -e "\t time_amount \t - +n - changed before n days"
    echo -e "\t time_amount \t - -n - changed during last n days"
    echo -e "\t time_amount \t -  n - exactly n days"
}

[[ $time_cat == '-atime' ]] || [[ $time_cat == '-mtime' ]] || [[ $time_cat == '-ctime' ]] || err=1

if [[ $err -ge 1 ]] ; then
    echo -e "invalid args\n"
    usage
    exit 1
fi

find . $time_cat ${fi_date} -type f -exec ls -lstku {} \; > $tmp_file

# Sum file sizes
v=0 ; for i in `cat $tmp_file  | awk '{print $1'}` ; do  v=$(($v + $i)) ; done
echo "${time_cat:1} $fi_date days : $v " | tee -a $log_file

#Cleanup tmp file
rm -rf $tmp_file
