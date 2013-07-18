exec 2>&1
echo "module guarded-recursion where" >$3
git ls-files guarded-recursion |
  grep '\.agda$' |
  sed -e 's|\(.*\)\.agda|import \1|' |
  tr / . >>$3
