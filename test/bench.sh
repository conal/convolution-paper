# stack bench 2>&1 > o
echo -n "\\stats{"
grep Group o | cut -c10-100 | sed 's/"/}{/' | tr -d '\n'
grep time o | cut -c22-29 | tr '\n' "#" | sed 's/#/}{/g'
echo "}"

