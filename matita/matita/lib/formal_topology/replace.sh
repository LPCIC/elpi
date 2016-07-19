#!/bin/sh
for MA in `find -name "*.ma"`; do
   echo ${MA}; sed "s!$1!$2!g" ${MA} > ${MA}.new
   if diff ${MA} ${MA}.new > /dev/null; 
      then rm -f ${MA}.new; 
      else mv -f ${MA} ${MA}.old; mv -f ${MA}.new ${MA};
   fi
done

unset MA
