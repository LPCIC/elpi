AC_INIT(matita/matitaTypes.ml)

# Distribution settings
# (i.e. settings (automatically) manipulated before a release)
DEBUG_DEFAULT="true"
DEFAULT_DBHOST="mysql://mowgli.cs.unibo.it"
RT_BASE_DIR_DEFAULT="`pwd`/matita"
MATITA_VERSION="0.99.3"
DISTRIBUTED="yes"  # "yes" for distributed tarballs
# End of distribution settings

SRCROOT=`pwd`
AC_CHECK_PROG(HAVE_OCAMLC, ocamlc, yes, no)
if test $HAVE_OCAMLC = "no"; then
  AC_MSG_ERROR(could not find ocamlc)
fi
AC_CHECK_PROG(HAVE_OCAMLOPT, ocamlopt, yes, no)
if test $HAVE_OCAMLOPT = "no"; then
  AC_MSG_WARN(could not find ocamlopt: native code compilation disabled)
fi
AC_CHECK_PROG(HAVE_OCAMLFIND, ocamlfind, yes, no)
if test $HAVE_OCAMLFIND = "yes"; then
  OCAMLFIND="ocamlfind"
else
  AC_MSG_ERROR(could not find ocamlfind)
fi
AC_CHECK_PROG(HAVE_LABLGLADECC, lablgladecc2, yes, no)
if test $HAVE_LABLGLADECC = "yes"; then
  LABLGLADECC="lablgladecc2"
else
  AC_MSG_ERROR(could not find lablgladecc2)
fi
AC_CHECK_PROG(HAVE_CAMLP5O, camlp5o, yes, no)
if test $HAVE_CAMLP5O = "yes"; then
  CAMLP5O="camlp5o"
else
  AC_MSG_ERROR(could not find camlp5o)
fi

# look for METAS dir

LIBSPATH="`pwd`/components"
OCAMLPATH="$LIBSPATH/METAS"

# creating META.*

echo -n "creating METAs ... "
for f in $OCAMLPATH/meta.*.src; do
  basename=`basename $f`
  metaname=`echo $basename | sed 's/meta\.\(.*\)\.src/\1/'`
  dirname=`echo $metaname | sed 's/^helm-//'`
  metafile="$OCAMLPATH/META.$metaname"
  cp $f $metafile
  echo "directory=\"$LIBSPATH/$dirname\"" >> $metafile
done
echo "done"

# (libs) findlib requisites

FINDLIB_LIBSREQUIRES="\
expat \
gdome2 \
http \
lablgtk2 \
netstring \
ulex08 \
zip \
"

# (Matita) findlib requisites

FINDLIB_COMREQUIRES="\
helm-disambiguation \
helm-grafite \
helm-grafite_engine \
helm-ng_disambiguation \
helm-ng_cic_content \
helm-grafite_parser \
helm-content_pres \
helm-ng_paramodulation \
helm-ng_tactics \
"
FINDLIB_CREQUIRES=" \
$FINDLIB_COMREQUIRES \
"
FINDLIB_REQUIRES="\
$FINDLIB_CREQUIRES \
lablgtk2.glade \
"
for r in $FINDLIB_LIBSREQUIRES $FINDLIB_REQUIRES
do
  AC_MSG_CHECKING(for $r ocaml library)
  if OCAMLPATH=$OCAMLPATH:/usr/lib/ocaml:../ $OCAMLFIND query $r &> /dev/null; then
    AC_MSG_RESULT(yes)
  else
    AC_MSG_ERROR(could not find $r ocaml library)
  fi
done

OCAMLFIND_COMMANDS=""
# AC_CHECK_PROG(HAVE_OCAMLC_OPT, ocamlc.opt, yes, no)
# if test $HAVE_OCAMLC_OPT = "yes"; then
#   if test "$OCAMLFIND_COMMANDS" = ""; then
#     OCAMLFIND_COMMANDS="ocamlc=ocamlc.opt"
#   else
#     OCAMLFIND_COMMANDS="$OCAMLFIND_COMMANDS ocamlc=ocamlc.opt"
#   fi
# fi
# AC_CHECK_PROG(HAVE_OCAMLOPT_OPT, ocamlopt.opt, yes, no)
# if test $HAVE_OCAMLOPT_OPT = "yes"; then
#   if test "$OCAMLFIND_COMMANDS" = ""; then
#     OCAMLFIND_COMMANDS="ocamlopt=ocamlopt.opt"
#   else
#     OCAMLFIND_COMMANDS="$OCAMLFIND_COMMANDS ocamlopt=ocamlopt.opt"
#   fi
# fi
if test "$OCAMLFIND_COMMANDS" != ""; then
  OCAMLFIND="OCAMLFIND_COMMANDS='$OCAMLFIND_COMMANDS' $OCAMLFIND"
fi

AC_MSG_CHECKING(--enable-debug argument)
AC_ARG_ENABLE(debug,
  [  --enable-debug	  Turn on debugging],
  [GIVEN="yes";
   case "${enableval}" in
   yes) DEBUG=true ;;
   no)  DEBUG=false ;;
   *) AC_MSG_ERROR(bad value ${enableval} for --enable-debug) ;;
  esac],
  [GIVEN="no"; DEBUG="$DEBUG_DEFAULT"])
MSG=$GIVEN
if test "$DEBUG" = "true"; then
  MSG="$MSG, debugging enabled."
else
  MSG="$MSG, debugging disabled."
fi
AC_MSG_RESULT($MSG)

AC_MSG_CHECKING(--enable-annot argument)
AC_ARG_ENABLE(annot,
  [  --enable-annot	  Turn on -dtypes compilation option],
  [GIVEN="yes";
   case "${enableval}" in
   yes) ANNOT=true;;
   no)  ANNOT=false;;
   *) AC_MSG_ERROR(bad value ${enableval} for --enable-annot) ;;
  esac],
  [GIVEN="no"; ANNOT="false"])
MSG=$GIVEN
if test "$ANNOT" = "true"; then
  MSG="$MSG, type annotation enabled."
else
  MSG="$MSG, type annotation disabled."
fi
AC_MSG_RESULT($MSG)


AC_MSG_CHECKING(--with-runtime-dir argument)
AC_ARG_WITH(runtime-dir,
  [  --with-runtime-dir      Runtime directory (current working directory if not given)],
  [ RT_BASE_DIR="${withval}" ],
  [ RT_BASE_DIR="$RT_BASE_DIR_DEFAULT" ])
MSG="$RT_BASE_DIR"
if test "yes" = "$RT_BASE_DIR"; then
  MSG="
** error:                                                                  **
**  empty --with-runtime-dir argument, please use --with-runtime-dir=value **"
fi
AC_MSG_RESULT($MSG)

AC_MSG_CHECKING(--with-dbhost argument)
AC_ARG_WITH(dbhost,
  [  --with-dbhost           SQL database hostname],
  [ DBHOST="${withval}" ],
  [ DBHOST="$DEFAULT_DBHOST" ])
MSG="$DBHOST"
if test "yes" = "$DBHOST"; then
  MSG="
** error:                                                                  **
**  empty --with-dbhost argument, please use --with-dbhost=value           **"
fi
AC_MSG_RESULT($MSG)

AC_SUBST(CAMLP5O)
AC_SUBST(DBHOST)
AC_SUBST(DEBUG)
AC_SUBST(ANNOT)
AC_SUBST(DISTRIBUTED)
AC_SUBST(FINDLIB_CREQUIRES)
AC_SUBST(FINDLIB_REQUIRES)
AC_SUBST(HAVE_OCAMLOPT)
AC_SUBST(LABLGLADECC)
AC_SUBST(MATITA_VERSION)
AC_SUBST(OCAMLFIND)
AC_SUBST(OCAMLPATH)
AC_SUBST(RT_BASE_DIR)
AC_SUBST(SRCROOT)
AC_SUBST(TRANSFORMER_MODULE)

AC_OUTPUT([
  components/extlib/componentsConf.ml
  matita/matita.conf.xml
  matita/buildTimeConf.ml
  matita/help/C/version.txt
  Makefile.defs
])

