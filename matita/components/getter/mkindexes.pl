#!/usr/bin/perl -w
# To be invoked in a directory where a tree of XML files of the HELM library is
# rooted. This script will then creates INDEX files in all directories of the
# tree.
use strict;
my $index_fname = "INDEX";
sub getcwd() {
  my $pwd = `pwd`;
  chomp $pwd;
  return $pwd;
}
sub add_trailing_slash($) {
  my ($dir) = @_;
  return $dir if ($dir =~ /\/$/);
  return "$dir/";
}
sub indexable($) {
  my ($fname) = @_;
  return 1 if ($fname =~ /\.(ind|types|body|var|theory).xml/);
  return 0;
}
my @todo = (getcwd());
while (my $dir = shift @todo) {
  print "$dir\n";
  chdir $dir or die "Can't chdir to $dir\n";
  open LS, 'ls | sed \'s/\\.gz//\' | sort | uniq |';
  open INDEX, "> $index_fname"
    or die "Can't open $index_fname in " . getcwd() .  "\n";
  while (my $entry = <LS>) {
    chomp $entry;
    if (-d $entry) {
      print INDEX add_trailing_slash($entry) . "\n";
      push @todo, getcwd() . "/$entry";
    } else {
      print INDEX "$entry\n" if indexable($entry);
    }
  }
  close INDEX;
  close LS;
}
