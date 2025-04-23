#!/usr/bin/perl

use strict;
use warnings;
use HTML::Template;

my $str = ` coqc -R . Mendelson Deduction.v`;
$str =~ s/^(.*?")//;
$str =~ s/(.*)".*/$1/s;

my ($theorem, $proof);
if ($str =~ /^(.*?\\\\)(.*)/)
{
    $theorem = $1;
    $proof = $2;
}

my $template = HTML::Template->new(filename => 'output.tmpl');

# # fill in some parameters
$template->param(proof => $proof);
$template->param(theorem => $theorem);

open(my $fh, ">", "T1.tex")
    or die "cannot open > T1_.tex: $!";

print $fh $template->output();
close($fh);

system("pdflatex T1.tex");
