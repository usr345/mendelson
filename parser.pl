#!/usr/bin/perl

use strict;
use warnings;
use utf8;
use open qw( :std :encoding(UTF-8) );

open(my $fh, "<", "Sequent.thy")
    or die "cannot open < Sequent.thy: $!";

my %table = (
    '\<turnstile>' => '⊢',
    '\<longrightarrow>' => '⊃',
    '\<and>' => '∧',
    '\<or>' => '∨',
    '\<not>' => '¬',
    '\<exists>' => '∃',
    '\<forall>' => '∀',
);
while (my $line = <$fh>)
{
    if ($line =~ /(lemma.*?)"(.*)"/)
    {
        my $formula = $2;
        while (my ($key, $value) = each(%table))
        {
            $formula =~ s/\Q$key\E/$value/g;
        }

        print qq{$1"$formula"\n};
    }
}
close($fh);
