#!/usr/bin/perl -w

=head1 SYNOPSIS

Removes spaces from stdin to the right of ==> of each line, then directs
unbuffered to stdout.  Understands widths of Unicode characters, lining up
columns as appropriate, either right- (if any RTL character encountered)
or left-justified.

Input comes form $ARGV[0].

Divides long lines into multiple lines if $ARG[1] = 'fold'.

If it exists, $ARGV[2] indicates width allowed.

=cut

use strict;
use utf8;

binmode STDIN, ":utf8";
binmode STDOUT, ":utf8";
binmode STDERR, ":utf8";

# global variables
my ($rightToLeft,
	$widthAllowed,
	@width,
);

$rightToLeft = 0;
if (defined($ARGV[1]) && $ARGV[1] eq 'fold') {
	$widthAllowed = $ARGV[2];
	if (!defined($widthAllowed)) {
		$widthAllowed = 200; # unless we learn otherwise
		if (-t STDOUT) {
			my $stty = `stty -a -F /dev/tty`;
			$stty =~ /columns (\d+)/;
			$widthAllowed = $1 if defined($1);
		} else {
			$widthAllowed = 80;
		}
	}
	# print "folding, $widthAllowed maxwidth\n"; # debug
} else {
	$widthAllowed = 100000; # no limit
}

sub printedLength {
	my ($string) = @_;
	my $result = 0;
	# if (!$rightToLeft and $string =~ /\p{BidiR}/) {$rightToLeft = 1;}
    while ($string =~ s/\p{InHangulSyllables}//) {
        $result += 2; # double-width forms
        # print "hangul\n";
	}
	while ($string =~ s/\PM\pM*//) {
		# print "[$string]";
		$result += 1
	}
	return $result;
} # printedLength

require 5.008; # new Unicode features
use utf8;
open(INPUT, "<:utf8", $ARGV[0]) or die ("can't open $ARGV[0]");
	# work around a Perl hang bug
$| = 1; # unbuffered output
my ($line, @toPrint, $succeeding, $maxNumColumns);
my %counts;
while (defined($line = <INPUT>)) {
	# print "working on $line\n";
	if ($line =~ /exception: (.*)/) {
		my $error = $1;
		print "Faulty KATR theory: $error\n";
		exit(0);
	}
	if ($line =~ /^(\w+) \[?([^\]]*)\]? =\s*(.*)/) {
		my ($node, $form, $result) = ($1, $2, $3);
		$node = "" if $node =~ /\bTEST\b/i;
		$node =~ s/u([0-9abcdef]{4})/sprintf('%c',hex($1))/eg;
		$node =~ s/U([0-9abcdef]{4})/uc sprintf('%c',hex($1))/eg;
		$form = "" if $form =~ /^(all|forms)$/;
		$result =~ s/ //g;
		$result =~ s/[∅Ø](\w)/$1/g;
		$result =~ tr/\|/\t/;
		$result =~ tr/,/ /;
		push @toPrint, "$node ${form}\t$result";
		# print "pushing $node ${form} =\t$result\n";
		$succeeding = 1;
		# print "debug: $node $form = $result\n";
	} elsif ($line =~ /(\S+) counting (.*) from (.*)\n/) {
		my ($node, $rule, $from) = ($1, $2, $3);
		$node =~ s/u([0-9abcdef]{3,4})/sprintf('%c',hex($1))/eg;
		$from =~ s/u([0-9abcdef]{3,4})/sprintf('%c',hex($1))/eg;
		# print "empty: $node\n" if $rule eq '';
		$counts{"$node $rule $from"} += 1;
	} else {
		next if $line =~ /\ball\b/;
		print $line if $line =~ /\?/ or $line =~ /</;
	}
} # each line of input
if (!defined($succeeding)) {
	print "The theory produces no output.\n";
	exit(0);
}

$maxNumColumns = 0;
# calculate widths
foreach $line (@toPrint) {
	my @parts = split(/\t/, $line);
	my $numColumns = $#parts;
	$maxNumColumns = $numColumns if $numColumns > $maxNumColumns;
	# print "numColumns $numColumns\n";
	foreach my $column (0 .. $#parts) {
		my $pl = printedLength($parts[$column]);
		# print "[$parts[$column]] ($pl)\n";
		$width[$column] = $pl
			if !defined($width[$column]) or $width[$column] < $pl;
	} # one column
} # one line

my $startColumn = 1; # we always print column 0
while ($startColumn <= $maxNumColumns) { # print more lines
	my $curWidth = $width[0] + 2;
	my $pastEndColumn = $startColumn;
	while (1) {
		$curWidth += $width[$pastEndColumn] + 2;
		# print "including $pastEndColumn gives width $curWidth\n";
		# print "widthAllowed is $widthAllowed; pastEndColumn is $pastEndColumn\n";
		last if ($curWidth > $widthAllowed and $pastEndColumn > 1);
		# print "not too wide\n";
		$pastEndColumn += 1;
		last if $pastEndColumn > $maxNumColumns;
		# print "more columns\n";
	}
	# print columns 0, $startColumn .. $pastEndColumn-1
	foreach $line (@toPrint) { # one line
		# print "widthAllowed $widthAllowed startColumn $startColumn pastEndColumn $pastEndColumn\n";
		my @parts = split(/\t/, $line);
		foreach my $column (0, $startColumn .. $pastEndColumn-1) {
			my $thisPart = $parts[$column];
			$thisPart = "∅" unless defined($thisPart);
			# $thisPart .= ' =' if $column == 0;
			my $pad = " " x ($width[$column] - printedLength($thisPart));
			if ($rightToLeft and $column != 0) {
				print sprintf("%s%s  ", $pad, $thisPart);
			} else {
				print sprintf("%s%s  ", $thisPart, $pad);
			}
		} # one column
		print "\n";
	} # one line
	$startColumn = $pastEndColumn;
	print "\n" unless $startColumn > $maxNumColumns;
} # print more lines

if (scalar keys %counts) {
	print "\n";
}
for my $countIndex (sort keys %counts) {
	$countIndex =~ /(\S+) (.*) (.*)/;
	my ($node, $rule, $from) = ($1, $2, $3);
	print "$node $rule = count $counts{$countIndex} from $from\n";
}
