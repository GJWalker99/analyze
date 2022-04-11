#!/usr/bin/perl -w
#
# align.pl [width]
# align columns by adding spaces
#
# Raphael Finkel 2/2007

use strict;
use Unicode::EastAsianWidth;

sub visualLength {
	my ($string) = @_;
	# print "[$string] ";
	$string =~ s/\pM//g; # Unicode marks have 0 width
	$string =~ s/\[\d+m//g; # Ascii color indicators have 0 width
	my $answer = 0;
	while ($string =~ s/\p{InFullwidth}//) {
		$answer += 2; # double-width forms
		# print "double width\n";
	}
	while ($string =~ s/\X//) {
		# print "ordinary\n";
		$answer += 1;
	}
	# print "$answer\n";
	return $answer;
} # visualLength

sub oneGroup {
	my ($text) = @_; # multiple lines to be aligned
	my @widths;
	my $lastColumn = 0;
	$text =~ s/\x{feff}//; # remove BOM if present.
	for my $line (split /\n/, $text, 0) { # discover widths
		next if $line =~ /^(\s*|%.*)$/;
		my @parts = split /\s+(?=\S)/, $line;
		$lastColumn = $#parts if $#parts > $lastColumn;
		for my $index (0 .. $#parts) {
			my $length = visualLength(shift @parts);
			if (defined($widths[$index])) {
				$widths[$index] = $length if $length > $widths[$index];
			} else {
				$widths[$index] = $length;
			}
		}
	} # each line: discover widths
	if ($lastColumn == 0) { # no real lines in this group
		print $text;
		return;
	}
	my $maxWidth = defined($ARGV[0]) ? $ARGV[0] : 10000;
	my $startingColumn = 1; # assume column 0 must repeat in each group
	while ($startingColumn <= $lastColumn) { # print as much as will fit screen
		my @toPrint;
		my $didColumn = 0;
		for my $line (split /\n/, $text) { 
			next if $line =~ /^\s*$/;
			if ($line =~ /^%/) { # treat comment lines specially
				if ($startingColumn == 1) { # first group: print it
					print "$line\n";
				}
				next;
			}
			my @parts = split /\s+(?=\S)/, $line, 0;
			my $part = $parts[0];
			my $breadth = $widths[0] + length($part) - visualLength($part);
			my $outLine = sprintf('%-' . ($breadth+1) . 's', $parts[0]);
			my $remainingWidth = $maxWidth - $widths[0];
			for my $index ($startingColumn .. $lastColumn) {
				last if ($index != $startingColumn and # must make progress!
					$widths[$index] > $remainingWidth);
				$didColumn = $index;
				$remainingWidth -= $widths[$index];
				$part = $parts[$index];
				next unless defined($part);
				$breadth = $widths[$index] + length($part) - visualLength($part);
				$outLine = $outLine . sprintf('%-' . ($breadth+1) . 's', $part);
			} # each part
			$outLine =~ s/\s+$//; # trim
			push @toPrint, $outLine;
		} # each line
		print STDOUT join("\n", @toPrint) . "\n\n";
		$startingColumn = $didColumn + 1;
		# print "still need columns $startingColumn .. $lastColumn\n";
	} # each group of lines to fit screen
} # oneGroup

sub printAll {
	binmode STDIN, ":utf8";
	binmode STDOUT, ":utf8";
	$/ = "\n\n";
	while (defined(my $group = <STDIN>)) {
		oneGroup($group);
	}
} # printAll

printAll();
