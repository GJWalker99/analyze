#!/usr/bin/perl -w
#
# compare.pl ONE TWO
#
# compare two files of full language paradigms for essential differences
#
# Raphael Finkel 8/2010
# Changes
#  9/2014: now insensitive to initial case of conjugation name

use Unicode::Normalize;
use utf8;
use strict;

my $path = $0; $path =~ s/[\w\.]+$//; unshift @INC, $path; require "common.pl";
# readPlatFile

my $complainNoFirst = 0; # boolean: complain about missing word in first file

sub init {
	@ARGV == 2 or die("usage: $0 ONE TWO\n");
	binmode STDOUT, ":utf8";
	binmode STDIN, ":utf8";
	binmode STDERR, ":utf8";
	print "Not warning about missing lemmata in first file.\n"
		unless $complainNoFirst;
} # init

sub showData {
	my ($ptr) = @_;
	for my $column (sort keys %$ptr) {
		print "$column: " . join(" ", @{${$ptr}{$column}}) . "\n";
	} # each column
} # showData

my $numLemmata;
my %missing; # lemmata in one file but not the other.
sub compareColumns {
	my ($column, $contents1, $contents2, $names1, $names2) = @_;
	my ($index, %content1, %content2); # indexed by name
	my $length = scalar @$contents1;
	if (!defined($numLemmata)) {
		$numLemmata = $length;
		# print "I see $numLemmata lemmata\n";
	} else { # check column length
		if ($numLemmata != $length){
			print STDERR "Column $column has $length, not $numLemmata entries.\n"
				. "\tmaybe there is a null entry?  Use NONE instead\n";
			exit(1);
		}
	}
	$index = 0;
	# print STDERR "names1: " . join(' ', @$names1) . "\n";
	for my $name1 (@$names1) {
		$name1 = lcfirst $name1;
		$content1{$name1} = ${$contents1}[$index];
		if (!defined($content1{$name1})) {
			print STDERR "key $name1 for $column exists but not data; " .
				" index $index\n";
		}
		$index += 1;
	}
	$index = 0;
	for my $name2 (@$names2) {
		$name2 = lcfirst $name2;
		$content2{$name2} = ${$contents2}[$index];
		$index += 1;
	}
	for my $name1 (keys %content1) {
		next if exists($missing{$name1});
		# print "first file has $name1\n";
		my $data1 = $content1{$name1};
		if (!defined($data1)) {
			print STDERR "No data1 for $column: $name1\n";
		print STDERR "content1 for $name1: " .
			join(' ', @$contents1) .  "\n";
		}
		my $data2 = $content2{$name1};
		if (!defined($data2)) {
			print "no $name1 in the second file\n";
			$missing{$name1} = 1;
			next;
		}
		if ($data1 ne $data2) {
			# $data1 =~ s/i/ı/g; # normalize
			# $data2 =~ s/i/ı/g; # normalize
			print "$column: $data1 vs $data2 ($name1)"
				.  (NFD($data1) eq NFD($data2)
					? " (just differ in presentation)\n"
					: "\n");
		}
		delete $content2{$name1};
		# print "I have seen $name1 in both files\n";
	} # each element in the first file
	for my $name2 (keys %content2) {
		next if exists($missing{$name2});
		print "no $name2 in the first file\n" if $complainNoFirst;
		$missing{$name2} = 1;
	} # each extra element in the second file
} # compareColumns

sub doCompare {
	my $dataPtr1 = readPlatFile($ARGV[0]);
	# showData($dataPtr1);
	my $dataPtr2 = readPlatFile($ARGV[1]);
	# showData($dataPtr2);
	my ($conjKey1, $conjKey2);
	for my $conjName ('Gloss', 'English', 'CONJ', 'Lexeme', 'IC') {
		$conjKey1 = lcfirst $conjName;
		last if defined(${$dataPtr1}{$conjKey1});
	}
	for my $conjName ('Gloss', 'English', 'CONJ', 'Lexeme', 'IC') {
		$conjKey2 = lcfirst $conjName;
		last if defined(${$dataPtr2}{$conjKey2});
	}
	for my $column (sort keys %$dataPtr1) {
		if (defined(${$dataPtr2}{$column})) {
			if (!defined(${$dataPtr2}{$conjKey2})) {
				print "No $conjKey2 for column $column\n";
				next;
			}
			compareColumns($column,
				${$dataPtr1}{$column}, ${$dataPtr2}{$column},
				${$dataPtr1}{$conjKey1}, ${$dataPtr2}{$conjKey2});
		} else {
			print STDERR "Only in $ARGV[0]: $column\n"
				unless $column =~ /ic|conj|lexeme|gloss|english/i;
		}
	} # each column
	for my $column (keys %$dataPtr2) {
		if (!defined(${$dataPtr1}{$column})) {
			print STDERR "Only in $ARGV[1]: $column\n"
				unless $column =~ /ic|conj|lexeme|gloss|english/i;
		}
	} # each column
} # doCompare

init();
doCompare();
