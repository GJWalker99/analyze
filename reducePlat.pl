#!/usr/bin/perl -w
#
# reducePlat.pl PLAT.data
#
# Tries to find commonalities to create a reduced version of the plat.
# Introduces TEMPLATE lines to represent common suffixes for each MPS.
# Introduces stems to represent common prefixes for each inflection class.
#
# Raphael Finkel 10/2010, 2/2014

use strict;
use utf8;
use Unicode::EastAsianWidth;

# use Data::Dumper;

my $path = $0; $path =~ s/([\w\.]+)$//;
	my $progName = $1;
	unshift @INC, $path; require "common.pl";
# readPlatFile, commonPrefix, commonSuffix

# constants
my $screenWidth = 75;
my $alignProgram = "${path}align.pl $screenWidth";
# $alignProgram = "cat";
my @conjNames = ('ic', 'gloss', 'conj', 'english', 'lexeme');
my $conjNamesPattern = '(' . join('|',@conjNames) . ')';

# globals
my (
	$dataPtr, # ptr to hash (indexed by MPS name) of arrays of columns
	$reducedDataPtr, # ptr to hash (indexed by MPS name) of arrays of columns
		# after template has been applied
	$numConjugations, # how many conjugations (computed by computeTemplates)
	@stems, # hash (indexed by conj number) of common parts of conjugations
	%prefixes, # hash (indexed by MPS name) of template prefixes
	%suffixes, # hash (indexed by MPS name) of template suffixes
	@MPSNames, # array of MPS names, in order wrt input file
);

sub init {
	binmode STDIN, ":utf8";
	binmode STDOUT, ":utf8";
	binmode STDERR, ":utf8";
	if (!defined($ARGV[0])) {
		die("Usage: $0 PlatFile\n");
	}
	$dataPtr = readPlatFile($ARGV[0]);
	findMPSNames();
} # init

sub findMPSNames {
	my @names;
	open FILE, $ARGV[0];
	binmode FILE, ":utf8";
	$/ = "\n\n";
	while (my $text = <FILE>) { # one chunk
		$text =~ s/\x{feff}//; # remove BOM if present
		for my $line (split(/\n/, $text)) {
			$line =~ s/%.*//;
			next unless $line =~ /\w/; # ignore comment lines
			push @names, split(/\s+(?=\S)/, $line, 0);
			last; # only interested in header of each chunk
		} # one line
	} # one chunk
	close FILE;
	# print "names are " . join('|', @names) . "\n";
	for my $name (@names) {
		$name = lcfirst($name);
		$name =~ s/\s+$//;
		push @MPSNames, $name;
	} # each name
	# print "MPS names: " . join(', ', @MPSNames) . "\n";
} # findMPSNames

sub computeTemplates {
	for my $MPS (@MPSNames) {
		my $columnPtr = ${$dataPtr}{$MPS};
		# print "before MPS: " . join(' ', @$columnPtr) . "\n";
	# compute common prefix, suffix to form template
		my $prefix = ${$columnPtr}[0];
		my $suffix = ${$columnPtr}[0];
		if (defined($numConjugations)) {
			die("wrong number of conjugations in $MPS;" .
				" saw " . scalar @$columnPtr . ", expected $numConjugations")
					unless @$columnPtr == $numConjugations;
		} else {
			$numConjugations = scalar @$columnPtr;
			# print "deriving numConjugations $numConjugations from $MPS\n";
		}
		for my $index (1 .. $numConjugations - 1) {
			my $entry = ${$columnPtr}[$index];
			next if length($entry) < 2;
			$prefix = commonPrefix($prefix, $entry);
			$suffix = commonSuffix($suffix, $entry);
		}
		$prefixes{$MPS} = "$prefix";
		$suffixes{$MPS} = "$suffix";
		# print "\ttemplate: $prefixes{$MPS} 1A $suffixes{$MPS}\n";
	# apply template to all elements
		my @newColumn;
		for my $exponence (@{$columnPtr}) {
			my $temp = $exponence;
			$temp =~ s/^\Q$prefix\E//;
				# or warn("cannot remove prefix $prefix from $exponence\n");
			$temp =~ s/\Q$suffix\E$//;
				# or warn("cannot remove suffix $suffix from $exponence\n");
			push @newColumn, $temp;
		}
		${$reducedDataPtr}{$MPS} = \@newColumn;
		# print "after MPS: " . join(' ', @newColumn) . "\n";
	} # each MPS
	# print STDERR "after templating: ${${$dataPtr}{'NomPl'}}[2]\n";
} # computeTemplates

sub computeStems {
	for my $index (0 .. $numConjugations - 1) { # compute stem for this conj
		my $stem;
		for my $MPS (@MPSNames) {
			next if $MPS =~ /^(gloss|conj|english)$/i;
			my $columnPtr = ${$reducedDataPtr}{$MPS};
			if (!defined($stem)) {
				$stem = ${$columnPtr}[$index];
				# print STDERR "starting stem (MPS $MPS): $stem\n";
			} else {
				my $exponence = ${$columnPtr}[$index];
				my $newStem = commonPrefix($stem, $exponence);
				if ($newStem eq '') { # see if we can't find stem inside
					$newStem = commonPart($stem, $exponence);
					if (length($newStem) < 2) {
						# print STDERR "\tStem of $stem would be empty because of $MPS: " .
						# 	"$exponence\n";
					} else {
						$stem = $newStem;
						# print STDERR "\trecovering from $exponence: $stem\n";
					}
				} else {
					$stem = $newStem;
				}
				# print STDERR "after seeing $exponence ($MPS) stem is $stem\n";
			}
		} # each MPS
		# print STDERR "\tStem of conjugation $index is $stem\n";
		push @stems, $stem;
	} # each conjugation "index"
	# print "The stems are: " . join(' ', @stems) . "\n";
} # computeStems

# find longest common part between two strings that is a prefix of either one 
sub commonPart {
	my ($first, $second) = @_;
	return $first if $second =~ /\Q$first\E/;
	return $second if $first =~ /\Q$second\E/;
	my $pattern1 = '';
	for my $letter (split //, $second) {
		my $newPattern = "$pattern1$letter";	
		if ($first !~ /\Q$pattern1\E/) {
			last;
		}
		$pattern1 = $newPattern;
	} # each letter of;
	my $pattern2 = '';
	for my $letter (split //, $first) {
		my $newPattern = "$pattern2$letter";	
		if ($second !~ /\Q$pattern2\E/) {
			last;
		}
		$pattern2 = $newPattern;
	} # each letter of second
	return (length $pattern1 > length $pattern2) ? $pattern1 : $pattern2;
} # commonPart

sub addSuffix {
	# add _1 or increment the final part
	my ($string) = @_;
	if ($string =~ /(.*)_(\d+)$/) {
		$string = "$1_" . ($2 + 1);
	} else {
		$string .= "_1";
	}
	return $string;
} # addSuffix

my %counts; # $counts{$conjugation} = number of tokens of this type
my %formsToConj; # $formsToConj{$combinedForms} = conjugation name
my %reflections; # $reflections{$conjugation} = canonical conjugation name

sub printPlat {
	open OUT, "| $alignProgram" or die("can't open align.nr\n");
	binmode OUT, ":utf8";
# boilerplate
	print OUT "% automatically generated by $progName from $ARGV[0]\n\n";
	print OUT "ABBR 1 1C1S2C\n\n";
# column headers
	print OUT "IC ";
	for my $MPS (@MPSNames) {
		next if $MPS =~ /^$conjNamesPattern$/i;
		print OUT " $MPS";
	} # each MPS
	print OUT "\n";
# templates
	print OUT "TEMPLATE";
	for my $MPS (@MPSNames) {
		next if $MPS =~ /^$conjNamesPattern$/i;
		print OUT " $prefixes{$MPS}1A$suffixes{$MPS}";
	} # each MPS
	print OUT "\n";
# conjugations
	my $conjMPS;
	# print STDERR "mpss: " . join(', ', keys %$dataPtr) . "\n";
	for my $conjName (@conjNames) {
		$conjMPS = ${$dataPtr}{$conjName};
		if (!defined($conjMPS)) {
			$conjMPS = ${$dataPtr}{ucfirst(uc($conjName))};
		}
		last if defined $conjMPS;
	}
	if (!defined($conjMPS)) {
		$conjMPS = ${$dataPtr}{$MPSNames[0]};
		print OUT "% no CONJ found; using $MPSNames[0]\n";
	}
	my %seenConjugation;
	for my $index (0 .. $numConjugations - 1) {
		my $conjugation = ${$conjMPS}[$index];
		my $effectiveConjugation = ${$conjMPS}[$index];
		if (defined($seenConjugation{$conjugation})) {
			$effectiveConjugation = addSuffix($seenConjugation{$conjugation});
		}
		$seenConjugation{$conjugation} = $effectiveConjugation;
		${$conjMPS}[$index] = $effectiveConjugation;
		my @forms;
		for my $MPS (@MPSNames) {
			next if $MPS =~ /^$conjNamesPattern$/i;
			my $columnPtr = ${$reducedDataPtr}{$MPS};
			my $exponence = ${$columnPtr}[$index];
			my $effectiveStem = $stems[$index];
			if ($effectiveStem eq '∅') {
				$exponence = "-$exponence";
			} elsif ($exponence !~ s/\Q$effectiveStem\E/-/) {
				# print STDOUT "% [$exponence] does not contain [$stems[$index]]\n";
				$exponence = "!${${$dataPtr}{$MPS}}[$index]";
			}
			push @forms, $exponence;
		}
		my $combinedForms = join(" ", @forms);
		if (defined($formsToConj{$combinedForms})) { # seen before
			my $actual = $formsToConj{$combinedForms};
			$reflections{$effectiveConjugation} = $actual;
			$counts{$actual} += 1;
		} else { # never seen before
			$formsToConj{$combinedForms} = $effectiveConjugation;
			$counts{$effectiveConjugation} = 1;
			print OUT "$effectiveConjugation $combinedForms\n";
		}
	} # each conjugation "index"
	print OUT "\n";
# keys
	for my $index (0 .. $numConjugations - 1) {
		my $conj = ${$conjMPS}[$index];
		next if defined($reflections{$conj});
		print OUT "KEYS $conj FREQ=$counts{$conj}\n";
	} # each lexeme "index"
	print OUT "\n";
# lexemes
	my $glossMPS;
	for my $conjName (@conjNames) {
		$glossMPS = ${$dataPtr}{$conjName};
		if (!defined($glossMPS)) {
			$glossMPS = ${$dataPtr}{lcfirst (uc($conjName))};
		}
		last if defined $glossMPS;
	}
	if (!defined($glossMPS)) {
		print OUT "% no gloss found; using CONJ\n";
		$glossMPS = $conjMPS;
	}
	my %seenGloss;
	for my $index (0 .. $numConjugations - 1) {
		my $gloss = ${$glossMPS}[$index];
		my $effectiveGloss = $gloss;
		my $conj = ${$conjMPS}[$index];
		if (defined($reflections{$conj})) {
			$conj = $reflections{$conj}; # belongs to a previous conjugation
		}
		if (defined($seenGloss{$gloss})) {
			$effectiveGloss = addSuffix($seenGloss{$gloss});
		}
		$seenGloss{$gloss} = $effectiveGloss;
		$stems[$index] = '∅' if $stems[$index] eq '';
		print OUT "LEXEME $effectiveGloss $conj 1:$stems[$index]\n"
	} # each lexeme "index"
	print OUT "\n";
# done
	close OUT;
} # printPlat

init();
computeTemplates();
computeStems();
printPlat();
