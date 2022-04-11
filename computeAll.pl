#!/usr/bin/perl -w # integers are only 32 bits

# #!/opt/perl5/usr/local/bin/perl -w

=head SYNOPSYS

computeAll.pl fileName

=head NOTATION

The data describing a language is a table.

Each row represents a conjugation (like o-stem), and each column represents an
MPS (morphosyntactic property set, such as 2nd plural masculine).  Each cell is
an exponence (such as ibimus).

=head INPUT

Comments start with % and go to the end of a line
Or they start with a line starting with /* through a line containing */

Each conjugation is given in a single line with MPSat

	conjugation exponence exponence ...

One line may use IC as the name of the conjugation; in this case, the
remainder of the line contains the names of the MPSs.

=head definitions

A static principal-part set as a set of MPSs that together uniquely identify all
conjugations.  That is, if there are two conjugations c and c', and the
principal-part set contains MPSs m_1 ..  m_k, then c and c' must disagree on at
least one of m_i. 

=cut

use strict;
use utf8;
use Getopt::Std;
my $path = $0; $path =~ s/[\w\.]+$//; unshift @INC, $path; require "common.pl";

# constants
	my $infinity = 100;
	my $maxConjLength = 4; # number of characters in a conjugation name
	my $bitsPerPattern = 4; # how many distillations in a pattern; can
		# be overridden by a parameter
	my $log2 = log(2.0);

# global variables: established during readFile
my (
	$bitsPerInt, # number of bits in an integer, typically 32 or 64
	%conjugations, # $conjugations{$conjName} = \@listOfExponences
	@conjugations, # $conjugations[n] = the name of the n-th conjugation
	@origConjugations, # $origConjugations[n] = the name of the n-th conjugation
	%duplicateConjugations, # $duplicateConjugations{$conj} = exemplar
	$MPSCount, # length of each conjugation
	$conjCount, # number of conjugations
	@MPSNames, # names of MPSs
	%MPSNameToIndex, # $MPSNameToIndex{'name'} = index into MPSNames
	@patternList, # list of patterns, sparse to dense, then numeric order
	$noEmptyPredictor, # if true, compute according to book: empty pattern out
	%exponenceAbbrevs, # $exponenceAbbrevs{$aConj} = (abbrev, abbrev ...)
	$abbrevsUsed, # how many abbreviations we use
	%roots, # $roots{meaning} = root; format like 1:absou 3:absolv
	@meanings, # in order seen
	%conjs, # $conjs{meaning} = conjName
	@templates, # $templates[n] is an exponence pattern
	@templateAbbrs, # $templateAbbrs[n] is an exponence pattern
	@identical, # $identical{4} = 2 means that MPS 4 is the same as 2.
	$identicalCount, # how many elements in @identical are set
	@essentiallyIdentical, # defined($essentiallyIdentical{4}) means
		# that MPS 4 has the same pattern as some earlier MPS
	%sameConj, # sameConj{aConj} = otherConj if they are identical,
		# including stem referral
	%similarConj, # similarConj{aConj} = otherConj if they are
		# identical in paradigm, not looking at stem referral
	%referralPointer, # in grouping referral patterns, points to other conj or
		# pseudo-conj with the same referral pattern.
	@statics, # static patterns, if computed
	%cache, # $cache{"$conj,$pattern"} = exponences
	%essencePerConj, # $essencePerConj{$conjName} = [essence, essence ...]
	%essencePerMPS, # $essencePerMPS{$MPSIndex} = \%map: conj -> essence
	@joinedNames, # grouped conjugations
	%partialEssence, # $partialEssence{$conjName or joined name} = essence ...
	%partialReferrals, # $partialReferrals{$conjName} = referral pattern
	$distillationCount, # number of distillations in each essence
	%parent, # $parent{$conjName} = joined conjugation name
	@sandhi, # sandhi rules in the theory
	%classes, # character classes for Sandhi
	$verbose, # level of output
	%cellPerEssence, # $cellPerEssence{e13_2} = ${$conjugations{someConj}}[MPS]
	@stems, # stems[stemNumber] = stem name
	%refersByConj, # $refersByConj{$conjName} = [earlier stem numbers]
	$expand, # boolean: expand all exponences by stem referral
	@helpers, # $helpers[index] = "lemma MPSName";
	%helpLemmas, # $helpLemmas{$lemma} = " index:MPSName ..."
	$forcedBits, # int (bit pattern): which distillations are required in a pp analysis
	$forcedMPS, # int (bit pattern): which MPSs must be in essence
	@toAnalyze, # requests for analysis: [MPSName=surface, ...]
	%keys, # $keys{$conjName} = string of keywords associated with conjugation
	$requiredKeys, # filter the conjugations on these keys
	$outputKeys, # output analysis only for these keys
	$MPSfilter, # set of strings that must appear in each MPS name
	$MPSfilteredCount, # how many MPSs were filtered out by MPSfilter
	%weights, # for entropy; indexed by conjugation name
	$totalWeight, # summed over all conjugations; for entropy
	$version, # software version
); # globals

=cut versions
3.1: modifed conjugation predictability to divide by 1 less.
3.2: outputs MPS pattern that covers the distillation
3.3: adds frequency data from identical conjugations into their exemplar
3.4: adds average computation at end of predictabilities
3.5: dies if #MPSs beyond word size; more careful with forced MPSs word size
3.7: computes near-static principal parts
3.8: new computation for conjugation entropy; 
   rounding for entropies; wording change conjugation=>inflection class;
   more care if some missing referral patterns
3.9: avoid using pattern=0 for paradigm predictability
3.10: added printing distillation details if verbose.
3.11: enhanced ANALYZE for multiple stems, taking into account TEMPLATE and
	making further suggestions based on expanding exponence.
3.12: introduced ascify routine, added conversions in it; added lookahead
	heuristic for near-principal parts.
3.13: direct-coding binomial coefficient code, fixing error
3.14: m-way entropy measure
3.15: components of m-way entropy measure
3.16: redefined components of m-way entropy measure
3.17: fixed computation of choose so that choose(n,n) = 1 
3.18: added density statistic to static principal parts
3.19: added focus number statistic to static principal parts
3.20: fixed error messages about STEM declarations and REFER usage.
3.21: fixed regex recognizing REFER
=cut
$version = "3.20";

sub readFile {
	my ($fileName) = @_;
	$fileName =~ s/\.data$//;
	open INPUT, "<:utf8", "$fileName.data"
		or die("Can't read $fileName.data.  Stopped");
	print "Data file $fileName\nAnalyzer version $version\n";
	@templateAbbrs = (); # to insure it is defined.
	my ($line);
	while ($line = <INPUT>) { # one line
		chomp $line;
		$line =~ s/﻿//; # Unicode marker
		if ($line =~ /\/\*/) { # multi-line comment
			while ($line = <INPUT>) {
				last if $line =~ /\*\//;
			}
			$line = <INPUT>;
		}
		$line =~ s/\s*%.*$//; # remove comments
		$line =~ s/\s+$//; # remove trailing blanks
		# print STDERR "[$line]\n";
		next if $line =~ /^\s*$/; # ignore empty lines
		if ($line =~ /^LEXEME\s+(\S+)\s+(\S+)(\s+(.+))?/) {
			# a lexeme
			my ($meaning, $conjugation, $stems) = ($1, $2, $4);
			if (!defined($conjugations{$conjugation})) {
				print STDERR "lexeme $meaning belongs to " .
					"nonexistent conjugation $conjugation: $line\n";
				next;
			}
			if (defined($conjs{$meaning})) {
				print STDERR "Lexeme $meaning is presented multiple times\n";
				next;
			}
			$stems = "" unless defined($stems); # could be empty
			$roots{$meaning} = $stems;
			push @meanings, $meaning;
			$conjs{$meaning} = $conjugation;
			next;
		} elsif ($line =~ /^ABBR\s+(\d+)\s+(.*)/) {
			my ($index, $abbr) = ($1, $2);
			print STDERR "Abbreviation $index is multiply defined\n"
				if defined($templateAbbrs[$index]);
			$templateAbbrs[$index] = $abbr;
			next;
		} elsif ($line =~ /^TEMPLATE\s+(.*)/) {
			my $rest = $1;
			push @templates, split(/\s+(?=\P{M})/, $rest);
			next;
		} elsif ($line =~ /^HELPER\s+(\d+)\s+(\w+)\s+(\w+)/) {
			my ($helperIndex, $helperLemma, $helperMPS) = ($1, $2, $3);
			$helpers[$helperIndex] = "$helperLemma $helperMPS";
			$helpLemmas{$helperLemma} .= " ${helperIndex}:$helperMPS";
			next;
		} elsif ($line =~ /^SANDHI\s+(.*)/) {
			push @sandhi, $1;
			next;
		} elsif ($line =~ /^CLASS\s+(\w+)\s+(.*)/) {
			my ($className, $classContents) = ($1, $2);
			$classContents =~ s/\s*$//;
			$classContents =~ s/\s+/\|/g;
			$classContents =~ s/∅//g;
			$classes{$className} = "($classContents)"; # a Perl pattern
			next;	
		} elsif ($line =~ /^STEM\s+(\d+)\s+(.*)/) {
			my ($stemNumber, $stemName) = ($1, $2);
			if (defined($stems[$stemNumber])) {
				print STDERR "Stem $stemNumber is multiply defined\n";
			} else {
				$stems[$stemNumber] = $stemName;
			}
			next;
		} elsif ($line =~ s/^ANALYZE//) {
			push @toAnalyze, [];
			while ($line =~ s/(\S+=\S+)//) {
				push @{$toAnalyze[-1]}, $1;
			}
			next;
		} elsif ($line =~ s/^KEYS\s+(\S+)\s*(.*)//) {
			my ($conj, $keyList) = ($1, $2);
			if (!defined($conjugations{$conj})) {
				print STDERR "Key for unknown inflection class: $conj\n";
				next;
			}
			$keys{$conj} = $keyList;
			# print STDERR "I see key $keyList for $conj\n"; # debug
			next;
		} elsif ($line =~ /^REFER\s+(\S+)\s+(.*)/) {
			my ($conjName, $tail) = ($1, $2);
			if (defined($refersByConj{$conjName})) {
				print STDERR "Multiple REFER lines for $conjName\n";
				next;
			}
			if (!defined($conjugations{$conjName})) {
				print STDERR
					"REFER $conjName: there is no such conjugation\n";
				next;
			}
			my @refers;
			for my $phrase (split /\s*;\s*/, $tail) { # phrase: 2, 7 -> 1
				# print STDERR "phrase is $phrase\n";
				if ($phrase !~ /^([-\d, ]+)->\s*(\d+)\s*$/) {
					print STDERR "malformed phrase $phrase\n";
					next;
				}
				my ($fromStems, $toStem) = ($1, $2);
				# print STDERR "toStem is $toStem\n";
				for my $fromStem (split /\s*,\s*/, $fromStems) {
					# print STDERR "fromStem is $fromStem\n";
					$fromStem =~ /(\d+)\s*(-\s*(\d+))?/;
					my ($lower, $upper) = ($1, $3);
					$upper = $lower unless defined($upper);
					for my $index ($lower .. $upper) {
						# print STDERR "index is $index\n";
						if ($index <= $toStem) {
							print STDERR "$conjName stem $index must not " .
								"refer to a higher stem $toStem.\n";
							next;
						}
						if (defined($refers[$toStem])) {
							$refers[$index] = $refers[$toStem];
						} else {
							$refers[$index] = $toStem;
						}
					} # one index
				} # each fromStem
			} # each phrase
			for my $index (0 .. $#stems) { # fill in missing elements
				$refers[$index] = 0 unless defined($refers[$index]);
			}
			$refersByConj{$conjName} = \@refers;
			# print STDERR "referral: $conjName " . join(', ', @refers) . "\n";
			next;
		}
		my @newMPSs = split(/\s+(?=\P{M})/, $line);
		# print "I see " . (scalar @MPSs) . " entries\n";
		# print "" . join(" ][ ", @MPSs) . "\n";
		my $conjName = shift @newMPSs;
		if ($conjName =~ /^(CONJ|IC)$/) { # names of MPSs (CONJ is deprecated)
			push @MPSNames, @newMPSs;
			for my $index (0 .. $#MPSNames) {
				$MPSNameToIndex{$MPSNames[$index]} = $index;
			}
			next;
		} elsif (!defined($conjugations{$conjName})) { # first batch
			$conjCount += 1;
			push @conjugations, $conjName;
			$maxConjLength = length($conjName)
				if length($conjName) > $maxConjLength;
			$conjugations{$conjName} = \@newMPSs;
		} else { # continuation batch
			push @{$conjugations{$conjName}}, @newMPSs;
		}
	} # one line
	close INPUT;
	die("Malformed or missing file; no conjugations\n") unless @conjugations != 0; 
	# check that all conjugations have the same length
	my $length;
	for my $conjName (keys %conjugations) {
		$MPSCount = scalar @{$conjugations{$conjName}}
			unless defined($MPSCount);
		# print "for $conjName: " . 
		# 		@{$conjugations{$conjName}} . ': '.
		# 		join(' ', @{$conjugations{$conjName}}) .
		# 		"\n";
		if (scalar @{$conjugations{$conjName}} != $MPSCount) {
			die("wrong number of MPSs for conjugation $conjName. " .
				"  Expected $MPSCount but got " .
				@{$conjugations{$conjName}} . ': '.
				join('] [', @{$conjugations{$conjName}}) .
				"\n")
		} else {
			# print "for $conjName I see: " . join('] [', @{$conjugations{$conjName}}) . "\n";
		}
	} # each conjName
	if (!scalar @templates) { # invent simplest template
		@templates = ('=1C') x $MPSCount;
	}
	# for my $index (0 .. $#MPSNames) {
	# 	print STDERR "$index $MPSNames[$index]: $templates[$index]\n";
	# }
	if (!defined($MPSNames[0])) {
		@MPSNames = (0 .. $MPSCount-1);
	}
} # readFile

sub printFile { # build exponenceAbbrevs and print them
	my @abbrevs = (1 .. 10000);
	$abbrevsUsed = 0;
	my $width = ($MPSCount >= 100) ? 4 : 3;
	if ($verbose) {
		print "\nInflection-class table\n";
		printf "\t%${maxConjLength}s ", "conj";
		for my $MPSIndex (1 .. $MPSCount) {
			printf "%${width}d", $MPSIndex;
		}
		print "\n";
		print "\t" . ("-" x $maxConjLength) . " " . ("---" x $MPSCount) . "\n";
	} # verbose
	for my $conjName (@conjugations) { # one conjugation
		printf "\t%${maxConjLength}s ", $conjName if $verbose;
		for my $exponence (lhs(@{$conjugations{$conjName}})) { # one cell
			if (!defined($exponenceAbbrevs{$exponence})) { 
				$exponenceAbbrevs{$exponence} = $abbrevs[$abbrevsUsed];
				$abbrevsUsed += 1;
			}
			if (!defined($exponenceAbbrevs{$exponence})) {
				printf STDERR
					"\nThe \@abbrevs variable doesn't have enough entries\n" .
					"\tfix by adding more entries in $0.\n";
				$exponenceAbbrevs{$exponence} = '??';
			}
			printf "%${width}s", $exponenceAbbrevs{$exponence} if $verbose;
		} # one cell
		print "\n" if $verbose;
	} # one conjugation
	if ($verbose) {
		print "\nMPS abbreviations\n";
		for my $MPSIndex (1 .. $MPSCount) {
			print "\t$MPSIndex  $MPSNames[$MPSIndex-1]\n";
		}
		print "\nExponence abbreviations\n";
		for my $exponence (
				sort {
					my $ea = $exponenceAbbrevs{$a};
					my $eb = $exponenceAbbrevs{$b};
					length($ea) == length($eb)
					? $ea cmp $eb
					: length($ea) <=> length($eb)
				}
				keys(%exponenceAbbrevs)) {
			print "\t$exponenceAbbrevs{$exponence}  $exponence\n";
		}
		if (scalar @stems) {
			print "\nStems\n";
			for my $index (0 .. $#stems) {
				if (defined($stems[$index])) {
					printf "\t%2d: %s\n", $index, $stems[$index];
				} # the stem exists
			} # each index
		} # there are stems
		print "\n";
	} # verbose
} # printFile

sub fixConjWeightsDup {
	for my $conjName (@conjugations) { # does not include duplicates
		$weights{$conjName} = 1; # initial value
		$totalWeight += 1;
	}
	for my $conjName (keys(%duplicateConjugations)) {
		my $destConj = $duplicateConjugations{$conjName};
		$weights{$destConj} += 1;
		$totalWeight += 1;
		# print STDERR "$conjName duplicates $destConj, whose weight is now $weights{$destConj}\n";
	} # each duplicate
	for my $conjName (@conjugations) { # show results
		print "$conjName is weighted $weights{$conjName}\n"
			if $weights{$conjName} > 1;
	}
} # fixConjWeightsDup

sub fixConjWeights {
	# $key is something like "FREQ" or "DUPLICATES"  Compute %weights.
	# FREQ means use a KEYS like "FREQ=4".
	# DUPLICATES means use the number of identical ICs as the weight.
	my ($key) = @_;
	if ($key eq 'DUPLICATES') { # special case
		fixConjWeightsDup();
		return;
	}
	# general case
	# add the weight of duplicate conjugations to their exemplars
	for my $conjName (keys %duplicateConjugations) { 
		my $conjKeys = $keys{$conjName};
		next unless defined($conjKeys);
		my $oldWeight = 0;
		if ($conjKeys =~ /\b$key=(\d+)/) {
			$oldWeight = $1;
			$keys{$conjName} =~ s/\b$key=\d+/$key=0/; # prevent repetition
		}
		my $destConj = $duplicateConjugations{$conjName};
		$conjKeys = $keys{$destConj};
		my $newWeight = 0;
		if ($conjKeys =~ /\b$key=(\d+)/) {
			$newWeight = $1 + $oldWeight;
			# print "Added $oldWeight to $destConj from $conjName now $newWeight\n";
			$keys{$destConj} =~ s/\b$key=\d+/$key=$newWeight/;
		}
	} # add weights from each duplicate
	$totalWeight = 0;
	for my $conjName (@conjugations) { # find the weight of each conjugation
		my $conjKeys = $keys{$conjName};
		my $value = 1; # unless we learn differently
		my $keysExist = scalar(keys %keys) > 0;
		if ($keysExist and $key ne "") {
			if (!defined($conjKeys)) {
				print "No keys defined for $conjName\n";
			} else { # conjugation has keys
				$conjKeys =~ /\b$key=(\d+)/;
				$value = $1;
				if (!defined($value)) {
					# print STDERR "No entropy weight (key $key) for $conjName\n";
					$value = 1;
				} # no such key for this conjugation
			} # conjugation has keys
		} # there is a key to check for
		$weights{$conjName} = $value;
		$totalWeight += $value;
	} # each conjugation
} # fixConjWeights

sub conditionalDistillationEntropy {
	# compute conditional entropy of $distillation given all the distillations
	# in $pattern.  If $details is defined, also show per-conjugation
	# information.
	my ($pattern, $distillation, $details) = @_;
	return 0 if ((1 << $distillation) & $pattern); # efficiency only
	my %seen;
	my %essenceWeight; # $essenceWeight{$distEssence}
	for my $conjName (@conjugations) {
		my @otherEssence;
		for my $other (0 .. $distillationCount-1) {
			push @otherEssence, ${$essencePerConj{$conjName}}[$other]
				if ((1 << $other) & $pattern);
		}	
		my $givenEssence = join(' ', @otherEssence);
		my $distEssence = ${$essencePerConj{$conjName}}[$distillation];
		$essenceWeight{$distEssence} += 1;
		$seen{$givenEssence} = {} unless (defined($seen{$givenEssence}));
		${$seen{$givenEssence}}{$distEssence} += $weights{$conjName};
		# printf STDERR "\tessences [%s], %s = %d\n",
		# 	$givenEssence, $distEssence,
		#	$weights{$conjName};
	} # each conjName
	my %contribution;
		# for details: $contribution{$conjName} sums entropy slices
	my $entropyTotal = 0.0; # weighted by number of occurences
	for my $givenEssence (keys %seen) {
		# print STDERR "\tI see [$givenEssence] matches\n";
		my $otherCount;
		for my $distEssence (keys %{$seen{$givenEssence}}) {
			$otherCount += ${$seen{$givenEssence}}{$distEssence};
			# print STDERR " $distEssence:${$seen{$givenEssence}}{$distEssence} ";
		} # each exponence distEssence that matches givenEssence
		# print STDERR "\n";
		my $entropy = 0.0;
		for my $distEssence (keys %{$seen{$givenEssence}}) {
			my $matchCount = ${$seen{$givenEssence}}{$distEssence};
			# print STDERR "\t\tMatchCount $matchCount; othercount $otherCount\n";
			my $probability = ($matchCount + 0.0)/$otherCount;
			my $delta = $probability * log($probability)/$log2;
			# print STDERR "\t\tdistEssence contributes $delta\n";
			$entropy -= $delta;
			if (defined($details)) {
				for my $conjName (@conjugations) {
					my $myEssence =
						${$essencePerConj{$conjName}}[$distillation];
					next unless $myEssence eq $distEssence;
					$contribution{$conjName} -=
						$delta * $otherCount / $totalWeight;
				} # each conjName
			} # details
		} # each exponence distEssence that matches givenEssence
		$entropyTotal += $entropy * $otherCount;
		# print STDERR "\tentropy is $entropy; total is $entropyTotal\n";
	} # each $exponence givenEssence
	return($entropyTotal/$totalWeight, \%contribution);
} # conditionalDistillationEntropy

sub computeMPSentropy {
	# Entropy(D1,D2) is a measure of the predictability of distillation D2
	# given the exponences for distillation D1.
	# If there are d distillations, there are d(d-1) such entropy measures.
	# The measure is not symmetric.
	my ($key) = @_;
	my $spaces = ' ' x 4;
	print "\n";
	printDistillationNumbers();
	print "\nEntropies (times 100) by distillation";
	print ", weighted according to key $key" unless $key eq "";
	print "\n${spaces}dist  |";
	for my $distNumber (0 .. $distillationCount-1) {
		printf " %3d", $distNumber+1;
	}
	print " | avg max\n";
	$distillationCount = scalar @{$essencePerConj{$conjugations[0]}};
	# unconditional MPS entropies
	print "${spaces}uncond|";
	my $entropySum = 0;
	for my $distNumber (0 .. $distillationCount-1) {
		my $totalWeight;
		my ($entropy) = conditionalDistillationEntropy(0, $distNumber);
		$entropySum += $entropy;
		printf " %3d", round($entropy*100);
	} # each distillation
	printf " | %3d\n", round($entropySum*100/$distillationCount);
	# m-conditional entropies
	$distillationCount = scalar @{$essencePerConj{$conjugations[0]}};
	my $max = 0;
	printf "${spaces}%d-cond|", $bitsPerPattern;
	$entropySum = 0;
	my %conjDistContribution; # indexed by "$conjName $distNumber"
	my $globalPatternCount;
	for my $distNumber (0 .. $distillationCount-1) {
		# printf STDERR "Distillation %d\n", $distNumber+1;
		my $distillation = 1 << $distNumber;
		my $perDistSum = 0;
		my $patternCount = 0;
		foreach my $pattern (@patternList) { # one pattern
			# print STDERR "\ttrying pattern $pattern\n";
			next if $distillation & $pattern; # certain to succeed
				# so we suppress considering it.
			$patternCount += 1;
			my $totalWeight;
			my ($entropy, $detailPtr) =
				conditionalDistillationEntropy($pattern, $distNumber, 1);
			# printf STDERR "\tpattern 0%o: entropy %3d\n", $pattern,
			# round($entropy*100);
			$perDistSum += $entropy;
			# printf STDERR "For pattern %s\n", patternToMPS($pattern);
			for my $conjName (@conjugations) {
				$conjDistContribution{"$conjName $distNumber"} +=
					${$detailPtr}{$conjName};
				# printf STDERR "\tfor %s, %d, adding contribution %d\n",
				# 	$conjName, $distNumber + 1,
				# 	round(100*${$detailPtr}{$conjName});
			}
		} # each pattern
		# printf STDERR "\tAverage: %3d\n",
		# 	round($perDistSum * 100 / $patternCount);
		$max = $perDistSum / $patternCount
			if $perDistSum / $patternCount > $max;
		printf " %3d", round($perDistSum * 100 / $patternCount);
		$entropySum += $perDistSum / $patternCount;
		$globalPatternCount = $patternCount;
	} # each distillation
	printf " | %3d %3d\n", round($entropySum *100 / $distillationCount),
		round($max * 100);
	# per-conjugation detail of m-conditional entropies
	print "${spaces}$bitsPerPattern-cond entropy by IC (predictability)\n";
	my @perDistTotal;
	my $grandTotal;
	for my $conjName (@conjugations) {
		printf "%10s| ", $conjName;
		my $total = 0.0;
		for my $distNumber (0 .. $distillationCount-1) {
			my $part = $conjDistContribution{"$conjName $distNumber"};
			$part /= $globalPatternCount;
			$total += $part;
			printf "%3d ", round(100*$part);
				$perDistTotal[$distNumber] += $part;
		} # each $distNumber
		$grandTotal += $total;
		printf "| %3d\n",
			round(100*$total / $distillationCount);
	} # each conjName
	print "${spaces}   avg|";
	for my $distNumber (0 .. $distillationCount-1) {
		printf " %3d", round($perDistTotal[$distNumber] * 100 / @conjugations);
	} # each distNumber
	printf " | %3d\n", round($grandTotal * 100 /
		($distillationCount * @conjugations));
	# conditional MPS entropies: D2 conditional on D1.
	print "${spaces}conditional entropy of MPS (col) given MPS (row)\n";
	my $totalEntropy = 0.0;
	my @colEntropyTotal;
	for my $D1 (0 .. $distillationCount-1) {
		my $lineTotal = 0.0;
		my $lineMax = 0.0;
		printf "${spaces}   %2d | ", $D1+1;
		for my $D2 (0 .. $distillationCount-1) {
			if ($D1 == $D2) {
				print "--- ";
				next;
			}
			my ($entropy) = conditionalDistillationEntropy((1<<$D1), $D2);
			# printf "%3.2f ", $entropy;
			printf "%3d ", round(100*$entropy);
			$lineTotal += $entropy;
			$lineMax = max($lineMax, $entropy);
			$colEntropyTotal[$D2] += round(100*$entropy);
			$totalEntropy += $entropy;
		} # each D2
		# printf "| %3.2f\n", $lineTotal / ($distillationCount-1);
		printf "| %3d %3d\n", round(100*$lineTotal / ($distillationCount-1)),
			# subtract 1 because each row has a -- cell.
			round(100*$lineMax);
	} # each D1
	printf "${spaces}  avg | ";
	for my $distIndex (0 .. $distillationCount-1) {
		printf "%3d ", $colEntropyTotal[$distIndex]/($distillationCount-1);
	} # each distIndex
	printf "| %3d\n",
		round(100*$totalEntropy / ($distillationCount * ($distillationCount-1)));
} # computeMPSentropy

sub nearStatic {
	# repeatedly pick MPS with highest entropy given previous MPSs, add to set.
	my ($key) = @_;
	my $epsilon = 0.0;
	my $pattern;
	printf "\nNear-static principal parts (simple heuristic)%s\n",
		$key eq '' ? '' : ", weighted according to key $key";
	$pattern = 0;
	while (1) { # repeat until entropy below epsilon
		my ($maxEntropy, $worstDistillation) = (0, 0);
		for my $distIndex (0 .. $distillationCount-1) {
			my ($entropy) = conditionalDistillationEntropy($pattern, $distIndex);
			($maxEntropy, $worstDistillation) = ($entropy, $distIndex)
				if $entropy > $maxEntropy;
		} # each distIndex
		last if $maxEntropy <= $epsilon;
		printf "\tHighest residual entropy is %7.6f, so choose MPS %d %s\n",
			$maxEntropy, 1+$worstDistillation,
			patternToMPS(1 << $worstDistillation);
		$pattern |= (1 << $worstDistillation);
	} # repeat with more MPSs
	printf "\tresult: %s\n", patternToMPS($pattern);
	printf "\nNear-static principal parts (lookahead)%s\n",
		$key eq '' ? '' : ", weighted according to key $key";
	$pattern = 0;
	while (1) { # repeat until entropy below epsilon
		my $maxEntropy;
		my $bestDistillation;
		for my $distIndex (0 .. $distillationCount-1) {
			# see what happens if we choose $distIndex as a near-static part
			next if $pattern & (1 << $distIndex);
			$pattern |= (1 << $distIndex);
			my $worstResidual = 0.0;
			for my $otherDist (0 .. $distillationCount-1) {
				next if $otherDist == $distIndex;
				my ($anEntropy) = 
					conditionalDistillationEntropy($pattern, $otherDist);
				$worstResidual = max($worstResidual, $anEntropy);
			}
			$pattern &= ~(1 << $distIndex);
			($maxEntropy, $bestDistillation) = ($worstResidual, $distIndex)
				if !defined($maxEntropy) || $worstResidual < $maxEntropy;
		} # each distIndex
		$pattern |= (1 << $bestDistillation);
		printf "\tChoose MPS %d %s, reducing highest residual to %7.6f\n",
			$bestDistillation+1, patternToMPS(1 << $bestDistillation),
			$maxEntropy;
		last if $maxEntropy <= $epsilon;
	} # repeat with more MPSs
	printf "\tresult: %s\n", patternToMPS($pattern);
} # nearStatic

sub computeConjEntropy {
	my ($key) = @_;
	my $intWidth = 3; # 3 is often insufficient
	printDistillationNumbers();
	my $conjWidth = 4; # minimum
	for my $conjName (@conjugations) {
		$conjWidth = max($conjWidth, length($conjName));
	}
	$conjWidth += 2;
	printf "\nInflection-class predictive entropies (times 100)%s\n",
		$key eq '' ? '' : ", weighted according to key $key";
	printf "%${conjWidth}s ", "IC";
	for my $D1 (0 .. $distillationCount-1) {
		printf "%${intWidth}d ", $D1+1;
	}
	print "| avg \n";
	my @perDistEntropyTotals;
	conj:
	for my $conjName (@conjugations) {
		my $keys = $keys{$conjName};
		for my $filter (split /\s+/, $outputKeys) {
			if (!defined($keys) or $keys !~ /\b$filter\b/) {
				# print "Not printing: $aConj\n";
				next conj;
			}
		} # each filter
		printf "%${conjWidth}s ", $conjName;
		my $entropyForConj = 0.0;
		for my $D1 (0 .. $distillationCount-1) {
			# print STDERR "D1: $D1\n";
			my $E1 = ${$essencePerConj{$conjName}}[$D1];
			# print STDERR "\tsee $E1 in " . patternToMPS(1 << $D1, 1) . "\n";
			my @fragConj; # subset of @conjugations agreeing with $E1 in $D1
			for my $otherConj (@conjugations) {
				my $E2 = ${$essencePerConj{$otherConj}}[$D1];
				push @fragConj, $otherConj if $E1 eq $E2;
			}
			my $entropyForConjDistillation = 0.0;
			for my $D2 (0 .. $distillationCount-1) {
				next if $D1 == $D2;
				# print STDERR "\tD2: $D2\n";
				my $E2 = ${$essencePerConj{$conjName}}[$D2];
				# print STDERR "\tIn distillation " .
				# 	patternToMPS(1 << $D2, 1) .  " I see $E2\n";
				my $weightSum = 0;
				my %seen;
				for my $otherConj (@fragConj) {
					my $E3 = ${$essencePerConj{$otherConj}}[$D2];
					$seen{$E3} += $weights{$otherConj} ; # if $E3 eq $E2; # debug
					$weightSum += $weights{$otherConj};
					# print STDERR "\t\tIn $otherConj I see $E3 there; weight $weightSum\n";
				} # each $otherConj
				my $entropy = 0;
				for my $seenEssence (keys %seen) {
					my $probability = ($seen{$seenEssence} + 0.0) / $weightSum;
					my $delta = $probability * log($probability)/$log2;
					# printf STDERR
					# 	"\t\tessence %s, weight %d, weightSum %d, prob %4.3f, info %4.3f\n",
					# 	$seenEssence, $seen{$seenEssence}, $weightSum,
					# 	$probability, -$delta;
					$entropy -= $delta;
				}
				# printf STDERR
				#	"\t\t$conjName: dist $D1, other dist $D2, frag size $weightSum, entropy $entropy\n";
				$entropyForConjDistillation += $entropy;
			} # each other distillation D2
			$entropyForConjDistillation /= $distillationCount -1; # average
			printf "%${intWidth}d ", round(100*$entropyForConjDistillation);
			$entropyForConj += $entropyForConjDistillation;
			$perDistEntropyTotals[$D1] += $entropyForConjDistillation;
		} # each distillation $D1
		printf "| %${intWidth}d\n", round(100*$entropyForConj / $distillationCount);
	} # each conjugation $conjName
	printf " %s\n%${conjWidth}s", "-" x ($conjWidth+($intWidth+2)*$distillationCount),
		"avg";
	my $totalEntropy = 0.0;
	for my $D1 (0 .. $distillationCount-1) {
		printf " %${intWidth}d", round(100*$perDistEntropyTotals[$D1] / (@conjugations));
		$totalEntropy += $perDistEntropyTotals[$D1];
	} # each distillation $D1
	printf " | %${intWidth}d\n",
		round(100 * $totalEntropy / (@conjugations * $distillationCount));
} # computeConjEntropy

sub filterConjugations {
	my @goodConjugations;
	conj: for my $conjName (@conjugations) {
		# print STDERR "working on IC $conjName\n";
		my $keys = $keys{$conjName};
		for my $filter (split /\s+/, $requiredKeys) {
			if (!defined($keys) or $keys !~ /\b$filter\b/) {
				# filter this conjugation out
				delete $conjugations{$conjName};
				# print "filtered out: $conjName\n";
				next conj;
			} # no good
		} # each filter
		push @goodConjugations, $conjName;
	}
	@origConjugations = @conjugations;
	@conjugations = @goodConjugations;
	$conjCount = scalar @conjugations;
	if ($conjCount == 0) {
		print STDERR "There are no inflection classes left after filtering.\n";
		exit(0);
	}
} # filterConjugations

sub printFragment {
	# print a data file containing only the given keys and MPS values
	# @conjugations is already filtered by keys
	my ($MPSfilter) = @_;
	print "\n---- fragment of $0, restricting keys and MPS values\n\n";
	for my $abbrevIndex (1 .. $#templateAbbrs) {
		print "ABBR $abbrevIndex $templateAbbrs[$abbrevIndex]\n";
	}
	print "\n";
	my $usableMPS = 0; # bit pattern
	my $count = -1;
	MPS:
	for my $MPSName (@MPSNames) {
		$count += 1;
		for my $string (split /\s+/, $MPSfilter) {
			if ($MPSName !~ /$string/i) {
				next MPS;
			}
		} # each MPS filter string
		$usableMPS |= 1 << $count;
	}
	# header line
	print "IC";
	$count = -1;
	for my $MPSName (@MPSNames) {
		$count += 1;
		print " $MPSName" if $usableMPS & (1 << $count);
	}
	print "\n";
	print "TEMPLATE";
	$count = -1;
	for my $MPSName (@MPSNames) {
		$count += 1;
		print " $templates[$count]" if $usableMPS & (1 << $count);
	}
	print "\n";
	# each conjugation gets a line
	my %usableConjugations;
	for my $conjName (@conjugations) {
		print "$conjName";
		$usableConjugations{$conjName} = 1;
		my $MPSptr = $conjugations{$conjName};
		$count = -1;
		for my $MPS (@$MPSptr) {
			$count += 1;
			print " $MPS" if $usableMPS & (1 << $count);
		}
		print "\n";
	} # one conjugation
	print "\n";
	# SANDHI section
	if (@sandhi) {
		print "SANDHI " . join("\nSANDHI ", @sandhi) . "\n\n";
	}
	# LEXEME section
	for my $meaning (@meanings) {
		my $conjName = $conjs{$meaning};
		next unless defined($usableConjugations{$conjName});
		print "LEXEME $meaning  $conjName $roots{$meaning}\n";
	}
	print "\n";
	# KEY section
	for my $conjName (@conjugations) {
		next unless defined($keys{$conjName});
		print "KEYS $conjName $keys{$conjName}\n";
	}
	print "\n------ end of fragment\n\n";
} # printFragment

sub expandConjugations {
	for my $conj (@conjugations) {
		# print "working on ic $conj\n";
		my @templateCopy = @templates;
		my @refers = @{$refersByConj{$conj}};
		my @newExponences;
		for my $exponence (@{$conjugations{$conj}}) {
			my @exponenceList = split(/-/, $exponence);
			my $cell = shift @templateCopy;
			$cell =~ s/(\d+)A/$templateAbbrs[$1]/eg;
			$cell =~ s/(\d+)C/$exponenceList[$1-1]/eg;
			$cell =~ s/(\d+)S/($refers[$1] ? $refers[$1] : $1) . 'S'/eg;
			$cell =~ s/.*!//; # remove default if overridden
			$cell =~ s/∅//g unless $cell eq '∅';
			# print "\tworking on exponence $exponence, cell $cell\n";
			push @newExponences, $cell;
		} # each exponence
		$conjugations{$conj} = \@newExponences;
		# print "new exponences for $conj: " . join(' ', @newExponences) . "\n";
	} # each conjugation
} # expandConjugations

# discard the paradigm entirely, replace it with the referral patterns
sub paradigmIsReferral {
	$MPSCount = 0;
# reset each conjugation
	for my $conj (@conjugations) {
		$conjugations{$conj} = $refersByConj{$conj};
		shift @{$conjugations{$conj}};
		$MPSCount = max($MPSCount, scalar @{$conjugations{$conj}});
	} # each conjugation
	@MPSNames = (1 .. $MPSCount);
# fill in empty or undefined slots
	for my $conj (@conjugations) {
		# print STDERR "working on $conj\n";
		for my $MPSIndex (0 .. $MPSCount-1) {
			my $value = ${$conjugations{$conj}}[$MPSIndex];
			${$conjugations{$conj}}[$MPSIndex] = $MPSIndex + 1
				unless defined($value) and $value > 0;
		} # each MPSIndex
		# print STDERR "\t" . join(' ', @{$conjugations{$conj}}) . "\n";		
	} # each conjugation
} # paradigmIsReferral

# compute which conjugations are identical; complain and remove
# duplicates
sub identicalConjugation {
	my @toPrint;
	my @goodConjugations;
	my %seen;
	my %classes;
	$identicalCount = 0;
	for my $conjName (@conjugations) {
		my $key = join(' ', @{$conjugations{$conjName}});
		my $fullKey = $key;
		my $refers = $refersByConj{$conjName};
		if (defined($refers)) {
			for my $index (0 .. @$refers) {
				${$refers}[$index] = '' unless defined(${$refers}[$index]);
			}
			$fullKey .= join(' ', @$refers);
		}
		if (defined($seen{$fullKey})) { # exact duplicate
			push @toPrint, "$conjName => $seen{$key}";
			$sameConj{$conjName} = $seen{$fullKey};
			push @{$classes{$seen{$fullKey}}}, $conjName;
			$duplicateConjugations{$conjName} = $seen{$key};
			delete $conjugations{$conjName};
		} elsif (defined ($seen{$key})) { # partial duplicate
			push @toPrint, "$conjName -> $seen{$key}";
			$similarConj{$conjName} = $seen{$key};
			print STDERR "similar? $conjName and $seen{$key}: $key\n"
				if $expand;
			$seen{$fullKey} = $conjName;
		} else { # not a duplicate
			$seen{$key} = $conjName;
			$seen{$fullKey} = $conjName;
			$classes{$conjName} = [];
			push @goodConjugations, $conjName;
		}
	} # each $conjName
	if (scalar @toPrint) {
		print "\nIdentical inflection classes\n";
		# print "\t" . join("\n\t", @toPrint) . "\n";
		for my $class (sort keys %classes) {
			next unless scalar @{$classes{$class}};
			print "\t$class = ", join(', ', @{$classes{$class}}) .
				"\n";
		} # each equivalence class
		@origConjugations = @conjugations;
		@conjugations = @goodConjugations;
		$conjCount = scalar @conjugations;
	} else {
		@origConjugations = @conjugations;
		print "\nNo identical inflection classes\n";
	}
} # identicalConjugation

# compute which conjugations are identical based on essence; complain and remove
# duplicates
sub identicalConjugationEssence {
	my @toPrint;
	my @goodConjugations;
	my %seen;
	for my $conjName (@conjugations) {
		my $key = join(' ', @{$essencePerConj{$conjName}});
		if (defined($seen{$key})) { # exact duplicate
			push @toPrint, "$conjName ==> $seen{$key}";
			$sameConj{$conjName} = $seen{$key};
		} else { # not a duplicate
			$seen{$key} = $conjName;
			push @goodConjugations, $conjName;
		}
	} # each $conjName
	if (scalar @toPrint) {
		print "\nEssentially identical inflection classes:\n\t" .
			join("\n\t", @toPrint) . "\n";
		@conjugations = @goodConjugations;
		$conjCount = scalar @conjugations;
	} else {
		print "\nNo essentially identical inflection classes\n";
	}
} # identicalConjugationEssence

# see if conjugations are identical except for defects
sub ignoreNulls {
	# print "\nChecking null equivalence\n";
	for my $conj1 (@conjugations) {
		my @exponences1 = @{$conjugations{$conj1}};
		inner: for my $conj2 (@conjugations) {
			next if $conj1 le $conj2;
			my ($value1, $value2);
			my @exponences2 = @{$conjugations{$conj2}};
			my ($nulls1, $nulls2) = (0, 0);
			for my $MPSIndex (0 .. $#exponences2) {
				$value1 = $exponences1[$MPSIndex];
				$value2 = $exponences2[$MPSIndex];
				# print "$value1 vs $value2\n";
				if ($value1 eq '!∅') {
					$nulls1 += 1;
				}
				if ($value2 eq '!∅') {
					$nulls2 += 1;
				}
				next if $value1 eq '!∅' or $value2 eq '!∅';
				next inner if $value1 ne $value2;
			}
			print "$conj1 ($nulls1) and $conj2 ($nulls2) are the same except for nulls\n";
		} # each $conj2
	} # each $conj1
} # ignoreNulls

# return number of bits turned on in pattern
sub bitCount {
	my ($pattern) = @_;
	my $answer = 0;
	while ($pattern) {
		if ($pattern & 01) {
			$answer += 1;
		}
		$pattern >>= 1;
	}
	return $answer;
} # bitCount

# build patternList, but only containing up to about 7 bits.  We really don't
# need more, and we print an error message if that happens.
sub initializePatternList {
	# print STDERR "initializing pattern list\n";
	my @prevList = (0);
	@patternList = @prevList;
	for my $bitCount (1 .. $bitsPerPattern) {
		@prevList = insertBit(@prevList);
		push @patternList, @prevList;
	} # bitCount times
	# print "last pattern is " . patternToNumber($patternList[-1]) . "\n";
	# print STDERR "first pattern is " . patternToNumber($patternList[0]) . "\n";
} # initializePatternList

# return a list containing all unique ways of adding a single bit to elements
# of the given list, but don't add bits representing duplicate MPSs.
sub insertBit {
	my @previousList = @_;
	my @newList = ();
	for my $pattern (@previousList) {
		my $serial = -1;
		for (my $bit = 1; $bit < 1 << $distillationCount; $bit <<= 1) {
			$serial += 1;
			next if $bit <= $pattern;
			push @newList, $pattern | $bit;
		} # for bit
	} # for pattern
	# print "" . join("\n", @newList) . "\n"; # debug
	return @newList;
} # insertBit

sub groupConjugations {
# compute analysis
	my %workingEssence; # $workingEssence{$conjName} = essence ...
	my $parentSequence = 0;
	my $parentName;
	for my $conjName (@conjugations) {
		$partialEssence{$conjName} = $workingEssence{$conjName} =
			join(' ', @{$essencePerConj{$conjName}});
	} # each conjName
	my @maybeJoinedNames;
	while (1) { # try to join two conjugations
		my ($distance, $conjName1, $conjName2) =
			closestConjugations(\%workingEssence);
		# print "closest: $conjName1, $conjName2 is $distance\n";
		last unless defined($distance);
		$parentSequence += 1;
		$parentName = "Join$parentSequence";
		$parent{$conjName1} = $parent{$conjName2} = $parentName;
		my @essenceArray1 = (split /\s+/, $workingEssence{$conjName1});
		# print STDERR "conj array 1 is: " . join(" ", @essenceArray1) . "\n";
		delete $workingEssence{$conjName1};
		my @essenceArray2 = (split /\s+/, $workingEssence{$conjName2});
		delete $workingEssence{$conjName2};
		# print STDERR "Joining $conjName1 and $conjName2 (dist $distance) " .
		# 	"to make Join$parentSequence\n";
		($partialEssence{$conjName1}, $partialEssence{$conjName2},
			$workingEssence{$parentName}) =
			intersectConjugations($conjName1, \@essenceArray1,
				$conjName2, \@essenceArray2);
		# print "after intersect\n\t" .
		# 	"$conjName1 $partialEssence{$conjName1}\n\t" .
		# 	"$conjName2 $partialEssence{$conjName2}\n\t" . 
		# 	"=> $parentName $workingEssence{$parentName}\n";
		$partialEssence{$parentName} = $workingEssence{$parentName};
		push @maybeJoinedNames, $parentName;
	} # while joining conjugations
# remove trivial join points
	my %usedJoins;
	for my $conjName (@conjugations, @maybeJoinedNames) {
		my $parent = $parent{$conjName};
		if (!defined($parent)) {
			# print STDERR "nobody parents $conjName\n";
			$usedJoins{$conjName} = 1;
			next;
		}
		# print STDERR "working on $conjName, parent is $parent\n";
		while ($partialEssence{$parent} eq "") {
			last unless defined($parent{$parent});
			$parent = $parent{$parent};
		}
		$parent{$conjName} = $parent;
		# print STDERR "setting parent of $conjName to $parent\n";
		$usedJoins{$parent} = 1;
	}
	for my $conjName (@maybeJoinedNames) {
		push @joinedNames, $conjName if defined($usedJoins{$conjName});
	}
# compute top-down tree
	my (@tops, %children);
	for my $conjName (@conjugations, @joinedNames) {
		my $parent = $parent{$conjName};
		if (defined($parent)) {
			$children{$parent} = [] unless defined $children{$parent};
			push @{$children{$parent}}, $conjName;
		} else {
			push @tops, $conjName;
		}
	}
# replace defects
	for my $conjName (@conjugations) {
		my @newEssences = ();
		for my $essence (@{$essencePerConj{$conjName}}) {
			my $replacement = $essence;
			if ($essence =~ /e(\d+)_0/) {
				my $base = $1;
				$replacement = findDefault($conjName, $base);
				# print "$conjName is defective in distillation $base => " .
				# 	"$replacement\n";
			}
			push @newEssences, $replacement;
		} # one essence
		$essencePerConj{$conjName} = \@newEssences;
		# print "$conjName: " . join(' ', @newEssences) . "\n";
	} # each conjName
# print analysis
	print "\nGrouping inflection classes together\n";
	my $total;
	for my $top (@tops) {
		$total += showChildren($top, \%children, 1);
	}
	print "\tTotal cost: $total\n";
} # groupConjugations

sub findCenter {
	# compute pairwise distances
	my %distances; # pairwise, indexed by "conj conj"
	my %distanceSums;
	for my $conjIndex1 (0 .. $#conjugations) {
		my $conjName1 = $conjugations[$conjIndex1];
		my @essences1 = @{$essencePerConj{$conjName1}};
		my (%seen1);
		for my $essence1 (@essences1) {
			$seen1{$essence1} = 1;
		}
		my $distanceSum = 0;
		for my $conjIndex2 (0 .. $conjIndex1-1) {
			my $conjName2 = $conjugations[$conjIndex2];
			$distanceSum += $distances{"$conjName2 $conjName1"};
		}
		# print STDERR "conjName1 = $conjName1\n";
		for my $conjIndex2 ($conjIndex1+1 .. $#conjugations) {
			# print STDERR "\tconjIndex2 is $conjIndex2\n";
			my $conjName2 = $conjugations[$conjIndex2];
			my (%seen2);
			my @essences2 = @{$essencePerConj{$conjName2}};
			for my $essence2 (@essences2) {
				$seen2{$essence2} = 1;
			}
			my $distance = 0;
			for my $essence1 (@essences1) {
				next if $essence1 =~ /_0$/; # ignore defects
				$distance += 1 unless defined($seen2{$essence1});
				# print STDERR "\tessence1 $essence1; distance $distance\n";
			}
			for my $essence2 (@essences2) {
				next if $essence2 =~ /_0$/; # ignore defects
				$distance += 1 unless defined($seen1{$essence2});
				# print STDERR "\tessence2 $essence2; distance $distance\n";
			}
			# print STDERR "distance $conjName1 to $conjName2 is $distance\n";
			$distances{"$conjName1 $conjName2"} = $distance;
			$distanceSum += $distance;
		} # each conjugation $conjName2 indexed by $conjIndex2
		# print STDERR "$conjName1 has distance sum $distanceSum\n";
		$distanceSums{$conjName1} = $distanceSum;
	} # each conjugation $conjName1 indexed by $conjIndex1
	print "\nSums of distances; central inflection classes are listed first.\n";
	for my $conjName (sort {$distanceSums{$a} <=> $distanceSums{$b}}
			keys %distanceSums) {
		print "$conjName($distanceSums{$conjName}) ";
	}
	print "\n";
} # findCenter

sub groupReferrals {
	my %workingReferrals; # $workingReferrals{$conjName} = referral pattern
	my $parentSequence = 0;
	my $parentName;
	%similarConj = (); # we only use it here and in closestReferrals()
	for my $conjName (@origConjugations) {
		$partialReferrals{$conjName} = $workingReferrals{$conjName} =
			$refersByConj{$conjName};
		print "$conjName has no referral pattern\n" unless
			defined($refersByConj{$conjName});
		if (defined($sameConj{$conjName})) {
			$referralPointer{$conjName} = $sameConj{$conjName};
		}
		if (defined($similarConj{$conjName})) {
			$referralPointer{$conjName} = $similarConj{$conjName};
		}
	} # each conjName
	print "I see " . scalar(@origConjugations) . " inflection classes\n";
# compute analysis
	my @maybeJoinedNames;
	while (1) { # try to join two referral patterns
		my ($distance, $conjName1, $conjName2) =
			closestReferrals(\%workingReferrals);
		last unless defined($distance);
		# print STDERR "closest: $conjName1, $conjName2 is $distance\n";
		$parentSequence += 1;
		$parentName = "Join$parentSequence";
		$parent{$conjName1} = $parent{$conjName2} = $parentName;
		if ($distance == 0) { # new similarities exist
			$referralPointer{$conjName1} = $parentName;
			$referralPointer{$conjName2} = $parentName;
		}
		my @referralArray1 = @{$workingReferrals{$conjName1}};
		# print STDERR "conj array 1 is: " . join(" ", @referralArray1) . "\n";
		delete $workingReferrals{$conjName1};
		my @referralArray2 = @{$workingReferrals{$conjName2}};
		delete $workingReferrals{$conjName2};
		# print STDERR "Joining $conjName1 and $conjName2 (dist $distance) " .
		#	"to make Join$parentSequence\n";
		($partialReferrals{$conjName1}, $partialReferrals{$conjName2},
			$workingReferrals{$parentName}) =
			intersectReferrals($conjName1, \@referralArray1,
				$conjName2, \@referralArray2);
		# print "after intersect\n\t" .
		# 	"$conjName1 $partialReferrals{$conjName1}\n\t" .
		# 	"$conjName2 $partialReferrals{$conjName2}\n\t" . 
		# 	"=> $parentName $workingReferrals{$parentName}\n";
		$partialReferrals{$parentName} =
			referArrayToString($workingReferrals{$parentName});
		push @maybeJoinedNames, $parentName;
	} # while joining referral pattens
# remove trivial join points
	my %usedJoins;
	for my $conjName (@origConjugations, @maybeJoinedNames) {
		my $parent = $parent{$conjName};
		if (!defined($parent)) {
			# print STDERR "nobody parents $conjName\n";
			$usedJoins{$conjName} = 1;
			next;
		}
		# print STDERR "working on $conjName, parent is $parent\n";
		while ($partialReferrals{$parent} eq "") {
			last unless defined($parent{$parent});
			$parent = $parent{$parent};
		}
		$parent{$conjName} = $parent;
		# print STDERR "setting parent of $conjName to $parent\n";
		$usedJoins{$parent} = 1;
	}
	for my $conjName (@maybeJoinedNames) {
		push @joinedNames, $conjName if defined($usedJoins{$conjName});
	}
# compute top-down tree
	my (@tops, %children);
	for my $conjName (@origConjugations, @joinedNames) {
		my $parent = $parent{$conjName};
		if (defined($parent)) {
			$children{$parent} = [] unless defined $children{$parent};
			push @{$children{$parent}}, $conjName;
		} else {
			push @tops, $conjName;
		}
	}
# print analysis
	print "\nGrouping referral patterns together\n";
	my $total;
	for my $top (@tops) {
		showReferralChildren($top, \%children, 1);
	}
} # groupReferrals

# for defective cells, walk up the join tree to find the replacement for
# the given distillation
sub findDefault {
	my ($conjName, $base) = @_;
	my $parent = $parent{$conjName};
	my $partial = $partialEssence{$parent};
# search in parent
	for my $essence (split /\s+/, $partialEssence{$parent}) {
		if ($essence =~ /e${base}_(\d+)/) {
			# print "$conjName $base => $essence\n";
			return $essence;
		}
	}
# not found; go higher
	return findDefault($parent, $base);
} # findDefault

sub showChildren {
	my ($top, $childrenPtr, $depth) = @_;
	my $total;
	my $indent = "  " x $depth;
	my $essences = $partialEssence{$top};
	$essences =~ s/e\d+_0\b\s*//g; # remove defects
	print "$indent$top: $essences\n";
	$total = scalar (my @dummy = split (/ /, $partialEssence{$top}));
	for my $child (@{${$childrenPtr}{$top}}) {
		$total += showChildren($child, $childrenPtr, $depth+1);
	}
	return $total;
} # showChildren

sub showReferralChildren {
	my ($top, $childrenPtr, $depth) = @_;
	my $total;
	my $indent = "  " x $depth;
	my $referrals = $partialReferrals{$top};
	# print "$indent$top: " . join(':', @{$referrals}) . "\n";
	$referrals =~ s/-1/X/g;
	$referrals = (length $referrals) ? ': ' . $referrals : '';
	my $trueConjugation = $sameConj{$top};
	$trueConjugation = defined($trueConjugation)
		? ' (identical to ' . $trueConjugation . ')' : '';
	print "$indent$top$trueConjugation$referrals\n";
	for my $child (@{${$childrenPtr}{$top}}) {
		showReferralChildren($child, $childrenPtr, $depth+1);
	}
} # showReferralChildren

sub intersectConjugations {
	# assume both conjugations have the same set of distillations
	my ($conj1, $essenceArrayPtr1, $conj2, $essenceArrayPtr2) = @_;
	my (@intersection, @diff1, @diff2); # answers
	@intersection = (); @diff1 = (); @diff2 = (); 
	for (my $distillationIndex = 0;
		$distillationIndex < $distillationCount;
		$distillationIndex += 1)
	{
		my $essence1 = ${$essenceArrayPtr1}[$distillationIndex];
		$essence1 =~ /e(\d*)_(\d+)$/ or die("what is $conj1($essence1)?");
		my ($base, $value1) = ($1, $2);
		my $essence2 = ${$essenceArrayPtr2}[$distillationIndex];
		$essence2 =~ /e${base}_(\d+)$/
			or die("unexpected base in $essence2; expected $base");
		my ($value2) = ($1);
		if ($value1 == $value2) { # identical is in intersection
			push @intersection, $essence1;
		} elsif ($value1 == 0) { # defect can become anything
			push @intersection, $essence2;
		} elsif ($value2 == 0) {# defect can become anything
			push @intersection, $essence1;
		} else { # true difference
			push @diff1, $essence1;
			push @diff2, $essence2;
			push @intersection, "e${base}_0";
		}
	} # each distillation
	return (join(' ', @diff1), join(' ', @diff2), join(' ', @intersection));
} # intersectConjugations

sub intersectReferrals {
	# assume both conjugations have the same set of stems
	my ($conj1, $referralArrayPtr1, $conj2, $referralArrayPtr2) = @_;
	my (@intersection, @diff1, @diff2); # answers
	@intersection = (); @diff1 = (); @diff2 = (); 
	for (my $stemIndex = 0; $stemIndex <= $#stems; $stemIndex += 1)
	{
		my $referral1 = ${$referralArrayPtr1}[$stemIndex];
		my $referral2 = ${$referralArrayPtr2}[$stemIndex];
		if ($referral1 == $referral2) { # identical is in intersection
			push @intersection, $referral1;
		} elsif ($referral1 == -1) {
			push @intersection, $referral2;
		} elsif ($referral2 == -1) {
			push @intersection, $referral1;
		} else { # true difference
			push @diff1, "$stemIndex->$referral1";
			push @diff2, "$stemIndex->$referral2";
			push @intersection, "-1";
		}
	} # each stem
	return (join(', ', @diff1), join(', ', @diff2), \@intersection);
} # intersectReferrals

sub closestConjugations {
	# returns triple: distance, conjName1, conjName2
	my ($conjHashPtr) = @_;
	my %conjHash = %$conjHashPtr;
	my @conjNameList = keys %conjHash;
	my $smallestDistance = 2 * length($conjHash{$conjNameList[0]}) + 1; # big
	my @answer = ();
	# compute pairwise distances, remembering the smallest
	for my $conjIndex1 (0 .. $#conjNameList) {
		my $conjName1 = $conjNameList[$conjIndex1];
		my @essences1 = split(/ /, ${$conjHashPtr}{$conjName1});
		next unless scalar @essences1;
		# print STDERR "conjName1 = $conjName1\n";
		# print STDERR "\t$conjName1 has contents " . ${$conjHashPtr}{$conjName1}
		# 	. "\n";
		for my $conjIndex2 ($conjIndex1+1 .. $#conjNameList) {
			my $conjName2 = $conjNameList[$conjIndex2];
			# my $showThis = ($conjName1 eq 'P16c') && ($conjName2 eq 'P16d');
			my (%seen1, %seen2);
			for my $essence1 (@essences1) {
				$seen1{$essence1} = 1;
			}
			my @essences2 = split(/ /, ${$conjHashPtr}{$conjName2});
			next unless scalar @essences2;
			for my $essence2 (@essences2) {
				$seen2{$essence2} = 1;
			}
			my $distance = 0;
			for my $essence1 (@essences1) {
				next if $essence1 =~ /_0$/; # ignore defects
				$distance += 1 unless defined($seen2{$essence1});
			}
			for my $essence2 (@essences2) {
				next if $essence2 =~ /_0$/; # ignore defects
				$distance += 1 unless defined($seen1{$essence2});
			}
			# print "Distance between $conjName1 and $conjName2 is $distance;" .
			# 	"smallest is $smallestDistance\n" if $showThis;
			next unless $distance < (scalar @essences1) + (scalar @essences2);
				# discard worthless splits
			if ($distance < $smallestDistance) { # CAN FLIP
				$smallestDistance = $distance;
				@answer = ($distance, $conjName1, $conjName2);
			}
		} # each conjugation $conjName2 indexed by $conjIndex2
	} # each conjugation $conjName1 indexed by $conjIndex1
	return @answer;
} # closestConjugations

sub closestReferrals {
	# returns triple: distance, conjName1, conjName2
	# shortcut return if conjName1 has a known referral pointer.
	my ($conjHashPtr) = @_;
	my %conjHash = %$conjHashPtr;
	my @conjNameList = keys %conjHash;
	my $smallestDistance = 2 * length($conjHash{$conjNameList[0]}) + 1; # big
	my @answer = ();
	# compute pairwise distances, remembering the smallest
	for my $conjIndex1 (0 .. $#conjNameList) {
		my $conjName1 = $conjNameList[$conjIndex1];
		my @referrals1 = @{${$conjHashPtr}{$conjName1}};
		# print STDERR "conjName1 = $conjName1\n";
		# print STDERR "\t$conjName1 has referrals " . join(':', @referrals1) 
		# 	. "\n";
		if (defined($referralPointer{$conjName1})) {
			my $target = $sameConj{$conjName1};
			while (defined($referralPointer{$target})) {
				$target = $referralPointer{$target};
			}
			# print "shortcut: $conjName1 => $target\n"; # debug
			return(0, $conjName1, $target);
		}
		for my $conjIndex2 ($conjIndex1+1 .. $#conjNameList) {
			my $conjName2 = $conjNameList[$conjIndex2];
			my @referrals2 = @{${$conjHashPtr}{$conjName2}};
			my $distance = 0;
			for my $index (0 .. $#referrals1-1) {
				$distance += 1
					if ($referrals1[$index] != $referrals2[$index])
						and ($referrals1[$index] != -1)
						and ($referrals2[$index] != -1);
			}
			# print "Distance between $conjName1 and $conjName2 is $distance;" .
			# 	"smallest is $smallestDistance\n" if $showThis;
			if ($distance < $smallestDistance) {
				$smallestDistance = $distance;
				@answer = ($distance, $conjName1, $conjName2);
			}
			return @answer if $distance == 0; # no need to belabor it
		} # each conjugation $conjName2 indexed by $conjIndex2
	} # each conjugation $conjName1 indexed by $conjIndex1
	return @answer;
} # closestReferrals

# If we remove the distillations given by the principalParts pattern,
# and only consider the distillations given by the toExplain pattern,
# compute the badness, that is, the number of times a given
# principalParts pattern generates multiple toExplain distillations.
sub countReduce {
	my ($principalParts, $toExplain) = @_;
	# remove the given distillation
	my ($conjName, $explainStructure, $princPartClass, %explainedBy,
		$bad);
	$bad = 0;
	foreach $conjName (@conjugations) { # one conjugation
		my $tmpPrincipalParts = $principalParts;
		my $tmpToExplain = $toExplain;
		my @oldConj = @{$essencePerConj{$conjName}};
		my @explainConj = ();
		my @princPartConj = ();
		while (scalar @oldConj) {
			# copy maybe one distillation from oldConj to explainConj
			if ($tmpPrincipalParts & 01) {
				# this distillation is a principal part
				push @princPartConj, (shift @oldConj);
			} elsif ($tmpToExplain & 01) { # this distillation must be explained
				push @explainConj, (shift @oldConj);
			} else { # ignore this distillation
				shift @oldConj;
			}
			$tmpPrincipalParts >>= 1;
			$tmpToExplain >>= 1;
		} # one distillation
		$explainStructure = join(",", @explainConj);
		# printf "principal parts %04o conj $conjName becomes $explainStructure\n",
		# 	$principalParts;
		$princPartClass = join(",", @princPartConj);
		# print "princPartClass is $princPartClass\n";
		if (defined($explainedBy{$princPartClass})) {
			# a known princPartClass distillation
			if ($explainedBy{$princPartClass} =~
				/(^| )\Q$explainStructure\E($| )/)
			{ # should not happen if $toExplain is full
				die ("two conjugations have the same distillation: " .
					$explainStructure)
					if ($toExplain == (1 << $distillationCount) -1);
			} else { # a new explainStructure for this princPartClass
				# print "bad: $explainStructure also explained by $princPartClass\n";
				$explainedBy{$princPartClass} .= " " . $explainStructure;
				$bad += 1;
			}
		} else { # a new princPartClass
			# print "ok: $explainStructure explained by $princPartClass\n";
			$explainedBy{$princPartClass} = $explainStructure;
		}
	} # one conjugation
	# print "bad value is $bad\n";
	return $bad;
} # countReduce

# given a bit pattern of distillations and a list of conjugations, return a hash
# keyed by those conjugations for which those distillations are principal, that is,
# are completely determined by those distillations.
sub distinguishedBy {
	my ($pattern, $conjList) = @_;
	my %conjSatisfying;
	my %answer;
	for my $conjugation (@$conjList) {
		my $exponences;
		my $allExponences = $essencePerConj{$conjugation};
		for my $distillationIndex (0 .. $distillationCount-1) {
			next unless ($pattern & (1 << $distillationIndex));
			$exponences .= " ${$allExponences}[$distillationIndex]";
			# print STDERR "IC $conjugation: exponences are now $exponences\n";
		} # each distillationIndex
		$conjSatisfying{$exponences} = []
			unless defined($conjSatisfying{$exponences});
		push @{$conjSatisfying{$exponences}}, $conjugation;
	} # each conjugation
	for my $exponences (keys %conjSatisfying) {
		if (scalar @{$conjSatisfying{$exponences}} == 1) {
			# print STDERR "we distinguish ${$conjSatisfying{$exponences}}[0]\n";
			$answer{${$conjSatisfying{$exponences}}[0]} = 1;
		}
	} # each exponence set
	return \%answer;
} # distinguishedBy

sub findStaticPatterns {
	my ($pattern, $numClasses, $bestBad, $bad, @bestPatterns);
	$bestBad = $conjCount + 1; # priming
	my $allBits = (1 << $distillationCount) - 1;
	if (1) {
		foreach $pattern (@patternList) { # in increasing bitcount order
		# for ($pattern = 00017; $pattern; $pattern = 0) 
			# print "Pattern is " . patternToNumber($pattern) . "\n";
			next unless ($pattern & $forcedBits) == $forcedBits;
			my $bitCount = bitCount($pattern);
			last if ($bitCount > $bestBad); # not worth considering
			$bad = countReduce($pattern, $allBits);
			next unless $bad == 0;
			# $bad = $conjCount - $numClasses + bitCount($pattern);
			if ($bitCount < $bestBad) {
				@bestPatterns = (); # reset; a better group is coming
			}
			if ($bad + $bitCount <= $bestBad) {
				# printf
				# 	"pattern %04o: %2d principal parts, bad %d\n",
				# 	$pattern, $bitCount, $bad;
				$bestBad = $bad + $bitCount;
				push @bestPatterns, $pattern;
			}
		} # one pattern
	} # if we do first step
	return @bestPatterns;
} # findStaticPatterns

sub findQuickStatic {
	my ($pattern, $bad);
	$pattern = 0;
	my $allBits = (1 << $distillationCount) - 1;
	$bad = countReduce($pattern, $allBits);
	# print "$bad\n";
	while ($bad > 0) {
		# print "pattern " . patternToNumber($pattern) . ": $bad\n";
		my $bestBad = scalar (@conjugations);
		my $bestBit;
		for my $distillation (0 .. $distillationCount-1) {
			my $bit = 1 << $distillation;
			next if $bit & $pattern; # we already have this bit
			my $newBad = countReduce($pattern | $bit, $allBits);
			if ($newBad < $bestBad) {
				$bestBad = $newBad;
				$bestBit = $bit;
			}
		}
		print "best bit is " . patternToNumber($bestBit) .
		 	" " . patternToMPS($bestBit) . ": $bestBad\n";
		$pattern |= $bestBit;
		$bad = $bestBad;
	} # while $bad > 1
# see if we can improve by removing any bits
	for my $distillation (0 .. $distillationCount-1) {
		my $bit = 1 << $distillation;
		next unless $bit & $pattern;
		if (countReduce($pattern - $bit, $allBits) == 0) {
			print "Can remove bit " . patternToNumber($bit) .
			 	" from the pattern!\n";
			$pattern -= $bit;
		}
	} # each distillation
	my @answer = ($pattern);
	return @answer;
} # findQuickStatic

sub computeStratify {
	my ($pattern, $bad);
	$pattern = 0;
	my $allBits = (1 << $distillationCount) - 1;
	$bad = countReduce($pattern, $allBits);
	# print "$bad\n";
	my $stratum = 0;
	my @liveConjugations = @conjugations;
	while ($bad > 0) {
		# print STDERR "pattern " . patternToNumber($pattern) . ": $bad\n";
		my $bestBad = scalar (@liveConjugations);
		my $bestBit;
		for my $distillation (0 .. $distillationCount-1) {
			my $bit = 1 << $distillation;
			next if $bit & $pattern; # we already have this bit
			my $newBad = countReduce($pattern | $bit, $allBits);
			if ($newBad < $bestBad) {
				$bestBad = $newBad;
				$bestBit = $bit;
			}
		}
		# print STDERR "best bit is " . patternToNumber($bestBit) .
		 	" " . patternToMPS($bestBit) . ": $bestBad\n";
		$pattern |= $bestBit;
		$bad = $bestBad;
		my $distinguishing = distinguishedBy($pattern, \@liveConjugations);
		$stratum += 1;
		print "\tstratum $stratum: " . patternToMPS($bestBit) .
			" distinguishes " .  join(', ', keys %$distinguishing) . "\n";
		my @nextLive;
		for my $conjugation (@liveConjugations) {
			push @nextLive, $conjugation unless
				defined(${$distinguishing}{$conjugation});
		}
		@liveConjugations = @nextLive;
	} # $bad > 0
	print "\n";
} # computeStratify

sub buildSubpatterns {
	my ($pattern) = @_;
	my $bit;
# find first bit in $patern
	for ($bit = 1; $bit < 1 << $distillationCount; $bit <<= 1) {
		last if $bit & $pattern;
	}
	my @list0 = (0);
	my @list1 = insertStaticBit($pattern, @list0);
	my @list2 = insertStaticBit($pattern, @list1);
	my @list3 = insertStaticBit($pattern, @list2);
	my @list4 = insertStaticBit($pattern, @list3);
	return (@list0, @list1, @list2, @list3, @list4);
} # buildSubpatterns

sub insertStaticBit {
	my ($allowed, @previousList) = @_;
	my @newList = ();
	for my $pattern (@previousList) {
		for (my $bit = 1; $bit < 1 << $distillationCount; $bit <<= 1) {
			next if $bit <= $pattern; # not big enough
			next unless $bit & $allowed; # restrict bits
			push @newList, $pattern | $bit;
		} # for bit
	} # for pattern
	return @newList;
} # insertStaticBit

# see how well each best pattern explains individual distillations
sub explainStatic {
	my (@staticPatterns) = @_;
	for my $staticPattern (@staticPatterns) { # one best pattern
		printf "\nHow well does set %s explain nonprincipal parts?\n",
			patternToNumber($staticPattern);
		my @staticSubPatterns = buildSubpatterns($staticPattern);
		my $bad;
		my $total = 0.0; # total number of principal parts needed, at best
		my ($oneDistillationPattern, $testPattern);
		for ($oneDistillationPattern = 1;
			$oneDistillationPattern < (1 << $distillationCount);
			$oneDistillationPattern <<= 1)
		{
			next if $oneDistillationPattern & $staticPattern;
			my $bestSize = $conjCount + 1; # priming
			my @winners = ();
			for $testPattern (@staticSubPatterns) {
				# $testPattern must be a subset of $staticPattern
				# printf "testPattern %04o, staticPattern %04o\n", $testPattern,
				# 	$staticPattern;
				last if bitCount($testPattern) > $bestSize;
				$bad = countReduce($testPattern, $oneDistillationPattern);
				if ($bad == 0) { # new winner
					push @winners, $testPattern;
					$bestSize = bitCount($testPattern);
				}
			} # one test pattern
			printf "\tCan explain %s by %s using %d principal parts:",
				patternToNumber($oneDistillationPattern),
				patternToNumber($staticPattern),
				$bestSize;
			printPatterns(\@winners, "", " ");
			print "\n";
			$total += $bestSize;
		} # one individual distillation
		my $score;
		if ($distillationCount == bitCount($staticPattern) and $total == 0) {
			$score = 0.0;
		} else {
			$score = (0.0 + $total) /
				($distillationCount - bitCount($staticPattern));
		}
		printf "\t%d references to %s are needed to explain other " .
			"distillations,\n\t\tfor a score of %4.2f\n",
			$total, patternToNumber($staticPattern), $score;
		computeStatistics($staticPattern, 'static');
	} # one best pattern
} # explainStatic

# Given a distillation and a set of conjugations, compute how many
# different exponences that distillation has for those conjugations, and
# also the set of such exponences.
sub spread {
	my ($distillation, $conjSet) = @_;
	my (%seenExponences, $numExponences);
	$numExponences = 0;
	for my $conj (keys %$conjSet) { # one conjugation
		my $exponence = ${${$conjSet}{$conj}}[$distillation];
		# print "spread: the distillation is $exponence\n"; # debug
		if (!$seenExponences{$exponence}) { # a new exponence
			$seenExponences{$exponence} = 1;
			$numExponences += 1;
		} # a new distillation
	} # one conjugation
	return($numExponences, \%seenExponences);
} # spread

# Given a distillation and a set of conjugations, compute how often each
# exponence occurs in that distillation over those conjugations,
# returning both the hash of counts and the largest count seen.
sub maxConj {
	my ($distillationIndex, $conjSet) = @_;
	my (%exponenceCounts, $answer);
	$answer = 0;
	for my $conj (keys %$conjSet) { # one conjugation
		print STDERR "should not use duplicate inflection class $conj\n"
			if defined($sameConj{$conj});
		my $exponence = lhs(${${$conjSet}{$conj}}[$distillationIndex]);
		# print "maxConj: the distillation is $exponence\n"; # debug
		$exponenceCounts{$exponence} += 1;
		# print "Have now seen $exponence $exponenceCounts{$exponence} times\n";
		$answer = $exponenceCounts{$exponence}
			if $answer < $exponenceCounts{$exponence};
	} # one conjugation
	return($answer, \%exponenceCounts);
} # maxConj

# backtracking.  Return max depth of best child for branch and bound.
sub findBestAdaptivePattern {
	my ($pattern, $conjSet, $depth, $limit) = @_;
		# the principal parts so far, remaining conjugations
	my $tabs = "." x $depth;
	return ($depth, [keys %$conjSet]) if (scalar keys %$conjSet <= 1);
	if ($depth >= $limit) {
		# print "$tabs over the limit; rejecting\n";
		return ($infinity, undef);
	}
	my ($theMetric, $distillationIndex, @possibilities, $possibility,
		$theExponenceSet, $bestResult, @bestTree);
	# print "best pattern is " . patternToNumber($statics[0]) . "\n";
	for ($distillationIndex = 0;
		$distillationIndex < $distillationCount;
		$distillationIndex += 1)
	{
		# print "shall I push $distillationIndex?\n";
		next if
			(defined($statics[0]) && !((1 << $distillationIndex) &
			$statics[0]));
		# print "\tIt is a static principal part\n";
		next if (1 << $distillationIndex) & $pattern;
		# print "\tit isn't already spoken for\n";
		($theMetric, $theExponenceSet) =
			maxConj($distillationIndex, $conjSet);
		push @possibilities,
			[$theMetric, $theExponenceSet, $distillationIndex];
	} # one distillation 
	$bestResult = $infinity;
	@bestTree = ();
	for $possibility (sort {${$a}[0] <=> ${$b}[0]} @possibilities) { 
		# record $possibility
		($theExponenceSet, $distillationIndex) = @{$possibility}[1 .. 2];
		my $resultDepth; # greatest depth for all distillations in
			# theExponenceSet
		my @resultTree = (); # capturing all the distillations
		for my $theDistillation (keys %$theExponenceSet) {
			# add this distillation
			# print "$tabs $distillationIndex $theDistillation: ICs ";
			my (%newConjSet, $aConj, $count);
			# build %newConjSet containing only conjugations agreeing that
			# $distillationIndex is $theDistillation
			$count = 0;
			for $aConj (keys %$conjSet) {
				if (lhs(${${$conjSet}{$aConj}}[$distillationIndex]) eq
					$theDistillation)
				{
					$newConjSet{$aConj} = ${$conjSet}{$aConj};
					# print "$aConj "; # debug
					$count += 1;
				}
			} # each aConj
			# print "\n"; # debug
			my ($foundDepth, $foundTree) = findBestAdaptivePattern(
				$pattern + (1<<$distillationIndex), \%newConjSet, $depth + 1,
					$limit);
			if ($foundDepth == $infinity) { # no good result can follow
				# print "$tabs abandoning\n";
				$resultDepth = $infinity;
				last; # don't bother with the other distillations
			} elsif (defined($resultDepth)) { # maintain max of result depths
				$resultDepth = max($foundDepth, $resultDepth);
			} else { # first result
				$resultDepth = $foundDepth;
			}
			push @resultTree, [$theDistillation, $foundTree];
		} # add this distillation
		if (!defined($resultDepth)) {
			# print "$tabs end of possibility: all paths bad\n";
			@bestTree = ();
		} elsif ($resultDepth < $limit) {
			# print "$tabs end of possibility $tabs $distillationIndex best depth: $resultDepth\n";
			$limit = $resultDepth;
			$bestResult = $limit;
			@bestTree = @resultTree;
			unshift @bestTree, $distillationIndex;
		} else {
			# print "$tabs end of possibility $distillationIndex; resultDepth " . "$resultDepth did not improve $limit\n";
		}
	} # one possibility
	# print "$tabs returning: result is $bestResult\n";
	return ($bestResult, \@bestTree);
} # findBestAdaptivePattern

sub showTree {
	my ($tree, $depth) = @_;
	my $tabs = "* " x $depth;
	my @localTree = @$tree;
	# print "$tabs working on tree $tree: ", join(",", @localTree), "\n";
	return if (scalar @$tree) == 0;
	my $distillationIndex = $localTree[0];
	if ($#localTree == 0) {
		print "" . ("  " x $depth) . " the inflection class is $localTree[0]\n";
	} else { # there are children
		for my $branch (@localTree[1 .. $#localTree]) {
			print "${tabs}if distillation " .
				patternToNumber(1 << $distillationIndex)  .
				' ' .
				patternToMPS(1 << $distillationIndex) .
				" has variant ${$branch}[0] ($cellPerEssence{${$branch}[0]})\n";
			showTree(${$branch}[1], $depth+1);
		} # each $branch
	} # there are children
} # showTree

sub patternToNumber {
	my ($pattern) = @_;
	my @Answer = ();
	for my $bit (0 .. $distillationCount-1) { # a bit in the pattern
		push @Answer, $bit+1
			if ((1<< $bit) & $pattern); 
	} # a bit in the pattern
	# return "(" . join(", ", @Answer) . ")";
	return join(",", @Answer);
} # patternToNumber

sub patternToMPSCode {
	my ($pattern) = @_;
	my $answer;
	my $bitFailure = 0;
	for my $bit (0 .. $distillationCount-1) { # a bit in the pattern
		next unless ((1<< $bit) & $pattern);
		my $essenceCell = ${$essencePerConj{$conjugations[0]}}[$bit];
		$essenceCell =~ /e(\d+)/;
		my $MPS = $1;
		# print STDERR "mps $MPS is a distillation\n";
		if ($MPS >= $bitsPerInt) {
			$bitFailure = 1;
		} else {
			$answer |= 1 << ($MPS-1);
		}
	} # a bit in the pattern
	return ($answer, $bitFailure);
} # patternToMPSCode

sub patternToMPS {
	my ($pattern, $short) = @_;
	my (@MPSNameList);
	@MPSNameList = ();
	for my $bit (0 .. $distillationCount-1) { # a bit in the pattern
		next unless ((1<< $bit) & $pattern);
		my $essenceCell = ${$essencePerConj{$conjugations[0]}}[$bit];
		$essenceCell =~ /e(\d+)/;
		my $MPS = $1;
		push @MPSNameList, $MPSNames[$MPS-1];
	} # a bit in the pattern
	if (defined $short) {
		return "" . join(",", @MPSNameList);
	} else {
		return "(" . join(", ", @MPSNameList) . ")";
	}
} # patternToMPS

sub printForced {
	if ($forcedBits) {
		print "\tForcing these MPSs to participate: " . 
			patternToNumber($forcedBits) . " " .
			patternToMPS($forcedBits) . "\n";
	}
} # printForced

sub printPatterns {
	my ($patterns, $header, $trailer) = @_;
	if (scalar @$patterns == 0) {
		print "Parameter m ($bitsPerPattern) is too small.\n";
		return;
	}
	for my $pattern (@$patterns) { # a pattern to print
		printf "%s %s %s%s", $header, patternToNumber($pattern),
			patternToMPS($pattern), $trailer;
	} # a pattern to print
} # printPatterns

sub patternExponence {
	my ($conj, $pattern) = @_;
	my @exponenceList = @{$essencePerConj{$conj}};
	my $answer = $cache{"$conj,$pattern"};
	if (!defined($answer)) {
		$answer = ""; 
		for (my $distillationPattern = 1, my $index = 0;
				$distillationPattern < (1 << $distillationCount);
				$distillationPattern <<= 1, $index += 1) { # one distillation
			$answer .= " " . $exponenceList[$index]
				if ($distillationPattern & $pattern);
		} # one distillation
		$cache{"$conj,$pattern"} = $answer;
	} # !defined($answer)
	return($answer);
} # patternExponence

# returns (count, \%needed), where count is how many principal parts are needed
# to explain the exponent found in the cell ($theConj, $theDistillation), and
# needed is a hash with keys for all the indices of principal parts that we
# needed.  "To explain" means to determine the correct exponent, even if other
# cells in the same column might have the same exponent.
sub computeStaticBadness {
	my ($theDistillation, $theConj, $prinPartPattern) = @_;
	my $debug = ($theConj eq 'conj4') && ($theDistillation == 0);
	$debug = 0;
	print "Working on $theConj, distillation " . ($theDistillation+1) . "\n"
		if $debug;
	if ((1 << $theDistillation) & $prinPartPattern) {
		print "It's a principal part; returning 1\n" if $debug;
		return(1, {$theDistillation => 1});
	}
	my $answer;
	my %needed;
	my $bestPattern;
	my @subPatterns = buildSubpatterns($prinPartPattern);
	print "there are " . scalar(@subPatterns) . " subpatterns\n" if $debug;
# compute completely different conjugation list
	my @uniqueConjugations = ();
	for my $conj (keys %conjugations) {
		push @uniqueConjugations, $conj
			unless defined($similarConj{$conj});
	}
# see which subpatterns explain the cell
	for my $testPattern (@subPatterns) {
		# maybe this pattern explains the cell
		print "\ttest pattern " . patternToNumber($testPattern) . "\n"
			if $debug;
		my @conjugations = @uniqueConjugations;
		$answer = bitCount($testPattern);
		$bestPattern = $testPattern; # at least for this iteration
		%needed = (); # fresh for this iteration
		my (@newConjugations, @tempConjugations, $distillationIndex);
		for ($distillationIndex = 0;
			$distillationIndex < $distillationCount;
			$distillationIndex += 1)
		{ # try reducing conjugations by principal part $distillationIndex
			my $distillationPattern = 1 << $distillationIndex;
			next unless $distillationPattern & $testPattern;
				# $distillationIndex must be a prinpart
			$needed{$distillationIndex} = 1;
			my $targetExponence = 
				# $exponenceAbbrevs{${$conjugations{$theConj}}
				# 	[$distillationIndex]};
				${$essencePerConj{$theConj}}[$distillationIndex];
			print "\t\ttrying prinpart " . patternToNumber($distillationPattern)
				. " where conjugation $theConj shows $targetExponence\n"
				if $debug;
			@tempConjugations = ();
			foreach my $aConj (@conjugations) {
				my $principalExponence =
					# $exponenceAbbrevs{${$conjugations{$aConj}}
					# 	[$distillationIndex]};
					${$essencePerConj{$aConj}}[$distillationIndex];
				# print "\t\t\tLooking at IC $aConj, exponence " 
				# 	. "$principalExponence =? $targetExponence\n"
				# 	if $debug;
				push @tempConjugations, $aConj
					if $principalExponence eq $targetExponence;
			}
			print "\t\tThese inflection classes remain: "
				. join(", ", @tempConjugations) . "\n" if $debug;
			@conjugations = @tempConjugations;
				# reduced by this distillationIndex
		} # one principal part $distillationIndex
		print "\twe might be in any of " . (scalar @conjugations)
			. " inflection classes: " .  join(", ", @conjugations) . "\n" if $debug;
		my %exponences = ();
		foreach my $aConj (@conjugations) {
			# $exponences{${$conjugations{$aConj}}[$theDistillation]} = 1;
			$exponences{${$essencePerConj{$aConj}}[$theDistillation]} = 1;
		}
		my $numExponences = scalar (keys %exponences);
		print "\twhich exhibit $numExponences distinct exponences in " .
			"distillation "
			. ($theDistillation + 1) . "\n" if $debug;
		last if $numExponences == 1; # we have enough principal parts to
			# determine this variety
	} # add another cell if necessary
	print "returning $answer; the principal parts needed are "
		.  patternToNumber($bestPattern) . "\n" if $debug;
	return ($answer, \%needed);
} # computeStaticBadness

# returns (count, \%needed), where count is how many principal parts are needed
# to explain the exponent found in the cell ($theConj, $theMPS), and needed is
# a hash with keys for all the indices of principal parts that we needed.
sub computeTreeBadness {
	my ($theDistillation, $theConj, $tree) = @_;
	my $answer = 0;
	my %needed;
	my @conjugations = keys %conjugations; # those not yet excluded
	while (1) { # one step down the tree
		my %distillations;
		# print "\twe have " . (scalar @conjugations) . " inflection classes: "
		# 	.  join(", ", @conjugations) ;
		foreach my $aConj (@conjugations) {
			$distillations{${$essencePerConj{$aConj}}[$theDistillation]} = 1;
		}
		my $numDistillations = scalar (keys %distillations);
		# print " with $numDistillations distinct distillations in cell $theDistillation\n";
		last if $numDistillations == 1;
		my @localTree = @$tree;
		my $distillationIndex = $localTree[0];
		$needed{$distillationIndex} = 1;
		my ($foundBranch);
		for my $branch (@localTree[1 .. $#localTree]) {
			# print "\ttrying ${$branch}[0]\n";
			# print "\t\tvs $essencePerConj{$theConj}[$distillationIndex]\n";
			if (${$branch}[0] eq
				$essencePerConj{$theConj}[$distillationIndex])
			{
				$foundBranch = $branch;
				last;
			}
		}
		# print "success was ${$foundBranch}[0]\n";
		my @newConjugations;
		foreach my $aConj (@conjugations) {
			# print "adding maybe $aConj, based on cell $theDistillation\n";
			push @newConjugations, $aConj
				if ${$essencePerConj{$aConj}}[$distillationIndex] eq
					${$foundBranch}[0];
			# print "checking if ${$essencePerConj{$aConj}}[$distillationIndex] eq " .
			# 	"${$foundBranch}[0]\n";
		}
		$tree = ${$foundBranch}[1];
		@conjugations = @newConjugations;
		$answer += 1;
	} # one step down the tree
	return ($answer, \%needed);
} # computeTreeBadness

sub computeStatistics {
	my ($parts, $how) = @_;
	my $numFields = $distillationCount;
	my %bads;
	print "\nStatistics for $how principal parts "
		. ($how eq 'static' ? patternToNumber($parts) : "")
		. "\n";
	# phase 1: collect data
	my %neededRefs;
	my $fieldWidth = 4; # minimum (we need room for statistics)
	my %entry; # to print
	foreach my $conj (@conjugations) {
		$bads{$conj} = [];
		foreach my $distillationIndex (0 .. $distillationCount - 1) {
			my $bad;
			my $cellID = "$conj=$distillationIndex";
			my $neededRef;
			if ($how eq 'adaptive') {
				($bad, $neededRef) =
					computeTreeBadness($distillationIndex, $conj, $parts);
			} elsif ($how eq 'static') {
				($bad, $neededRef) =
					computeStaticBadness($distillationIndex, $conj, $parts);
			} else {
				print "\n\n";
				print STDERR "I can't compute $how statistics\n";
				return;
			}
			$neededRefs{$cellID} = $neededRef;
			my $neededPattern = 0;
			foreach my $pp (0 .. $distillationCount - 1) {
				$neededPattern += 1 << $pp
					if defined(${$neededRef}{$pp});	
			}
			$entry{$cellID} = patternToNumber($neededPattern);
			$fieldWidth = max($fieldWidth, length($entry{$cellID}));
			${$bads{$conj}}[$distillationIndex] = $bad;
			# print "IC $conj, cell $distillationNames[$distillationIndex]: " .
			# 	"badness $bad\n";
		} # foreach $distillationIndex
	} # foreach $conj
	# phase 2: output values and averages
	my ($conjTotal, @cellTotals, @toPrint);
	print " " . (" " x $maxConjLength);
	my $distillationName;
	foreach my $distillationIndex (0 .. $distillationCount -1) { 
		# printf "%${fieldWidth}s", $distillationNames[$distillationIndex];
		printf "%${fieldWidth}d ", $distillationIndex+1;
	}
	print "\n";
	foreach my $conj (@conjugations) {
		$conjTotal = 0.0;	
		@toPrint = ();
		foreach my $distillationIndex (0 .. $distillationCount -1) { 
			my $cellID = "$conj=$distillationIndex";
			my $value = ${$bads{$conj}}[$distillationIndex];
			# push @toPrint, sprintf("%${fieldWidth}d", $value);
			push @toPrint, sprintf("%${fieldWidth}s ", $entry{$cellID});
			$conjTotal += $value;
			$cellTotals[$distillationIndex] += $value + 0.0;
		} # foreach $distillationIndex
		printf "%${maxConjLength}s %s| %${fieldWidth}.2f\n", $conj,
			join("", @toPrint), $conjTotal / $numFields;
	} # foreach $conj	
	print " " . (" " x $maxConjLength) . # dashed line
		("-" x ($numFields*($fieldWidth+1)+6)) .
		"\n";
	print " " . (" " x $maxConjLength); # summary line
	my $value = 0.0;
	foreach my $distillationIndex (0 .. $distillationCount -1) { 
		printf "%${fieldWidth}.2f ",
			$cellTotals[$distillationIndex] / $conjCount;
		$value += $cellTotals[$distillationIndex];
	}
	printf "| %${fieldWidth}.2f\n", $value / ($conjCount * $numFields);
	# phase 3: output per-principal part statistics
	return if $how ne 'static';
	my $partIndex;
	for ($partIndex = 0; $partIndex < $distillationCount; $partIndex += 1) {
		# one principal part
		my $part = 1 << $partIndex;
		next unless ($part & $parts);
		print "\nPrincipal part " .  patternToNumber($part)
			. " applies to the following:\n";
		print " " . " " x $maxConjLength;
		my $fieldWidth = 2;
		foreach my $distillationIndex (0 .. $distillationCount -1) {
			printf "%${fieldWidth}d ", $distillationIndex+1;
		}
		print "\n";
		foreach my $conj (@conjugations) {
			printf "%${maxConjLength}s|", $conj;
			foreach my $distillationIndex (0 .. $distillationCount -1) { 
				my $neededRef = $neededRefs{"$conj=$distillationIndex"};
				printf "%${fieldWidth}s ",
					defined(${$neededRef}{$partIndex})
					? ($partIndex == $distillationIndex ? "O" : "X")
					: "";
			} # one column
			print "|\n";
		} # one conjugation
		print "\n";
	} # one principal part
} # computeStatistics

sub max {
	my ($a, $b) = @_;
	return ($a > $b ? $a : $b);
} # max

sub round {
	# good enough for positive numbers.
	my ($a) = @_;
	return int($a + 0.5);
} # round

my $displayedDistillationNumbers = 0;
sub printDistillationNumbers {
	return if $displayedDistillationNumbers;
	$displayedDistillationNumbers = 1; # avoid repeating later
	print "\nDistillation numbers\n";
	foreach my $distillationIndex (0 .. $distillationCount -1) {
		printf "\t%d: %s\n", $distillationIndex+1,
			patternToMPS(1 << $distillationIndex, 1);
	}
} # printDistillationNumbers

sub choose { # binomial coefficient
	my ($n, $k) = @_;
	$k = $n - $k if $k > $n - $k;
	my $answer = 1;
	# print "starting with $answer\n";
	for my $index (1 .. $k) {
		my $multiplier = (1.0 + $n - $index) / $index;
		$answer *= $multiplier;
		# print "\tmultiplying by $multiplier gives $answer\n";
	}
	return $answer;
} # choose

sub findBestDynamicPatterns {
	my ($allPatterns) = @_;
	my ($bestBitCount, $index);
	my $numFields = $distillationCount;
	my $headerLength = $maxConjLength + 5;
	my $fieldWidth = 6;
	printDistillationNumbers();
	print " " . " " x $headerLength;
	foreach my $distillationIndex (0 .. $distillationCount -1) {
		printf "%-${fieldWidth}d ", $distillationIndex+1;
	}
	print "\n";
	print " " . " " x $headerLength;
	foreach my $distillationIndex (0 .. $distillationCount -1) {
		printf "%-${fieldWidth}.${fieldWidth}s ", patternToMPS(1 << $distillationIndex, 1);
	}
	print "\n";
	my ($totalRatio, $totalAnalyses, $totalLowAverage, $totalSize); # summary statistics
tryConj:
	foreach my $aConj (@conjugations) { # one conjugation
		my $keys = $keys{$aConj};
		for my $filter (split /\s+/, $outputKeys) {
			if (!defined($keys) or $keys !~ /\b$filter\b/) {
				# print "Not printing: $aConj\n";
				next tryConj;
			}
		}
		# print "inflection class $aConj\n";
		print " " . ("-" x ($headerLength + ($fieldWidth+1)*$numFields)) . "\n";
		printf "%${headerLength}s\n", $aConj;
		my @exponenceList = @{$essencePerConj{$aConj}};
		$bestBitCount = $conjCount + 1; # priming
		my $patternCount = 0;
		my $lowAverage = $numFields;
	tryPattern:
		foreach my $pattern (@patternList) { # in increasing bitcount order
			last if bitCount($pattern) > $bestBitCount && !$allPatterns;
			next unless ($pattern & $forcedBits) == $forcedBits;
			# print "trying " . patternToNumber($pattern) . "\n"; # debug
			# compute aConj's exponences for this pattern
			my $myExponences = patternExponence($aConj, $pattern);
			# compare it to the exponences for other conjugations
			foreach my $otherConj (@conjugations) { # one otherConj
				next if $otherConj eq $aConj;
				my $itsExponences = patternExponence($otherConj, $pattern);
				next tryPattern if $itsExponences eq $myExponences;
			} # one otherConj
			# no other conjugation has the same exponences in this pattern.
			# my $fieldWidth = 4 * bitCount($pattern) + 1;
			# to prepare printing, compute reasonable fieldWidth.
			# $fieldWidth = 2; # minimal size
			my (@toPrint, $totalBits, $columnsShown);
			foreach my $distillationIndex (0 .. $distillationCount -1) {
				my ($bad, $neededRefs) =
					computeStaticBadness($distillationIndex, $aConj, $pattern);
				my $neededPattern = 0;
				foreach my $pp (0 .. $distillationCount - 1) {
					$neededPattern += 1 << $pp
						if defined(${$neededRefs}{$pp});	
				}
				$toPrint[$distillationIndex] = patternToNumber($neededPattern);
				$totalBits += bitCount($neededPattern);
				$columnsShown += 1;
			}
			# now print out details.
			printf "%${headerLength}s ", patternToNumber($pattern) . "|" ;
			foreach my $distillationIndex (0 .. $distillationCount -1) {
				printf "%-${fieldWidth}s ", $toPrint[$distillationIndex];
			}
			my $average = (0.0 + $totalBits) / $columnsShown;
			$lowAverage = $average if $average < $lowAverage;
			print sprintf("avg %4.2f\n", $average);
			$bestBitCount = bitCount($pattern);
			$patternCount += 1;
		} # one pattern
		if ($patternCount == 0) {
			printf("%10s: more than %d principal parts\n", $aConj,
				$bitsPerPattern);
		} else {
			my $coeff = choose($distillationCount, $bestBitCount);
			# print "$distillationCount choose $bestBitCount = $coeff\n";
			printf("%10s: %d principal parts; lowest average %4.2f; %d analyses;"
				. " %3.1f%% of %d possible analyses\n",
				$aConj, $bestBitCount, $lowAverage, $patternCount,
				(100.0*$patternCount)/$coeff, $coeff);
			$totalSize += $bestBitCount;
			$totalLowAverage += $lowAverage;
			$totalAnalyses += $patternCount;
			$totalRatio += (100.0*$patternCount)/$coeff;
		}
	} # one conjugation
	printf "Average number of principal parts: %3.2f\n",
		$totalSize / @conjugations;
	printf "Average lowest average of principal parts needed: %3.2f\n",
		$totalLowAverage / @conjugations;
	printf "Average number of alternative analyses: %3.2f\n",
		$totalAnalyses / @conjugations;
	printf "Average ratio of actual to possible: %3.2f%%\n",
		$totalRatio / @conjugations;
} # findBestDynamicPatterns

sub arrayAdd {
	my ($arrayPtr1, $arrayPtr2) = @_;
	my @answer;
	if (!defined($arrayPtr1)) {
		return @$arrayPtr2;
	}
	for my $index (0 .. $#{$arrayPtr2}) {
		${$arrayPtr1}[$index] = 0 unless defined(${$arrayPtr1}[$index]);
		$answer[$index] = ${$arrayPtr1}[$index] + ${$arrayPtr2}[$index];
	}
	return(@answer);
} # arrayAdd

sub findPredictablePatterns {
	# for each conjugation, each distillation, compute how many patterns
	# predict it.
	my ($full) = @_;
	printDistillationNumbers();
	print "\nPredictabilities\n";
	my ($coverCount, $distillationPattern, $index);
	my $distillationIndex;
	my $headerLength = $maxConjLength + 3;
	print " " . " " x $headerLength;
	my $fieldWidth = 5;
	if ($full) {
		foreach $distillationIndex (0 .. $distillationCount -1) {
			printf "%-${fieldWidth}d ", $distillationIndex+1;
		}
		print "| Avg   Inflection-class predictability\n";
	} else {
		print "| Inflection-class predictability\n";
	}
	my @avgPerDistillationPredictable;
	my ($predTotal, $conjCount) = (0, 0); # to compute averages
	conj:
	foreach my $aConj (@conjugations) { # one conjugation
		my $keys = $keys{$aConj};
		for my $filter (split /\s+/, $outputKeys) {
			if (!defined($keys) or $keys !~ /\b$filter\b/) {
				# print "Not printing: $aConj\n";
				next conj;
			}
		} # each filter
		$conjCount += 1;
		my @exponenceList = @{$essencePerConj{$aConj}};
		my @perDistillationPredictable;
		my $predictCount;
		my $predictableSum = 0;
		my $average;
		if ($full) {
			foreach $distillationIndex (0 .. $distillationCount -1) {
			# (1) per-distillation predictable (cell predictability)
				my $exponence = $exponenceList[$distillationIndex];
				my $distillation = 1 << $distillationIndex;
				$predictCount = 0;
				my $patternCount = 0;
			tryPattern:
				foreach my $pattern (@patternList) { # one pattern
					# compute aConj's exponences for this pattern
					next if $distillation & $pattern; # certain to succeed
						# so we suppress considering it.
					next if $noEmptyPredictor and $pattern == 0;
					$patternCount += 1;
					my $myExponences = patternExponence($aConj, $pattern);
					# compare it to the exponences for other conjugations;
					# complete this loop if this pattern predicts $exponence
					# for all conjugations for which it applies.  Otherwise try
					# next pattern.
					foreach my $otherConj (@conjugations) { # one otherConj
						next if $otherConj eq $aConj; # skip self
						next if
							${$essencePerConj{$otherConj}}[$distillationIndex]
							eq $exponence;
							# predicts $exponence
						my $itsExponences =
							patternExponence($otherConj, $pattern);
						next tryPattern if $itsExponences eq $myExponences;
							# this pattern applies, but doesn't predict
							# $exponence.
					} # one otherConj
					# This pattern predicts $exponence.
					$predictCount += 1;
				} # one pattern
				# printf "%5.2f\n", $predictCount/$patternCount;
				my $predictable = (0.0 + $predictCount) / $patternCount;
				$predictableSum += $predictable;
				push @perDistillationPredictable,
					sprintf("%5.3f", $predictable);
			} # each distillation
		# (2) average of all per-distillation predictables
			$average = $predictableSum / $distillationCount;
		} # full
	# (3) per-conjugation predictable
		$predictCount = 0;
		outerLoop:
		foreach my $pattern (@patternList) { # one pattern
			# next if $pattern == 0; # ignore empty pattern
			my $myExponences = patternExponence($aConj, $pattern);
			foreach my $otherConj (@conjugations) { # one otherConj
				next if $aConj eq $otherConj;
				my $itsExponences = patternExponence($otherConj, $pattern);
				if ($itsExponences eq $myExponences) {
					# print "pattern $pattern does not predict\n";
					next outerLoop;
				}
			} # each otherConj
			$predictCount += 1;
		} # one pattern
	# (4) print information for this IC
		my $size = scalar(@patternList) - 1;
		# We take $size = scalar(@patternList) - 1, 
		# because the empty pattern is almost never predictive of a whole IC.
		my $conjPredictable = (0.0 + $predictCount) / $size;
		$predTotal += $conjPredictable;
		if ($full) {
			printf("%${headerLength}s %s | %5.3f %5.3f (%d out of %d)\n",
				$aConj, join(" ", @perDistillationPredictable),
				$average, $conjPredictable, $predictCount, $size);
			@avgPerDistillationPredictable =
				arrayAdd(\@avgPerDistillationPredictable,
				\@perDistillationPredictable);
		} else {
			printf("%${headerLength}s | %5.3f (%d out of %d)\n",
				$aConj, $conjPredictable, $predictCount, $size);
		}
	} # one conjugation
	# (5) print summary information
	printf "%${headerLength}s ", "Avg";
	my $avgTotal = 0;
	for my $avg (@avgPerDistillationPredictable) {
		printf "%5.3f ", $avg / $conjCount;
		$avgTotal += $avg;
	} 
	if ($full) {
		printf "| %5.3f %5.3f\n",
			$avgTotal / ($conjCount * @avgPerDistillationPredictable),
			$predTotal / $conjCount
	} else {
		printf "| %5.3f\n", $predTotal / $conjCount
	}
} # findPredictablePatterns

sub findPredictivePatterns {
	# for each distillation d, compute how many other distillations d predicts.
	# (eventually, we want a more inclusive definition based on patterns
	# containing d).
	my ($coverCount, $distillationPattern, $index);
	my $distillationIndex;
	my $headerLength = $maxConjLength + 3;
	my $fieldWidth = 5;
	if ($distillationCount == 1) {
		print STDOUT "\tOnly one distillation; " .
			"results are not very meaningful\n";
	}
	my $effectiveCount = $distillationCount > 1
		? $distillationCount - 1
		: $distillationCount;
	my $totalOverall = 0;
	foreach my $d (0 .. $distillationCount - 1) {
		# see how predictive distillation d is
		my $predictiveGrandSum = 0;
		print STDOUT "predictiveness of distillation " . ($d+1)
			. " " .  patternToMPS(1 << $d) . "\n";
		foreach my $aConj (@conjugations) { # one conjugation
			# print STDOUT "\ttrying IC $aConj\n";
			my @exponenceList = @{$essencePerConj{$aConj}};
			my @perDistillationPredictive;
			my $predictCount;
			my $predictiveSum = 0;
			my $average;
			foreach $distillationIndex (0 .. $distillationCount -1) {
			# (1) per-distillation predictive
				my $exponence = $exponenceList[$distillationIndex];
				my $distillation = 1 << $distillationIndex;
				$predictCount = 0;
				my $patternCount = 0;
			tryPattern:
				# foreach my $pattern (@patternList) { # one pattern }
				# foreach my $pattern (03) { # only stem and gender }
				foreach my $pattern ((1 << $d)) { # just singleton for now
					# compute aConj's exponences for this pattern
					# print STDOUT "\tpattern is $pattern " .
					#	patternToMPS($pattern) . "\n";
					next if $distillation & $pattern; # certain to succeed
						# so we suppress considering it.
					$patternCount += 1;
					my $myExponences = patternExponence($aConj, $pattern);
					# compare it to the exponences for other conjugations; complete
					# this loop if this pattern predicts $exponence for all
					# conjugations for which it applies.  Otherwise try next
					# pattern.
					foreach my $otherConj (@conjugations) { # one otherConj
						next if $otherConj eq $aConj; # skip self
						next if
							${$essencePerConj{$otherConj}}[$distillationIndex] eq
							$exponence;
							# predicts $exponence
						my $itsExponences = patternExponence($otherConj, $pattern);
						next tryPattern if $itsExponences eq $myExponences;
							# this pattern applies, but doesn't predict $exponence.
					} # one otherConj
					# This pattern predicts $exponence.
					$predictCount += 1;
				} # one pattern
				my $predictive;
				if ($patternCount) {
					$predictive = (0.0 + $predictCount) / $patternCount;
					# printf "%5.2f\n", $predictive;
					$predictiveSum += $predictive;
				} else {
					$predictive = "X";
					# printf "%s\n", $predictive;
				}
				push @perDistillationPredictive, $predictive;
			} # each distillation
		# (2) average of all per-distillation predictives
			# we subtract 1 because d always predicts itself.
			$average = $predictiveSum / $effectiveCount;
			# print STDOUT "average is $average\n";
		# (3) per-conjugation predictive
			# not very useful, so we don't compute it
		# (4) print information for this IC
			printf("%${headerLength}s %s | %5.3f\n",
				$aConj, join(" ", @perDistillationPredictive), $average);
			$predictiveGrandSum += $predictiveSum;
		} # one conjugation
		my $overall = ($predictiveGrandSum + 0.0) /
		                (@conjugations * $effectiveCount);
		$totalOverall += $overall;
		printf "\toverall predictiveness of %s: %5.3f\n",
			patternToMPS(1<<$d), $overall;
	} # one distillation d
	printf "\nAverage predictiveness across all distillations: %5.3f\n",
		$totalOverall / $distillationCount;
} # findPredictivePatterns

sub lhs { # convert a list of exponences to a form for KATR left-hand side
	my @exponences = @_;
	my @answer = ();
	for my $exponence (@exponences) {
		$exponence =~ s/\[[^\]]*\]//g; # bracketed material disappears
		$exponence =~ s/<([^>]*)>//g; # brocketed material disappears
		# $exponence =~ s/-//g; # hyphens disappear
		$exponence =~ s/^$/-/; # but leave at least a single symbol
		push @answer, $exponence;
	} # each $exponence
	if (scalar @answer == 1) { # a singleton
		return $answer[0];
	} else {
		return @answer;
	}
} # lhs

sub rhs { # convert a list of exponences to a form for KATR right-hand side
	my @exponences = @_;
	my @answer = ();
	for my $exponence (@exponences) {
		if (!defined $exponence) {
			print STDERR "cannot convert RHS for element of ",
				join(' ', @exponences), "\n";
		}
		$exponence =~ s/[][]//g; # bracketed material stays
		# $exponence =~ s/<([^>]*)>/ "<r$1>" /g; # brocketed material is reference
		# $exponence =~ s/-/'/g; # hyphens become tick
		push @answer, $exponence;
	} # each $exponence
	return @answer;
} # rhs

sub ascify {
	my ($string) = @_;
	# $string =~ tr/éèîāīūśṣṭḍñṛḷḥăşţâêïʌʊæɹɪɛɔə/eeiaiusstdnrlhastaeiuuarieoe/;
	# $string =~ s/ŋ/ng/g;
	# $string =~ s/θ/th/g;
	# $string =~ s/ʧ/ch/g;
	# $string =~ s/ʃ/sh/g;
	# $string =~ s/\p{M}/_/g; # remove markers
	# $string =~ s/([^[:ascii:]])/'u' . sprintf("%04x", ord($1))/eg;
	# $string =~ s/[^a-zA-Z0-9]/_/g; # replace non-alpha
	$string =~ s/([^a-zA-Z0-9])/'u' . sprintf("%04x", ord($1))/eg;
	return($string);
} # ascify

my $conjSequence; 
my %knownKatrNode; 
my %seenKatrNodes;
sub katrNode { # convert a conjugation name into a valid KATR node name
	my ($conjName) = @_;
	return $knownKatrNode{$conjName} if defined($knownKatrNode{$conjName});
	my $answer = $conjName;
	$answer = ascify($answer);
	if ($answer !~ /\w/) {
		print STDERR "I can't convert $conjName to a node name\n";
		$conjSequence += 1;
		$knownKatrNode{$conjName} = "IC$conjSequence";
		return "IC$conjSequence";
	}
	while (defined($seenKatrNodes{"IC$answer"})) {
		$answer .= "x";
	}
	$knownKatrNode{$conjName} = "IC$answer";
	$seenKatrNodes{"IC$answer"} = 1;
	return "IC$answer";
} # katrNode

sub surface { # convert a list of MPS names to surface forms
	my @names = @_;
	my @answer = ();
	for my $name (@names) {
		$name = lcfirst($name);
		push @answer, $name;
	} # each $name
	return @answer;
} # surface

my $ruleSequence = 0;
my %seenRuleTemplates;
sub template2rule { # convert an MPS template to a KATR rule name
	my ($theTemplate) = @_;
	if (!defined($seenRuleTemplates{$theTemplate})) {
		$ruleSequence += 1;
		$seenRuleTemplates{$theTemplate} = sprintf("T%02d", $ruleSequence);
	}
	# print STDERR "template $theTemplate = $seenRuleTemplates{$theTemplate}\n";
	return $seenRuleTemplates{$theTemplate};
	# $theTemplate =~ s/^/R/;
	# $theTemplate =~ s/[-=\/ "<>]//g;
	# $theTemplate =~ s/\W/x/g;
	# return $theTemplate;
} # template2rule

sub sameMap { # boolean: are two maps the same?  Assume same length, keys
	my ($mapPtr1, $mapPtr2) = @_;
	for my $key (keys(%$mapPtr1)) {
		my $value1 = ${$mapPtr1}{$key};
		$value1 =~ s/\d+_//;
		my $value2 = ${$mapPtr2}{$key};
		$value2 =~ s/\d+_//;
		return 0 if ($value1 ne $value2);
	}
	return 1;
} # sameMap

sub identicalMPS { # for each MPS, compute its exponence signature
	# report identical ones.
	my %seen;
	my $diffMPScount = 0;
	my @toPrint = ();
	for my $MPSIndex (0 .. $MPSCount-1) {
		my @MPSexponences;
		my $MPSName = $MPSNames[$MPSIndex];
		# print "working on $MPSName\n";
		for my $conjName (@conjugations) {
			my $cell = ${$conjugations{$conjName}}[$MPSIndex];
			push @MPSexponences, $cell;
		} # each $conjName
		my $signature = join(' ', @MPSexponences);
		if (defined($seen{$signature})) {
			my $selfForced = ((1 << $MPSIndex) & $forcedMPS);
			my $otherMPS = $seen{$signature};
			my $otherForced = ((1 << $otherMPS) & $forcedMPS);
			if ($selfForced and !$otherForced) {
				# we need to point them the reversed way so they are
				# not both included in the essence.
				$identical[$otherMPS] = $MPSIndex;
				$identicalCount += 1;
				push @toPrint, ($MPSIndex+1) . "<=" . ($seen{$signature}+1);
			} else {
				$identical[$MPSIndex] = $seen{$signature};
				$identicalCount += 1;
				push @toPrint, ($MPSIndex+1) . "=>" . ($seen{$signature}+1);
			}
		} else {
			$seen{$signature} = $MPSIndex;
			$diffMPScount += 1;
		}
	} # each MPSIndex
	if (@toPrint && $verbose) {
		print "\nIdentical MPSs\n\t" . join(', ', @toPrint) . "\n";
	}
} # identicalMPS

sub expandCell {
	# given MPSIndex, $conjName, expand the exponence by applying the template
	# (if any) and expanding the nC parts, leaving the nS parts.
	my ($MPSIndex, $conjName) = @_;
	my $cell = ${$conjugations{$conjName}}[$MPSIndex];
	my $expandedExponent = $templates[$MPSIndex];
	# print "\texpanded exponent $expandedExponent\n";
	while ($expandedExponent =~ /(\d+)A/) {
		my $abbrevIndex = $1;
		if (defined($templateAbbrs[$abbrevIndex])) {
			$expandedExponent =~
				s/${abbrevIndex}A/$templateAbbrs[$abbrevIndex]/g;
			# print "\texpanded exponent -> $expandedExponent\n";
		} else {
			print STDERR "${abbrevIndex}A is not a defined template\n";
			last;
		}
	} # while there is a template to expand
	if ($cell =~ s/‑/-/g) {
		print STDERR "Use - instead of \\u2011 in the paradigm\n";
	}
	# print "\tcell $cell\n";
	my @exponenceParts = ('dummy', split(/-/, $cell, -1));
		# -1 so we get trailing empty part
	if (@exponenceParts == 1) { # input error
		push @exponenceParts, '∅';
		print STDERR "Use ∅ instead of - as an exponence\n";
	}
	# print STDERR "cell [$cell] parts: @exponenceParts\n";
	$expandedExponent = '' unless defined ($expandedExponent);
	$expandedExponent =~ s/(\d+)C/defined($exponenceParts[$1]) ? $exponenceParts[$1] : '' /eg;
	$expandedExponent =~ s/∅//g;
	return $expandedExponent;
} # expandCell

sub computeEssence {
	my @mapList; # temporary: list of unique maps
	my @toPrint;
	if (0.0+$forcedMPS > exp($bitsPerInt*$log2)) {
		print "\nThe pattern for forced MPS exceeds $bitsPerInt bits, " .
			"so no MPS will be forced.\n";
		$forcedMPS = 0;
	}
	MPS:
	for my $MPSIndex (0 .. $MPSCount-1) {
		my $forcing =  ($MPSIndex < $bitsPerInt) &&
			((1 << $MPSIndex) & $forcedMPS);
		if ($forcing) {
			# printf "forced: $forcedMPS (" .
			# 	((1 << $MPSIndex) & $forcedMPS) . ") ";
			printf "Forcing %s (%d) to be a distillation\n",
				$MPSNames[$MPSIndex], $MPSIndex+1;
		}
		next if !$forcing && defined($identical[$MPSIndex]); # skip duplicate
		# filter MPS based on MPSfilter.
		for my $string (split /\s+/, $MPSfilter) {
			if ($MPSNames[$MPSIndex] !~ /$string/i) {
				$MPSfilteredCount += 1;
				next MPS;
			}
		} # each MPS filter string
	# populate %map: conj -> essence
		my %map; # $map{$conjName} = essence
		my %seen = ();
		my $seq = 0;
		for my $conjName (@conjugations) {
			my $cell = ${$conjugations{$conjName}}[$MPSIndex];
			if (!defined($seen{$cell})) {
				if ($cell eq '!∅') { # special essence for defect
					$seen{$cell} = "e" . ($MPSIndex+1) . "_0";
				} else {
					$seq += 1;
					$seen{$cell} = "e" . ($MPSIndex+1) . "_$seq";
				}
			};
			$map{$conjName} = $seen{$cell};
			$cellPerEssence{$seen{$cell}} = expandCell($MPSIndex, $conjName);
		} # each conjName
	# determine if this %map is unique
		my $unique = 1; # true unless shown false
		my $otherMapPtr;
		for $otherMapPtr (@mapList) {
			if (sameMap(\%map, $otherMapPtr)) {
				${$otherMapPtr}{$conjugations[0]} =~ /e(\d+)_/;
				my $otherMPS = $1 - 1;
				my $otherForced = ($otherMPS < $bitsPerInt) &&
					((1 << $otherMPS) & $forcedMPS);
				if ($forcing && !$otherForced) {
					print "\t$MPSIndex forced, equiv to $otherMPS, not forced\n";
					$essentiallyIdentical[$otherMPS] = $MPSIndex;
				} else {
					$essentiallyIdentical[$MPSIndex] = $otherMPS;
					$unique = 0;
				}
				$essencePerMPS{$MPSIndex} = $otherMapPtr;
				# print "$MPSIndex ($MPSNames[$MPSIndex]) " .
				# 	"is essentially identical to $MPSNames[$otherMPS]\n";
				last;
			} # if sameMap
		} # each otherMapPtr
		if ($forcing || $unique) {
			# print STDERR "$MPSNames[$MPSIndex] $MPSIndex is unique\n";
			$essencePerMPS{$MPSIndex} = \%map;
			push @mapList, \%map;
			for my $conjName (@conjugations) {
				$essencePerConj{$conjName} = []
					unless defined $essencePerConj{$conjName};
				push @{$essencePerConj{$conjName}}, $map{$conjName};
			} # each conjName
		} else {
			${$essencePerMPS{$MPSIndex}}{$conjugations[0]} =~ /e(\d+)_/;
			push @toPrint, ($MPSIndex+1) . "->$1";
		}
	} # each $MPSIndex	
	$distillationCount = scalar @{$essencePerConj{$conjugations[0]}};
# print essence
	if ($verbose && scalar(@toPrint)) {
		print "Essentially identical MPSs: " . 
			join(', ', @toPrint) . "\n";
	}
	if ($verbose) {
		print "\nEssence\n";
		for my $conjName (@conjugations) { # slight cleanup
			my $discrepancy = visualLength($conjName) - length($conjName);
			printf "\t%s%${maxConjLength}s ", " " x ($maxConjLength - $discrepancy), $conjName;         
			for my $essenceName (@{$essencePerConj{$conjName}}) {
				printf("%-7.7s", $essenceName);
			}
			print "\n";
		} # each conjName
		my $total = (scalar @conjugations) * $distillationCount;
		print "\tTotal cost: $total\n";
	} # verbose
} # computeEssence

sub showDistillations {
	print "\nDistillation details ('*' marks isomorphic; = marks identical)\n";
	my %inDistillation; # indexed by name of MPS that exemplifies
	for my $MPSIndex (0 .. $MPSCount-1) {
		my $dest = $identical[$MPSIndex];
		my $edest = $essentiallyIdentical[$MPSIndex];
		if (defined($dest)) {
			my $edest = $essentiallyIdentical[$dest];
			if (defined($edest)) {
				$dest = $edest;
			}
			if (!defined($inDistillation{$MPSNames[$dest]})) {
				print STDERR "strange: $MPSNames[$MPSIndex] identical " .
					"to unlisted $MPSNames[$dest]\n";
			}
			$inDistillation{$MPSNames[$dest]} .=
				"\t\t= $MPSNames[$MPSIndex]\n";
		} elsif (defined($edest)) {
			$inDistillation{$MPSNames[$edest]} .=
				"\t\t* $MPSNames[$MPSIndex]\n";
		} else {
			$inDistillation{$MPSNames[$MPSIndex]} =
				"\t$MPSNames[$MPSIndex]\n";
		}
	} # each MPSIndex
	for my $dist (sort keys %inDistillation) {
		print "$inDistillation{$dist}";
	}
} # showDistillations

sub computeNoEssence {
	my @mapList; # temporary: list of unique maps
	my @toPrint;
	for my $MPSIndex (0 .. $MPSCount-1) {
	# populate %map: conj -> essence
		my %map; # $map{$conjName} = essence
		my %seen = ();
		my $seq = 0;
		for my $conjName (@conjugations) {
			my $cell = ${$conjugations{$conjName}}[$MPSIndex];
			if (!defined($seen{$cell})) {
				if ($cell eq '!∅') { # special essence for defect
					$seen{$cell} = "e" . ($MPSIndex+1) . "_0";
				} else {
					$seq += 1;
					$seen{$cell} = "e" . ($MPSIndex+1) . "_$seq";
				}
			};
			$map{$conjName} = $seen{$cell};
			my $expandedExponent = $templates[$MPSIndex];
			while ($expandedExponent =~ /(\d+)A/) {
				my $abbrevIndex = $1;
				if (defined($templateAbbrs[$abbrevIndex])) {
					$expandedExponent =~
						s/${abbrevIndex}A/$templateAbbrs[$abbrevIndex]/g;
				} else {
					print STDERR "${abbrevIndex}A is not a defined template\n";
					last;
				}
			} # while there is a template to expand
			if ($cell =~ s/‑/-/g) {
				print STDERR "Use - instead of \\u2011 in the paradigm\n";
			}
			my @exponenceParts = ('dummy', split(/-/, $cell));
			if (@exponenceParts == 1) { # input error
				push @exponenceParts, '∅';
				print STDERR "Use ∅ instead of - as an exponence\n";
			}
			$expandedExponent =~ s/(\d+)C/$exponenceParts[$1]/eg;
			$expandedExponent =~ s/∅//g;
			$cellPerEssence{$seen{$cell}} = $expandedExponent;
		} # each conjName
		# print STDERR "MPS $MPSIndex is unique\n";
		$essencePerMPS{$MPSIndex} = \%map;
		push @mapList, \%map;
		for my $conjName (@conjugations) {
			$essencePerConj{$conjName} = []
				unless defined $essencePerConj{$conjName};
			push @{$essencePerConj{$conjName}}, $map{$conjName};
		} # each conjName
	} # each $MPSIndex	
	$distillationCount = scalar @{$essencePerConj{$conjugations[0]}};
# print essence
	print "\nEssence\n";
	for my $conjName (@conjugations) { # slight cleanup
		printf "\t%${maxConjLength}s %s\n", $conjName,         
			join(' ', @{$essencePerConj{$conjName}});
	} # each conjName
	my $total = (scalar @conjugations) * $distillationCount;
	print "\tTotal cost: $total\n";
} # computeNoEssence

sub identicalSignatures {
	print "\nPlat of referrals\n";
	my %seenSignatures;
	my %classes;
	my $fieldWidth = 4; # minimum
	for my $conjName (@conjugations) {
		$fieldWidth = max($fieldWidth, length($conjName));
	}
	$fieldWidth += 2;
	for my $conjName (@conjugations) {
		my %seenExponences;
		my $sequence = 0;
		my $signatureString = "";
		printf " %-${fieldWidth}s ", $conjName;
		for my $essence (@{$conjugations{$conjName}}) {
			# print STDERR "[$essence]";
			$sequence += 1;
			if (!defined($seenExponences{$essence})) {
				$seenExponences{$essence} = $sequence;
			}
			$signatureString .= " $seenExponences{$essence}";
			$seenExponences{$essence} = $sequence; # so we always report most recent
		}
		print "$signatureString\n";
		my $class = $seenSignatures{$signatureString};
		if (defined($class)) {
			# print "\t$conjName = $class\n";
			push @{$classes{$class}}, $conjName; 
		} else {
			$seenSignatures{$signatureString} = $conjName;
			$classes{$conjName} = [$conjName];
		}
	} # each $conjName
	print "\nSignature equivalence classes\n";
	for my $class (sort keys %classes) {
		next unless scalar @{$classes{$class}} > 1;
		print "\tclass $class: " .  join(', ', @{$classes{$class}}) . "\n";
	}
	print "The " . (scalar @conjugations) . " distinct inflection classes have " .
		(scalar keys %seenSignatures) . " distinct signatures.\n";
} # identicalSignatures

sub introduceHelper {
	my ($rhs) = @_;
	while ($rhs =~ /(\d+)H/) {
		my $helperIndex = $1;
		my $replacement = $helpers[$helperIndex];
		print STDERR "No helper $helperIndex\n"
			unless defined($replacement);
		$replacement =~ /(\w+)\s+(\w+)/;
		my ($helpLemma, $MPSNumber) = ($1, $MPSNameToIndex{$2}+1);
		$rhs =~ s/${helperIndex}H/' "' . ucfirst(ascify($helpLemma)) .
			":<h$helperIndex>\""/e;
	}
	return($rhs);
} # introduceHelper

sub makeKATR { # each MPS has its own KATR rule
	my ($method, $data) = @_; # method is 'static', 'adaptive', or 'no'
	my ($pattern, $tree) = ($data, $data);
		# call it $pattern for static, $tree for dynamic
	# print STDERR "--------------------\n"; # debug
	# print STDERR "pattern is $pattern\n";
	my $language = $ARGV[0];
	$language =~ s/\.data//;
	my $katrFile = "$language.katr";
	open KATR, ">:utf8", $katrFile or die("Can't write to $katrFile");
	print KATR
		"% KATR theory for $language based on $method principal parts\n" .
		"% generated by $0 from $language.data\n";
	if ($method eq 'static') {
		print KATR "% using principal parts " . patternToNumber($pattern) .
			"\n";
	}
# conjugation fragments
	my (@frags, @atoms, $conjName, $exponence, $fragment, %seen);
	for $conjName (@conjugations) {
		for $exponence (@{$conjugations{$conjName}}) { # one cell
			if ($exponence eq '-') {
				next if $exponence =~ /=?\d+S/;
				push @frags, $exponence unless defined($seen{$exponence});
				$seen{$exponence} = 1;
			} else { # not just '-'
				for $fragment (split(/-/, $exponence)) { # one fragment
					next if $fragment =~ /=?\d+S/;
					$fragment =~ s/^!//; # remove quote
					if (!defined($seen{$fragment})) {
						push @frags, $fragment;
						push @atoms, $fragment if $fragment =~ /^[A-Z]/;
					}
					$seen{$fragment} = 1;
				} # each fragment
			} # not just '-'
		} # each cell
	} # one conjugation
	print KATR "\n% inflection class fragments from the paradigm\n" .
		(scalar(@atoms) ? "#atom " . join(' ', @atoms) . " .\n" : "") .
		"#vars \$cfrag: ∅ " . join(' ', @frags) . " .\n\n";
# @expandedTemplates[$bit], used in the per-MPS nodes
	my @expandedTemplates;
	for my $bit (0 .. $MPSCount-1) { # expand A and L in templates, but not C
		my $expandedExponent = $templates[$bit];
		# print STDERR "first expanded exponent is $expandedExponent\n";
		if ($expandedExponent =~ s/=?(\d+)A/$templateAbbrs[$1] /eg) {
			if (defined($1) && !defined $templateAbbrs[$1]) {
				print "no expansion for $1\n";
			}
		}
		# print STDERR "second expanded exponent is $expandedExponent\n";
		$expandedExponent =~ s/=?(\d+)S/ "<r$1>" /g;
		# print STDERR "third expanded exponent is $expandedExponent\n";
		push @expandedTemplates, $expandedExponent;
	} # each MPS index
# $handles{$conjugation} = "exp exp ... "
	#   a unique pattern for each conjugation; specific to method
	my %handles;
	for my $conjugation (@conjugations) {
		my @handle = ();
		if ($method eq 'static') {
			for my $bit (0 .. $distillationCount-1) { # each distillation index
				next unless (1 << $bit) & $pattern; 
				my $exponent = ${$essencePerConj{$conjugation}}[$bit];
				# print STDERR "exponent $exponent\n"; # debug
				# clean up $exponent to make it acceptable to KATR
				$exponent =~ s/ (?=\PM)/_/g;
				$exponent = lcfirst $exponent;
				push @handle, $exponent;
			} # each distillation index
		} elsif ($method eq 'adaptive') {
			# compute the principalExponents for this conjugation
			my $treePtr = $tree;
			while ($#{$treePtr}) { # dive down the tree
				my $distillationIndex = ${$treePtr}[0];
				my $exponent =
					lhs(${$essencePerConj{$conjugation}}[$distillationIndex]);
				push @handle, $exponent;
				for my $branch (1 .. $#{$treePtr}) {
					if (${${$treePtr}[$branch]}[0] eq $exponent) {
						# print "\ttaking branch $branch\n";
						$treePtr = ${${$treePtr}[$branch]}[1];
						last;
					}
				}
			} # dive down the tree
		} elsif ($method eq 'no') {
			push @handle, lcfirst $conjugation;
		}
		# print "principalExponents for $conjugation: " .
		# 	join(" ", @{$principalExponents{$conjugation}}) . "\n";
		$handles{$conjugation} = join(" ", lhs(@handle));
	} # each $conjugation (real)
	for my $conjugation (keys %sameConj) {
		$handles{$conjugation} = $handles{$sameConj{$conjugation}};
	}
	for my $conjugation (keys %similarConj) {
		$handles{$conjugation} = $handles{$similarConj{$conjugation}};
	}
# Forms rule
	print KATR "Lexeme:\n" .
		"\t<> ==  " . join(" | ", surface(@MPSNames)) . "\n" .
		"\t.\n\n";
# lexeme rules
	my %usable;
	for my $conjName (@conjugations) {
		$usable{$conjName} = 1;
		# print STDERR "$conjName is usable\n";
	}
	for my $meaning (@meanings) {
		my $root = $roots{$meaning};
		# print STDERR "meaning $meaning IC $conjs{$meaning} " .
		#  	"roots $root\n";
		# next unless defined($usable{$conjs{$meaning}});
		# print STDERR "using it\n";
		print KATR "" . ucfirst(ascify($meaning)) . ":\n";
		my @knownStems;
		for my $rootFragment (split /\s+/, $root) {
			next unless $rootFragment =~ /\w/;
			if ($rootFragment !~ /(\d+):(\S+)/) {
				print STDERR "$meaning has a bad stem $rootFragment\n";
				next;
			}
			my ($fragNumber, $stem) = ($1, $2);
			# print STDERR "stem $fragNumber of $meaning is $stem\n";
			print KATR "\t<r$fragNumber> == $stem\n";
			$knownStems[$fragNumber] = $stem;
		}
		my @defaultStems = ();
		if (defined($refersByConj{$conjs{$meaning}})) {
			@defaultStems = @{$refersByConj{$conjs{$meaning}}};
			# print STDERR "setting default stems to " .
			# 	join(', ', @defaultStems) . "\n";
		}
		if ($#defaultStems -1 > $#stems) {
			print STDERR "There are at least " . (@defaultStems-2) .
				" stems, but only " . max(0,@stems-1) .
				" are defined in STEM declarations.\n";
			# print STDERR join (' ', @{$refersByConj{$conjs{$meaning}}}) . "\n";
			while ($#defaultStems -1 > $#stems) {
				push @stems, "undefined";
			}
		}	
		while ($#defaultStems < $#stems) {
			push @defaultStems, 0;
		}
		for my $index (1 .. $#stems) { # one stem
			my $refer = $defaultStems[$index];
			$refer = 0 unless defined($refer) && $refer ne '';
			if ($refer == 0 && !defined($knownStems[$index])) {
				print STDERR "$meaning fails to provide stem $index\n";
				next;
			}
			if ($refer > 0 && defined($knownStems[$index])) {
				print STDERR "$meaning provides stem $index, but " .
					"its conjugation $conjs{$meaning} refers stem $index to " .
					"$refer\n";
				next;
			}
			# print KATR "\t<r$index> == $knownStems[$refer]" .
			# 	" % referred to stem $refer\n";
		} # each stem
		my $conjName = $conjs{$meaning};
		$conjName =  $sameConj{$conjName} if defined($sameConj{$conjName});
		if (defined($helpLemmas{$meaning})) { # used as a helping verb
			for my $helperName (split / /, $helpLemmas{$meaning}) {
				next if $helperName eq "";
				$helperName =~ /(\w+):(\w+)/;
				my ($helperIndex, $helperMPS) = ($1, $2);
				my $MPSIndex = $MPSNameToIndex{$helperMPS};
				if (!defined($MPSIndex)) {
					print STDERR "$helperName is not defined\n";
					next;
				}
				my $fragment = ${$conjugations{$conjName}}[$MPSIndex];
				# let's hope the fragment needs no cleaning up
				print KATR "\t<h$helperIndex> == " .
					template2rule($expandedTemplates[$MPSIndex]) .
					":<$fragment>\n";
			} # each helperName
		} # used as a helping verb
		print KATR "\t<> == " . katrNode($conjName) . "\n\t.\n\n";
	} # each $conjugation
# conjugation rules
	for my $conjName (@conjugations, keys(%similarConj)) {
		next if defined($sameConj{$conjName});
		print KATR "#hide " . katrNode($conjName) . " .\n"
			. katrNode($conjName) . ":\n";
		my @defaultStems = ();
		if (defined($refersByConj{$conjName})) {
			@defaultStems = @{$refersByConj{$conjName}};
		}
		for my $index (1 .. $#defaultStems) { # one default stem
			my $refer = $defaultStems[$index];
			# print STDERR "point 1, index $index, refer $refer\n";
			next unless $refer ne "" and $refer > 0; # 0 is an empty referral;
			print KATR "\t<r$index> == \"<r$refer>\"\n";
		} # each default stem
		if (defined($similarConj{$conjName})) {
			$conjName = $similarConj{$conjName};
			print KATR "\t<> = " . katrNode($conjName) .
				" % like $conjName except for stem referral\n\t.\n\n";
			next;
		}
		if (defined($partialEssence{$conjName})) {
			foreach my $essence (split /\s+/, $partialEssence{$conjName}) {
				my $base = $essence;
				$base =~ s/_\d*//;
				print KATR "\t{$base} = $essence\n";
			} # each essence
		} else {
			foreach my $essence (@{$essencePerConj{$conjName}}) {
				my $base = $essence;
				$base =~ s/_\d*//;
				print KATR "\t{$base} = $essence\n";
			} # each essence
		}
		print KATR "\t<> == ";
		if (defined($parent{$conjName})) {
			print KATR "$parent{$conjName}";
		} else { # not grouping or root of grouping tree
			# BUG: need parent of effective conjName: joinedName with same handle
			print KATR "EXPAND";
		}
		print KATR " % principal parts $handles{$conjName}\n\t.\n\n";
	} # each conjName
# Join rules
	for my $conjName (@joinedNames) {
		print KATR "\n$conjName:\n\t<> == "; 
		if (defined($parent{$conjName})) {
			print KATR "$parent{$conjName}\n";
		} else { # not grouping
			print KATR "EXPAND\n";
		}
		foreach my $essence (split /\s+/, $partialEssence{$conjName}) {
			my $base = $essence;
			$base =~ s/_\d*//;
			print KATR "\t{$base} = $essence\n";
		} # each essence
		print KATR "\t.\n";
	}
# EXPAND rule
	print KATR "\nEXPAND:\n\t<> == ";
	my @toPrint = ();
	for my $MPSIndex (0 .. $MPSCount-1) {
		my $effectiveIndex = $MPSIndex;
		$effectiveIndex = $identical[$effectiveIndex]
			if defined($identical[$MPSIndex]);
		my %map = %{$essencePerMPS{$effectiveIndex}};
		my $essence = $map{$conjugations[0]};
		$essence =~ s/_\d*//;
		push @toPrint, "MPS" . ($MPSIndex+1) . ":< \"<$essence>\" >";
	} # each column
	print KATR join(' | ', @toPrint) . "\n\t.\n";
# MPS rules (MPS1, MPS2, ...)
	for my $MPSIndex (0 .. $MPSCount-1) {
		print KATR "\nMPS" . ($MPSIndex+1) . ": % $MPSNames[$MPSIndex]\n";
		my $effectiveIndex = $MPSIndex;
		$effectiveIndex = $identical[$MPSIndex]
			if defined($identical[$MPSIndex]);
		my %seen = ();
		my %map = %{$essencePerMPS{$effectiveIndex}};
		for my $conjName (@conjugations) {
			my $essence = $map{$conjName};
			next if defined($seen{$essence});
			$seen{$essence} = 1;
			my $rhs = ${$conjugations{$conjName}}[$MPSIndex];
			$rhs = '∅' . $rhs if $rhs =~ /^-/;
			$rhs .= '∅' if $rhs =~ /-$/;
			$rhs = join(' ', split(/-/, $rhs)) unless ($rhs eq '-');
			print KATR "\t{$essence} == ";
			my $et = $expandedTemplates[$MPSIndex];
			if ($rhs =~ s/.*\@//) { # override stem, but not template
				my $rule = $et;
				# print STDERR "rhs [$rhs] rule [$rule] ";
				$rule =~ s/=?\d[CS].*\d[CS]/$rhs/;
				# print STDERR " rule becomes [$rule]\n";
				print KATR "$rule\n";
			} elsif ($rhs =~ s/.*\!//) { # override template
				$rhs =~ s/=?(\d+)S/ "<r$1>" /g;
				# print STDERR "ordinary ! becomes [$rhs]\n";
				print KATR "$rhs\n";
			} elsif ($expand) { # don't use expanded templates
				$rhs =~ s/=?(\d+)S/ "<r$1>" /g;
				print KATR "$rhs\n";
			} elsif ($rhs =~ s/=?(\d+)S/ "<r$1>" /g) {
				my $rule = $et;
				$rule =~ s/=?1C/$rhs/;
				print KATR "$rule\n";
			} else {
				print KATR "" . (template2rule($et)) . ":<$rhs>\n";
			}
		} # each conjName
		print KATR "\t.\n";
	} # each $MPSIndex
# Template rules (T01, T02, ...)
	for my $theTemplate (sort {
			$seenRuleTemplates{$a} cmp $seenRuleTemplates{$b}
		} keys %seenRuleTemplates) {
		my $ruleName = $seenRuleTemplates{$theTemplate};
		my $highestFragment = -1;
		while ($theTemplate =~ s/=?(\d)C/$1D/) {
			$highestFragment = $1 if $highestFragment < $1;
		}
		my $lhs = "";
		for my $index (1 .. $highestFragment) {
			$lhs .= " \$cfrag#$index";
		}
		$lhs =~ s/^ //;
		$theTemplate =~ s/=?(\d)D/ \$cfrag#$1 /g;
		$theTemplate =~ s/-/ , /g;
		$theTemplate = introduceHelper($theTemplate);
		# print STDERR "theTemplate is $theTemplate\n";
		print KATR "\n$ruleName:\n\t<$lhs> ==$theTemplate\n\t.\n";
	} # each MPS template
# final hide rule
	print KATR "#hide PARADIGM EXPAND";
	for my $theTemplate (sort {
			$seenRuleTemplates{$a} cmp $seenRuleTemplates{$b}
		} keys %seenRuleTemplates) {
		print KATR " $seenRuleTemplates{$theTemplate}";
	}
	for my $MPSIndex (0 .. $MPSCount-1) {
		print KATR " MPS" . ($MPSIndex+1);
	}
	print KATR " .\n";
# final parts of KATR file
	print KATR "\n" .
		"% #show <forms> .\n" .
		"% #show <all> .\n\n" .
		"#show <> .\n\n" .
		"% vim:filetype=KATR tw=10000 nospell:\n";
	close KATR;
} # makeKATR

sub makeSandhi {
	my $language = $ARGV[0];
	$language =~ s/\.data//;
	my $sandhiFile = "$language.sand.pl";
	open SANDHI, ">:utf8", $sandhiFile or die("Can't write $sandhiFile");
	print SANDHI '#!/usr/bin/perl -w
use strict;
use utf8;
binmode STDIN, ":utf8";
binmode STDOUT, ":utf8";
use utf8;
while (my $line = <STDIN>) {
	if ($line =~ /^Lexeme/) {
		print $line;
		next;
	}
	my ($head, $tail);
	if ($line =~ /(.*=)(.*)/) {
		($head, $tail) = ($1, $2);
	} else {
		($head, $tail) = ("", $line);
	}
	$tail =~ s/^/\|/;
	$tail =~ s/$/\|/;
	$tail =~ s/∅//g;

	# language-specific Sandhi rules
'; # initial boilerplate
	for my $rule (@sandhi) {
		$rule =~ /\s*(.*)\s*=>\s*(.*)/;
		my ($lhs, $rhs) = ($1, $2);
		if (!defined($rhs)) {
			print STDERR "Unintelligible Sandhi rule: $rule\n";
			next;
		}
		$lhs =~ s/\s*$//; # remove trailing blanks
		$rhs =~ s/\s*$//;
		$lhs =~ s/\|/\\s*\\|/g; # escape the bar
		$lhs =~ s/\^/\\^/; # escape the caret
		$rhs .= '|' if ($lhs =~ /\|$/ and $rhs !~ /\|$/);
		$lhs =~ s/\s+/\\s\*/g; # spaces in rule are optional crossers
		$lhs =~ s/\\s\*\\s\*/\\s*/g; # remove extraneous space-crossers
		$lhs =~ s/\[:(\w+):\]/$classes{$1}/eg;
		print SANDHI '	$tail =~ s/' . $lhs . '/' . $rhs . "/g;\n";
	} # each sandhi rule
	print SANDHI '	# end of language-specific rules

	$tail =~ s/^\|//;
	$tail =~ s/\|$//;
	print "$head$tail\n";
}
'; # final boilerplate
	close SANDHI;
	chmod 0755, $sandhiFile;
} # makeSandhi;

sub usage {
	print "Usage: $0 [-hvgsakdpPitE] [-mn] fileName\n" .
		"\t-h: show this help\n" .
		"\t-v: verbose\n" .
		"\t-e: expand paradigm based on stem referrals\n" .
		"\t-E: do not compute essence; retain original MPPs\n" .
		"\t-r: replace paradigm with the stem referrals\n" .
		"\t-g: group inflection classes\n" .
		"\t-s: compute static principal parts\n" .
		"\t-q: compute quick static principal parts\n" .
		"\t-a: compute adaptive principal parts\n" .
		"\t-d: compute dynamic principal parts\n" .
		"\t-o: compute MPS entropies\n" .
		"\t-w: compute inflection-class entropies\n" .
		"\t-W: compute m-fold inflection-class entropies\n" .
		"\t-O k: weight entropies based on key k\n" .
		"\t-k: output KATR source\n" .
		"\t-p: compute inflection-class predictabilities\n" .
		"\t-P: compute full predictabilities\n" .
		"\t-y: do not include the empty set as a predictor\n" .
		"\t-i: compute predictiveness\n" .
		"\t-t: output statistics\n",
		"\t-f: output refer list in canonical notation\n",
		"\t-c: output inflection-class refer table\n",
		"\t-n: find center of the paradigm\n",
		"\t-mn: set m (number of distillations in patterns)\n",
		"\t-Fn: force bits n to participate in all analyses\n",
		"\t-x: output paradigm of stem referrals\n",
		"\t-j: stratify inflection classes on required number of principal parts\n",
		"\t-b: compare inflection classes for identical signature\n",
		"\t-z: compare MPSs for identical exponences\n",
		"\t-Mn: require essence to have distillations in bit pattern n\n", 
		"\t-R keys: restrict analysis to fragment containing given keys\n",
		"\t-S keys: restrict output to fragment containing given keys\n",
		"\t-A strings: restrict analysis to MPSs whose name has given strings\n",
		"\t-u: output a new data file restricted according to -R and -A\n",
		"";
	exit(1);
} # usage

sub printSynopsis {
	print "\nSynopsis\n" .
		($requiredKeys ? "\tOnly inflection classes marked as " .
			"\"$requiredKeys\"\n" : "") .
		($MPSfilter ? "\tOnly MPSs that match \"$MPSfilter\"\n" : "") .
		"\t$conjCount inflection classes\n" .
		(scalar keys %sameConj
			? "\t\tplus " . (scalar keys %sameConj) . " identical ones\n"
			: "" ) .
		(scalar keys %similarConj
			? "\t\tplus " . (scalar keys %similarConj) .
				" identical ones except for stem referral\n"
			: "" ) .
		"\t$abbrevsUsed distinct exponences\n" .
		"\t$MPSCount MPSs" .
		($MPSfilteredCount ? " (of which $MPSfilteredCount filtered out) " : "")
		. "\n";
	my @toPrint;
	foreach my $MPSIndex (0 .. $MPSCount -1) {
		next if defined($identical[$MPSIndex]);
		push @toPrint, $MPSNames[$MPSIndex];
	}
	print "\t" . ($MPSCount - $identicalCount) . " unique MPSs\n\t\t" .
		join(' ', @toPrint) . "\n";
	if ($distillationCount >= $bitsPerInt) {
		printf "\t%d distillations (pattern unprintable in %d bits)\n\t\t",
			$distillationCount, $bitsPerInt;
	} else {
		my ($code, $failure) = patternToMPSCode((1 << $distillationCount) - 1);
		printf "\t%d distillations (pattern %s)\n\t\t",
			$distillationCount, ($failure
				?  "cannot be represented in $bitsPerInt bits"
				: $code);
		foreach my $distillationIndex (0 .. $distillationCount -1) {
			printf "%s ", patternToMPS(1 << $distillationIndex, 1);
		}
	}
	print "\n\n";
} # printSynopsis

# given (0, 0, 1, 1, 0, 4) generate 2-3 -> 1; 5 -> 4
sub referArrayToString {
	my (@refers) = @_;
	my @referer = ();
	for my $index (1 .. $#refers) {
		my $referent = $refers[$index];
		next if $referent eq "" or $referent == 0;
		$referer[$referent] = [] unless defined $referer[$referent];
		push @{$referer[$referent]}, $index;
	} # each index of refers
	my @termStrings = (); # array of elements like "8, 11-14 -> 1"
	for my $referent (1 .. $#referer) {
		next unless defined $referer[$referent];
		my @subtermStrings = (); # array of eleements like 8 or 11-14
		my @term = @{$referer[$referent]};
		my $first;
		while (@term) {
			$first = shift @term;
			my $last = $first;
			my $next = shift @term;
			last unless defined $next;
			while ($next == $last + 1) {
				$last = $next;
				$next = shift @term;
				last unless defined $next;
			}
			unshift @term, $next if defined $next;
			my $subtermString = $first;
			$subtermString .= "-$last" if $last != $first;
			push @subtermStrings, $subtermString;
			undef $first;
		} # while @term
		push @subtermStrings, $first if defined $first;
		push @termStrings, "" . join(', ', @subtermStrings) .
			" -> $referent";
	} # each referent
	return(join('; ', @termStrings));
} # referArrayToString

sub printReferrals {
	print "\nReferrals\n\n";
	for my $conjName (@conjugations) {
		printf("REFER %-15s %s\n", $conjName,
			referArrayToString(@{$refersByConj{$conjName}}));
	} # each conjName
} # printReferrals

sub makeCRTable {
	my %CRTable;
	my %referCount;
	my %members;
	for my $conjName (@origConjugations) {
		next if defined($sameConj{$conjName});
		my $referString = referArrayToString(@{$refersByConj{$conjName}});
		my $canonicalConj = defined($similarConj{$conjName}) ?
			$similarConj{$conjName} : $conjName;
		# print STDERR "canonical for $conjName is $canonicalConj\n";
		$CRTable{"$canonicalConj $referString"} = 'X';
		$members{$referString} .= " $canonicalConj:$conjName";
		$referCount{$referString} += 1;
	} # each conjName
	printf "\n%d referral patterns, %d inflection classes\n",
		scalar keys %referCount, scalar @conjugations;
	printf "\n%-15s | %s\n", 'inflection class', 'referral pattern';
	for my $conjName (@conjugations) {
		printf "%-15s |", $conjName;
		my $count = 0;
		for my $referString (sort keys %referCount) {
			my $entry = $CRTable{"$conjName $referString"};
			delete $CRTable{"$conjName $referString"};
			$count += defined($entry) ? 1 : 0;
			printf "%1s", defined($entry) ? $entry : ""; 	
		} # each referString
		print "| $count\n";
	} # each conjName
	for my $category (keys %members) {
		# print "Group $category has these members:\n\t" . 
		# 	join("\n\t", split(' ', $members{$category})) . "\n";
	} # one member
	for my $entry (keys %CRTable) { # is this entry missing?
		print "table is missing $entry\n";
	} 
	printf "%-15s |%s|\n", "", '-' x (scalar keys %referCount);
	printf "%-15s |", "totals";
	for my $referString (sort keys %referCount) {
		printf "%1d", $referCount{$referString};
	} # each referString
	print "|\n";
} # makeCRTable

# build a meta-paradigm based on stems into FILE-stems.data
sub showStemParadigm {
	my ($fileName) = @_;
	$fileName .= '-stems.data';
	open STEMS, ">$fileName" or die("Cannot write $fileName");
	binmode STEMS, ":utf8";
	print STEMS "% meta-paradigm automatically generated from $ARGV[0]\n\n" .
		"IC         " . join(" ", (1 .. @stems-1)) . "\n" .
		"TEMPLATE " . ("1S1C " x (@stems-1)) . "\n";
	my @lexemes;
	for my $meaning (%conjs) {
	# compute minimal prefix $common
		next unless defined($roots{$meaning});
		# print "$meaning: " . $roots{$meaning} . "\n";
		my ($common, @theStems);
		for my $stemData (split /\s+/, $roots{$meaning}) {
			$stemData =~ /(\d+):(.*)/;
			my ($index, $stem) = ($1, $2);
			$theStems[$index] = $stem;
			next if $stem eq 'nope';
			if (defined($common)) {
				$common = commonPrefix($common, $stem);
			} else {
				$common = $stem;
			}
		} # each stemData
	# try to improved $common by adding one letter
		my @referrals = @{$refersByConj{$conjs{$meaning}}};
		pop @referrals; # one extra at the end
		# print STDERR "referrals " . join(':', @referrals) . "\n";
		my $toRemove;
		for my $index (1 .. scalar @referrals - 1) {
			my $referral = $referrals[$index];
			$referral = $index if $referral eq "" or $referral == 0; 
			my $excess = $theStems[$referral];
			$excess = $common if $theStems[$referral] eq 'nope';
			$excess =~ s/^$common//;
			$excess = '∅' if $excess eq '';
			if ($excess ne '∅') {
				$excess =~ /(\p{L}\p{M}*)/;
				my $startLetter = $1;
				if (defined($toRemove)) {
					if ($toRemove ne $startLetter) {
						$toRemove = 'none';
					}
				} else {
					$toRemove = $startLetter;
				}
			}
		} # each stem index
		if (defined($toRemove) && $toRemove ne 'none') {
			# print "Let's adjust using $toRemove\n";
			$common .= $toRemove;
		}
	# compute cells of meta-paradigm based on $common
		# printf "%15s\t%s ", $meaning, ($common eq '' ? '∅' : $common);
		# print "referrals: " . join(":", @referrals) . "\n";
		my @cells; # the cells of the meta-paradigm
		for my $index (1 .. scalar @referrals - 1) {
			my $referral = $referrals[$index];
			$referral = $index if $referral eq "" or $referral == 0; 
			my $excess = $theStems[$referral];
			$excess = $common if $theStems[$referral] eq 'nope';
			$excess =~ s/^$common// or $excess = "#";
			$excess = '∅' if $excess eq '';
			# print "\t$excess ";
			push @cells, $excess;
		} # each referral index
		# print "\n";
		push @lexemes, sprintf("LEXEME  %10s %20s 1:%s",
			$conjs{$meaning}, $meaning, ($common eq '' ? '∅' : $common));
		printf STEMS "$meaning  " . join("\t", @cells) . "\n";;
	} # each $meaning
	print STEMS "\n" . join("\n", @lexemes) . "\n";
	close STEMS;
} # showStemParadigm

sub applyTheme {
	# substitute the theme (like 's-ng') into the expansion (like '1Su2S')
	# to get a pre-sandhi surface form (like 'sung').  
	# Index.  Ignores the stem numbers; assumes 1S...2S...
	my ($theme, $expansion) = @_;
	my $stemNumber = 0;
	# print STDERR "applying $theme to $expansion ";
	for my $stem (split /-/, $theme) {
		$stemNumber += 1;
		$expansion =~ s/${stemNumber}S/$stem/;
	}
	$expansion =~ s/\dS//g; # all other stems are null
	# print STDERR "yields $expansion\n";
	return $expansion;
} # applyTheme

sub analyzeQueries {
	$MPSNameToIndex{'ANY'} = -1;
	query:
	for my $query (@toAnalyze) {
		print "Analyzing: " . join(' ', @$query) . "\n";
		my @OKConjugations = @conjugations;
		my $queryIndex = 0;
		my $triedMPS = 0;
		my %themes;
		while ($queryIndex < @{$query}) {
			# consider next part of query
			my @nextOK = ();
			my ($MPS, $surface) = split(/=/, ${$query}[$queryIndex]);
			$queryIndex += 1;
			my $MPSIndex = $MPSNameToIndex{$MPS};
			if (!defined($MPSIndex)) {
				print "I don't understand MPS $MPS\n";
				next query;
			}
			$triedMPS |= 1 << $MPSIndex unless $MPSIndex < 0;
			print "\tgiven MPS $MPS=$surface\n";
			for my $conjName (@OKConjugations) {
				# print "\t\tTrying IC $conjName\n";
				my $paradigm = $conjugations{$conjName};
				my ($exponence, $theme);
				if ($MPSIndex < 0) {
					for my $MI (0 .. $MPSCount-1) {
						my $expansion =	expandCell($MI, $conjName);
						$exponence = $expansion;
						$expansion =~ s/(\dS)/(.*)/g;
						# print "\t\texpansion $expansion\n";
						next unless ($surface =~ /^$expansion$/);
						my ($theme1, $theme2, $theme3) = ($1, $2, $3);
						$theme = $theme1;
						$theme .= "-$theme2" if defined $theme2;
						$theme .= "-$theme3" if defined $theme3;
						if (defined($themes{$conjName})) {
							last if $themes{$conjName} eq $theme;
						} else {
							last; # stop at the first match
						}
					} # each possible MPS
					next unless defined($theme);
				} else {
					my $expansion =	expandCell($MPSIndex, $conjName);
					$exponence = $expansion;
					$expansion =~ s/(\dS)/(.*)/g;
					if ($surface !~ /^$expansion$/) {
						print "\t\t not IC $conjName; it doesn't match this surface form\n"
							if $queryIndex > 1;
						next;
					}
					my ($theme1, $theme2, $theme3) = ($1, $2, $3);
					$theme = $theme1;
					$theme .= "-$theme2" if defined $theme2;
					$theme .= "-$theme3" if defined $theme3;
				}
				if (defined($themes{$conjName}) &&
						$themes{$conjName} ne $theme) {
					print "\t\t not IC $conjName; it would need a new stem $theme\n";
					next;
				}
				push @nextOK, $conjName;
				$themes{$conjName} = $theme;
				$exponence =~ s/1S/$theme/;
				printf "\t\tmaybe IC %s: stem %s, exponence %s",
					$conjName, $theme, $exponence;
				if ($totalWeight != scalar(keys %conjugations)) {
					printf " (type frequency %3.1f%%)\n",
						(100.0*$weights{$conjName})/$totalWeight;
				} else {
					print "\n";
				}
			} # each conjugation
			@OKConjugations = @nextOK;
			if (@OKConjugations == 0) {
				print "\tNo inflection class matches.\n";
				last;
			} 
			# give some advice on what to try next
			my @distincts; # $distincts[MPSIndex] = {exponence => 1}
			for my $conjName (@OKConjugations) {
				my $paradigm = $conjugations{$conjName};
				# print "tried: $triedMPS\n";
				for my $MPSIndex (0 .. $MPSCount-1) {
					next if (1 << $MPSIndex) & $triedMPS;
					$distincts[$MPSIndex] = {}
						unless defined($distincts[$MPSIndex]);
					my $expansion = applyTheme(
						$themes{$conjName}, expandCell($MPSIndex, $conjName));
					${$distincts[$MPSIndex]}{$expansion} = 1;
				} # each MPSIndex
			} # each remaining conjugation
			my @certainties = ();
			my %probs = ();
			for my $MPSIndex (0 .. $MPSCount-1) {
				next if (1 << ($MPSIndex)) & $triedMPS;
				my $numPossibilities = scalar keys %{$distincts[$MPSIndex]};
				next if $numPossibilities == 1; # bad advice
				my $prob = sprintf "%3.0f",
					($numPossibilities * 100.0) / @OKConjugations;
				$certainties[$prob] .= " $MPSNames[$MPSIndex]";
				$probs{$prob} = 1;
			} # each MPSIndex
			for my $prob (sort {$b <=> $a} keys %probs) {
				print "\t\tto determine with probability (cum granō salis) $prob\n";
				print "\t\t\t$certainties[$prob]\n";
			}
		} # next part of query
		if (@OKConjugations == 1) {
			print "\tCertainly in inflection class $OKConjugations[0].\n";
		}
	} # each query
} # analyzeQueries

	sub main {
	my $optString = 'hvgsakdpPtqeErfcxnim:F:bjM:R:A:oO:uwS:y';
	my %opt;
	getopts($optString, \%opt) or usage();
	usage() unless $#ARGV == 0; # one file
	usage() if defined($opt{'h'});
	$bitsPerInt = (1 << 33) == 2 ? 32 :
		(1 << 65) == 2 ? 64 :
		128;
	# print "bits per int: $bitsPerInt\n";
	@toAnalyze = ();
	my ($group, $static, $stats, $adaptive, $KATR, $dynamic,
		$predictable, $fullPredictable, $quickStatic, $referParadigm,
		$newReferral, $wantCRTable, $wantStemParadigm, $findCenter, $noEssence,
		$predictive, $signature, $stratify, $doMPSentropy, $entropyWeight,
		$outputFragment, $doConjEntropy,
		);
	$verbose = defined($opt{'v'});
	$group = defined($opt{'g'});
	$static = defined($opt{'s'});
	$quickStatic = defined($opt{'q'});
	$stats = defined($opt{'t'});
	$adaptive = defined($opt{'a'});
	$KATR = defined($opt{'k'});
	$dynamic = defined($opt{'d'});
	$predictable = defined($opt{'p'});
	$fullPredictable = defined($opt{'P'});
	if ($fullPredictable) {
		$predictable = 1;
	}
	$noEmptyPredictor = defined($opt{'y'});
	$predictive = defined($opt{'i'});
	$expand = defined($opt{'e'});
	$referParadigm = defined($opt{'r'});
	$bitsPerPattern = defined($opt{'m'}) ? $opt{'m'} : $bitsPerPattern;
	$forcedBits = defined($opt{'F'}) ? $opt{'F'} : 0;
	$forcedMPS = defined($opt{'M'}) ? $opt{'M'} : 0;
	$newReferral = defined($opt{'f'});
	$wantCRTable = defined($opt{'c'});
	$wantStemParadigm = defined($opt{'x'});
	$findCenter = defined($opt{'n'});
	$noEssence = defined($opt{'E'});
	$signature = defined($opt{'b'});
	$stratify = defined($opt{'j'});
	$requiredKeys = defined($opt{'R'}) ? $opt{'R'} : "";
	$outputKeys = defined($opt{'S'}) ? $opt{'S'} : "";
	$MPSfilter = defined($opt{'A'}) ? $opt{'A'} : "";
	$doMPSentropy = defined($opt{'o'});
	$entropyWeight = defined($opt{'O'}) ? $opt{'O'} : "FREQ";
	print "entropyWeight $entropyWeight\n";
	$doConjEntropy = defined($opt{'w'});
	$outputFragment = defined($opt{'u'});
	binmode STDOUT, ":utf8";
	binmode STDERR, ":utf8";
	readFile($ARGV[0]);
	filterConjugations() unless $requiredKeys eq "";
	printFragment($MPSfilter) if $outputFragment;
	expandConjugations() if $expand;
	paradigmIsReferral() if $referParadigm;
	printFile();
	if ($newReferral) {
		printReferrals();
	}
	identicalConjugation();
	if ($wantCRTable) {
		makeCRTable();
		groupReferrals();
	}
	ignoreNulls();
	identicalMPS();
	if ($wantStemParadigm) {
		showStemParadigm($ARGV[0]);
	}
	if ($noEssence) {
		computeNoEssence();
	} else {
		computeEssence();
	}
	showDistillations() if $verbose;
	if ($signature) {
		identicalSignatures();
	}
	fixConjWeights($entropyWeight);
	if ($static || $dynamic || $predictable || $predictive || $doMPSentropy) {
		initializePatternList();
	}
	if ($doMPSentropy) {
		computeMPSentropy($entropyWeight);
		# computeMConjEntropy($entropyWeight);
		nearStatic($entropyWeight);
	}
	computeConjEntropy($entropyWeight) if $doConjEntropy;
	if ($group) {
		groupConjugations();
		identicalConjugationEssence();
	}
	if ($findCenter) {
		findCenter();
	}
	printSynopsis();
	if ($distillationCount >= 32 && (1 << 33) == 2) {
		print "Too many distillations to analyze further\n";
		$static = $dynamic = $adaptive = 0;
	}
	if ($quickStatic) { 
		@statics = findQuickStatic();
		print "\nQuick static principal parts\n";
		printPatterns(\@statics, "\t", "\n");
		explainStatic(@statics) if $stats;
	}
	if ($stratify) { 
		print "\nStratifying\n";
		computeStratify();
	}
	if ($static) {
		@statics = findStaticPatterns();
		print "Best sets of static principal parts\n";
		printForced();
		printPatterns(\@statics, "\t", "\n");
		explainStatic(@statics) if $stats;
		my $number = @statics;
		if ($number) {
			my @anAnalysis = split(',', patternToNumber($statics[0]));
			my $length = scalar @anAnalysis;
			my $possible = choose($distillationCount, $length);
			printf "\t%s analyses with %s principal parts" .
				" out of %s possible: density=%0.3f\n",
				$number, $length, $possible, (0.0+$number) / $possible;
			# count distillations used in static principal parts
			my $distCount = 0;
			my @seen;
			for my $static (@statics) {
				for my $dist (split(',', patternToNumber($static))) {
					if (!defined($seen[$dist])) { # a new one
						$seen[$dist] = 1;
						$distCount += 1;
					} # a new one
				} # each distillation used
			} # each static principal part set
			printf "\tmorphosyntactic focus number: %0.6f\n",
				1.0 - (0.0+$distCount)/($number*$length);
		} # found some static principal parts
	} # require static principal parts
	my $foundTree;
	if ($adaptive) {
		my $foundDepth;
		($foundDepth, $foundTree) =
			findBestAdaptivePattern(0, \%essencePerConj, 0, $infinity);
		print "\nWe need $foundDepth adaptive principal parts:\n";
		showTree($foundTree, 1);
		print "\n";
		computeStatistics($foundTree, 'adaptive') if $stats;
	}
	if ($KATR) {
		if ($static || $quickStatic) {
			$statics[0] = 0 unless defined $statics[0];
			makeKATR('static', $statics[0]);
		} elsif ($adaptive) {
			makeKATR('adaptive', $foundTree);
		} else {
			makeKATR('no', '');
		}
		makeSandhi();
	}
	analyzeQueries() if (@toAnalyze);
	if ($dynamic) {
		print "\nDynamic principal parts". 
			($outputKeys ne ''
				? " (only showing conjugations marked $outputKeys)"
				: '') .
			"\n";
		printForced();
		findBestDynamicPatterns(0);
	}
	if ($predictable) {
		print "\nPredictability (based on m=$bitsPerPattern" .
			($outputKeys ne ''
				? "; only showing conjugations marked $outputKeys"
				: '') .
			")\n";
		findPredictablePatterns($fullPredictable);
	}
	if ($predictive) {
		print "\nPredictiveness (based on m=1)\n";
		findPredictivePatterns();
	}
} # main

main();
# vim:nospell:
