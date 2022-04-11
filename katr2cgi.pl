#!/usr/bin/perl -w
#
# katr2cgi.pl [-f] < FILE
# 
# takes the file output by KATR from a PPA plat, generates a web page
# if -f is given, the build a full web page; otherwise, just a table.
#
# Raphael Finkel © 2014

use CGI qw/:standard :debug/;
require '/homes/raphael/links/r/showKATR.pm';
use strict;

sub init {
	binmode STDIN, ":utf8";
	binmode STDOUT, ":utf8";
	binmode STDERR, ":utf8";
	open (DUMMY, "/dev/null"); # avoid reading CGI parameters from STDIN
	restore_parameters(\*DUMMY);
	close DUMMY;
	# $| = 1; # flush output
} # init

sub firstHtml {
	print header(-expires=>'+1m', -charset=>'UTF-8', -expires=>'-1d'),
		start_html(-title=>'Forms',
			-head=>Link({-rel=>'icon', -href=>'kentucky_wildcats.ico'}),
		);
	print "<h1>Morphological forms</h1>\n";
} # firstHtml

my %contents;
sub readData {
	while (my $line = <STDIN>) {
		chomp $line;
		$line =~ s/^(\S+) \[\] =\s+// or next;
		my $lexeme = $1;
		my @pieces = split(/\s*\|\s*/, $line);
		$contents{$lexeme} = \@pieces;
		# print STDERR "pieces: " . join(' : ', @pieces) . "\n";
	} # each line
} # readData

my @converted;
sub convertData {
	my @mpss;
	for my $mps (@{$contents{'Lexeme'}}) {
		while ($mps =~ s/(\w)([A-Z1-5])/$1,$2/) {
		}
		while ($mps =~ s/([1-5])(\w)/$1,$2/) {
		}
		push @mpss, $mps;
	} # each mps
	for my $lexeme (keys %contents) {
		next if $lexeme eq 'Lexeme'; # pseudo-lexeme
		my $index = 0;
		for my $piece (@{$contents{$lexeme}}) {
			$piece =~ s/ //g;
			$piece =~ s/,/ /g;
			# $piece = '∅' if $piece eq ''; # null
			push @converted, "$lexeme $mpss[$index] $piece"
				unless $piece eq '';
			$index += 1;
		} # each surface form
	} # each lexeme
} # convertData

sub formatOutput {
	my $tree = [];
		# internal nodes are [MP, subtree, MP, subtree, ...]
	my $prevHead = '';
	my @lexemes = ();
	for my $line (@converted) { # discover all the lexemes
		$line =~ /^(\w+|)\s+([\w,]+)\s+(.*)/;
		my $head = $1;
		$head =~ s/_/, /g;
		next if $head eq $prevHead;
		my $printableHead = $head;
		# $printableHead =~ s/u(\d+)/chr($1)/eg;
		$printableHead =~ s/u([0-9abcdef]{4})/sprintf('%c',hex($1))/eg;
		push @lexemes, "<a href='#$printableHead'>$printableHead</a>";
		$prevHead = $head;
	}
	print "" . join(" | ", @lexemes) . "\n" unless @lexemes < 2;
	$prevHead = '';
	print "\n";
	for my $line (@converted) {
		$line =~ /^(\w+|)\s+([\w,]+)\s+(.*)/;
		my ($head, $MPSstring, $value) = ($1, $2, $3);
		# print "<br/>value is: $value\n";
		$head =~ s/_/, /g;
		if ($head ne $prevHead) {
			if ($prevHead ne '') { # finished a tree
				# print "Tree for $prevHead: " . Dumper($tree) . "\n";
				displayTree($prevHead, $tree);
			}
			$prevHead = $head;
			$tree = [];
		} # new head word
		$MPSstring =~ s/([A-Z])/" " . lc($1)/eg;
		my @MPS = split(/,/, $MPSstring);
		$value =~ s/ *$//; # strip blanks
		# print "Inserting $value for " . join(', ', @MPS) . "\n";
		$tree = insertValue($tree, $value, @MPS);
		# print "So far for $head: " . Dumper($tree) . "\n";
		# @prevMPS = @MPS;
	} # each line
	displayTree($prevHead, $tree);
} # formatOutput

sub finalize {
	print end_html();
} # finalize

my $full = (defined($ARGV[0]) and $ARGV[0] eq '-f');
init();
firstHtml() if $full;
readData();
convertData();
formatOutput();
finalize() if $full;
