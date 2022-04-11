#!/usr/bin/perl -w

=head SYNOPSIS

Parses a KATR file (in stdin), generating a Prolog theory (to stdout).
The Prolog output is acceptible to gnu prolog
(http://www.gnu.org/software/prolog).

To make parsing easy, we assume KATR nodes always start at start of line, no
rules on first line of a node.  Rules always start with a tab, one per line,
and end with a line containing only <tab><period>.

Can handle this syntax:
	% comments in this style
	/* comments in this style */
	<lhs> == rhs   
	<lhs> =+= rhs (the lhs is placed after any explicit paths on rhs)
	<foo/bar> =+= rhs
	{lhs} == rhs    [but can't handle reverse queries over sets]
	{lhs} =+= rhs    [but can't handle reverse queries over sets]
	acceptible RHS terms:
		atoms (may contain non-Ascii and atoms starting with numbers)
		<path> (including recursive queries inside the path)
		Node  (may contain non-Ascii after first character)
		Node:<path> (including recursive queries inside the path)
		"<path>" (including recursive queries inside the path)
		"Node:<path>" (including recursive queries inside the path)
		"Node"
	<$foo $bar> == rhs  (also {...})
	<$var#1 $var2> == rhs (also {...})
	<atom ... +n>	 [increases Pāṇini preference by n] (also {...})
	<atom ... ++>	 [increases Pāṇini preference by 100] (also {...})
		[Pāṇini preference is primarily on length of lhs, secondarily on number
		of atoms (as opposed to variables) in the lhs.]
	#hide NODE ... . [all on one line]
	#hideInternal hides all internal nodes.
	#show < generation :: pattern > . [all on one line, but may have several]
	   the :: sign is optional.
	#vars: both lists and expressions, without limited *, + , - operators
	#atom ... [including the atom ']
	! in the rhs means failure
	#trace in a rule rhs means to add tracing information for this rule
	#trace in a node rhs means to add tracing information for this node
	#count in a node rhs means to add count information for the rules of node
	#countall means to add count information for all rules of all nodes
	#pretrace in a rule rhs means to add pretracing information for this rule
	#pretrace in a node rhs means to add tracing information for this node
	#class name elements in the list .
	#sandhi orig => replacement .
		Applied after all KATR rules.  The orig may use $vars, refered to in
		replacement with $1, $2, ...
	#alternative orig => replacement .
		Applied after Sandhi.

Cannot yet handle this syntax:
	Any syntax element crossing a line; terminating . not on a line of its own,
		rules not starting with space.
	Regular expressions in rhs results (lhs is now ok).
	$vars: joint use of + and - operators (single use is ok)
	$vars: use of !value in a {lhs}
	Macro syntax for vocabulary shorthand
	#show with conditional syntax
	Node whose spelling includes a nonascii character.
	'<' as an atom confuses the parser; it is taken as a structured element.
	
Should improve:
	place marked IMPROVE

Backword solution:
	Some progress.  We completely separate the forward from the backward rules.
	Backward rules of the form
		<atom> = some result
	if we know that "atom" is at the head of the known part of the Query should
	fire in a way that prevents alternatives; as it stands, we try all
	alternatives, although in Pāṇini order.

Bugs:
	In sorting, we treat the unit:  ְ/ ̃ as two units because there is a hidden space.
Fixed:
	3/2019
	After *, instead of \s+, we place \s*, because there is likely to be a \s+
	before the repeated element, and we don't want to require two spaces.

The resulting Prolog program has a goal leaves/0 that applies all the "#show"
patterns (typically morphosyntactic properties) to the non-hidden leaf nodes,
printing resulting surface forms.  The Prolog goal all/0 invokes leaves/0 until
it fails.

Backward queries (given a surface form, parse to discover morphosyntactic
properties) are theoretically possible, but are not currently supported.

Raphael Finkel 11/2002 - 1/2003

=cut

use strict;
use vars qw/ %isLeaf @leaves %atom %opts %stars %pluses %redirects %doTrace
	%doPretrace %doCount $analyze @lineNumbers @sandhi @alternative %classes
	$autoLeaf $countAll / ;


binmode STDIN, ":utf8";
binmode STDOUT, ":utf8";
binmode STDERR, ":utf8";

$autoLeaf = 0; # if 1, then leaves are nodes not referred to; if 0, everything
	# not explicitly hidden is a leaf.
$countAll = 0; # if 1, we count statistics on all nodes
sub parseFile {
	my ($nodeName, $type, $lhs, $rhs, $line, @rules, @leafDetails, @toShow);
	$analyze = 0;
	while (defined($line=<STDIN>)) {
		chomp $line;
		print (($line !~ /^\s*$/) ? "% $line\n" : "\n");
		$line =~ s/%.*//; # remove comments
		if ($line =~ /\/\*/) { # long comment
			while ($line !~ /\*\//) {
				$line = <STDIN>;
				last unless defined $line; # unterminated comment
				print "% $line";
			}
			print "% $line";
			next;
		}
		last unless defined $line; # unterminated comment
		next if $line =~ /^\s*$/; # remove blank lines
		if ($line =~ /^(([a-z]\S*\.)*([A-Z]\S*)):(.*)$/) { # start of a node
			# the pattern above discards qualifiers; foo.bar.This is just This
			$nodeName = $3;
			my $extraInfo = $4;
			if (!defined($isLeaf{$nodeName})) {
				$isLeaf{$nodeName} = 1;
				push @leaves, $nodeName;
			}
			# print "% $nodeName is a leaf? " , $isLeaf{$nodeName}, "\n";
			$doTrace{$nodeName} = ($extraInfo =~ /#trace/);
			$doPretrace{$nodeName} = ($extraInfo =~ /#pretrace/);
			$doCount{$nodeName} = ($extraInfo =~ /#count/);
			@rules = ();
			# print "% starting node $nodeName\n";
		} elsif ($line =~ /\s+([<{])([^>}]*)[>}]\s*=((\+)?=?)\s*(.*)/) { # rule
			$type = $1; # '<' or '{', possibly followed by + for =+=
			$lhs = $2;
			$rhs = $5;
			if ($3 eq "+=") {
				push @rules, "$type+=$lhs=$rhs=$.";
			} else {
				push @rules, "$type=$lhs=$rhs=$.";
			}
		} elsif ($line =~ /^\s*\./) { # end of rule
			# print "% end of a rule\n";
			emit($nodeName, @rules);
		} elsif ($line =~ /#atom\s+(.*)\./) {
			my $trailer = $1;
			$trailer =~ s/\s*$//;
			my $piece;
			foreach $piece (split /\s+(?=\P{M})/, $trailer) {
				$atom{$piece} = 1;
				# print STDERR "is an atom: [$piece]\n"; # debug
			}
		} elsif ($line =~ /#\s*vars\s+\$(\S+):\s*([^.]+)\./) {
			# variable declaration
			my ($varName, $varExpr, $value, $term, $operator, @toSay);
			$varName = $1;
			$varExpr = $2;
			my $classContents = $varExpr;
			$classContents =~ s/\s*$//;
			$classContents =~ s/\s+/\|/g;
			$classContents =~ s/∅//g;
			$classes{$varName} = $classContents; # a Perl pattern
			# print STDERR "classes{$varName} is $classes{$varName}\n";
			if ($varExpr =~ /^\$/) { # expression 
				print "var_$varName(X) :- ";
				@toSay = ();
				$varExpr = "* $varExpr"; # pump priming
				while ($varExpr =~ s/([-*+])\s*\$(\S+)\s*//) { # one term
					$operator = $1;
					$term = "var_" . $2;
					if ($operator eq "*") {
						push @toSay, "${term}(X) ";
					} elsif ($operator eq "-") {
						push @toSay, "not(${term}(X)) ";
					} elsif ($operator eq "+") {
						print join(", ", @toSay), " . \n";
						print "var_$varName(X) :- ";
						@toSay = ();
						push @toSay, "${term}(X) ";
					}
				} # one term
				print join(", ", @toSay), " . \n";
			} else { # simple list
				foreach $value (split(/\s+/, $varExpr)) {
					print "var_$varName(" . normalizeAtom($value) . ") .\n"
						unless $value eq "";
				}
			} # simple list
		} elsif ($line =~ /#hideInternal/) { # internals are hidden
			$autoLeaf = 1;
		} elsif ($line =~ /#countAll/) { # count all nodes
			$countAll = 1;
		} elsif ($line =~ /#hide\s+([^.]*)/) { # hide declaration
			my $value;
			foreach $value (split(/\s+/, $1)) {
				$isLeaf{$value} = 0;
			}
		} elsif ($line =~ /#show\s+<([^>]*)>/) { # show declaration
			push @toShow, $1;
		} elsif ($line =~ /#analyze\b/) { # analyze declaration
			$analyze = 1;
		} elsif ($line =~ /^#sandhi\s+(.*)\./) { # sandhi declaration
			push @sandhi, $1;
		} elsif ($line =~ /^#alternative\s+(.*)\./) { # alternative declaration
			push @alternative, $1;
		} else {
			print "% untreated line: $line\n";
			print STDERR "Can't handle line $.: [$line]\n";
		}
	} # one line
	# emit leafNode/2 rules.
	my @toSay = ();
	foreach $nodeName (@leaves) {
		next unless $isLeaf{$nodeName}; # some might be hidden
		my $goodName = normalizeNodeName($nodeName);
		print "leafNode(Query, Result, Name) :- % forward\n" .
				"\tName = '" . $goodName . "',\n" .
				"\tvariety(Query),\n" .
				"\tnode_$goodName" .  "(Query, Result, start_$goodName, show) .\n";
	}
=cut backward
	foreach $nodeName (keys %isLeaf) {
		print "backLeafNode(Query, Result, Name) :- % backward\n",
				"\tbackVariety(Query),\n",
				"\tName = '" . $nodeName . "',\n",
				"\tback_node_$nodeName" . "(Query, Result, start_$nodeName) .\n"
			if $isLeaf{$nodeName};
	}
=cut 
	# emit redirect/2 rule.
	foreach $nodeName (keys %isLeaf) {
		my $goodName = normalizeNodeName($nodeName);
		print "redirect(Query, Result, start_$goodName, FromNode) :- " .
				"node_$goodName(Query, Result, start_$goodName, FromNode) .\n"
			if defined($redirects{$nodeName}) or $isLeaf{$nodeName};
	}
	# emit all "show" rules
	my ($parts, $part, $varName, @list, $index);
	foreach $parts (@toShow) { # forward
		$parts =~ s/:://g;
		@leafDetails = ();
		$index = 0;
		print "variety(Query) :- % forward: generate\n";
		foreach $part (split(/\s+/, $parts)) { # set variables
			$index += 1;
			next unless $part =~ /^\$/;
			$varName = $part;
			$varName =~ s/\$//;
			print "\tvar_$varName(" . ucfirst($varName) . $index . "),\n";
		}
		@list = ();
		$index = 0;
		foreach $part (split(/\s+/, $parts)) { # list
			$index += 1;
			$varName = $part;
			if ($varName =~ s/\$//) {$varName = ucfirst($varName) . $index;}
			push @list, normalizeAtom($varName);
		}
		my $serialList = join(", ", @list);
		print "\tQuery = [$serialList] .\n";
	} # foreach $parts 
	foreach $parts (@toShow) { # backward
		print "backVariety(Query) :- % backward: stipulate\n";
		$parts =~ s/:://g;
		$parts =~ s/[\$\w]+/_/g;
		print "\tQuery = [" . join(",", split(/\s+/, $parts)) . "] .\n";
	}
	# emit any opt and rules we discovered we need.
	my $optvar;
	foreach $optvar (keys %opts) { # subtractive opt_ rules
		print "\n% opt_$optvar(list, matched sublist, remainder)\n" ,
			"opt_$optvar([X|Y], [X], Y) :- var_$optvar(X) , ! .\n" ,
			"opt_$optvar(X, [], X) .\n";
	}
	my $plusvar;
	foreach $plusvar (keys %pluses) { # subtractive plus_ rules
		$stars{$plusvar} = $pluses{$plusvar};
		print "\n% plus_$plusvar(list, matched sublist, remainder)\n" ,
			"plus_$plusvar([X|Y], [X|W], Z) :- var_$plusvar(X), !, " .
				"star_$plusvar(Y, W, Z) .\n" ;
	}
	my $starvar;
	foreach $starvar (keys %stars) { # subtractive star_ rules
		print "\n% star_$starvar(list, matched sublist, remainder)\n" ,
			"star_$starvar([X|Y], [X|W], Z) :- var_$starvar(X), !, " .
				"star_$starvar(Y, W, Z) .\n" .
			"star_$starvar(X, [], X) .\n" ;
	}
	# isrule rules
	my $ruleNumber;
	foreach $ruleNumber (@lineNumbers) {
		print "isrule($ruleNumber) .\n";
	}
} # parseFile

sub normalizeNodeName {
	my ($name) = @_;
	$name =~ s/([^a-z_0-9])/"u" . sprintf("%x", ord($1))/eig;
	return $name;
} # normalizeNodeName

sub addCommas {
	# produce a list of the elements in $string, such as   "[a, b, c]". (Here,
	# $string = "a b c".) Insert prophylactic quotes around non-ascii elements
	# and atoms starting with non-letters.
	my ($string) = @_;
	my ($piece, @quotedString);
	$string =~ s/^\s+//;
	foreach $piece (split(/\s+/, $string)) {
		push @quotedString, normalizeAtom($piece);
	}
	return("[" . join(", ", @quotedString) . "]");
} # addCommas

sub normalizeAtom {
	# make the atom acceptable to Prolog by quoting if necessary.
	my ($string) = @_;
	$string =~ s/\\/\\\\/g;
	$string =~ s/'/\\'/g;
	if ($string !~ /^'.*'$/ and 
		(
			$string =~ /\W/ or $string =~ /^\d+[^\d]/ or 
			(defined($atom{$string}) and $string !~ /^Var_/) or
			($string =~ '_' and $string !~ /^Var_/) or
			$string =~ /[^[:ascii:]]/
		)
	)
	# if (($string =~ /[^[:ascii:]]/ and $string !~ /^'.*'$/) or
	# 	defined($atom{$string}) or $string =~ /'/ or $string =~ /^\d+[^\d]/)
	{
		# print STDERR "normalized with quotes: '$string'\n";
		return("'" . $string . "'");
	} else {
		# print STDERR "not with quotes: $string\n";
		return($string);
	}
} # normalizeAtom

sub balanced {
	# return 0 or 1 to indicate if $string is balanced.
	# check only for <> and {}, assume in order.
	my ($string) = @_;
	if ($string =~ s/<//) {
		if ($string =~ s/>//) {
			return(balanced($string))
		} else {
			return(0);
		}
	} elsif ($string =~ s/{//) {
		if ($string =~ s/}//) {
			return(balanced($string))
		} else {
			return(0);
		}
	}
	return(1);
} # balanced

sub findPieces {
	# string might be "a b VERB:<bar> FOO:<baz <this>>".
	# Return an array containing the top-level clauses, such as:
	# (a b, VERB:<bar>, FOO:<baz this>).
	# We combine atoms together into one array element at the top level.
	my ($string) = @_;
	my ($previous, $piece, @answer);
	my ($pieceIsAtomic, $previousIsAtomic);
	$previous = "";
	$previousIsAtomic = 1;
	for $piece (split(/\s+(?=\P{M})/, $string)) {
		$pieceIsAtomic = (defined($atom{$piece}) or
				($piece !~ /^[A-Z]/ and $piece !~ /[<>"]/)
			);
		# print "% piece is $piece; atomicity $pieceIsAtomic.\n";
		# print "%\thas brackets\n" if $pieceIsAtomic =~ /[<>"]/;
		if (balanced($piece) and $pieceIsAtomic and $previousIsAtomic) {
			$previous .= " " . $piece;
			# print "% still a list of atoms; we now have $previous\n";
		} elsif (balanced($previous)) {
			$previous =~ s/^\s*//;
			# print "% emitting $previous\n" unless $previous eq "";
			push @answer, $previous unless $previous eq "";
			$previous = $piece;
			$previousIsAtomic = $pieceIsAtomic;
		} else {
			$previous .= " " . $piece;
			$previousIsAtomic = 0;
			# print "% need balance, now have $previous.\n";
		}
	} # foreach piece
	$previous =~ s/^\s*//;
	push @answer, $previous unless $previous eq "";
	# print "% Pieces of [$string]: ", join("|", @answer), "\n";
	return(@answer);
} # findPieces

my $nonceVal = 0; # may be reset between Prolog outputs
sub nonce { # returns a new number each time.
	$nonceVal += 1;
	return $nonceVal;
} # nonce

sub makeNodeCall {
	# given $nodename, $query, $startNode, $postpend,
	# return "$nodeName($newQuery, Result, $startNode)",
	# if ($postpend = "") we are working on an == rule, so
	#      $newQuery = query Rest
	# else we are working on an =+= rule, so
	#      $newQuery = $query $postpend Rest
	# use append to get the effects needed.
	my ($postpend, $nodeName, $query, $startNode, $fromNodeName) = @_;
	$fromNodeName = "'" . normalizeNodeName($fromNodeName) . "'";
	my $answer = "";
	my $theNonce;
	if ($postpend eq "") { # part of == rule
		# print "% makeNodeCall: query is $query; no postpend\n";
		if ($query eq "[]") {
			$answer = "$nodeName(Rest, Result, $startNode, $fromNodeName)";
		} elsif ($query =~ /\[/) {
			$query =~ s/\]/ | Rest]/;
			$answer = "$nodeName($query, Result, $startNode, $fromNodeName)";
		} else {
			$theNonce = "Tmp" . nonce();
			$answer = "append($query, Rest, $theNonce),\n\t" .
				"$nodeName($theNonce, Result, $startNode, $fromNodeName)";
		}
	} else { # part of =+= rule
		print "% makeNodeCall: query is $query; postpend is $postpend\n";
		my $theNonce = "Tmp" . nonce();
		# IMPROVE: will the query still have | Rest?
		# the following is quick and dirty, not always right.  The $query may
		# be in a comma-delimited form with | Rest on it; we need to use append
		# instead and put the Rest at the very end.  So we first remove the
		# |Rest.
		# $query =~ s/\bRest\b//;
		# $query =~ s/\[\s*(\|)?\s*\]//;
		$query =~ s/,/ /g;
		$query =~ s/\[([^\]]*)\]/$1/;
		print "% assembling =+= rhs; query=$query, postpend=$postpend\n" ;
		my @postpend = appendRhsParts("$query $postpend", $theNonce);
		$answer = join(",\n\t", @postpend) .
			",\n\t$nodeName($theNonce, Result, $startNode, $fromNodeName)";
	}
	# print "% makeNodeCall: $answer\n";
	return($answer);
} # makeNodeCall

sub hasStructure { # return true iff the param is a path with substructure,
	# that is, nodes or other paths.
	my ($path) = @_;
	my ($part);
	return 1 if ($path =~ /</ or $path =~ /\?/);
	foreach $part (split(/\s+/, $path)) {
		return 1 if ($part =~ /^[A-Z]/ and !defined($atom{$part}));
	}
	return 0;
} # hasStructure

sub emitRHS {
	my ($rhs, $style, $nodeName, $postpend) = @_;
	# print "% emitRHS: rhs is $rhs; postpend is $postpend; style is $style\n";
	$nodeName = normalizeNodeName($nodeName);
	my (@pieces);
	$rhs =~ s/\s+$//;
	@pieces = findPieces($rhs);
	if (@pieces == 0) { # no pieces at all!
		return("Result = []");
	} elsif (@pieces == 1) { # only one piece
		$rhs = $pieces[0];
		# print "% only one piece: [$rhs]\n";
		$rhs =~ /^([^: "]*)/;
		my $firstComponent = $1;
		if ($rhs =~ /^[A-Z]/ and !defined($atom{$rhs}) and $rhs !~ /^Var_/ 
				and !defined($atom{$firstComponent})) {
			# Node
			if ($rhs =~ /([^:]*):<(.*)>$/) { # Node:<path>
				my ($node, $path) = ($1, $2);
				# print "% it's type 1: $node:<$path>\n";
				$isLeaf{$node} = 0 if $autoLeaf;
				if (hasStructure($path)) {
					my ($soFar, $newCode, $aNonce);
					# print "% Structured (type 1): $node:<$path>\n";
					$soFar = emitRHS($path, $style, $nodeName, $postpend);
					$aNonce = "Result" . nonce();
					$soFar =~ s/Result\b/$aNonce/g;
					$newCode = makeNodeCall($postpend ,
						($style eq "forward" ? "" : "back_") .
						normalizeNodeName("node_$node"),
						$aNonce, "StartNode", $nodeName);
					return $soFar . ",\n\t" . $newCode ;
				} else {
					# print "% non-structured (type 1): $node:<$path>\n";
					return makeNodeCall($postpend,
						($style eq "forward" ? "" : "back_") .
						normalizeNodeName("node_$node"),
						addCommas($path), "StartNode", $nodeName);
				}
			} else { # with no path
				$isLeaf{$rhs} = 0 if $autoLeaf;
				return(
					($style eq "forward" ? "" : "back_") . 
					normalizeNodeName("node_$rhs") .
					"(Query, Result, StartNode, '$nodeName')");
			} # with no path
		} elsif ($rhs =~ /^<(.*)>\s*$/) { # <path>
			my ($path) = $1;
			if (hasStructure($path)) { # <structured path>
				my ($soFar, $newCode, $aNonce);
				# print "% Structured (type 2): <$path>\n";
				$soFar = emitRHS($path, $style, $nodeName, $postpend);
				$aNonce = "Result" . nonce();
				$soFar =~ s/Result\b/$aNonce/g;
				$newCode = makeNodeCall($postpend ,
					($style eq "forward" ? "" : "back_") .
					normalizeNodeName("node_$nodeName"),
					$aNonce, "StartNode", $nodeName);
				return $soFar . ",\n\t" . $newCode ;
			} else { # <simple path>
				return makeNodeCall($postpend,
					($style eq "forward" ? "" : "back_") .
					normalizeNodeName("node_$nodeName"),
					addCommas($path), "StartNode", $nodeName);
			}
		} elsif ($rhs =~ /^"<(.*)>"\s*$/) { # "<path>"
			my ($path) = $1;
			if (hasStructure($path)) { # "<structured path>"
				my ($soFar, $newCode, $aNonce);
				# print "% Structured (type 3): \"StartNode:<$path>\"\n";
				$soFar = emitRHS($path, $style, $nodeName, $postpend);
				$aNonce = "Result" . nonce();
				$soFar =~ s/Result\b/$aNonce/g;
				$newCode = makeNodeCall($postpend , "redirect", $aNonce,
					"StartNode", $nodeName);
				return $soFar . ",\n\t" . $newCode ;
			} else { # "<simple path>"
				# print "% simple (type 3): \"StartNode:<$path>\"\n";
				return makeNodeCall($postpend, "redirect",
					addCommas($path), "StartNode", $nodeName);
			}
		} elsif ($rhs =~ /^"([A-Z]\S*):<(.*)>"$/) { # "Node:<path>"
			my ($node, $path) = ($1, $2);
			$redirects{$node} = 1;
			my $goodNode = normalizeNodeName($node);
			if (hasStructure($path)) { # "Node:<structured path>"
				my ($soFar, $newCode, $aNonce);
				# print "% Structured (type 4): $node:<$path>\n";
				$soFar = emitRHS($path, $style, $nodeName, $postpend);
				$aNonce = "Result" . nonce();
				$soFar =~ s/Result\b/$aNonce/g;
				$newCode = makeNodeCall($postpend ,
					($style eq "forward" ? "" : "back_") .
					"node_$goodNode",
					$aNonce, "start_$goodNode", $nodeName);
				return $soFar . ",\n\t" . $newCode ;
			} else { # "Node:<simple path>"
				return makeNodeCall($postpend,
					($style eq "forward" ? "" : "back_") .
					"node_$goodNode",
					addCommas($path), "start_$goodNode", $nodeName);
			}
		} elsif ($rhs =~ /^"([A-Z]\S*)"$/) { # "Node"; postpend irrelevant
			my $node = $1;
			$redirects{$node} = 1;
			return(
				($style eq "forward" ? "" : "back_") . 
				normalizeNodeName("node_$node") .
				"(Query, Result, start_$node, $nodeName)");
		} elsif ($rhs =~ /^Var_(\w+)\?/) { # $var?
			return("Result = Opt_$1");
		} elsif ($rhs =~ /^Var_(\w+)\*/) { # $var*
			return("Result = Star_$1");
		} elsif ($rhs =~ /^Var_(\w+)\+/) { # $var+
			return("Result = Plus_$1");
		} else { # atom; postpend irrelevant
			if ($rhs =~ /!/) {
				return("!, fail"); # KATR extension: ! in rhs means failure
			} else {
				return("Result = " . addCommas($rhs));
			}
		}
	} else { # multiple pieces: recur and glue results together
		my (@result, $piece, $aNonce, $clause, $index, @nonces);
		# print "multiple pieces\n";
		@result = ();
		if ($style eq "forward") {
			for $piece (@pieces) {
				$aNonce = nonce();
				push @nonces, $aNonce;
				$clause = emitRHS($piece, $style, $nodeName, $postpend);
				$clause =~ s/Result\b/Result$aNonce/;
				push @result, $clause;
			}
			# push @result, "MoreResult$nonces[0] = Result$nonces[0]";
			if ($#nonces < 2) { # just 1 append neeed
				push @result, "append(Result" . $nonces[0] .
					", Result" . $nonces[1] . ", Result)";
			} else { # at least 2 appends needed
				push @result, "append(Result$nonces[0], Result$nonces[1], " .
					"MoreResult$nonces[1])";
				for ($index = 2; $index < $#nonces; $index += 1) {
					push @result, ("append(MoreResult" . $nonces[$index-1] .
						", Result" . $nonces[$index] .
						", MoreResult" . $nonces[$index] .
						")");
				}
				push @result, "append(MoreResult" . $nonces[$#nonces-1] .
					", Result" . $nonces[$#nonces] . ", Result)";
				# push @result, "MoreResult" . $nonces[$index-1] . " = Result";
			} # at least 2 appends needed
		} else { # backward style
			my ($aNonce, $nextNonce);
			$aNonce = nonce();
			push @result, "Result = MoreResult$aNonce";
			for $piece (@pieces) {
				$nextNonce = nonce();
				$clause = emitRHS($piece, $style, $nodeName, $postpend);
				push @result,
					"append(Result$aNonce, MoreResult$nextNonce, " .
					"MoreResult$aNonce)";
				$clause =~ s/Result\b/Result$aNonce/;
				push @result, $clause;
				$aNonce = $nextNonce;
			}
			push @result, "MoreResult$aNonce = []";
		} # backward style
		return("\n\t" . join(",\n\t", @result));
	} # multiple pieces
} # emitRHS

sub replacement { # convert "foo/bar a baz/rag" to "foo a baz", "bar a rag"
	my ($string) = @_;
	my ($trueString, $replacementString) = ($string, $string);
	use utf8;
	$trueString =~ s/\/\s*\S+//g;
	no utf8;
	$replacementString =~ s/\S+\///g;
	# print "% REPLACE: $trueString | $replacementString\n";
	return($trueString, $replacementString);
} # replacement

sub appendLhsParts { # Assemble parts of the lhs.
	# parts is of the form "this that Other"; 
	# either build a single list, if all parts are atoms, or append together to
	# form Query otherwise.  "Rest" is appended to the end.
	my ($parts) = @_;
	my (@pieces, $piece, @result, $index, $aNonce, $prevNonce);
	@pieces = findPieces($parts);
	for ($index = 0; $index <= $#pieces; $index += 1) {
		$pieces[$index] = addCommas($pieces[$index])
			unless ($pieces[$index] =~ /^(Opt|Star|Plus)_/);
	}
	# print "% TRY: I found these pieces: ", join(" | ", @pieces), "\n";
	if ($#pieces == -1) { # empty
		return "Query = Rest"; # we need at least one clause
	}
	@result = ();
	$prevNonce = "Query";
	for ($index = 0; $index <= $#pieces; $index += 1) {
		$aNonce = ($index == $#pieces) ? "Rest" : ("Query" . nonce());
		(my $predName = lcfirst $pieces[$index]) =~ s/\d+$//;
		if ($pieces[$index] =~ /^(Opt|Star|Plus)_/) {
			push @result, "$predName($prevNonce, $pieces[$index], $aNonce)";
			if ($predName =~ /^opt_(.*)/) {$opts{$1} = 1;}
			if ($predName =~ /^star_(.*)/) {$stars{$1} = 1;}
			if ($predName =~ /^plus_(.*)/) {$pluses{$1} = 1;}
		} else {
			push @result,
				("append($pieces[$index], $aNonce, $prevNonce)");
		}
		$prevNonce = $aNonce;
	}
	# push @result, "$aNonce = Rest";
	return @result;
} # appendLhsParts

sub appendRhsParts { # Assemble parts of the rhs.
	# We use this routine only for a rhs of a =+= rule.
	# parts is of the form "this Var_that? Var_other* and more"; 
	# either build a single list, if all parts are atoms, or append together to
	# form an intermediate variable.  Then append Rest.  The result should be
	# $theResult.
	my ($parts, $theResult) = @_;
	my (@pieces, $piece, @result, $index, $aNonce, $prevNonce);
	$parts =~ s/Var(_\w+)\?/Opt$1/g;
	$parts =~ s/Var(_\w+)\*/Star$1/g;
	$parts =~ s/Var(_\w+)\+/Plus$1/g;
	@pieces = findPieces($parts);
	for ($index = 0; $index <= $#pieces; $index += 1) {
		$pieces[$index] = addCommas($pieces[$index])
			unless ($pieces[$index] =~ /^(Opt_|Star_|Plus_|Result)/);
	}
	# print "% pieces so far: ", join("|", @pieces), "\n";
	if ($#pieces == -1) { # empty
		return "$theResult = Rest"; # unusual, but it could happen
	} else { # at least two pieces
		@result = ();
		$prevNonce = "$pieces[0]";
		for ($index = 1; $index <= $#pieces; $index += 1) {
			$aNonce = "Rhs" . nonce();
			push @result, "append($prevNonce, $pieces[$index], $aNonce)";
			$prevNonce = $aNonce;
		}
		push @result, "append($prevNonce, Rest, $theResult)";
		return @result;
	} # at least two pieces
} # appendRhsParts

sub emit {
	my ($nodeName, @rules) = @_;
	$nodeName = normalizeNodeName($nodeName);
	my ($index, $lhs, $rhs, $type, $lineNumber);
	@rules = sort { # sort, reverse order, based on number of lhs elements
		my ($lhs1, $lhs2) = ($a, $b);
		my (@tmp1, @tmp2);
		my ($count1, $count2, $unit);
		$lhs1 =~ s/^.(\+)?=\s*//; # remove type
		$lhs1 =~ s/\s*=.*//; # remove rhs
		$lhs2 =~ s/^.(\+)?=\s*//; # remove type
		$lhs2 =~ s/\s*=.*//; # remove rhs
		$lhs1 =~ s/\+\+/" a " x 100/e; # enhance ++
		$lhs2 =~ s/\+\+/" a " x 100/e; # enhance ++
		$lhs1 =~ s/\+(\d+)/" a " x $1/e; # enhance +n
		$lhs2 =~ s/\+(\d+)/" a " x $1/e; # enhance +n
		$lhs1 =~ s/\/( )?[^ ]+//g; # remove / and its following atom
		$lhs2 =~ s/\/( )?[^ ]+//g; # remove / and its following atom
		$count1 = 0;
		foreach $unit (split(/\s+/, $lhs1)) {
			$count1 += 1; # ordinary credit for each unit
			$count1 += 0.01 unless $unit =~ /^\$/; # extra credit for atoms
		}
		$count2 = 0;
		foreach $unit (split(/\s+/, $lhs2)) {
			$count2 += 1; # ordinary credit for each unit
			$count2 += 0.01 unless $unit =~ /^\$/; # extra credit for atoms
		}
		$count2 <=> $count1
	} @rules;
	# print "% $nodeName:\n";
	my $style;
	# for $style ("forward", "backward") {
	for $style ("forward") {
		for ($index = 0; $index <= $#rules; $index += 1) { # one rule
			($type, $lhs, $rhs, $lineNumber) = split(/=/,$rules[$index]);
			my ($lhsPiece, @stipulation);
			my $traceRule = ($rhs =~ s/#trace\s*//);
			my $pretraceRule = ($rhs =~ s/#pretrace\s*//);
			$rhs =~ s/([a-z]\S*\.)+([A-Z]\S*)/$2/g; # ignore qualifiers
			print "% for $type$lhs" .
				($type =~ /</ ? ">" : "}") .
				($type =~ /\+/ ? " =+= " : " == ") .
				"$rhs\n";
			$lhs =~ s/ \+[+\d]*/ /; # remove ++ and +n
			# print "%\t$type$lhs", $type eq "<" ? ">" : "}", " = $rhs\n";
			@stipulation = ();
			foreach $lhsPiece (split /\s+/, $lhs) {
				if ($lhsPiece =~ /^\$([^#?*+]*)(#(\d*))?$/) {
					my $newPiece = "Var_" . $1 . (defined($3) ? $3 : "");
					$atom{$newPiece} = 1; # treat as an atom in lists.
					# print "% need to type: var_$1($newPiece)\n";
					push @stipulation, "var_$1($newPiece)";
				}
			}
			# print "% stipulation: " . join(", ", @stipulation) . "\n";
			$lhs =~ s/\$([^\s#]+)#?/Var_$1/g;
			$rhs =~ s/\$([^\s#]+)#?/Var_$1/g;
			my ($trueLhs, $replacementLhs);
			my ($leftOutput, $lhsCode, $rhsCode, $analyzeCode);
			$nonceVal = 0;
			$leftOutput = ($style eq "forward" ? "" : "back_") . 
				normalizeNodeName("node_$nodeName") .
				"(Query, Result, StartNode, FromNode) :- % $style\n";
			# $leftOutput .= ($style eq "forward") ? "nonvar(Query)," :
			#	 "var(Query),";
			if ($type =~ /\+/) { # extending (=+=)
				($trueLhs, $replacementLhs) = replacement($lhs);
			} else { # ordinary (==)
				($trueLhs, $replacementLhs) = ($lhs, undef);
			}
			$lhsCode = "\t% lhs code\n\t";
			if ($analyze) {
				push @lineNumbers, $lineNumber;
				$analyzeCode = "\tassertz(usedrule($lineNumber)) , % analyze\n";
			} else {
				$analyzeCode = "";
			}
			$rhsCode = "\t% rhs code\n\t";
			if ($type =~ /</) { # <lhs>
				while ($trueLhs =~ /\bVar_(\w+)\?/) { # <... $var? ...> = 
					my $optvar = $1;
					$trueLhs =~ s/\bVar_$optvar\?/Opt_$optvar/;
				}
				while ($trueLhs =~ /\bVar_(\w+)\*/) { # <... $var* ...> = 
					my $starvar = $1;
					$trueLhs =~ s/\bVar_$starvar\*/Star_$starvar/;
				}
				while ($trueLhs =~ /\bVar_(\w+)\+/) { # <... $var+ ...> = 
					my $plusvar = $1;
					$trueLhs =~ s/\bVar_$plusvar\+/Plus_$plusvar/;
				}
				while ($trueLhs =~ /!(\w+)/) { # <... !atom ...> = 
					my $starvar = $1;
					$trueLhs =~ s/!$starvar/Except_$starvar/;
				}
				$lhsCode .= join(",\n\t", appendLhsParts($trueLhs));
				$nonceVal = 0;
				$rhsCode .= join(",\n\t", @stipulation) . ",\n\t"
					if (@stipulation and $style eq "forward");
				$rhsCode .= emitRHS($rhs, $style, $nodeName,
						($type =~ /\+/) ? $replacementLhs : "");
				while ($rhsCode =~ /!(\w+)/) { # <... !atom ...> = 
					my $starvar = $1;
					$rhsCode =~ s/'!$starvar'/Except_$starvar/;
				}
			} else { # {lhs}
				$lhsCode .= "\t" . join(",\n\t", @stipulation) . ",\n"
					if (@stipulation and $style eq "forward");
				my @negatives = ();
				while ($trueLhs =~ s/!(\w+)\s*//) {
					push @negatives, $1;
				}
				$lhsCode .= "inSet(" . addCommas($trueLhs) .
					", Query, Rest)" ;
				my $aNegative;
				foreach $aNegative (@negatives) {
					$lhsCode .= ",\n\tnot(inSet([$aNegative], Query, _))";
				}
				$rhsCode .= emitRHS($rhs, $style, $nodeName,
					($type =~ /\+/) ? $replacementLhs : "");
			}
			$leftOutput =~ s/Query/_/ if ($lhsCode !~ /\bQuery\b/);
			$leftOutput =~ s/StartNode/_/ if ($rhsCode !~ /\bStartNode\b/);
			$lhsCode =~ s/\bRest\b/_/ if ($rhsCode !~ /\bRest\b/);
			if ($style eq "forward") {
				my $pre = $pretraceRule || $doPretrace{$nodeName};
				my $trace = !$pre && ($traceRule || $doTrace{$nodeName});
				my $post = $pre || $trace;
				my $printableLHS = $trueLhs;
				$printableLHS =~ s/\s/,/g;
				print "$leftOutput$lhsCode,\n" .
					($pre ? (
						"\n\twrite('$nodeName $printableLHS query <'), "
							. "printOut(Query), write('>\\n'),\n")
					: "") . 
					(($countAll || $doCount{$nodeName}) ?
						("\twrite('$nodeName counting $printableLHS from '), "
						. "write(FromNode), write('\\n'), \n")
						: "") .
					"$analyzeCode$rhsCode," .
					($trace ? (
						"\n\twrite('$nodeName $printableLHS query <'), "
							. "printOut(Query), write('>\\n'),\n")
					: "") . 
					($post ? (
						"\twrite('\\n\\t$nodeName $printableLHS result <'), "
							. "printOut(Result), write('>\\n'),\n")
					: "") .
					" ! .\n";
			} else { # backward
				print "$leftOutput$rhsCode,\n$lhsCode",
					(($traceRule || $doTrace{$nodeName}) ? (
						",\n\twrite('node $nodeName, line $lineNumber: " .
						"desired result is <'), printOut(Result),\n" .
						"\twrite('> query is <'), printOut(Query), " .
						" write('>\\n')")
					: "") . ".\n";
			} # backward
		} # for $style
	} # for each rule
} # emit

sub boilerPlate {
	print "\n% standard program-independent rules\n",
		"\n% memberOf(Element, List, List - Element)\n",
		"memberOf(X, [X | Y], Y) .\n",
		"memberOf(X, [Z | Y], [Z | Rest]) :- memberOf(X, Y, Rest).\n",
		"\n% inSet(SubList, List, List-SubList)\n",
		"\ninSet([], X, X) .\n",
		"inSet([X | Y], Z, W) :- nonvar(Z), memberOf(X, Z, Rst), ",
			"inSet(Y, Rst, W).\n",
		"inSet(X, Z, []) :- var(Z) , Z = X.\n",
		"\nprintOut([]) .\n",
		"printOut([X | Y]) :- write(' '), write(X), printOut(Y) .\n",
		"\nleaves :- leafNode(Query, Result, Name) ,\n",
		"\twrite(Name), write(' '), write(Query), write(' = '),\n",
		"\tprintOut(Result), write('\\n') .\n",
		"\nall :- leaves , fail .\n",
		($analyze ? "all :- isrule(X), not(usedrule(X)), \n" .
			"\twrite('The rule in line '), write(X), " .
			"write(' is never used.\\n'), fail .\n" : ""),
		"\nnot(A) :- A, !, fail .\n",
		"not(_) .\n",
		"\n% vi", "m:filetype=prolog:\n" ;
} # boilerPlate

sub normalizePattern {
	my ($lhs, $rhs) = @_;
	$lhs =~ s/\s*$//; # remove trailing blanks
	$rhs =~ s/\s*$//;
	$lhs =~ s/\|/\\s*\\|/; # escape the bar
	$lhs =~ s/\^/\\^/; # escape the caret
	$lhs =~ s/\+/\\+/; # escape the plus
	# $rhs .= '|' if ($lhs =~ /\|$/ and $rhs !~ /\|$/);
	$lhs =~ s/\s+/\\s\+/g;
	$lhs =~ s/\\s\+\\s\*/\\s*/g; # remove extraneous space-crossers
	$lhs =~ s/\$(\w+)\*/"((?:$classes{$1}| )*)"/eg; # if there is *, as in $letter*
	$lhs =~ s/\$(\w+)/"(" . ($classes{$1} \/\/ '') . ")"/eg; # if there is no *, as in $letter
	$lhs =~ s/\\s\+/\\s*/g; # after a *, don't demand a space.
	# print STDERR "lhs is $lhs; rhs is $rhs\n";
	return($lhs, $rhs);
} # normalizePattern

sub makeSandhi {
	return unless (@sandhi) or (@alternative);
	$ARGV[0] = "/tmp/katr" unless defined($ARGV[0]);
	my $sandhiFile = "$ARGV[0].sandhi.pl";
	open SANDHI, ">:utf8", $sandhiFile or die("Can't write $sandhiFile");
	use utf8;
	print SANDHI '#!/usr/bin/perl -w
use strict;
use utf8;
binmode STDIN, ":utf8";
binmode STDOUT, ":utf8";
use utf8;
while (my $line = <STDIN>) {
	chomp $line;
	if ($line !~ /(.*)=(.*)/) {
		print "$line\n";
		next;
	}
	my ($first, $rest) = ($1, $2);
	# language-specific Sandhi rules
'; # initial boilerplate
	for my $rule (@sandhi) {
		$rule =~ /\s*(.*)\s*=>\s*(.*)/;
		unless (defined $1) {
			print STDERR "Unintelligible Sandhi rule: $rule\n";
			next;
		}
		my ($lhs, $rhs) = ($1, $2);
		if (!defined($rhs)) {
			print STDERR "Unintelligible Sandhi rule: $rule\n";
			next;
		}
		($lhs, $rhs) = normalizePattern($lhs, $rhs);
		print SANDHI '	$rest =~ s/' . $lhs . '/' . $rhs . "/g;\n";
	} # each sandhi rule
	for my $rule (@alternative) {
		$rule =~ /\s*(.*)\s*=>\s*(.*)/;
		my ($lhs, $rhs) = ($1, $2);
		if (!defined($rhs)) {
			print STDERR "Unintelligible Sandhi rule: $rule\n";
			next;
		}
		($lhs, $rhs) = normalizePattern($lhs, $rhs);
		print SANDHI '	$rest =~ s/' . $lhs . "/ \$\& , ($rhs) /g;\n";
	}
	print SANDHI '	# end of language-specific rules
	print "$first=$rest\n";
}
'; # final boilerplate
	close SANDHI;
	chmod 0755, $sandhiFile;
} # makeSandhi;

parseFile();
boilerPlate();
makeSandhi();

# Hit [subj,sg,1,obj,sg,gen12,habitual2] = n a k o m o bet a k a
#  node_VERB([subj,sg,1,obj,sg,gen12,habitual2], Result, StartNode) .
#  node_VERB(Query, [n, a, k, o, m, o, bet, a, k, a], StartNode) .
#  backLeafNode(Query, [n, a, k, o, m, o, bet, a, k, a], StartNode) .
