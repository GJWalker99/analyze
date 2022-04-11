#!/usr/bin/perl -T
# The -T flag forces checking of tainted values, for security.

# CGI-bin script to analyze principal parts.

use CGI qw/:standard -debug/;
# use_named_parameters(1);
use strict;
use Encode;

# initialized constants
my $tmpFile = "/tmp/principalParts$$";
$ENV{'PATH'} = '/bin:/usr/bin'; # for security
my $Debug = 0;
$| = 1; # flush output
my $analyzeProgram = "/homes/raphael/cs/links/pp/src/computeAll.pl";
# $smallAnalyzeProgram = "/homes/raphael/cs/links/pp/src/computeAllSmall.pl";
my $makeKATRprogram = "/homes/raphael/cs/links/r/parseKATR.pl";
my $condenseProgram = "/homes/raphael/cs/links/r/condense.pl";
my $makeTableprogram = "/homes/raphael/cs/links/pp/src/katr2cgi.pl";
my $alignProgram = "/homes/raphael/cs/links/pp/src/align.pl";
my $compareProgram = "/homes/raphael/cs/links/pp/src/compare.pl";
my $reduceProgram = "/homes/raphael/cs/links/pp/src/reducePlat.pl";
my $fastMachine = "zon"; # others that work in 64 bits: vio

if ($Debug) {
	print header(-expires=>'+1m', -charset=>'UTF-8', -expires=>'-1d');
	# print "unparsed form: $form<p>\n";
}

# parameters
my $chartText;
if (param('chart') ne "") {
	my $InFile = param('chart');
	$/ = undef; # read file all at one gulp
	binmode $InFile, "utf8";
	$chartText = <$InFile>;
} elsif (param('chartData') ne '') {
	$chartText = decode("utf-8", param('chartData'), Encode::FB_DEFAULT);
}
my $Text;
if (param('File') ne "") {
	$/ = undef; # read file all at one gulp
	my $InFile = param('File');
	binmode $InFile, "utf8";
	$Text = <$InFile>;

} else {
	$Text = param('Text');
	$Text = decode("utf-8", $Text, Encode::FB_DEFAULT);
}
my $check = param('check');
my $truthText;
if ($check) {
	if (param('truth') ne "") {
		my $InFile = param('truth');
		binmode $InFile, "utf8";
		$/ = undef; # read file all at one gulp
		$truthText = <$InFile>;
		close $InFile;
	} else {
		$check = 0; # can't compare if there is no file to compare to.
	}
} 
my $grouping = param('grouping');
my $center = param('center');
my $static = param('static');
my $adaptive = param('adaptive');
my $dynamic = param('dynamic');
my $expand = param('expand');
my $referral = param('referral');
my $katr = param('katr');
my $katrPretty = param('katrPretty');
my $latin = param('latin');
my $quick = param('quickStatic');
my $limit = param('limit');
my $cpred = param('cpred');
my $fpred = param('fpred');
my $emptyPredictor = param('emptyPred');
my $predictiveness = param('predictiveness');
my $stems = param('stems');
my $stratify = param('stratify');
my $verbose = param('verbose');
my $signature = param('signature');
my $forceMPS = param('forceMPS');
my $keys = param('keys');
my $MPSfilter = param('MPSfilter');
my $outputFilter = param('outputFilter');
my $MPSentropy = param('MPSentropy');
my $ConjEntropy = param('ConjEntropy');
my $entropyWeight = param('entropyWeight');
my $entropyByDuplicates = param('entropyByDuplicates');
my $showFragment = param('showFragment');
binmode STDOUT, "utf8";

print header(-type=>'text/html', -charset=>'UTF-8') . "\n" .
	start_html(
		'-title'=>'Principal parts',
		'-encoding' => 'UTF-8',
		-head=>Link({-rel=>'icon', -href=>'kentucky_wildcats.ico'}),
		) .
	"<h1>Principal-part analysis</h1>\n
	<p>If you use results from this tool, please acknowledge its creators:
	Raphael Finkel and Gregory Stump at the University of Kentucky.  Send
	suggestions and comments to <a href='mailto:raphael\@cs.uky.edu'>Raphael
	Finkel</a>.</p> <pre style='font-family:monospace;'>\n";

# convert text if necessary
$Text =~ s/^\x{FEFF}//; # byte-order mark (BOM)
$Text =~ s/&#(\d+);/chr($1)/ge; # convert unicode input form.
if ($latin) {
	$Text = decode("iso-8859-1", $Text, Encode::FB_DEFAULT);
} else {
}

# run reducer
if (defined($chartText)) {
	open TMPFILE, ">", "$tmpFile.true" or die("Can't write to $tmpFile.true\n");
	binmode TMPFILE, "utf8";
	print TMPFILE $chartText;
	close TMPFILE;	
	open CHART, "/homes/raphael/bin/within 10 $reduceProgram $tmpFile.true |";
	binmode CHART, "utf8";
	$/ = undef; # read file all at one gulp
	my $plat = <CHART>;
	close CHART;
	$plat =~ s/%.*//;
	print $plat . end_html() . "\n";
	unlink "$tmpFile.true";
	exit 0;
} # defined chartText

# if ($Debug) {print "Text is $Text.<p>\n"; exit(0)}

open TMPFILE, ">", "$tmpFile.data"
	or die("Can't write to $tmpFile.data");
binmode TMPFILE, "utf8";
print TMPFILE $Text;
close TMPFILE;

# establish options to the analyze program
my $options = '';
$options .= "e" if $expand;
$options .= "r" if $referral;
$options .= "g" if $grouping;
$options .= "n" if $center;
$options .= "s" if $static;
$options .= "a" if $adaptive;
$options .= "d" if $dynamic;
$options .= "k" if $katr or $katrPretty;
$options .= "q" if $quick;
$options .= "p" if $cpred;
$options .= "P" if $fpred;
$options .= "y" if $emptyPredictor;
$options .= "x" if $stems;
$options .= "b" if $signature;
$options .= "j" if $stratify;
$options .= "i" if $predictiveness;
$options .= "v" if $verbose;
$options .= "o" if $MPSentropy;
$options .= "w" if $ConjEntropy;
$options .= "u" if $showFragment;
$options .= " -m $limit " if $limit != 4;
$options .= " -M $forceMPS " if $forceMPS;
$options .= " -R \"$keys\" " if $keys ne "";
$options .= " -S \"$outputFilter\" " if $outputFilter ne "";
$options .= " -A \"$MPSfilter\" " if $MPSfilter ne "";
$options .= " -O \"$entropyWeight\" " if $entropyWeight ne "";
$options = '-' . $options if length($options) and $options !~ /^ /;

$options =~ /(.*)/; # untaint options
$options = $1;

print "running $analyzeProgram $options $tmpFile\n" if ($Debug);
my $result;
my $remote = remote_host();
if ($remote =~ /(^128\.163|uky.edu$|^10\.163\.|^86\.188.\111|^144\.32\.109)/ and !$check) { # no time limit, run on $fastMachine
	# 86.188.111.197 is Dunstan Brown
	# 144.32.109.254 is Dunstan Brown
	# print "Privileged user: no time limit, but be patient\n";
	# $| = 1;
	system("scp $tmpFile.data $fastMachine:$tmpFile.data");
	$options =~ s/"/\\"/g; # to preserve quotes across an ssh invocation
	$result .= decode("utf-8",
		`ssh $fastMachine $analyzeProgram $options $tmpFile 2>&1`,
		Encode::FB_DEFAULT);
	system("ssh $fastMachine /bin/rm -rf $tmpFile.data");
	if ($katr or $katrPretty) {
		system("scp $fastMachine:$tmpFile'*' /tmp");
		system("ssh $fastMachine /bin/rm -rf $tmpFile'*'");
	}
} else {
	$result = decode("utf-8",
		`/homes/raphael/bin/within 60 $analyzeProgram $options $tmpFile 2>&1`,
		Encode::FB_DEFAULT);
	unlink "$tmpFile.data";
}
$result =~ s/Data file .*//; # no need to name the file

print $result .  "</pre>\n";
if ($katr) {
	if (-r "$tmpFile.katr") {
		print "<h1>Surface forms</h1>\n";
		$result = decode("utf-8",
			`$makeKATRprogram $tmpFile < $tmpFile.katr > $tmpFile.katr.pro`,
			Encode::FB_DEFAULT);
		if ($result =~ /\w/) { # some sort of error
			print "Failure: $result\n";
			unlink "$tmpFile.katr";
		} else {
			system("echo end_of_file . | " .
				"gprolog --init-goal \"['$tmpFile.katr.pro']\" --query-goal all |" .
				"$tmpFile.sand.pl >" .
				"$tmpFile.out");
			open RESULT, "$condenseProgram $tmpFile.out fold 90 |";
			binmode RESULT, "utf8";
			$/ = undef;
			$result = <RESULT>;
			close RESULT;
			$result =~ s/\| \?- all\.\s*\n//;
			print "<pre style='font-family:monospace;'>\n$result</pre>\n";
		}
		if ($check) { # check correctness of output
			# print "checking; truth is <pre>$truthText</pre>\n";
			open COMPUTED, ">$tmpFile.computed"; binmode COMPUTED, "utf8";
			print COMPUTED $result;
			close COMPUTED;
			open TRUTH, ">$tmpFile.truth"; binmode TRUTH, "utf8";
			print TRUTH $truthText;
			close TRUTH;
			open COMPARE, "$compareProgram $tmpFile.computed $tmpFile.truth 2>&1 |";
			binmode COMPARE, "utf8";
			$/ = undef;
			my $comparison = <COMPARE>;
			close COMPARE;
			print "<h2>Comparison</h2>";
			if ($comparison =~ /\S/) {
				print "<pre style='font-family:monospace;'>$comparison</pre>\n";
			} else {
				print "The theory matches the provided paradigm.\n";
			}
		} # check correctness of output
	} else {
		print "No surface-form output because of errors\n";
	}
} # if $katr
if ($katrPretty) {
	if (-r "$tmpFile.katr") {
		print "<h1>Table of surface forms</h1>\n";
		$result = decode("utf-8",
			`$makeKATRprogram $tmpFile < $tmpFile.katr > $tmpFile.katr.pro`,
			Encode::FB_DEFAULT);
		if ($result =~ /\w/) { # some sort of error
			print "Failure: $result\n";
		} else {
			system("echo end_of_file . | " .
				"gprolog --init-goal \"['$tmpFile.katr.pro']\" --query-goal all |" .
				"$tmpFile.sand.pl >" .
				"$tmpFile.out");
			system("$makeTableprogram < $tmpFile.out");
		}
	} else {
		print "No table output because of errors\n";
	}
} # if $katrPretty

if ($stems) {
	$result = decode("utf-8",
		`$alignProgram < $tmpFile-stems.data`,
		Encode::FB_DEFAULT);
	print "<h1>Paradigm of stem referrals</h1>
		<pre style='font-family:monospace;'>$result</pre>\n";
} # if $stems
my $files = join(' ', glob("$tmpFile.*"));
$files =~ /(.*)/; # untaint
$files = $1;
# print "$tmpFile: $files</br>\n";
unlink split(/\s/, $files);
print end_html() . "\n";


exit 0;
# /var/log/apache2/suexec.log
