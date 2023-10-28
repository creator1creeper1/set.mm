$( $t
	htmldef "0" as "0";
	htmldef "+" as " + ";
	htmldef "=" as " = ";
	htmldef "->" as " &rarr; ";
	htmldef "(" as "(";
	htmldef "term" as "term ";
	htmldef "wff" as "wff ";
	htmldef ")" as ")";
	htmldef "|-" as " &#8866; ";
	htmldef "a" as "a";
	htmldef "b" as "b";
	htmldef "t" as "t";
	htmldef "r" as "r";
	htmldef "s" as "s";
	htmldef "P" as "P";
	htmldef "Q" as "Q";
$)

$( Declare the constant symbols we will use $)
	$c 0 + = -> ( ) term wff |- $.
$( Declare the metavariables we will use $)
	$v a b t r s P Q $.
$( Specify properties of the metavariables $)
	ta $f term a $.
	tb $f term b $.
	tt $f term t $.
	tr $f term r $.
	ts $f term s $.
	wp $f wff P $.
	wq $f wff Q $.
$( Define "term" and "wff" $)
	tze $a term 0 $.
	tpl $a term ( t + r ) $.
	weq $a wff t = r $.
	wim $a wff ( P -> Q ) $.
$( State the axioms $)
	a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
	a2 $a |- ( t + 0 ) = t $.
$( Define the modus ponens inference rule $)
	${
		min $e |- P $.
		maj $e |- ( P -> Q ) $.
		mp $a |- Q $.
	$}
$( Prove a theorem $)
	th1 $p |- t = t $=
	$( Here is its proof: $)
		tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
		tt weq tt tze tpl tt weq tt tt weq wim tt a2
		tt tze tpl tt tt a1 mp mp
	$.
$( Theorem 2: (t + 0) = (t + 0) $)
	th2 $p |- ( t + 0 ) = ( t + 0 ) $=
		tt tze tpl th1
	$.

$( Theorem 3: t = (t + 0) $)
	th3 $p |- t = ( t + 0 ) $=
		tt tze tpl tt tze tpl weq
		tt tt tze tpl weq
		tt th2
			tt tze tpl tt weq
				tt tze tpl tt tze tpl weq
				tt tt tze tpl weq
			wim
			tt a2
			tt tze tpl tt tt tze tpl a1
		mp
	mp
	$.

${
	assume $e |- a = b $.
	$( Symmetry: (a = b) -> (b = a) $)
	thsym $p |- b = a $=
		ta ta weq
		tb ta weq
		ta th1
			ta tb weq
			ta ta weq tb ta weq wim
			assume
			ta tb ta a1
		mp
	mp
	$.
$}
