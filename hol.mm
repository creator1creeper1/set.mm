$( hol.mm  7-Oct-2014 $)

$(
                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/

Mario Carneiro - email: di.gama at gmail.com

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Foundations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for lambda calculus. $)
  $c var $.   $( Typecode for variables (syntax) $)
  $c type $.  $( Typecode for types (syntax) $)
  $c term $.  $( Typecode for terms (syntax) $)
  $c |- $.    $( Typecode for theorems (logical) $)
  $c : $.     $( Typehood indicator $)
  $c . $.     $( Separator $)
  $c |= $.    $( Context separator $)
  $c bool $.     $( Boolean type $)
  $c ind $.   $( 'Individual' type $)
  $c -> $.    $( Function type $)
  $c ( $.     $( Open parenthesis $)
  $c ) $.     $( Close parenthesis $)
  $c , $.     $( Context comma $)
  $c \ $.     $( Lambda expression $)
  $c = $.     $( Equality term $)
  $c T. $.    $( Truth term $)
  $c [ $.     $( Infix operator $)
  $c ] $.     $( Infix operator $)

  $v al $.  $( Greek alpha $)
  $v be $.  $( Greek beta $)
  $v ga $.  $( Greek gamma $)
  $v de $.  $( Greek delta $)

  $v x y z f g p q $.  $( Bound variables $)
  $v A B C F R S T $.  $( Term variables $)

  $( $j syntax 'var' 'type' 'term'; bound 'var'; $)

  $( Let variable ` al ` be a type. $)
  hal $f type al $.
  $( Let variable ` be ` be a type. $)
  hbe $f type be $.
  $( Let variable ` ga ` be a type. $)
  hga $f type ga $.
  $( Let variable ` de ` be a type. $)
  hde $f type de $.

  $( Let variable ` x ` be a var. $)
  vx $f var x $.
  $( Let variable ` y ` be a var. $)
  vy $f var y $.
  $( Let variable ` z ` be a var. $)
  vz $f var z $.
  $( Let variable ` f ` be a var. $)
  vf $f var f $.
  $( Let variable ` g ` be a var. $)
  vg $f var g $.
  $( Let variable ` p ` be a var. $)
  vp $f var p $.
  $( Let variable ` q ` be a var. $)
  vq $f var q $.

  $( Let variable ` A ` be a term. $)
  ta $f term A $.
  $( Let variable ` B ` be a term. $)
  tb $f term B $.
  $( Let variable ` C ` be a term. $)
  tc $f term C $.
  $( Let variable ` F ` be a term. $)
  tf $f term F $.
  $( Let variable ` R ` be a term. $)
  tr $f term R $.
  $( Let variable ` S ` be a term. $)
  ts $f term S $.
  $( Let variable ` T ` be a term. $)
  tt $f term T $.

  $( A var is a term. $)
  tv $a term x : al $.

  $( The type of all functions from type ` al ` to type ` be ` . $)
  ht $a type ( al -> be ) $.
  $( The type of booleans (true and false). $)
  hb $a type bool $.
  $( The type of individuals. $)
  hi $a type ind $.

  $( A combination (function application). $)
  kc $a term ( F T ) $.
  $( A lambda abstraction. $)
  kl $a term \ x : al . T $.
  $( The equality term. $)
  ke $a term = $.
  $( Truth term. $)
  kt $a term T. $.
  $( Infix operator. $)
  kbr $a term [ A F B ] $.
  $( Context operator. $)
  kct $a term ( A , B ) $.

  $c wff $.  $( Not used; for mmj2 compatibility $)

  $( $j syntax 'wff'; syntax '|-' as 'wff'; $)

  $( Internal axiom for mmj2 use. $)
  wffMMJ2 $a wff A |= B $.

  $( Internal axiom for mmj2 use. $)
  wffMMJ2t $a wff A : al $.

  ${
    idi.1 $e |- R |= A $.
    $( The identity inference.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    idi $p |- R |= A $=
      (  ) C $.
  $}

  ${
    idt.1 $e |- A : al $.
    $( The identity inference.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    idt $p |- A : al $=
      (  ) C $.
  $}

  ${
    ax-syl.1 $e |- R |= S $.
    ax-syl.2 $e |- S |= T $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-syl $a |- R |= T $.

    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    syl $p |- R |= T $=
      ( ax-syl ) ABCDEF $.
  $}

  ${
    ax-jca.1 $e |- R |= S $.
    ax-jca.2 $e |- R |= T $.
    $( Join common antecedents.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-jca $a |- R |= ( S , T ) $.

    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    jca $p |- R |= ( S , T ) $=
      ( ax-jca ) ABCDEF $.
  $}

  ${
    syl2anc.1 $e |- R |= S $.
    syl2anc.2 $e |- R |= T $.
    syl2anc.3 $e |- ( S , T ) |= A $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
    syl2anc $p |- R |= A $=
      ( kct jca syl ) BCDHABCDEFIGJ $.
  $}

  ${
    ax-simpl.1 $e |- R : bool $.
    ax-simpl.2 $e |- S : bool $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-simpl $a |- ( R , S ) |= R $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-simpr $a |- ( R , S ) |= S $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    simpl $p |- ( R , S ) |= R $=
      ( ax-simpl ) ABCDE $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    simpr $p |- ( R , S ) |= S $=
      ( ax-simpr ) ABCDE $.
  $}

  ${
    ax-id.1 $e |- R : bool $.
    $( The identity inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-id $a |- R |= R $.

    $( The identity inference.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
    id $p |- R |= R $=
      ( ax-id ) ABC $.
  $}

  ${
    ax-trud.1 $e |- R : bool $.
    $( Deduction form of ~ tru .  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-trud $a |- R |= T. $.

    $( Deduction form of ~ tru .  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    trud $p |- R |= T. $=
      ( ax-trud ) ABC $.

    ax-a1i.2 $e |- T. |= A $.
    $( Change an empty context into any context.  (Contributed by Mario
       Carneiro, 7-Oct-2014.) $)
    a1i $p |- R |= A $=
      ( kt ax-trud syl ) BEABCFDG $.
  $}

  ${
    ax-cb.1 $e |- R |= A $.
    $( A context has type boolean.

       This and the next few axioms are not strictly necessary, and are
       conservative on any theorem for which every variable has a specified
       type, but by adding this axiom we can save some typehood hypotheses in
       many theorems.  The easy way to see that this axiom is conservative is
       to note that every axiom and inference rule that constructs a theorem of
       the form ` R |= A ` where ` R ` and ` A ` are type variables, also
       ensures that ` R : bool ` and ` A : bool ` .  Thus it is impossible to
       prove any theorem ` |- R |= A ` unless both ` |- R : bool ` and
       ` |- A : bool ` had been previously derived, so it is conservative to
       deduce ` |- R : bool ` from ` |- R |= A ` .  The same remark applies to
       the construction of the theorem ` ( A , B ) : bool ` - there is only one
       rule that creates a formula of this type, namely ~ wct , and it requires
       that ` A : bool ` and ` B : bool ` be previously established, so it is
       safe to reverse the process in ~ wctl and ~ wctr .  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-cb1 $a |- R : bool $.

    $( A theorem has type boolean.  (This axiom is unnecessary; see ~ ax-cb1 .)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-cb2 $a |- A : bool $.
  $}

  ${
    wctl.1 $e |- ( S , T ) : bool $.
    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  Prefer ~ wctl .  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wctl $a |- S : bool $.

    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  Prefer ~ wctr .  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wctr $a |- T : bool $.

    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wctl $p |- S : bool $=
      ( ax-wctl ) ABCD $.

    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wctr $p |- T : bool $=
      ( ax-wctr ) ABCD $.
  $}

  ${
    mpdan.1 $e |- R |= S $.
    mpdan.2 $e |- ( R , S ) |= T $.
    $( Modus ponens deduction.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    mpdan $p |- R |= T $=
      ( ax-cb1 id syl2anc ) CAABABADFGDEH $.
  $}

  ${
    syldan.1 $e |- ( R , S ) |= T $.
    syldan.2 $e |- ( R , T ) |= A $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    syldan $p |- ( R , S ) |= A $=
      ( kct ax-cb1 wctl wctr simpl syl2anc ) ABCGZBDBCBCDMEHZIBCNJKEFL $.
  $}

  ${
    simpld.1 $e |- R |= ( S , T ) $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    simpld $p |- R |= S $=
      ( kct ax-cb2 wctl wctr simpl syl ) ABCEZBDBCBCKADFZGBCLHIJ $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    simprd $p |- R |= T $=
      ( kct ax-cb2 wctl wctr simpr syl ) ABCEZCDBCBCKADFZGBCLHIJ $.
  $}

  ${
    trul.1 $e |- ( T. , R ) |= S $.
    $( Deduction form of ~ tru .  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    trul $p |- R |= S $=
      ( kt kct ax-cb1 wctr trud id syl2anc ) BADAADABDAECFGZHAKICJ $.
  $}

  $( The equality function has type ` al -> al -> bool ` , i.e. it is
     polymorphic over all types, but the left and right type must agree.
     (New usage is discouraged.)  (Contributed by Mario Carneiro,
     7-Oct-2014.) $)
  ax-weq $a |- = : ( al -> ( al -> bool ) ) $.

  $( The equality function has type ` al -> al -> bool ` , i.e. it is
     polymorphic over all types, but the left and right type must agree.
     (Contributed by Mario Carneiro, 7-Oct-2014.) $)
  weq $p |- = : ( al -> ( al -> bool ) ) $=
    ( ax-weq ) AB $.

  ${
    ax-refl.1 $e |- A : al $.
    $( Reflexivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-refl $a |- T. |= ( ( = A ) A ) $.
  $}

  $( Truth type.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
  wtru $p |- T. : bool $=
    ( ke kc kt hb ht weq ax-refl ax-cb1 ) AABABCDDDEEADFGH $.

  $( Tautology is provable.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
  tru $p |- T. |= T. $=
    ( kt wtru id ) ABC $.

  ${
    ax-eqmp.1 $e |- R |= A $.
    ax-eqmp.2 $e |- R |= ( ( = A ) B ) $.
    $( Modus ponens for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqmp $a |- R |= B $.
  $}

  ${
    ax-ded.1 $e |- ( R , S ) |= T $.
    ax-ded.2 $e |- ( R , T ) |= S $.
    $( Deduction theorem for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-ded $a |- R |= ( ( = S ) T ) $.
  $}

  ${
    wct.1 $e |- S : bool $.
    wct.2 $e |- T : bool $.
    $( The type of a context.  (Contributed by Mario Carneiro, 7-Oct-2014.)
       (New usage is discouraged.) $)
    ax-wct $a |- ( S , T ) : bool $.

    $( The type of a context.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
    wct $p |- ( S , T ) : bool $=
      ( ax-wct ) ABCDE $.
  $}

  ${
    wc.1 $e |- F : ( al -> be ) $.
    wc.2 $e |- T : al $.
    $( The type of a combination.  (Contributed by Mario Carneiro, 7-Oct-2014.)
       (New usage is discouraged.) $)
    ax-wc $a |- ( F T ) : be $.

    $( The type of a combination.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    wc $p |- ( F T ) : be $=
      ( ax-wc ) ABCDEFG $.
  $}

  ${
    ax-ceq.1 $e |- F : ( al -> be ) $.
    ax-ceq.2 $e |- T : ( al -> be ) $.
    ax-ceq.3 $e |- A : al $.
    ax-ceq.4 $e |- B : al $.
    $( Equality theorem for combination.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-ceq $a |- ( ( ( = F ) T ) , ( ( = A ) B ) ) |=
      ( ( = ( F A ) ) ( T B ) ) $.
  $}

  ${
    eqcomx.1 $e |- A : al $.
    eqcomx.2 $e |- B : al $.
    eqcomx.3 $e |- R |= ( ( = A ) B ) $.
    $( Commutativity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    eqcomx $p |- R |= ( ( = B ) A ) $=
      ( ke kc ax-cb1 ax-refl a1i hb ht weq ax-ceq syl2anc wc ax-eqmp ) HBIZBIZH
      CIZBIZDUADTCIZDGJZABEKLZHUAIUCIDHTIUBIZUAUGDHHIHIZUDUHDUEAAMNZNHAOZKLGAUI
      BCHHUJUJEFPQUFAMBBTUBAUIHBUJERAUIHCUJFREEPQS $.
  $}

  ${
    mpbirx.1 $e |- B : bool $.
    mpbirx.2 $e |- R |= A $.
    mpbirx.3 $e |- R |= ( ( = B ) A ) $.
    $( Deduction from equality inference.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    mpbirx $p |- R |= B $=
      ( hb ax-cb2 eqcomx ax-eqmp ) ABCEGBACDACEHFIJ $.
  $}

  ${
    ancoms.1 $e |- ( R , S ) |= T $.
    $( Swap the two elements of a context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ancoms $p |- ( S , R ) |= T $=
      ( kct ax-cb1 wctr wctl simpr simpl syl2anc ) CBAEABBAABCABEDFZGZABLHZIBAM
      NJDK $.
  $}

  ${
    adantr.1 $e |- R |= T $.
    adantr.2 $e |- S : bool $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    adantr $p |- ( R , S ) |= T $=
      ( kct ax-cb1 simpl syl ) ABFACABCADGEHDI $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    adantl $p |- ( S , R ) |= T $=
      ( adantr ancoms ) ABCABCDEFG $.
  $}

  ${
    ct1.1 $e |- R |= S $.
    ct1.2 $e |- T : bool $.
    $( Introduce a right conjunct.  (Contributed by Mario Carneiro,
       30-Sep-2023.) $)
    ct1 $p |- ( R , T ) |= ( S , T ) $=
      ( kct adantr ax-cb1 simpr jca ) ACFBCACBDEGACBADHEIJ $.

    $( Introduce a left conjunct.  (Contributed by Mario Carneiro,
       30-Sep-2023.) $)
    ct2 $p |- ( T , R ) |= ( T , S ) $=
      ( kct ax-cb1 simpl adantl jca ) CAFCBCAEBADGHACBDEIJ $.
  $}

  ${
    sylan.1 $e |- R |= S $.
    sylan.2 $e |- ( S , T ) |= A $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    sylan $p |- ( R , T ) |= A $=
      ( kct ax-cb1 wctr adantr simpr syl2anc ) ABDGCDBDCECDACDGFHIZJBDCBEHMKFL
      $.
  $}

  ${
    an32s.1 $e |- ( ( R , S ) , T ) |= A $.
    $( Commutation identity for context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    an32s $p |- ( ( R , T ) , S ) |= A $=
      ( kct ax-cb1 wctl wctr simpl ct1 simpr adantr syl2anc ) ABDFZCFBCFZDOBCBD
      BCPDAPDFEGZHZHZPDQIZJBCRIZKOCDBDSTLUAMEN $.

    $( Associativity for context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    anasss $p |- ( R , ( S , T ) ) |= A $=
      ( kct ax-cb1 wctl id ancoms sylan an32s ) CDFBAACBDACBFBCFZDBCMMMDAMDFEGH
      IJEKLJ $.
  $}

  ${
    anassrs.1 $e |- ( R , ( S , T ) ) |= A $.
    $( Associativity for context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    anassrs $p |- ( ( R , S ) , T ) |= A $=
      ( kct ax-cb1 wctl wctr simpl adantr simpr ct1 syl2anc ) ABCFZDFBCDFZODBBC
      BPABPFEGZHZCDBPQIZHZJCDSIZKOCDBCRTLUAMEN $.
  $}

  $( The type of a typed variable.  (New usage is discouraged.)  (Contributed
     by Mario Carneiro, 8-Oct-2014.) $)
  ax-wv $a |- x : al : al $.

  $( The type of a typed variable.  (Contributed by Mario Carneiro,
     8-Oct-2014.) $)
  wv $p |- x : al : al $=
    ( ax-wv ) ABC $.

  ${
    wl.1 $e |- T : be $.
    $( The type of a lambda abstraction.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wl $a |- \ x : al . T : ( al -> be ) $.

    $( The type of a lambda abstraction.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    wl $p |- \ x : al . T : ( al -> be ) $=
      ( ax-wl ) ABCDEF $.
  $}

  ${
    ax-beta.1 $e |- A : be $.
    $( Axiom of beta-substitution.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-beta $a |- T. |= ( ( = ( \ x : al . A x : al ) ) A ) $.

    ax-distrc.2 $e |- B : al $.
    ax-distrc.3 $e |- F : ( be -> ga ) $.
    $( Distribution of combination over substitution.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    ax-distrc $a |- T. |= ( ( = ( \ x : al . ( F A ) B ) )
      ( ( \ x : al . F B ) ( \ x : al . A B ) ) ) $.
  $}

  ${
    $d x R $.
    ax-leq.1 $e |- A : be $.
    ax-leq.2 $e |- B : be $.
    ax-leq.3 $e |- R |= ( ( = A ) B ) $.
    $( Equality theorem for abstraction.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-leq $a |- R |= ( ( = \ x : al . A ) \ x : al . B ) $.
  $}

  ${
    $d x y $.  $d y B $.
    ax-distrl.1 $e |- A : ga $.
    ax-distrl.2 $e |- B : al $.
    $( Distribution of lambda abstraction over substitution.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-distrl $a |- T. |=
      ( ( = ( \ x : al . \ y : be . A B ) ) \ y : be . ( \ x : al . A B ) ) $.
  $}

  ${
    wov.1 $e |- F : ( al -> ( be -> ga ) ) $.
    wov.2 $e |- A : al $.
    wov.3 $e |- B : be $.
    $( Type of an infix operator.  (New usage is discouraged.)  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-wov $a |- [ A F B ] : ga $.

    $( Type of an infix operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    wov $p |- [ A F B ] : ga $=
      ( ax-wov ) ABCDEFGHIJ $.

    $( Infix operator.  This is a simple metamath way of cleaning up the syntax
       of all these infix operators to make them a bit more readable than the
       curried representation.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    df-ov $a |- T. |= ( ( = [ A F B ] ) ( ( F A ) B ) ) $.
  $}

  ${
    dfov1.1 $e |- F : ( al -> ( be -> bool ) ) $.
    dfov1.2 $e |- A : al $.
    dfov1.3 $e |- B : be $.
    ${
      dfov1.4 $e |- R |= [ A F B ] $.
      $( Forward direction of ~ df-ov .  (Contributed by Mario Carneiro,
         8-Oct-2014.) $)
      dfov1 $p |- R |= ( ( F A ) B ) $=
        ( kbr kc ke ax-cb1 hb df-ov a1i ax-eqmp ) CDEKZECLDLZFJMSLTLFSFJNABOCDE
        GHIPQR $.
    $}

    dfov2.4 $e |- R |= ( ( F A ) B ) $.
    $( Reverse direction of ~ df-ov .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    dfov2 $p |- R |= [ A F B ] $=
      ( kc kbr hb wov ke ax-cb1 df-ov a1i mpbirx ) ECKDKZCDELZFABMCDEGHINJOUAKT
      KFTFJPABMCDEGHIQRS $.
  $}

  ${
    weqi.1 $e |- A : al $.
    weqi.2 $e |- B : al $.
    $( Type of an equality.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    weqi $p |- [ A = B ] : bool $=
      ( hb ke weq wov ) AAFBCGAHDEI $.
  $}

  ${
    eqcomi.1 $e |- A : al $.
    eqcomi.2 $e |- R |= [ A = B ] $.
    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)
       (New usage is discouraged.)  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqtypi $a |- B : al $.

    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)  (Contributed by Mario
       Carneiro, 7-Oct-2014.) $)
    eqtypi $p |- B : al $=
      ( ax-eqtypi ) ABCDEFG $.

    $( Commutativity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    eqcomi $p |- R |= [ B = A ] $=
      ( ke weq eqtypi dfov1 eqcomx dfov2 ) AACBGDAHZABCDEFIZEABCDENAABCGDMENFJK
      L $.
  $}

  ${
    eqtypri.1 $e |- A : al $.
    eqtypri.2 $e |- R |= [ B = A ] $.
    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)
       (New usage is discouraged.)  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqtypri $a |- B : al $.

    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)  (Contributed by Mario
       Carneiro, 7-Oct-2014.) $)
    eqtypri $p |- B : al $=
      ( ax-eqtypri ) ABCDEFG $.
  $}

  ${
    mpbi.1 $e |- R |= A $.
    mpbi.2 $e |- R |= [ A = B ] $.
    $( Deduction from equality inference.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    mpbi $p |- R |= B $=
      ( hb ke weq ax-cb2 eqtypi dfov1 ax-eqmp ) ABCDFFABGCFHACDIZFABCMEJEKL $.
  $}

  ${
    eqid.1 $e |- R : bool $.
    eqid.2 $e |- A : al $.
    $( Reflexivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    eqid $p |- R |= [ A = A ] $=
      ( ke weq kc ax-refl a1i dfov2 ) AABBFCAGEEFBHBHCDABEIJK $.
  $}

  ${
    ded.1 $e |- ( R , S ) |= T $.
    ded.2 $e |- ( R , T ) |= S $.
    $( Deduction theorem for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ded $p |- R |= [ S = T ] $=
      ( hb ke weq kct ax-cb2 ax-ded dfov2 ) FFBCGAFHBACIEJCABIDJABCDEKL $.
  $}

  ${
    dedi.1 $e |- S |= T $.
    dedi.2 $e |- T |= S $.
    $( Deduction theorem for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    dedi $p |- T. |= [ S = T ] $=
      ( kt wtru adantl ded ) EABAEBCFGBEADFGH $.
  $}

  ${
    eqtru.1 $e |- R |= A $.
    $( If a statement is provable, then it is equivalent to truth.
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    eqtru $p |- R |= [ T. = A ] $=
      ( kt wtru adantr kct ax-cb1 ax-cb2 wct tru a1i ded ) BDABDACEFDBAGBAABCHA
      BCIJKLM $.
  $}

  ${
    mpbir.1 $e |- R |= A $.
    mpbir.2 $e |- R |= [ B = A ] $.
    $( Deduction from equality inference.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    mpbir $p |- R |= B $=
      ( hb ax-cb2 eqtypri eqcomi mpbi ) ABCDFBACFABCACDGEHEIJ $.
  $}

  ${
    ceq12.1 $e |- F : ( al -> be ) $.
    ceq12.2 $e |- A : al $.
    ${
      ceq12.3 $e |- R |= [ F = T ] $.
      ${
        ceq12.4 $e |- R |= [ A = B ] $.
        $( Equality theorem for combination.  (Contributed by Mario Carneiro,
           7-Oct-2014.) $)
        ceq12 $p |- R |= [ ( F A ) = ( T B ) ] $=
          ( kc ke weq wc ht eqtypi dfov1 ax-ceq syl2anc dfov2 ) BBECLZGDLZMFBNA
          BECHIOABGDABPZEGFHJQZACDFIKQZOMUBLUCLFMELGLMCLDLUDUDEGMFUDNHUEJRAACDM
          FANIUFKRABCDEGHUEIUFSTUA $.
      $}

      $( Equality theorem for combination.  (Contributed by Mario Carneiro,
         7-Oct-2014.) $)
      ceq1 $p |- R |= [ ( F A ) = ( T A ) ] $=
        ( ke kbr ax-cb1 eqid ceq12 ) ABCCDEFGHIACEDFJKEILHMN $.
    $}

    ceq2.3 $e |- R |= [ A = B ] $.
    $( Equality theorem for combination.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ceq2 $p |- R |= [ ( F A ) = ( F B ) ] $=
      ( ht ke kbr ax-cb1 eqid ceq12 ) ABCDEFEGHABJEFCDKLFIMGNIO $.
  $}

  ${
    $d x R $.
    leq.1 $e |- A : be $.
    leq.2 $e |- R |= [ A = B ] $.
    $( Equality theorem for lambda abstraction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    leq $p |- R |= [ \ x : al . A = \ x : al . B ] $=
      ( ht kl ke weq wl eqtypi dfov1 ax-leq dfov2 ) ABIZRACDJACEJKFRLABCDGMABCE
      BDEFGHNZMABCDEFGSBBDEKFBLGSHOPQ $.
  $}

  ${
    beta.1 $e |- A : be $.
    $( Axiom of beta-substitution.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    beta $p |- T. |= [ ( \ x : al . A x : al ) = A ] $=
      ( kl tv kc ke kt weq wl wv wc ax-beta dfov2 ) BBACDFZACGZHDIJBKABQRABCDEL
      ACMNEABCDEOP $.
  $}

  ${
    distrc.1 $e |- F : ( be -> ga ) $.
    distrc.2 $e |- A : be $.
    distrc.3 $e |- B : al $.
    $( Distribution of combination over substitution.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    distrc $p |- T. |= [ ( \ x : al . ( F A ) B ) =
      ( ( \ x : al . F B ) ( \ x : al . A B ) ) ] $=
      ( kc kl ke kt weq wc wl ht ax-distrc dfov2 ) CCADGEKZLZFKADGLZFKZADELZFKZ
      KMNCOACUBFACDUABCGEHIPQJPBCUDUFABCRZUCFAUGDGHQJPABUEFABDEIQJPPABCDEFGIJHS
      T $.
  $}

  ${
    $d x y $.  $d y B $.
    distrl.1 $e |- A : ga $.
    distrl.2 $e |- B : al $.
    $( Distribution of lambda abstraction over substitution.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    distrl $p |- T. |=
      [ ( \ x : al . \ y : be . A B ) = \ y : be . ( \ x : al . A B ) ] $=
      ( ht kl kc ke kt weq wl wc ax-distrl dfov2 ) BCJZTADBEFKZKZGLBEADFKZGLZKM
      NTOATUBGATDUABCEFHPPIQBCEUDACUCGACDFHPIQPABCDEFGHIRS $.
  $}

  ${
    eqtri.1 $e |- A : al $.
    eqtri.2 $e |- R |= [ A = B ] $.
    eqtri.3 $e |- R |= [ B = C ] $.
    $( Transitivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    eqtri $p |- R |= [ A = C ] $=
      ( ke weq eqtypi kc dfov1 hb ht wc ceq2 mpbi dfov2 ) AABDIEAJZFACDEABCEFGK
      ZHKIBLZCLUBDLEAABCIETFUAGMANCDUBEAANOIBTFPUAHQRS $.
  $}

  ${
    3eqtr4i.1 $e |- A : al $.
    3eqtr4i.2 $e |- R |= [ A = B ] $.
    ${
      3eqtr4i.3 $e |- R |= [ S = A ] $.
      3eqtr4i.4 $e |- R |= [ T = B ] $.
      $( Transitivity of equality.  (Contributed by Mario Carneiro,
         7-Oct-2014.) $)
      3eqtr4i $p |- R |= [ S = T ] $=
        ( eqtypri eqtypi eqcomi eqtri ) AEBFDABEDGIKIABCFDGHAFCDACFDABCDGHLJKJM
        NN $.
    $}

    3eqtr3i.3 $e |- R |= [ A = S ] $.
    3eqtr3i.4 $e |- R |= [ B = T ] $.
    $( Transitivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    3eqtr3i $p |- R |= [ S = T ] $=
      ( eqcomi eqtypi 3eqtr4i ) ABCDEFGHABEDGIKACFDABCDGHLJKM $.
  $}

  ${
    oveq.1 $e |- F : ( al -> ( be -> ga ) ) $.
    oveq.2 $e |- A : al $.
    oveq.3 $e |- B : be $.
    ${
      oveq123.4 $e |- R |= [ F = S ] $.
      oveq123.5 $e |- R |= [ A = C ] $.
      oveq123.6 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq123 $p |- R |= [ [ A F B ] = [ C S T ] ] $=
        ( kc kbr wc ke ht ceq12 weq wov ax-cb1 df-ov a1i dfov2 eqtypi 3eqtr4i )
        CGDQZEQZIFQZJQZHDEGRZFJIRZBCUKEABCUAZGDKLSZMSZBCEJUKHUMURMAUQDFGHIKLNOU
        BPUBCCUOULTHCUCZABCDEGKLMUDUSTUOQULQHGITRHNUEZABCDEGKLMUFUGUHCCUPUNTHUT
        ABCFJIAUQUAGIHKNUIZADFHLOUIZBEJHMPUIZUDBCUMJAUQIFVBVCSVDSTUPQUNQHVAABCF
        JIVBVCVDUFUGUHUJ $.
    $}

    ${
      oveq1.4 $e |- R |= [ A = C ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq1 $p |- R |= [ [ A F B ] = [ C F B ] ] $=
        ( ht ke kbr ax-cb1 eqid oveq123 ) ABCDEFGHGEIJKABCMMGHDFNOHLPZIQLBEHSKQ
        R $.

      oveq12.5 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq12 $p |- R |= [ [ A F B ] = [ C F T ] ] $=
        ( ht ke kbr ax-cb1 eqid oveq123 ) ABCDEFGHGIJKLABCOOGHDFPQHMRJSMNT $.
    $}

    ${
      oveq2.4 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq2 $p |- R |= [ [ A F B ] = [ A F T ] ] $=
        ( ke kbr ax-cb1 eqid oveq12 ) ABCDEDFGHIJKADGEHMNGLOJPLQ $.
    $}

    ${
      oveq.4 $e |- R |= [ F = S ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq $p |- R |= [ [ A F B ] = [ A S B ] ] $=
        ( ke kbr ax-cb1 eqid oveq123 ) ABCDEDFGHEIJKLADGFHMNGLOZJPBEGRKPQ $.
    $}
  $}

  ${
    ax-hbl1.1 $e |- A : ga $.
    ax-hbl1.2 $e |- B : al $.
    $( ` x ` is bound in ` \ x A ` .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-hbl1 $a |- T. |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ] $.

    hbl1.3 $e |- R : bool $.
    $( Inference form of ~ ax-hbl1 .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    hbl1 $p |- R |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ] $=
      ( kl kc ke kbr ax-hbl1 a1i ) ADBDEKZKFLQMNGJABCDEFHIOP $.
  $}

  ${
    $d x A $.
    ax-17.1 $e |- A : be $.
    ax-17.2 $e |- B : al $.
    $( If ` x ` does not appear in ` A ` , then any substitution to ` A `
       yields ` A ` again, i.e. ` \ x A ` is a constant function.  (Contributed
       by Mario Carneiro, 8-Oct-2014.) $)
    ax-17 $a |- T. |= [ ( \ x : al . A B ) = A ] $.

    a17i.3 $e |- R : bool $.
    $( Inference form of ~ ax-17 .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    a17i $p |- R |= [ ( \ x : al . A B ) = A ] $=
      ( kl kc ke kbr ax-17 a1i ) ACDJEKDLMFIABCDEGHNO $.
  $}

  ${
    $d x R $.
    hbxfr.1 $e |- T : be $.
    hbxfr.2 $e |- B : al $.
    ${
      hbxfrf.3 $e |- R |= [ T = A ] $.
      hbxfrf.4 $e |- ( S , R ) |= [ ( \ x : al . A B ) = A ] $.
      $( Transfer a hypothesis builder to an equivalent expression.
         (Contributed by Mario Carneiro, 8-Oct-2014.) $)
      hbxfrf $p |- ( S , R ) |= [ ( \ x : al . T B ) = T ] $=
        ( kl kc kct eqtypi wl ke kbr adantl wc leq ceq1 ax-cb1 wctl 3eqtr4i ) B
        ACDMZENZDGFOZACHMZENZHABUGEABCDBHDFIKPQJUALFGUKUHRSABEUJFUGABCHIQJABCHD
        FIKUBUCGFUHDRSUILUDUEZTFGHDRSKULTUF $.
    $}

    hbxfr.3 $e |- R |= [ T = A ] $.
    hbxfr.4 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    $( Transfer a hypothesis builder to an equivalent expression.  (Contributed
       by Mario Carneiro, 8-Oct-2014.) $)
    hbxfr $p |- R |= [ ( \ x : al . T B ) = T ] $=
      ( kl kc ke kbr ax-cb1 id adantr hbxfrf syl2anc ) ACGLEMGNOFFFFGDNOFJPZQZU
      BABCDEFFGHIJFFACDLEMDNOKUARST $.
  $}

  ${
    $d x R $.
    hbth.1 $e |- B : al $.
    hbth.2 $e |- R |= A $.
    $( Hypothesis builder for a theorem.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    hbth $p |- R |= [ ( \ x : al . A B ) = A ] $=
      ( hb kt ax-cb2 wtru eqtru eqcomi ax-cb1 a17i hbxfr ) AHBIDECCEGJFHICEKCEG
      LMAHBIDEKFCEGNOP $.
  $}

  ${
    hbc.1 $e |- F : ( be -> ga ) $.
    hbc.2 $e |- A : be $.
    hbc.3 $e |- B : al $.
    hbc.4 $e |- R |= [ ( \ x : al . F B ) = F ] $.
    hbc.5 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    $( Hypothesis builder for combination.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    hbc $p |- R |= [ ( \ x : al . ( F A ) B ) = ( F A ) ] $=
      ( kc kl wc wl ke kbr ax-cb1 distrc a1i ht eqtypri ceq12 eqtri ) CADGENZOZ
      FNZADGOZFNZADEOFNZNZUGHACUHFACDUGBCGEIJPQKPUIUMRSHUKGRSHLTABCDEFGIJKUAUBB
      CULEUKHGABCUCZUJFAUNDGIQKPBEULHJMUDLMUEUF $.
  $}

  ${
    hbov.1 $e |- F : ( be -> ( ga -> de ) ) $.
    hbov.2 $e |- A : be $.
    hbov.3 $e |- B : al $.
    hbov.4 $e |- C : ga $.
    hbov.5 $e |- R |= [ ( \ x : al . F B ) = F ] $.
    hbov.6 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    hbov.7 $e |- R |= [ ( \ x : al . C B ) = C ] $.
    $( Hypothesis builder for binary operation.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    hbov $p |- R |= [ ( \ x : al . [ A F C ] B ) = [ A F C ] ] $=
      ( kt kbr kc kl ke ax-cb1 trud wov weq ht wc df-ov dfov2 hbc adantr hbxfrf
      wtru mpdan ) JRAEFHISZUAGTUPUBSJAEIUAGTIUBSJOUCUDADEIFTZHTZGRJUPBCDFHIKLN
      UEZMDDUPURUBRDUFUSCDUQHBCDUGZIFKLUHZNUHBCDFHIKLNUIUJJRAEURUAGTURUBSACDEHG
      UQJVANMABUTEFGIJKLMOPUKQUKUNULUMUO $.
  $}

  ${
    $d x y $.  $d y B $.  $d y R $.
    hbl.1 $e |- A : ga $.
    hbl.2 $e |- B : al $.
    hbl.3 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    $( Hypothesis builder for lambda abstraction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    hbl $p |- R |= [ ( \ x : al . \ y : be . A B ) = \ y : be . A ] $=
      ( ht kl kc wl wc ke kbr ax-cb1 distrl a1i leq eqtri ) BCLZADBEFMZMZGNZBEA
      DFMZGNZMZUEHAUDUFGAUDDUEBCEFIOOJPUGUJQRHUIFQRHKSABCDEFGIJTUABCEUIFHACUHGA
      CDFIOJPKUBUC $.
  $}

  ${
    $d x y $.  $d y B $.  $d y S $.
    ax-inst.1 $e |- R |= A $.
    ax-inst.2 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    ax-inst.3 $e |- T. |= [ ( \ x : al . S y : al ) = S ] $.
    ax-inst.4 $e |- [ x : al = C ] |= [ A = B ] $.
    ax-inst.5 $e |- [ x : al = C ] |= [ R = S ] $.
    $( Instantiate a theorem with a new term.  The second and third hypotheses
       are the HOL equivalent of set.mm "effectively not free in" predicate
       (see set.mm's ax-17, or ~ ax17m ).  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-inst $a |- S |= B $.
  $}

  ${
    $d x y R $.  $d y B $.
    insti.1 $e |- C : al $.
    insti.2 $e |- B : bool $.
    insti.3 $e |- R |= A $.
    insti.4 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    insti.5 $e |- [ x : al = C ] |= [ A = B ] $.
    $( Instantiate a theorem with a new term.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    insti $p |- R |= B $=
      ( hb tv ax-cb1 wv ax-17 ke kbr eqid ax-inst ) ABCDEFGGJKAMBGACNDGJOZACPQL
      MGABNFRSZDERSUCLOUBTUA $.
  $}

  ${
    $d y A $.  $d y B $.  $d y C $.  $d x y al $.
    clf.1 $e |- A : be $.
    clf.2 $e |- C : al $.
    clf.3 $e |- [ x : al = C ] |= [ A = B ] $.
    clf.4 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    clf.5 $e |- T. |= [ ( \ x : al . C y : al ) = C ] $.
    $( Evaluate a lambda expression.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    clf $p |- T. |= [ ( \ x : al . A C ) = B ] $=
      ( kl tv kc ke kbr kt wc hb wl eqtypi weqi ax-cb1 beta a1i wv ht a17i hbl1
      weq hbc hbov id ceq2 oveq12 insti ) ACDACEMZACNZOZEPQZURGOZFPQGRIBVBFABUR
      GABCEHUAZISZBEFUSGPQZHJUBZUCVARACFMADNZOFPQRKUDZABCEHUEUFABBTCVBVGFPRBUKZ
      VDADUGZVFABBTUHUHCPVGRVIVJVHUIAABCGVGURRVCIVJAABCEVGRHVJVHUJLULKUMBBTUTEV
      BPVEFVIABURUSVCACUGZSHABUSGURVEVCVKVEAUSGVKIUCUNUOJUPUQ $.
  $}

  ${
    $d y A $.  $d x y B $.  $d x y C $.  $d x y al $.
    cl.1 $e |- A : be $.
    cl.2 $e |- C : al $.
    cl.3 $e |- [ x : al = C ] |= [ A = B ] $.
    $( Evaluate a lambda expression.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    cl $p |- T. |= [ ( \ x : al . A C ) = B ] $=
      ( vy tv ke kbr eqtypi wv ax-17 clf ) ABCJDEFGHIABCEAJKZBDEACKFLMGINAJOZPA
      ACFRHSPQ $.
  $}

  ${
    $d x B $.  $d y C $.  $d x y S $.  $d y T $.  $d x al $.  $d y be $.
    ovl.1 $e |- A : ga $.
    ovl.2 $e |- S : al $.
    ovl.3 $e |- T : be $.
    ovl.4 $e |- [ x : al = S ] |= [ A = B ] $.
    ovl.5 $e |- [ y : be = T ] |= [ B = C ] $.
    $( Evaluate a lambda expression in a binary operation.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ovl $p |- T. |= [ [ S \ x : al . \ y : be . A T ] = C ] $=
      ( kl kbr kc kt ke ht wl wov weq wc wtru df-ov a1i dfov2 distrl ceq1 eqtri
      tv wv weqi cl ) CIJADBEFPZPZQZBEADFPZIRZPZJRZHSABCIJURABCUAZDUQBCEFKUBUBZ
      LMUCZCUSURIRZJRZVCSVFCCUSVHTSCUDVFBCVGJAVDURIVELUEZMUETUSRVHRSUFABCIJURVE
      LMUGUHUIBCJVGSVBVIMVGVBTQSUFABCDEFIKLUJUHUKULBCEVAHJACUTIACDFKUBLUEZMCVAG
      HBEUMZJTQZVJVAGTQVLBVKJBEUNMUOACDFGIKLNUPUHOULUPUL $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                 Add propositional calculus definitions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c F. $.   $( Contradiction term $)
  $c /\ $.   $( Conjunction term $)
  $c ~ $.    $( Negation term $)
  $c ==> $.  $( Implication term $)
  $c ! $.    $( For all term $)
  $c ? $.    $( There exists term $)
  $c \/ $.   $( Disjunction term $)
  $c ?! $.   $( There exists unique term $)

  $( Contradiction term. $)
  tfal $a term F. $.
  $( Conjunction term. $)
  tan $a term /\ $.
  $( Negation term. $)
  tne $a term ~ $.
  $( Implication term. $)
  tim $a term ==> $.
  $( For all term. $)
  tal $a term ! $.
  $( There exists term. $)
  tex $a term ? $.
  $( Disjunction term. $)
  tor $a term \/ $.
  $( There exists unique term. $)
  teu $a term ?! $.

  ${
    $d f p q x y $.
    $( Define the for all operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-al $a |- T. |=
      [ ! = \ p : ( al -> bool ) . [ p : ( al -> bool ) = \ x : al . T. ] ] $.

    $( Define the constant false.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-fal $a |- T. |= [ F. = ( ! \ p : bool . p : bool ) ] $.

    $( Define the 'and' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-an $a |- T. |=
        [ /\ = \ p : bool . \ q : bool . [ \ f : ( bool -> ( bool -> bool ) ) .
        [ p : bool f : ( bool -> ( bool -> bool ) ) q : bool ] =
          \ f : ( bool -> ( bool -> bool ) ) .
            [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ] $.

    $( Define the implication operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-im $a |- T. |= [ ==> =
      \ p : bool . \ q : bool . [ [ p : bool /\ q : bool ] = p : bool ] ] $.

    $( Define the negation operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-not $a |- T. |= [ ~ = \ p : bool . [ p : bool ==> F. ] ] $.

    $( Define the existence operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-ex $a |- T. |= [ ? = \ p : ( al -> bool ) .
      ( ! \ q : bool . [ ( ! \ x : al .
        [ ( p : ( al -> bool ) x : al ) ==> q : bool ] ) ==> q : bool ] ) ] $.

    $( Define the 'or' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-or $a |- T. |= [ \/ = \ p : bool . \ q : bool . ( ! \ x : bool .
        [ [ p : bool ==> x : bool ] ==>
          [ [ q : bool ==> x : bool ] ==> x : bool ] ] ) ] $.

    $( Define the 'exists unique' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-eu $a |- T. |= [ ?! = \ p : ( al -> bool ) .
      ( ? \ y : al . ( ! \ x : al .
        [ ( p : ( al -> bool ) x : al ) = [ x : al = y : al ] ] ) ) ] $.
  $}

  ${
    $d f p q x y $.
    $( For all type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wal $p |- ! : ( ( al -> bool ) -> bool ) $=
      ( vp vx hb ht tv kt kl ke kbr tal wv wtru wl weqi df-al eqtypri ) ADEZDER
      BRBFZACGHZIJZHKGRDBUARSTRBLADCGMNONACBPQ $.

    $( Contradiction type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wfal $p |- F. : bool $=
      ( vp hb tal tv kl kc tfal kt ht wal wv wl wc df-fal eqtypri ) BCBABADZEZF
      GHBBIBCQBJBBAPBAKLMANO $.

    $( Conjunction type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wan $p |- /\ : ( bool -> ( bool -> bool ) ) $=
      ( vp vq vf hb ht tv kbr kl kt ke tan wv wov wl wtru weqi df-an eqtypri )
      DDDEZEZDADBTCDAFZDBFZTCFZGZHZTCIIUCGZHZJGZHZHKIDSAUIDDBUHTDEUEUGTDCUDDDDU
      AUBUCTCLZDALDBLMNTDCUFDDDIIUCUJOOMNPNNCABQR $.

    $( Implication type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wim $p |- ==> : ( bool -> ( bool -> bool ) ) $=
      ( vp vq hb ht tv tan kbr ke kl tim kt wan wv wov weqi wl df-im eqtypri )
      CCCDZDCACBCAEZCBEZFGZTHGZIZIJKCSAUDCCBUCCUBTCCCTUAFLCAMZCBMNUEOPPABQR $.

    $( Negation type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wnot $p |- ~ : ( bool -> bool ) $=
      ( vp hb ht tv tfal tim kbr kl tne kt wim wv wfal wov wl df-not eqtypri )
      BBCBABADZEFGZHIJBBASBBBREFKBALMNOAPQ $.

    $( There exists type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wex $p |- ? : ( ( al -> bool ) -> bool ) $=
      ( vp vq vx hb ht tal tv kc tim kbr kl tex kt wal wim wv wc wov wl eqtypri
      df-ex ) AEFZEFUCBGECGADUCBHZADHZIZECHZJKZLZIZUGJKZLZIZLMNUCEBUMEEFEGULEOE
      ECUKEEEUJUGJPUCEGUIAOAEDUHEEEUFUGJPAEUDUEUCBQADQRECQZSTRUNSTRTADBCUBUA $.

    $( Disjunction type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wor $p |- \/ : ( bool -> ( bool -> bool ) ) $=
      ( vp vq vx hb ht tal tv tim kbr kl kc tor kt wal wim wv wov wl wc df-or
      eqtypri ) DDDEZEDADBFDCDAGZDCGZHIZDBGZUDHIZUDHIZHIZJZKZJZJLMDUBAULDDBUKUB
      DFUJDNDDCUIDDDUEUHHODDDUCUDHODAPDCPZQDDDUGUDHODDDUFUDHODBPUMQUMQQRSRRCABT
      UA $.

    $( There exists unique type.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    weu $p |- ?! : ( ( al -> bool ) -> bool ) $=
      ( vp vy vx hb ht tex tal tv kc ke kbr kl teu kt wex wv wc weqi wl eqtypri
      wal df-eu ) AEFZEFUDBGACHADUDBIZADIZJZUFACIZKLZKLZMZJZMZJZMNOUDEBUNUDEGUM
      APAECULUDEHUKAUBAEDUJEUGUIAEUEUFUDBQADQZRAUFUHUOACQSSTRTRTADCBUCUA $.
  $}

  ${
    $d p q x y al $.  $d p q y F $.
    alval.1 $e |- F : ( al -> bool ) $.
    $( Value of the for all predicate.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    alval $p |- T. |= [ ( ! F ) = [ F = \ x : al . T. ] ] $=
      ( vp hb tal kc ht tv kt kl ke kbr wal wc df-al ceq1 wv weqi wtru wl oveq1
      weq id cl eqtri ) FGCHAFIZEUHEJZABKLZMNZLZCHCUJMNZKUHFGCAOZDPUHFCGKULUNDA
      BEQRUHFEUKUMCUHUIUJUHESZAFBKUAUBZTDUHUHFUIUJCMUICMNZUHUDUOUPUQUHUICUODTUE
      UCUFUG $.

    $d x F $.
    $( Value of the 'there exists' predicate.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    exval $p |- T. |= [ ( ? F ) = ( ! \ q : bool . [ ( ! \ x : al .
        [ ( F x : al ) ==> q : bool ] ) ==> q : bool ] ) ] $=
      ( vp hb tex kc ht tal tv tim kbr kl kt wc ceq1 wim wv wex df-ex wal wl ke
      wov weqi id oveq1 leq ceq2 cl eqtri ) GHDIAGJZFKGCKABUNFLZABLZIZGCLZMNZOZ
      IZURMNZOZIZOZDIKGCKABDUPIZURMNZOZIZURMNZOZIZPUNGHDAUAZEQUNGDHPVEVMEABFCUB
      RUNGFVDVLDGGJZGKVCGUCZGGCVBGGGVAURMSUNGKUTAUCZAGBUSGGGUQURMSAGUOUPUNFTZAB
      TZQZGCTZUFZUDZQZVTUFZUDZQEVNGVCVKKUODUENZVOWEGGCVBVJWFWDGGGVAURVIMWFSWCVT
      UNGUTVHKWFVPWBAGBUSVGWFWAGGGUQURVFMWFSVSVTAGUPUOWFDVQVRWFUNUODVQEUGUHRUIU
      JUKUIUJUKULUM $.

    $( Value of the 'exists unique' predicate.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    euval $p |- T. |= [ ( ?! F ) = ( ? \ y : al . ( ! \ x : al .
        [ ( F x : al ) = [ x : al = y : al ] ] ) ) ] $=
      ( vp hb teu kc tex tal tv ke kbr kl kt wc ceq1 wv weqi ht weu wex wal weq
      df-eu wl id oveq1 leq ceq2 cl eqtri ) GHDIAGUAZFJACKABUNFLZABLZIZUPACLZMN
      ZMNZOZIZOZIZOZDIJACKABDUPIZUSMNZOZIZOZIZPUNGHDAUBZEQUNGDHPVEVLEABCFUFRUNG
      FVDVKDUNGJVCAUCZAGCVBUNGKVAAUDZAGBUTGUQUSAGUOUPUNFSZABSZQZAUPURVPACSTZTZU
      GZQZUGZQEUNGVCVJJUODMNZVMWBAGCVBVIWCWAUNGVAVHKWCVNVTAGBUTVGWCVSGGGUQUSVFM
      WCGUEVQVRAGUPUOWCDVOVPWCUNUODVOETUHRUIUJUKUJUKULUM $.
  $}

  ${
    $d f p q x A $.  $d f q x B $.
    imval.1 $e |- A : bool $.
    $( Value of negation.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    notval $p |- T. |= [ ( ~ A ) = [ A ==> F. ] ] $=
      ( vp hb tne kc tv tfal tim kbr kl kt wnot wc df-not ceq1 wim wv wfal wov
      ke weqi id oveq1 cl eqtri ) DEAFDCDCGZHIJZKZAFAHIJZLDDEAMBNDDAELUIMBCOPDD
      CUHUJADDDUGHIQDCRZSTBDDDUGHAIUGAUAJZQUKSULDUGAUKBUBUCUDUEUF $.

    imval.2 $e |- B : bool $.
    $( Value of the implication.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    imval $p |- T. |= [ [ A ==> B ] = [ [ A /\ B ] = A ] ] $=
      ( vp vq hb tim kbr tv tan ke kl kt wim wov wan wv weqi id df-im weq oveq1
      oveq oveq12 oveq2 ovl eqtri ) GABHIABGEGFGEJZGFJZKIZUILIZMMZIABKIZALIZNGG
      GABHOCDPGGGABHNUMOCDEFUAUDGGGEFULAUJKIZALIUOABGUKUIGGGUIUJKQGERZGFRZPZUQS
      CDGGGUKUIUPLUIALIZAGUBZUSUQGGGUIUJAKUTQUQURUTGUIAUQCSTZUCVBUEGGGUPAUNLUJB
      LIZVAGGGAUJKQCURPCGGGAUJKVCBQCURVCGUJBURDSTUFUCUGUH $.

    $( Value of the disjunction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    orval $p |- T. |= [ [ A \/ B ] = ( ! \ x : bool .
      [ [ A ==> x : bool ] ==> [ [ B ==> x : bool ] ==> x : bool ] ] ) ] $=
      ( vp vq hb tor kbr tal tv tim kl kc kt wov wim wv oveq1 wor df-or oveq ht
      wal wl wc ke weqi id leq ceq2 oveq2 ovl eqtri ) HBCIJBCHFHGKHAHFLZHALZMJZ
      HGLZUQMJZUQMJZMJZNZOZNNZJKHABUQMJZCUQMJZUQMJZMJZNZOZPHHHBCIUADEQHHHBCIPVE
      UADEAFGUBUCHHHFGVDKHAVFVAMJZNZOVKBCHHUDZHKVCHUEZHHAVBHHHURVAMRHHHUPUQMRHF
      SZHASZQZHHHUTUQMRHHHUSUQMRHGSZVQQZVQQZQZUFZUGDEVNHVCVMKUPBUHJZVOWCHHAVBVL
      WDWBHHHURVAVFMWDRVRWAHHHUPUQBMWDRVPVQWDHUPBVPDUIUJTTUKULVNHVMVJKUSCUHJZVO
      HHAVLHHHVFVAMRHHHBUQMRDVQQZWAQZUFHHAVLVIWEWGHHHVFVAMWEVHRWFWAHHHUTUQVGMWE
      RVTVQHHHUSUQCMWERVSVQWEHUSCVSEUIUJTTUMUKULUNUO $.

    $( Value of the conjunction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    anval $p |- T. |= [ [ A /\ B ] = [ \ f : ( bool -> ( bool -> bool ) ) .
      [ A f : ( bool -> ( bool -> bool ) ) B ] =
        \ f : ( bool -> ( bool -> bool ) ) .
          [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ] $=
      ( vp vq hb tan kbr ht tv kl kt ke wov wv wl weqi oveq1 wan df-an oveq weq
      wtru id leq oveq2 ovl eqtri ) HBCIJBCHFHGHHHKKZAHFLZHGLZUKALZJZMZUKANNUNJ
      ZMZOJZMMZJUKABCUNJZMZUROJZNHHHBCIUADEPHHHBCINUTUADEAFGUBUCHHHFGUSUKABUMUN
      JZMZUROJVCBCUKHKZUPURUKHAUOHHHULUMUNUKAQZHFQZHGQZPZRZUKHAUQHHHNNUNVGUEUEP
      RZSDEVFVFHUPURVEOULBOJZVFUDZVKVLUKHAUOVDVMVJHHHULUMBUNVMVGVHVIVMHULBVHDSU
      FTUGTVFVFHVEURVBOUMCOJZVNUKHAVDHHHBUMUNVGDVIPZRVLUKHAVDVAVOVPHHHBUMUNVOCV
      GDVIVOHUMCVIESUFUHUGTUIUJ $.
  $}

  ${
    $d p F $.  $d p al $.
    ax4g.1 $e |- F : ( al -> bool ) $.
    ax4g.2 $e |- A : al $.
    $( If ` F ` is true for all ` x : al ` , then it is true for ` A ` .
       (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    ax4g $p |- ( ! F ) |= ( F A ) $=
      ( vp kt kc tal hb ht wal wc trud kl ke kbr ax-cb1 id alval mpbi ceq1 hbth
      a1i eqtri mpbir ) GCBHZICHZUHAJKJICALDMNZJUGAFGOZBHGUHAJCBDEMAJBCUHUJDEUH
      CUJPQZUHUHGUHUIRZSUHUKPQUHULAFCDTUDUAUBAFGBUHEUIUCUEUF $.
  $}

  ${
    ax4.1 $e |- A : bool $.
    $( If ` A ` is true for all ` x : al ` , then it is true for ` A ` .
       (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    ax4 $p |- ( ! \ x : al . A ) |= A $=
      ( kl tv kc tal hb wl wv ax4g ke kbr ax-cb1 beta a1i mpbi ) ABCEZABFZGZCHS
      GZATSAIBCDJABKLZUACMNUBUAUBUCOAIBCDPQR $.
  $}

  ${
    $d x R $.  $d x al $.
    alrimiv.1 $e |- R |= A $.
    $( If one can prove ` R |= A ` where ` R ` does not contain ` x ` , then
       ` A ` is true for all ` x ` .  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    alrimiv $p |- R |= ( ! \ x : al . A ) $=
      ( kl kt ke kbr tal kc hb ax-cb2 wtru eqtru eqcomi leq ax-cb1 wl alval a1i
      mpbir ) ABCFZABGFHIZJUCKZDALBCGDCDEMZLGCDNCDEOPQUEUDHIDCDERABUCALBCUFSTUA
      UB $.
  $}

  ${
    $d x B $.  $d x C $.  $d x al $.
    cla4v.1 $e |- A : bool $.
    cla4v.2 $e |- B : al $.
    cla4v.3 $e |- [ x : al = B ] |= [ A = C ] $.
    $( If ` A ( x ) ` is true for all ` x : al ` , then it is true for
       ` C = A ( B ) ` .  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    cla4v $p |- ( ! \ x : al . A ) |= C $=
      ( kl kc tal hb wl ax4g ke kbr ax-cb1 cl a1i mpbi ) ABCIZDJZEKUAJZADUAALBC
      FMGNZUBEOPUCUBUCUDQALBCEDFGHRST $.
  $}

  ${
    $d p A $.
    pm2.21.1 $e |- A : bool $.
    $( A falsehood implies anything.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    pm2.21 $p |- F. |= A $=
      ( vp tfal tal hb tv kl kc wfal id ke kbr df-fal a1i mpbi weqi cla4v syl
      wv ) DEFCFCGZHIZADUBDDJKDUBLMDJCNOPFCUAAAFCTZBUAALMFUAAUCBQKRS $.
  $}

  ${
    $d f x y A $.  $d f x y B $.
    dfan2.1 $e |- A : bool $.
    dfan2.2 $e |- B : bool $.
    $( An alternative defintion of the "and" term in terms of the context
       conjunction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    dfan2 $p |- T. |= [ [ A /\ B ] = ( A , B ) ] $=
      ( vf vx vy kbr kt hb kl kc wl ke id a1i weqi oveq eqid wtru tan kct ht tv
      wan wov trud wv wc anval mpbi ceq1 ovl eqtri cl 3eqtr3i mpbir simpl eqtru
      jca simpr oveq12 eqcomi leq ax-cb1 dedi ) ABUAHZABUBZVGABIAVGVGJJJABUAUEC
      DUFZUGZJJJJUCZUCZEABVLEUDZHZKZJFJGJFUDZKZKZLZVLEIIVMHZKZVRLZVGAIVLJVOVRVL
      JEVNJJJABVMVLEUHZCDUFZMZJVKFVQJJGVPJFUHZMMZUIVLJVRVOVGWAWEWGVGVOWANHZVGVG
      VIOVGWHNHZVGVIEABCDUJZPUKZULVSANHVGVIVLJEVNAVRWDWGJVNABVRHZAVMVRNHZWDJJJA
      BVMWMVRWCCDWMVLVMVRWCWGQZOZRWLANHWMWNJJJFGVPAAABWFCDVPANHZJVPAWFCQZOJAJGU
      DZBNHZJWRBJGUHZDQZCSUMPUNUOPWBINHVGVIVLJEVTIVRJJJIIVMWCTTUFZWGJVTIIVRHZIW
      MXBJJJIIVMWMVRWCTTWORXCINHWMWNJJJFGVPIIIIWFTTVPINHZJVPIWFTQZOJIWRINHZJWRI
      WTTQZTSUMPUNUOPUPUQIBVGVJJVOJFJGWRKZKZLZWAXILZVGBIVLJVOXIWEJVKFXHJJGWRWTM
      MZUIZVLJXIVOVGWAWEXLWKULXJBNHVGVIJXJABXIHZBIXMVLJEVNXNXIWDXLJJJABVMVMXINH
      ZXIWCCDXOVLVMXIWCXLQZOZRUOXNBNHITJJJFGWRWRBABWTCDJWRWPWQWTSWSXAOUMPUNPXKI
      NHVGVIVLJEVTIXIXBXLJVTIIXIHZIXOXBJJJIIVMXOXIWCTTXQRXRINHXOXPJJJFGWRWRIIIW
      TTTJWRXDXEWTSXFXGOUMPUNUOPUPUQUTWHVGVHVLJEVNVTVHWDJVTVNVHXBJJJIIAVMVHBWCT
      TAVHABCDURZUSBVHABCDVAUSVBVCVDWIVHAVHXSVEWJPUQVF $.
  $}

  ${
    hbct.1 $e |- A : bool $.
    hbct.2 $e |- B : al $.
    hbct.3 $e |- C : bool $.
    hbct.4 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    hbct.5 $e |- R |= [ ( \ x : al . C B ) = C ] $.
    $( Hypothesis builder for context conjunction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    hbct $p |- R |= [ ( \ x : al . ( A , C ) B ) = ( A , C ) ] $=
      ( kt kl kc ke kbr hb tan wan ht kct ax-cb1 trud wct wov dfan2 eqcomi a17i
      hbov wtru adantr hbxfrf mpdan ) FLABCEUAZMDNUNOPFABCMDNCOPFJUBZUCAQBCERPZ
      DLFUNCEGIUDHQUPUNLQQQCERSGIUECEGIUFUGFLABUPMDNUPOPAQQQBCDERFSGHIAQQQTTBRD
      FSHUOUHJKUIUJUKULUM $.
  $}

  ${
    mp.1 $e |- T : bool $.
    mp.2 $e |- R |= S $.
    mp.3 $e |- R |= [ S ==> T ] $.
    $( Modus ponens.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    mpd $p |- R |= T $=
      ( tan kbr kct tim ke ax-cb1 ax-cb2 imval a1i mpbi mpbir dfan2 simprd ) AB
      CBCGHZBCIZABTAEBCJHZTBKHZAFUBUCKHABAELZBCBAEMZDNOPQTUAKHAUDBCUEDROPS $.
  $}

  ${
    imp.1 $e |- S : bool $.
    imp.2 $e |- T : bool $.
    imp.3 $e |- R |= [ S ==> T ] $.
    $( Importation deduction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    imp $p |- ( R , S ) |= T $=
      ( kct tim kbr ax-cb1 simpr adantr mpd ) ABGBCEABBCHIZAFJDKABNFDLM $.
  $}

  ${
    ex.1 $e |- ( R , S ) |= T $.
    $( Exportation deduction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    ex $p |- R |= [ S ==> T ] $=
      ( tan kbr ke tim kct wan ax-cb1 wctr ax-cb2 wov wctl dfan2 a1i wct simpr
      hb simpld jca ded eqtri imval mpbir ) BCEFZBGFZBCHFZATUGBCIZBATTTBCEJABCA
      BIZDKZLZCUKDMZNUGUJGFAABULOZBCUMUNPQAUJBAUJIBCAUJUOBCUMUNRSUAUKBCABUOUMSD
      UBUCUDZUIUHGFAUHAUPKBCUMUNUEQUF $.
  $}

  ${
    notval2.1 $e |- A : bool $.
    $( Another way two write ` ~ A ` , the negation of ` A ` .  (Contributed by
       Mario Carneiro, 9-Oct-2014.) $)
    notval2 $p |- T. |= [ ( ~ A ) = [ A = F. ] ] $=
      ( hb tne kc tfal tim kbr ke kt wnot wc notval kct wim wov simpr simpl mpd
      wfal pm2.21 adantl ded ax-cb2 mpbi ex dedi eqtri ) CDAEAFGHZAFIHZJCCDAKBL
      ABMUIUJUIAFUIANAFTUIACCCAFGOBTPZBQUIAUKBRSFUIAABUAUKUBUCZUJAFAFUJANUJAUJU
      IULUDZBQUJAUMBRUEUFUGUH $.

    $( One side of ~ notnot .  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    notnot1 $p |- A |= ( ~ ( ~ A ) ) $=
      ( tne kc tfal tim kbr kct wfal hb wnot simpl simpr ax-cb1 notval a1i mpbi
      wc ke mpd ex mpbir ) CADZEFGZCUCDZAAUCEAUCHZAEIAUCBJJCAKBRZLZUCAEFGZUFAUC
      BUGMUCUISGUFAUFUHNABOPQTUAUEUDSGABUCUGOPUB $.
  $}

  ${
    con2d.1 $e |- T : bool $.
    con2d.2 $e |- ( R , S ) |= ( ~ T ) $.
    $( A contraposition deduction.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    con2d $p |- ( R , T ) |= ( ~ S ) $=
      ( tfal tim kbr tne kc kct wfal ke ax-cb1 notval a1i mpbi imp an32s ex wct
      wctl wctr mpbir ) BFGHZIBJZACKZUGBFFABCABKZCFDLICJZCFGHZUHEUIUJMHUHUIUHEN
      ZCDOPQRSTUFUEMHUGACABUKUBDUABABUKUCOPUD $.
  $}

  ${
    con3d.1 $e |- ( R , S ) |= T $.
    $( A contraposition deduction.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    con3d $p |- ( R , ( ~ T ) ) |= ( ~ S ) $=
      ( tne kc hb wnot kct ax-cb2 wc notnot1 syl con2d ) ABECFZGGECHCABIZDJZKPC
      EOFDCQLMN $.
  $}

  ${
    $d x A $.  $d x B $.  $d x T $.
    ecase.1 $e |- A : bool $.
    ecase.2 $e |- B : bool $.
    ecase.3 $e |- T : bool $.
    ecase.4 $e |- R |= [ A \/ B ] $.
    ecase.5 $e |- ( R , A ) |= T $.
    ecase.6 $e |- ( R , B ) |= T $.
    $( Elimination by cases.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    ecase $p |- R |= T $=
      ( vx tim kbr ex hb wim wov ke oveq2 oveq12 tal tv kl tor ax-cb1 orval a1i
      kc mpbi wv weqi id cla4v syl mpd ) CBDLMZDGCBDJNCADLMZUPDLMZOOOUPDLPOOOBD
      LPFGQGQCADINCUAOKAOKUBZLMZBUSLMZUSLMZLMZUCUHZUQURLMZABUDMZVDCHVFVDRMCVFCH
      UEKABEFUFUGUIOKVCDVEOOOUTVBLPOOOAUSLPEOKUJZQZOOOVAUSLPOOOBUSLPFVGQZVGQZQG
      OOOUTVBUQLUSDRMZURPVHVJOOOAUSLVKDPEVGVKOUSDVGGUKULZSOOOVAUSUPLVKDPVIVGOOO
      BUSLVKDPFVGVLSVLTTUMUNUOUO $.
  $}

  ${
    $d x A $.  $d x B $.
    olc.1 $e |- A : bool $.
    olc.2 $e |- B : bool $.
    $( Or introduction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    olc $p |- B |= [ A \/ B ] $=
      ( vx hb tv tim kbr kl kt ke tor wim wv wov wtru kct simpl ex simpr adantr
      mpd eqtru eqcomi leq tal kc wor orval wl alval eqtri a1i mpbir ) FEAFEGZH
      IZBUPHIZUPHIZHIZJZFEKJLIZABMIZBFFEUTKBFFFUQUSHNFFFAUPHNCFEOZPZFFFURUPHNFF
      FBUPHNDVDPZVDPPZFKUTBQUTBBUQUSBUQUSBURUPBURRBUPVDBURDVFSBURDVFUAUCTVEUBTU
      DUEUFVCVBLIBDFVCUGVAUHVBKFFFABMUICDPEABCDUJFEVAFFEUTVGUKULUMUNUO $.

    $( Or introduction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    orc $p |- A |= [ A \/ B ] $=
      ( vx hb tv tim kbr kl kt ke tor wim wv wov wtru kct simpl ex simpr adantr
      mpd eqtru eqcomi leq tal kc wor orval wl alval eqtri a1i mpbir ) FEAFEGZH
      IZBUPHIZUPHIZHIZJZFEKJLIZABMIZAFFEUTKAFFFUQUSHNFFFAUPHNCFEOZPZFFFURUPHNFF
      FBUPHNDVDPZVDPPZFKUTAQUTAAUQUSAUQRZURUPVHURUPVHAUPVDAUQCVESAUQCVEUAUCVFUB
      TTUDUEUFVCVBLIACFVCUGVAUHVBKFFFABMUICDPEABCDUJFEVAFFEUTVGUKULUMUNUO $.
  $}

  ${
    $d p x F $.  $d x R $.  $d p x T $.  $d p x al $.
    exlimdv2.1 $e |- F : ( al -> bool ) $.
    exlimdv2.2 $e |- ( R , ( F x : al ) ) |= T $.
    $( Existential elimination.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    exlimdv2 $p |- ( R , ( ? F ) ) |= T $=
      ( vp tex kc kct tal tv tim kbr kl hb wc ke wim ax-cb2 ex ht adantr ax-cb1
      alrimiv wex wctl simpr wct exval a1i mpbi wal wv wov wl weqi id oveq2 leq
      ceq2 oveq12 cla4v syl mpd ) DICJZKZLABCABMZJZENOZPZJZEEDVJKZGUAZDVGVMABVK
      DDVJEGUBUFAQUCZQICAUGFRZUDVHLQHLABVJQHMZNOZPZJZVRNOZPJZVMENOZVGWCVHDVGDVJ
      EVNGUEUHZVQUIVGWCSOVHDVGWEVQUJABHCFUKULUMQHWBEWDQQQWAVRNTVPQLVTAUNZAQBVSQ
      QQVJVRNTAQCVIFABUORZQHUOZUPZUQZRZWHUPVOQQQWAVRVMNVRESOZETWKWHVPQVTVLLWLWF
      WJAQBVSVKWLWIQQQVJVRNWLETWGWHWLQVREWHVOURUSZUTVAVBWMVCVDVEVF $.
  $}

  ${
    $d y z A $.  $d x y z R $.  $d x y z T $.  $d x y z al $.
    exlimdv.1 $e |- ( R , A ) |= T $.
    $( Existential elimination.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    exlimdv $p |- ( R , ( ? \ x : al . A ) ) |= T $=
      ( vy vz hb tv kc wv wc tim kbr wim kt ht ax-17 ke kl kct ax-cb1 wl ax-cb2
      wctr wov ex ax-hbl1 hbc hbov weqi beta eqcomi a1i id ceq2 eqtri oveq1 imp
      insti exlimdv2 ) AGABCUAZDEAIBCDCEDCUBZFUCUFZUDZDVCAGJZKZEAIVCVGVFAGLZMZE
      VDFUEZABHCENOVHENOVGDVIIIIVHENPVJVKUGDCEFUHAIIIBVHAHJZENQPVJAHLZVKAIIIRRB
      NVLPVMSAAIBVGVLVCQVFVIVMAAIBCVLVEVMUIAABVGVLVIVMSUJAIBEVLVKVMSUKIIICEVHNA
      BJZVGTOZPVEVKICVCVNKZVHVOVECVPTOVOAVNVGABLZVIULZIVPCQAIVCVNVFVQMAIBCVEUMU
      NUOAIVNVGVCVOVFVQVOVRUPUQURUSVAUTVB $.
  $}

  ${
    $d p x A $.  $d p x F $.  $d p x al $.
    ax4e.1 $e |- F : ( al -> bool ) $.
    ax4e.2 $e |- A : al $.
    $( Existential introduction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    ax4e $p |- ( F A ) |= ( ? F ) $=
      ( vp vx tal hb tv kc tim kbr kl tex kct wv wc wim ke ht wal wl simpl weqi
      wov id ceq2 oveq1 cla4v adantl mpd ex alrimiv exval a1i mpbir ) HIFHAGCAG
      JZKZIFJZLMZNZKZUTLMZNKZOCKZCBKZIFVDVGVGVCUTVGVCPVGUTIFQZVGVCAICBDERZAIUAI
      HVBAUBAIGVAIIIUSUTLSAICURDAGQZRZVHUFZUCRUDVCVGVGUTLMZAGVABVMVLEIIIUSUTVGL
      URBTMZSVKVHAIURBCVNDVJVNAURBVJEUEUGUHUIUJVIUKULUMUNVFVETMVGVIAGFCDUOUPUQ
      $.
  $}

  ${
    $d x B $.  $d x C $.  $d x al $.
    cla4ev.1 $e |- A : bool $.
    cla4ev.2 $e |- B : al $.
    cla4ev.3 $e |- [ x : al = B ] |= [ A = C ] $.
    $( Existential introduction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    cla4ev $p |- C |= ( ? \ x : al . A ) $=
      ( kl kc tex hb tv ke kbr eqtypi id cl a1i mpbir wl ax4e syl ) EABCIZDJZKU
      DJEUEEELCEABMDNOFHPZQUEENOEUFALBCEDFGHRSTADUDALBCFUAGUBUC $.
  $}

  ${
    19.8a.1 $e |- A : bool $.
    $( Existential introduction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    19.8a $p |- A |= ( ? \ x : al . A ) $=
      ( kl tv kc tex ax-id ke kbr hb beta a1i mpbir wl wv ax4e syl ) CABCEZABFZ
      GZHTGCUBCCDIUBCJKCDALBCDMNOAUATALBCDPABQRS $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                 Type definition mechanism
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c typedef $.

  $( Internal axiom for mmj2 use. $)
  wffMMJ2d $a wff typedef al ( A , B ) C $.

  ${
    $d x A $.  $d x R $.  $d x F $.
    ax-tdef.1 $e |- B : al $.
    ax-tdef.2 $e |- F : ( al -> bool ) $.
    ax-tdef.3 $e |- T. |= ( F B ) $.
    ax-tdef.4 $e |- typedef be ( A , R ) F $.
    $( Type of the abstraction function.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wabs $a |- A : ( al -> be ) $.

    $( Type of the representation function.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wrep $a |- R : ( be -> al ) $.

    $( Type of the abstraction function.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    wabs $p |- A : ( al -> be ) $=
      ( ax-wabs ) ABCDEFGHIJK $.

    $( Type of the representation function.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    wrep $p |- R : ( be -> al ) $=
      ( ax-wrep ) ABCDEFGHIJK $.

    $( The type definition axiom.  The last hypothesis corresponds to the
       actual definition one wants to make; here we are defining a new type
       ` be ` and the definition will provide us with pair of bijections
       ` A , R ` mapping the new type ` be ` to the subset of the old type
       ` al ` such that ` F x ` is true.  In order for this to be a valid
       (conservative) extension, we must ensure that the new type is non-empty,
       and for that purpose we need a witness ` B ` that ` F ` is not always
       false.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-tdef $a |- T. |= ( ( ! \ x : be . [ ( A ( R x : be ) ) = x : be ] ) ,
      ( ! \ x : al . [ ( F x : al ) = [ ( R ( A x : al ) ) = x : al ] ] ) ) $.
  $}
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                       Extensionality
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    $d f x $.
    $( The eta-axiom: a function is determined by its values.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-eta $a |- T. |= ( ! \ f : ( al -> be ) .
      [ \ x : al . ( f : ( al -> be ) x : al ) = f : ( al -> be ) ] ) $.
  $}

  ${
    $d f x F $.  $d f x al $.  $d f x be $.
    eta.1 $e |- F : ( al -> be ) $.
    $( The eta-axiom: a function is determined by its values.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    eta $p |- T. |= [ \ x : al . ( F x : al ) = F ] $=
      ( vf kt tal ht tv kc kl ke kbr ax-eta hb weq wv wc wl weqi id ceq1 oveq12
      wov leq cla4v syl ) GHABIZFACUIFJZACJZKZLZUJMNZLKACDUKKZLZDMNZABCFOUIFUND
      UQUIUIPUMUJMUIQZABCULABUJUKUIFRZACRZSZTZUSUEEUIUIPUMUJUPMUJDMNZDURVBUSABC
      ULUOVCVAABUKUJVCDUSUTVCUIUJDUSEUAUBZUCUFVDUDUGUH $.
  $}

  ${
    $d p z A $.  $d p z B $.  $d p x y z al $.  $d p be $.
    cbvf.1 $e |- A : be $.
    cbvf.2 $e |- T. |= [ ( \ y : al . A z : al ) = A ] $.
    cbvf.3 $e |- T. |= [ ( \ x : al . B z : al ) = B ] $.
    cbvf.4 $e |- [ x : al = y : al ] |= [ A = B ] $.
    $( Change bound variables in a lambda abstraction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    cbvf $p |- T. |= [ \ x : al . A = \ y : al . B ] $=
      ( vp ht kl tv kc kt wc ke kbr wl eqtypi weqi ax-17 clf weq hbl hbc ax-cb1
      wv hb hbl1 hbov ceq2 beta eqcomi a1i eqtri oveq12 insti leq eta 3eqtr3i
      id ) ABMALACFNZALOZPZNALADGNZVFPZNQVEVHABLVGABVEVFABCFHUAZALUJZRZUAABLVGV
      IQVLADEVEADOZPZGSTVGVISTVFQVKBVGVIVLABVHVFABDGBFGACOVMSTHKUBZUAZVKRZUCABC
      EFGVMHADUJZKJAACVMAEOZVRAEUJZUDUEABBUKDVGVSVISQBUFZVLVTVQABBUKMMDSVSWAVTU
      DAABDVFVSVEQVJVKVTAABDCFVSQHVTIUGAADVFVSVKVTUDZUHAABDVFVSVHQVPVKVTAABDGVS
      QVOVTADFNVSPFSTQIUIULWBUHUMBBUKVNGVGSVMVFSTZVIWAABVEVMVJVRRVOABVMVFVEWCVJ
      VRWCAVMVFVRVKUCVDZUNZBGVHVMPZVIWCVOGWFSTWCVNVGSTWCWEUIBWFGQABVHVMVPVRRABD
      GVOUOUPUQABVMVFVHWCVPVRWDUNURUSUTVAABLVEVJVBABLVHVPVBVC $.
  $}

  ${
    $d y z A $.  $d x z B $.  $d x y z al $.  $d y be $.
    cbv.1 $e |- A : be $.
    cbv.2 $e |- [ x : al = y : al ] |= [ A = B ] $.
    $( Change bound variables in a lambda abstraction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    cbv $p |- T. |= [ \ x : al . A = \ y : al . B ] $=
      ( vz tv wv ax-17 ke kbr eqtypi cbvf ) ABCDIEFGABDEAIJZGAIKZLABCFQBEFACJAD
      JMNGHORLHP $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z R $.  $d x y z al $.  $d z be $.
    leqf.1 $e |- A : be $.
    leqf.2 $e |- R |= [ A = B ] $.
    leqf.3 $e |- T. |= [ ( \ x : al . R y : al ) = R ] $.
    $( Equality theorem for lambda abstraction, using bound variable instead of
       distinct variables.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    leqf $p |- R |= [ \ x : al . A = \ x : al . B ] $=
      ( vz ht kl tv kc wc ke kbr a1i hb wl wv ax-cb1 beta eqtypi 3eqtr4i kt weq
      ax-17 ax-hbl1 hbc hbov weqi id ceq2 oveq12 eqid ax-inst leq eta 3eqtr3i )
      ABLAKACEMZAKNZOZMZAKACFMZVCOZMZGVBVFABKVDABVBVCABCEHUAZAKUBZPZUAABKVDVGGV
      KACDVBACNZOZVFVLOZQRVDVGQRVCGGBEFGVMVNHIVMEQRGEFQRGIUCZABCEHUDSVNFQRGVOAB
      CFBEFGHIUEZUDSUFABBTCVDADNZVGQUGBUHZVKADUBZABVFVCABCFVPUAZVJPABBTLLCQVQVR
      VSUIAABCVCVQVBUGVIVJVSAABCEVQHVSUJAACVCVQVJVSUIZUKAABCVCVQVFUGVTVJVSAABCF
      VQVPVSUJWAUKULJBBTVMVNVDQVLVCQRZVGVRABVBVLVIACUBZPABVFVLVTWCPABVLVCVBWBVI
      WCWBAVLVCWCVJUMZUNZUOABVLVCVFWBVTWCWEUOUPTGWBWDVOUQURUSVEVBQRGVOABKVBVIUT
      SVHVFQRGVOABKVFVTUTSVA $.
  $}

  ${
    $d y A $.  $d y R $.  $d x y al $.
    alrimi.1 $e |- R |= A $.
    alrimi.2 $e |- T. |= [ ( \ x : al . R y : al ) = R ] $.
    $( If one can prove ` R |= A ` where ` R ` does not contain ` x ` , then
       ` A ` is true for all ` x ` .  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    alrimi $p |- R |= ( ! \ x : al . A ) $=
      ( kl kt ke kbr tal kc hb ax-cb2 wtru eqtru eqcomi leqf ax-cb1 alval mpbir
      wl a1i ) ABDHZABIHJKZLUEMZEANBCDIEDEFOZNIDEPDEFQRGSUGUFJKEDEFTABUEANBDUHU
      CUAUDUB $.
  $}

  ${
    $d y z A $.  $d y z R $.  $d y z T $.  $d x y z al $.
    exlimd.1 $e |- ( R , A ) |= T $.
    exlimd.2 $e |- T. |= [ ( \ x : al . R y : al ) = R ] $.
    exlimd.3 $e |- T. |= [ ( \ x : al . T y : al ) = T ] $.
    $( Existential elimination.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    exlimd $p |- ( R , ( ? \ x : al . A ) ) |= T $=
      ( vz kl kc tal tv tim kbr hb wim wov kt tex ax-cb2 ax-cb1 wctr wl wv wctl
      kct wc id ex wtru adantl ax-17 ax-hbl1 hbc hbov weqi beta eqcomi a1i ceq2
      ht ke eqtri oveq1 oveq2 insti mpd alrimiv wex adantr simpr exval mpbi wal
      leq oveq12 cla4v syl ) EUAABDKZLZUHZMAJWAAJNZLZFOPZKZLZFFEDUHZGUBZEWBWHAJ
      WFEEEWFQQQWEFORAQWAWDAQBDEDFWIGUCZUDZUEZAJUFZUIZWJSZEEDWKUGZUJEWFOPZEWQAB
      CEDFOPZOPWRWDTWNQQQEWFORWQWPSTEWSETWSEDFGUKULUMUKAQQQBEACNZWFOTRWQACUFZWP
      AQQQVCVCBOWTRXAUNZHAQQQBWEWTFOTRWOXAWJXBAAQBWDWTWATWMWNXAAAQBDWTWLXAUOAAB
      WDWTWNXAUNUPIUQUQQQQEWSOABNZWDVDPZWFRWQQQQDFORWLWJSQQQDFWEOXDRWLWJQDWAXCL
      ZWEXDWLDXEVDPXDAXCWDABUFZWNURZQXEDTAQWAXCWMXFUIAQBDWLUSUTVAAQXCWDWAXDWMXF
      XDXGUJVBVEVFVGVHVAVIVJAQVCZQUAWAAVKWMUIZVLZWCMQCMAJWEQCNZOPZKZLZXKOPZKLZW
      HFOPZWBXPWCEWBWQXIVMWBXPVDPWCWHWCXJUCAJCWAWMVNVAVOQCXOFXQQQQXNXKORXHQMXMA
      VPZAQJXLQQQWEXKORWOQCUFZSZUEZUIZXSSWJQQQXNXKWHOXKFVDPZFRYBXSXHQXMWGMYCXRY
      AAQJXLWFYCXTQQQWEXKOYCFRWOXSYCQXKFXSWJURUJZVGVQVBYDVRVSVTVI $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y R $.  $d x y al $.
    alimdv.1 $e |- ( R , A ) |= B $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 9-Oct-2014.) $)
    alimdv $p |- ( R , ( ! \ x : al . A ) ) |= ( ! \ x : al . B ) $=
      ( vy tal kl kc kct ax-cb1 wctr ax4 wctl adantl kt hb ht ax-17 tv wv wl wc
      syldan wal ax-hbl1 hbc hbct alrimi ) ABGDEHABCIZJZKDEULCULECABCECDECKFLZM
      ZNECUMOZPFUEABEAGUAZULQUOAGUBZARSZRHUKAUFZARBCUNUCZUDARBEUPUOUQTAURRBUKUP
      HQUSUTUQAURRSBHUPUSUQTAARBCUPUNUQUGUHUIUJ $.

    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 9-Oct-2014.) $)
    eximdv $p |- ( R , ( ? \ x : al . A ) ) |= ( ? \ x : al . B ) $=
      ( vy tex kl kc kct ax-cb2 19.8a syl hb tv ax-cb1 wctl ax-17 ht wv ax-hbl1
      kt wex wl hbc exlimd ) ABGCEHABDIZJZECKZDUIFABDDUJFLZMNAOBEAGPZECDUJFQRAG
      UAZSAAOTZOBUHULHUCAUDZAOBDUKUEUMAUNOTBHULUOUMSAAOBDULUKUMUBUFUG $.
  $}

  ${
    $d y A $.  $d x y al $.
    alnex1.1 $e |- A : bool $.
    $( Theorem 19.7 of [Margaris] p. 89.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    alnex $p |- T. |=
        [ ( ! \ x : al . ( ~ A ) ) = ( ~ ( ? \ x : al . A ) ) ] $=
      ( vy tal tne kc kl tex tfal tim kbr wfal hb wnot ht kt ax-17 hbc ax4 mpbi
      wc ke ax-cb1 notval a1i imp tv wal wl wv ax-hbl1 exlimd ex wex mpbir wtru
      19.8a adantl con3d trul alrimi dedi ) FABGCHZIZHZGJABCIZHZHZVIKLMZVJVGVGV
      IKABECVGKVGCKDNVECKLMZVGABVEOOGCPDUCZUAZVEVLUDMVGVEVGVNUEZCDUFUGUBUHAAOQZ
      OBVFAEUIZFRAUJZAOBVEVMUKAEULZAVPOQZBFVQVRVSSAAOBVEVQVMVSUMTAOBKVQNVSSUNUO
      VJVKUDMVGVOVIVPOJVHAUPZAOBCDUKZUCZUFUGUQABEVEVJVJVERCVICRVIABCDUSURUTVAVB
      AOOBVIVQGRPWCVSAOOQBGVQPVSSAVPOBVHVQJRWAWBVSAVTBJVQWAVSSAAOBCVQDVSUMTTVCV
      D $.

    $( Forward direction of ~ exnal .  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    exnal1 $p |- ( ? \ x : al . ( ~ A ) ) |= ( ~ ( ! \ x : al . A ) ) $=
      ( tex tne kc kl tal kt hb ht wex wnot wc wl kct notnot1 wtru adantl id ke
      alimdv wal kbr alnex a1i mpbi syl con2d trul ) EABFCGZHZGZFIABCHGZGJUOUNA
      KLZKEUMAMAKBULKKFCNDOZPOJUOQIABFULGZHZGZFUNGZABCURJCJURCDRSTUCUTVAUTUTUPK
      IUSAUDAKBURKKFULNUQOPOZUAUTVAUBUEUTVBABULUQUFUGUHUIUJUK $.

    isfree.2 $e |- T. |= [ ( \ x : al . A y : al ) = A ] $.
    $( Derive the metamath "is free" predicate in terms of the HOL "is free"
       predicate.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    isfree $p |- T. |= [ A ==> ( ! \ x : al . A ) ] $=
      ( kt tal kl kc id alrimi tv ke kbr ax-cb1 adantl ex ) GDHABDIZJZDGTABCDDD
      EKFLSACMJDNOGFPQR $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                       Axioms of infinity and choice
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c 1-1 $.   $( One-to-one function $)
  $c onto $.  $( Onto function $)
  $c @ $.     $( Indefinite descriptor $)

  $( One-to-one function. $)
  tf11 $a term 1-1 $.
  $( Onto function. $)
  tfo $a term onto $.
  $( Indefinite descriptor. $)
  tat $a term @ $.

  $( The type of the indefinite descriptor.  (New usage is discouraged.)
     (Contributed by Mario Carneiro, 10-Oct-2014.) $)
  ax-wat $a |- @ : ( ( al -> bool ) -> al ) $.

  $( The type of the indefinite descriptor.  (Contributed by Mario Carneiro,
     10-Oct-2014.) $)
  wat $p |- @ : ( ( al -> bool ) -> al ) $=
    ( ax-wat ) AB $.

  ${
    $d f p x y $.
    $( Define a one-to-one function.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    df-f11 $a |- T. |= [ 1-1 = \ f : ( al -> be ) .
      ( ! \ x : al . ( ! \ y : al .
        [ [ ( f : ( al -> be ) x : al ) = ( f : ( al -> be ) y : al ) ] ==>
          [ x : al = y : al ] ] ) ) ] $.

    $( Define an onto function.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    df-fo $a |- T. |= [ onto = \ f : ( al -> be ) . ( ! \ y : be .
      ( ? \ x : al . [ y : be = ( f : ( al -> be ) x : al ) ] ) ) ] $.

    $( Defining property of the indefinite descriptor: it selects an element
       from any type.  This is equivalent to global choice in ZF. (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    ax-ac $a |- T. |= ( ! \ p : ( al -> bool ) .
      ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==>
        ( p : ( al -> bool ) ( @ p : ( al -> bool ) ) ) ] ) ) $.
  $}

  ${
    $d x A $.  $d p x F $.  $d p x al $.
    ac.1 $e |- F : ( al -> bool ) $.
    ac.2 $e |- A : al $.
    $( Defining property of the indefinite descriptor: it selects an element
       from any type.  This is equivalent to global choice in ZF. (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    ac $p |- ( F A ) |= ( F ( @ F ) ) $=
      ( vx vp kc tat hb wc id tim kbr kt tal tv kl wim ceq2 ht wat ax-cb1 ax-ac
      wal wv wov wl weqi ceq1 ceq12 oveq12 leq cla4v syl eqtypi oveq1 a1i mpd
      ke ) CBHZVACICHZHZAJCVBDAJUAZAICAUBZDKKZVAAJCBDEKLZVAVCMNZVAVAVAVGUCOPAFC
      AFQZHZVCMNZRZHZVHOPVDGPAFVDGQZVIHZVNIVNHZHZMNZRZHZRHVMAFGUDVDGVTCVMVDJPVS
      AUEZAJFVRJJJVOVQMSAJVNVIVDGUFZAFUFZKZAJVNVPWBVDAIVNVEWBKZKZUGZUHZKDVDJVSV
      LPVNCUTNZWAWHAJFVRVKWIWGJJJVOVQVJMWIVCSWDWFAJVIVNWICWBWCWIVDVNCWBDUILZUJA
      JVPVBVNWICWBWEWJVDAVNCIWIVEWBWJTUKULZUMTUNUOAFVKBVHJVRVKWIWGWKUPEJJJVJVCV
      AMVIBUTNZSAJCVIDWCKVFAJVIBCWLDWCWLAVIBWCEUILTUQUNUOURUS $.
  $}

  ${
    $d x F $.  $d x al $.
    dfex2.1 $e |- F : ( al -> bool ) $.
    $( Alternative definition of the "there exists" quantifier.  (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    dfex2 $p |- T. |= [ ( ? F ) = ( F ( @ F ) ) ] $=
      ( vx kt tex kc tat tv wv ac wtru adantl exlimdv2 hb ht wat wc ax4e ded )
      EFBGZBHBGZGZADBEUCCBADIZGEUCAUDBCADJKLMNUCEUAAUBBCAOPAHBAQCRSLMT $.
  $}

  ${
    $d x y A $.  $d x al $.
    exmid.1 $e |- A : bool $.
    $( Diaconescu's theorem, which derives the law of the excluded middle from
       the axiom of choice.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    exmid $p |- T. |= [ A \/ ( ~ A ) ] $=
      ( vx vy tat hb tor kbr kc kt tne wor wc wnot wtru ke weqi id tfal wfal tv
      kl ht wat wv wov wl orc oveq1 cl mpbir ac syl ax-17 ax-hbl1 hbc hbov mpbi
      clf ceq2 tim simpr notval eqtru eqcomi a1i eqtri kct wct simpl simpld olc
      ex leq adantl simprd ax-cb1 mpd ecase ) EFCFCUAZAGHZUBZIZAJAKAIZGHZFFUCZF
      EWBFUDZFFCWAFFFVTAGLFCUEZBUFZUGZMZBFFFAWDGLBFFKANBMZUFZWBWCIZWCAGHZJJWBJI
      ZWNJAGHZWPJJAOBUHZFFCWAWQJWIOFFFVTAJGVTJPHZLWHBWSFVTJWHOQRUIUJUKFJWBWJOUL
      UMFFCDWAWOWCWIWKFFFVTAWCGVTWCPHZLWHBWTFVTWCWHWKQRUIFFFFCWCFDUAZAGJLWKFDUE
      ZBFFWFUCCGXALXBUNZFWFFCWBXAEJWGWJXBFWFFUCCEXAWGXBUNZFFFCWAXAWIXBUOUPZFFCA
      XABXBUNZUQXEUSURWCJWEKEFCKVTIZAGHZUBZIZIZAWCWEFFKXJNWFFEXIWGFFCXHFFFXGAGL
      FFKVTNWHMZBUFZUGZMZMZBWMXKAGHZWCWKXIXJIZXQJJXISIZXRWQXSJWRFFCXHWQSXMTFFFX
      GAJGVTSPHZLXLBFXGKSIZJXTXLFFVTSKXTNWHXTFVTSWHTQZRUTYAJPHXTYBFJYAJOYAJSSVA
      HYAJJSSJSOTVBVMSTVCUKVDVEVFVGUIUJUKFSXIXNTULUMFFCDXHXQXJXMXOFFFXGAXKGVTXJ
      PHZLXLBFFVTXJKYCNWHYCFVTXJWHXOQRUTUIFFFFCXKXAAGJLXPXBBXCFFFCXJXAKJNXOXBFW
      FCKXANXBUNFWFFCXIXAEJWGXNXBXDFFFCXHXAXMXBUOUPZUPXFUQYDUSURVFWCXKVHZWDWEAS
      VAHZWDYEYEASYEAVHZXJSTWCXJYGYGWCXKYEAWCXKWKXPVIZBVJZVKAYEWCXJPHWFFWBXIEAW
      GWJFFCWAXHAWIFWAJXHAWIFJWAAOWAAVTAWHBVLVDVEXHAXGAXLBVLVDVGVNUTYHVOURXKXJS
      VAHZYGYGWCXKYIVPXKYJPHYGYEYGYIVQXJXOVCVFURVRVMWDYFPHYEYHABVCVFUKAWDBWLVLU
      MAWCWEAWDBWLUHZWKVOVSOVOAJWEYKOVOVS $.

    $( Rule of double negation.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    notnot $p |- T. |= [ A = ( ~ ( ~ A ) ) ] $=
      ( tne kc notnot1 hb wnot tor kbr ax-cb2 exmid a1i simpr kct tfal wfal tim
      wc id ke notval mpbi imp pm2.21 syl ecase dedi ) ACCADZDZABEZAUHUIABFFCAG
      BRZBAUHHIUIUIAUJJZABKLUIAULBMUIUHNOAUIUHOUKPUIUHOQIZUIUIULSUIUMTIUIULUHUK
      UALUBUCABUDUEUFUG $.

    $( Theorem 19.14 of [Margaris] p. 90.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    exnal $p |- T. |=
      [ ( ? \ x : al . ( ~ A ) ) = ( ~ ( ! \ x : al . A ) ) ] $=
      ( hb tne tex kc kl tal kt wnot ht wex wc wl wal alnex ceq2 notnot 3eqtr4i
      eqcomi leq ) EFFGABFCHZIZHZHZHFJABFUDHZIZHZHKUFFJABCIZHZHEEFUGLEEFUFLAEMZ
      EGUEANAEBUDEEFCLDOZPOZOZOEEUGUJFKLUPEUJUGKUMEJUIAQZAEBUHEEFUDLUNOPOABUDUN
      RUBSUFUOTEEULUJFKLUMEJUKUQAEBCDPZOUMEUKUIJKUQURAEBCUHKDCDTUCSSUA $.
  $}

  $( The axiom of infinity: the set of "individuals" is not Dedekind-finite.
     Using the axiom of choice, we can show that this is equivalent to an
     embedding of the natural numbers in ` ind ` .  (Contributed by Mario
     Carneiro, 10-Oct-2014.) $)
  ax-inf $a |- T. |= ( ? \ f : ( ind -> ind ) .
    [ ( 1-1 f : ( ind -> ind ) ) /\ ( ~ ( onto f : ( ind -> ind ) ) ) ] ) $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                       Rederive the Metamath axioms
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    ax1.1 $e |- R : bool $.
    ax1.2 $e |- S : bool $.
    $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  (Contributed by Mario
       Carneiro, 9-Oct-2014.) $)
    ax1 $p |- T. |= [ R ==> [ S ==> R ] ] $=
      ( kt tim kbr kct wtru simpr adantr ex ) EABAFGEAHZBAMBAEAICJDKLL $.

    ax2.3 $e |- T : bool $.
    $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  (Contributed by Mario
       Carneiro, 9-Oct-2014.) $)
    ax2 $p |- T. |=
      [ [ R ==> [ S ==> T ] ] ==> [ [ R ==> S ] ==> [ R ==> T ] ] ] $=
      ( kt tim kbr kct hb wim wov wct simpr simpl simprd mpd simpld ex adantl
      wtru ) GABCHIZHIZABHIZACHIZHIZUDGUGUDUEUFUDUEJZACUHAJZBCFUIABEUHAUDUEKKKA
      UCHLDKKKBCHLEFMZMKKKABHLDEMNZDOZUIUDUEUHAUKDPZQRUIAUCUJULUIUDUEUMSRRTTUBU
      AT $.
  $}

  ${
    ax3.1 $e |- R : bool $.
    ax3.2 $e |- S : bool $.
    $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  (Contributed by Mario
       Carneiro, 10-Oct-2014.) $)
    ax3 $p |- T. |= [ [ ( ~ R ) ==> ( ~ S ) ] ==> [ S ==> R ] ] $=
      ( kt tne kc tim kbr kct hb wnot wc tor wim a1i ax-cb1 tfal imp ex wov wct
      exmid simpr wfal id ke notval mpbi an32s pm2.21 syl ecase wtru adantl ) E
      FAGZFBGZHIZBAHIZUREUSURBAAUPURBJZACKKFALCMZCAUPNIZUTURBKKKUPUQHOVAKKFBLDM
      ZUAZDUBACUCPZUTAVBUTVEQCUDUTUPJRARURUPBURUPJZBRDUEUQBRHIZVFURUPUQVAVCURVD
      UFSZUQVGUGIVFUQVFVHQBDUHPUISUJACUKULUMTUNUOT $.
  $}

  ${
    axmp.1 $e |- S : bool $.
    axmp.2 $e |- T. |= R $.
    axmp.3 $e |- T. |= [ R ==> S ] $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See e.g.  Rule 1 of [Hamilton] p. 73.  (Contributed by Mario
       Carneiro, 10-Oct-2014.) $)
    axmp $p |- T. |= S $=
      ( kt mpd ) FABCDEG $.
  $}

  ${
    $d y R $.  $d y S $.  $d x y al $.
    ax5.1 $e |- R : bool $.
    ax5.2 $e |- S : bool $.
    $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105.
       (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax5 $p |- T. |= [ ( ! \ x : al . [ R ==> S ] ) ==>
      [ ( ! \ x : al . R ) ==> ( ! \ x : al . S ) ] ] $=
      ( vy kt tal tim kbr kl kc ax4 hb ht wl adantl ax-hbl1 hbc kct wal wim wov
      wc ax-cb1 adantr mpd tv wv ax-17 hbct alrimi ex wtru ) HIABCDJKZLZMZIABCL
      ZMZIABDLMZJKZURHVBURUTVAABGDURUTUAZVCCDFUTURCABCENZAOPZOIUQAUBZAOBUPOOOCD
      JUCEFUDZQZUEZRURUTUPABUPVGNCUTVDUFZUGUHABURAGUIZUTHVIAGUJZVJAVEOBUQVKIHVF
      VHVLAVEOPBIVKVFVLUKZAAOBUPVKVGVLSTAVEOBUSVKIHVFAOBCEQVLVMAAOBCVKEVLSTULUM
      UNUORUN $.
  $}

  ${
    $d y R $.  $d x y al $.
    ax6.1 $e |- R : bool $.
    $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.
       (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax6 $p |- T. |= [ ( ~ ( ! \ x : al . R ) ) ==>
      ( ! \ x : al . ( ~ ( ! \ x : al . R ) ) ) ] $=
      ( vy tne tal kl kc hb wnot ht wal wl wc tv kt wv ax-17 hbc ax-hbl1 isfree
      ) ABEFGABCHZIZIJJFUDKAJLZJGUCAMZAJBCDNZOZOAJJBUDAEPZFQKUHAERZAJJLBFUIKUJS
      AUEJBUCUIGQUFUGUJAUEJLBGUIUFUJSAAJBCUIDUJUATTUB $.
  $}

  ${
    $d z R $.  $d x y z al $.
    ax7.1 $e |- R : bool $.
    $( Axiom of Quantifier Commutation.  Axiom scheme C6' in [Megill] p. 448
       (p. 16 of the preprint).  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    ax7 $p |- T. |= [ ( ! \ x : al . ( ! \ y : al . R ) ) ==>
      ( ! \ y : al . ( ! \ x : al . R ) ) ] $=
      ( vz kt tal kl kc hb ht wal wl wc ax4 ax-17 ax-hbl1 hbc alrimi syl tv hbl
      wv wtru adantl ex ) GHABHACDIZJZIZJZHACHABDIJZIJZUKGUMACFULUKABFDUKUKUIDA
      BUIAKLZKHUHAMZAKCDENZOZPACDEPUAAUNKBUJAFUBZHGUOAKBUIUQNZAFUDZAUNKLZBHURUO
      UTQAAKBUIURUQUTRSTAUNKCUJURHGUOUSUTAVACHURUOUTQZAAKCBUIURGUQUTAUNKCUHURHG
      UOUPUTVBAAKCDUREUTRSUCSTUEUFUG $.
  $}

  ${
    $d x al $.
    axgen.1 $e |- T. |= R $.
    $( Rule of Generalization.  See e.g.  Rule 2 of [Hamilton] p. 74.
       (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    axgen $p |- T. |= ( ! \ x : al . R ) $=
      ( kt alrimiv ) ABCEDF $.
  $}

  ${
    ax8.1 $e |- A : al $.
    ax8.2 $e |- B : al $.
    ax8.3 $e |- C : al $.
    $( Axiom of Equality.  Axiom scheme C8' in [Megill] p. 448 (p. 16 of the
       preprint).  Also appears as Axiom C7 of [Monk2] p. 105.  (Contributed by
       Mario Carneiro, 10-Oct-2014.) $)
    ax8 $p |- T. |= [ [ A = B ] ==> [ [ A = C ] ==> [ B = C ] ] ] $=
      ( kt ke kbr tim kct weqi simpl eqcomi simpr eqtri ex wtru adantl ) HBCIJZ
      BDIJZCDIJZKJZUAHUDUAUBUCACBDUAUBLZFABCUEEUAUBABCEFMZABDEGMZNOUAUBUFUGPQRS
      TR $.
  $}

  ${
    $d y A $.  $d x y al $.
    ax9.1 $e |- A : al $.
    $( Axiom of Equality.  Axiom scheme C8' in [Megill] p. 448 (p. 16 of the
       preprint).  Also appears as Axiom C7 of [Monk2] p. 105.  (Contributed by
       Mario Carneiro, 10-Oct-2014.) $)
    ax9 $p |- T. |= ( ~ ( ! \ x : al . ( ~ [ x : al = A ] ) ) ) $=
      ( vy tne tex tv kl kc tal kt wv hb ht wl ax-17 wtru wc wnot ke weqi 19.8a
      kbr wex ax-hbl1 hbc eqid eqtru eqcomi ax-inst notnot1 syl wal alnex mpbir
      id ceq2 ) FFGABABHZCUAUDZIZJZJZJZFKABFUTJZIZJZJLLVBVDABEVBVBCUTLABUTAUSCA
      BMDUBZUCAANOZNBVAAEHZGLAUEZANBUTVHPZAEMZAVINOBGVJVKVMQAANBUTVJVHVMUFUGANB
      LVJRVMQNVBUTVHVINGVAVKVLSZUHNLUTUTRUTUTUTVHUQUIUJUKVBVNULUMNNVGVCFLTVINKV
      FAUNANBVENNFUTTVHSPSABUTVHUOURUP $.
  $}

  ${
    $d x y z al $.
    $( Axiom of Quantifier Substitution.  Appears as Lemma L12 in [Megill]
       p. 445 (p. 12 of the preprint).  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    ax10 $p |- T. |= [ ( ! \ x : al . [ x : al = y : al ] ) ==>
      ( ! \ y : al . [ y : al = x : al ] ) ] $=
      ( vz kt tal tv ke kbr kl kc wv weqi hb weq wov id oveq1 cla4v wl eqtri ht
      ax4 eqcomi alrimiv wal wc cbv ceq2 a1i mpbir wtru adantl ex ) EFABABGZACG
      ZHIZJZKZFACUPUOHIZJZKZUSEVBFADADGZUOHIZJZKZVBUSADVDUSAVCUPUOUSADLZABUQVCV
      CUPHIAUOUPABLZACLZMZVGAANUOUPVCHUOVCHIZAOZVHVIVKAANUOVCHVLVHVGPQRSAUOUPUS
      VHABUQVJUCUDUAUEVBVFHIUSANUBZNFURAUFZANBUQVJTUGVMNVAVEFEVNANCUTAUPUOVIVHM
      ZTANCDUTVDVOAANUPUOVCHUPVCHIZVLVIVHVPAUPVCVIVGMQRUHUIUJUKULUMUN $.
  $}

  ${
    $d x A $.  $d x y al $.
    ax11.1 $e |- A : bool $.
    $( Axiom of Variable Substitution.  It is based on Lemma 16 of [Tarski]
       p. 70 and Axiom C8 of [Monk2] p. 105, from which it can be proved by
       cases.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax11 $p |- T. |= [ [ x : al = y : al ] ==> [ ( ! \ y : al . A ) ==>
      ( ! \ x : al . [ [ x : al = y : al ] ==> A ] ) ] ] $=
      ( kt tv ke kbr tal kl kc tim kct hb wl wc id a1i ex ht wal eta ceq2 mpbir
      wv wim weqi wov simpr ax-cb1 ax-cb2 simpl wct beta eqtri mpbi wtru adantl
      alrimiv ax5 mpd syl ) FABGZACGZHIZJACDKZLZJABVFDMIZKZLZMIFVFNZVHVKVHVLVKV
      HJABVGVDLZKZLZVKVHVOVHVHAOUAZOJVGAUBZAOCDEPZQZRVOVHHIZVHVSVPOVNVGJFVQAOBV
      MAOVGVDVRABUFZQZPZAOBVGVRUCUDZSUEVOVOVKVPOJVJVQAOBVIOOOVFDMUGAVDVEWAACUFU
      HZEUIZPQZVOVPOJVNVQWCQZRVOVKMIZVOWHFJABVMVIMIZKLWIOOOVOVKMUGVOVFVHNZVHVOW
      KVFVHWEVSUJZVTWKVHWKWLUKWDSUEULWGUIABWJFFVMVIVMFVIVMVFDVMDVMVFNZVMVFWBWEU
      MOVMVGVELZDWMWBAOVDVEVGWMVRWAVMVFWBWEUJUDWNDHIWMVMVFWBWEUNAOCDEUOSUPUQTUR
      USTUTABVMVIWBWFVAVBSVBVCFVFURWEUNUSTT $.
  $}

  ${
    $d p x z $.  $d p y z $.  $d p z al $.
    $( Axiom of Quantifier Introduction.  Axiom scheme C9' in [Megill] p. 448
       (p. 16 of the preprint).  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    ax12 $p |- T. |=
      [ ( ~ ( ! \ z : al . [ z : al = x : al ] ) ) ==>
        [ ( ~ ( ! \ z : al . [ z : al = y : al ] ) ) ==>
    [ [ x : al = y : al ] ==> ( ! \ z : al . [ x : al = y : al ] ) ] ] ] $=
      ( vp kt tne tal tv ke kbr kl kc tim wv weqi hb wnot wl wc ax-17 isfree ht
      wal adantr ex ) FGHADADIZABIZJKZLZMZMZGHADUGACIZJKZLZMZMZUHUMJKZHADURLMNK
      ZNKZFULUTFUQUSFUQUSADEURAUHUMABOZACOZPZAQDURAEIVCAEOUAUBQQGUPRAQUCZQHUOAU
      DZAQDUNAUGUMADOZVBPSTTUEUFQQGUKRVDQHUJVEAQDUIAUGUHVFVAPSTTUEUF $.
  $}

  ${
    ax13.1 $e |- A : al $.
    ax13.2 $e |- B : al $.
    ax13.3 $e |- C : ( al -> bool ) $.
    $( Axiom of Equality.  Axiom scheme C12' in [Megill] p. 448 (p. 16 of the
       preprint).  It is a special case of Axiom B8 (p. 75) of system S2 of
       [Tarski] p. 77.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax13 $p |- T. |= [ [ A = B ] ==> [ ( C A ) ==> ( C B ) ] ] $=
      ( kt ke kbr kc tim kct wtru weqi wct hb wc simpr ex ceq2 adantr mpbi ) HB
      CIJZDBKZDCKZLJHUDMZUEUFUEUFUGUEMUGUEHUDNABCEFOZPAQDBGERZSUGUEUEUFIJAQBCDU
      GGEHUDNUHSUAUIUBUCTT $.
  $}

  ${
    ax14.1 $e |- A : ( al -> bool ) $.
    ax14.2 $e |- B : ( al -> bool ) $.
    ax14.3 $e |- C : al $.
    $( Axiom of Equality.  Axiom scheme C12' in [Megill] p. 448 (p. 16 of the
       preprint).  It is a special case of Axiom B8 (p. 75) of system S2 of
       [Tarski] p. 77.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax14 $p |- T. |= [ [ A = B ] ==> [ ( A C ) ==> ( B C ) ] ] $=
      ( kt ke kbr kc tim kct wtru hb ht weqi wct simpr ex wc ceq1 adantr mpbi )
      HBCIJZBDKZCDKZLJHUEMZUFUGUFUGUHUFMUHUFHUENAOPBCEFQZRAOBDEGUAZSUHUFUFUGIJA
      ODBUHCEGHUENUISUBUJUCUDTT $.
  $}

  ${
    $d x y A $.  $d x y al $.
    ax17m.1 $e |- A : bool $.
    $( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax17m $p |- T. |= [ A ==> ( ! \ x : al . A ) ] $=
      ( vy hb tv wv ax-17 isfree ) ABECDAFBCAEGDAEHIJ $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y al $.
    axext.1 $e |- A : ( al -> bool ) $.
    axext.2 $e |- B : ( al -> bool ) $.
    $( Axiom of Extensionality.  An axiom of Zermelo-Fraenkel set theory.  It
       states that two sets are identical if they contain the same elements.
       Axiom Ext of [BellMachover] p. 461.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    axext $p |- T. |=
      [ ( ! \ x : al . [ ( A x : al ) = ( B x : al ) ] ) ==> [ A = B ] ] $=
      ( vy kt tal tv kc ke kbr kl hb ht wv wc wl eta weqi ax4 wal ax-17 ax-hbl1
      hbc leqf ax-cb1 a1i 3eqtr3i wtru adantl ex ) HIABCABJZKZDUNKZLMZNZKZCDLMZ
      USHUTAOPZABUONZABUPNZUSCDAOBUOAOCUNEABQZRZSAOBGUOUPUSVEABUQOUOUPVEAODUNFV
      DRUAZUBAVAOBURAGJZIHAUCZAOBUQVFSAGQZAVAOPBIVGVHVIUDAAOBUQVGVFVIUEUFUGZVBC
      LMUSVBVCLMUSVJUHZAOBCETUIVCDLMUSVKAOBDFTUIUJUKULUM $.
  $}

  ${
    $d f A $.  $d f y B $.  $d f y al $.  $d f x y be $.  $d f y z be $.
    axrep.1 $e |- A : bool $.
    axrep.2 $e |- B : ( al -> bool ) $.
    $( Axiom of Replacement.  An axiom scheme of Zermelo-Fraenkel set theory.
       Axiom 5 of [TakeutiZaring] p. 19.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    axrep $p |- T. |= [ ( ! \ x : al . ( ? \ y : be . ( ! \ z : be .
      [ ( ! \ y : be . A ) ==> [ z : be = y : be ] ] ) ) ) ==>
      ( ? \ y : ( be -> bool ) .
        ( ! \ z : be . [ ( y : ( be -> bool ) z : be ) =
          ( ? \ x : al . [ ( B x : al ) /\ ( ! \ y : be . A ) ] ) ] ) ) ] $=
      ( kt tal tex kl kc ke kbr hb ht wl wc vf hga tim tan wal wex wim weqi wov
      tv wv wtru wan eqid alrimiv a1i ax-cb1 weq id ceq1 beta eqtri oveq1 ax-17
      ax-hbl1 hbov leqf ceq2 hbl1 hbc hbl clf mpbir ax4e syl adantl ex ) JKACLB
      DKBEKBDFMZNZBEUJZBDUJZOPZUCPZMZNZMZNZMZNZLBQRZDKBEWJDUJZVTNZLACGACUJZNZVS
      UDPZMZNZOPZMZNZMZNZWIJXBWIXABEWQMZNZXBKBEWQWQOPZMZNZXDWIXGWIAQRZQKWHAUEAQ
      CWGWJQLWFBUFZBQDWEWJQKWDBUEZBQEWCQQQVSWBUCUGWJQKVRXJBQDFHSZTZBVTWABEUKZBD
      UKUHUISTSTSTBEXEJQWQJULXHQLWPAUFZAQCWOQQQWNVSUDUMAQGWMIACUKTZXLUIZSZTZUNU
      OUPZXDXGOPWIXGWIXSUQWJQDUAWTXGXCWJQKWSXJBQEWRQWLWQBQWKVTWJDUKZXMTZXRUHZSZ
      TZBQEWQXRSZWJQWSXFKWKXCOPZXJYCBQEUAWRXEYFYBQQQWLWQWQOYFQURZYAXRQWLXCVTNZW
      QYFYABQVTWKYFXCXTXMYFWJWKXCXTYEUHZUSUTYHWQOPYFYIBQEWQXRVAUPVBVCBWJWJQEWKB
      UAUJZXCOJWJURXTBUAUKZYEBQQQRRZEOYJYGYKVDBWJEWKYJXTYKVDBBQEWQYJXRYKVEVFVGV
      HWJWJQDXFWJUAUJZKJXJBQEXEQWQWQXRXRUHZSWJUAUKZWJWJQRZDKYMXJYOVDZWJBQDEXEYM
      JYNYOWJQQQDWQYMWQOJYGXRYOXRWJUBUBQRRDOYMUBURYOVDWJXHQDWPYMLJXNXQYOWJYPDLY
      MXIYOVDWJAQDCWOYMJXPYOWJQQQDWNYMVSUDJUMXOYOXLWJYLDUDYMUMYOVDWJQDWNYMXOYOV
      DWJWJQDVRYMKJXJXKYOYQWJBQDFYMJHYOULVIVJVFVKVJZYRVFVKVJWJBQDEWQYMJXRYOYRVK
      VLUPVMWJXCXAWJQDWTYDSYEVNVOULVPVQ $.
  $}

  ${
    $d x y $.  $d y A $.  $d p y z al $.
    axpow.1 $e |- A : ( al -> bool ) $.
    $( Axiom of Power Sets.  An axiom of Zermelo-Fraenkel set theory.
       (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    axpow $p |- T. |=
      ( ? \ y : ( ( al -> bool ) -> bool ) . ( ! \ z : ( al -> bool ) .
        [ ( ! \ x : al .
            [ ( z : ( al -> bool ) x : al ) ==> ( A x : al ) ] ) ==>
          ( y : ( ( al -> bool ) -> bool ) z : ( al -> bool ) ) ] ) ) $=
      ( vp kt tal hb tv kc tim kbr kl wtru wim wv wc wl ht tex wal wov simpl ex
      alrimiv ke weqi id ceq1 eqid cl a1i eqtri oveq2 leq ceq2 cla4ev syl ) HIA
      JUAZDIABVADKZABKZLZEVCLZMNZOZLZHMNZOZLZUBVAJUAZCIVADVHVLCKZVBLZMNZOZLZOLV
      ADVIHHVHHHVHPVAJIVGAUCAJBVFJJJVDVEMQAJVBVCVADRZABRZSAJEVCFVSSUDTSZUEUFUGV
      LCVQVAGHOZVKVLJIVPVAUCZVAJDVOJJJVHVNMQVTVAJVMVBVLCRZVRSZUDZTZSVAJGHPTZVLJ
      VPVJIVMWAUHNZWBWFVAJDVOVIWHWEJJJVHVNMWHHQVTWDJVNWAVBLZHWHWDVAJVBVMWHWAWCV
      RWHVLVMWAWCWGUIZUJUKWIHUHNWHWJVAJGHHVBPVRJHVAGKZVBUHNVAWKVBVAGRVRUIPULUMU
      NUOUPUQURUSUT $.
  $}

  ${
    $d x y $.  $d p y z $.  $d y A $.  $d y z al $.  $d p y z al $.
    axun.1 $e |- A : ( ( al -> bool ) -> bool ) $.
    $( Axiom of Union.  An axiom of Zermelo-Fraenkel set theory.  (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    axun $p |- T. |=
      ( ? \ y : ( al -> bool ) . ( ! \ z : al . [ ( ? \ x : ( al -> bool ) .
        [ ( x : ( al -> bool ) z : al ) /\ ( A x : ( al -> bool ) ) ] ) ==>
          ( y : ( al -> bool ) z : al ) ] ) ) $=
      ( vp kt tal tex hb tv kc kbr kl tim wtru wv wc wl tan kct wex wan wov wct
      ht trud ex alrimiv wal wim ke weqi id ceq1 a17i eqtri leq ceq2 cla4ev syl
      oveq2 ) HIADJAKUGZBVDBLZADLZMZEVEMZUANZOZMZHPNZOZMZJVDCIADVKVDCLZVFMZPNZO
      ZMZOMADVLHHVKHHVKUBHVKQVDKUGKJVJVDUCVDKBVIKKKVGVHUAUDAKVEVFVDBRZADRZSVDKE
      VEFVTSUETSZUFUHUIUJVDCVSAGHOZVNVDKIVRAUKZAKDVQKKKVKVPPULWBAKVOVFVDCRZWASZ
      UEZTZSAKGHQTZVDKVRVMIVOWCUMNZWDWHAKDVQVLWJWGKKKVKVPPWJHULWBWFKVPWCVFMHWJW
      FAKVFVOWJWCWEWAWJVDVOWCWEWIUNZUOUPAKGHVFWJQWAWKUQURVCUSUTVAVB $.
  $}

  $( ax-reg, ax-inf, and ax-ac are "true" in the broad strokes in HOL, but
     the set.mm versions of these axioms are not well-typed and so cannot be
     expressed. $)

$( $t

/* The '$ t' (no space between '$' and 't') token indicates the beginning
    of the typesetting definition section, embedded in a Metamath
    comment.  There may only be one per source file, and the typesetting
    section ends with the end of the Metamath comment.  The typesetting
    section uses C-style comment delimiters.  Todo:  Allow multiple
    typesetting comments */

/* These are the LaTeX and HTML definitions in the order the tokens are
    introduced in $c or $v statements.  See HELP TEX or HELP HTML in the
    Metamath program. */

/******* Web page format settings *******/

/* Page title, home page link */
htmltitle "Higher-Order Logic Explorer";
htmlhome '<A HREF="mmhol.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="hol.gif" BORDER=0 ALT=' +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE>' +
    'Home</FONT></A>';
/* Optional file where bibliographic references are kept */
/* If specified, e.g. "mmset.html", Metamath will hyperlink all strings of the
   form "[rrr]" (where "rrr" has no whitespace) to "mmset.html#rrr" */
/* A warning will be given if the file "mmset.html" with the bibliographical
   references is not present.  It is read in order to check correctness of
   the references. */
htmlbibliography "mmhol.html";

/* Variable color key at the bottom of each proof table */
htmlvarcolor '<FONT COLOR="#0000FF">type</FONT> '
    + '<FONT COLOR="#FF0000">var</FONT> '
    + '<FONT COLOR="#CC33CC">term</FONT>';

/* GIF and Unicode HTML directories - these are used for the GIF version to
   crosslink to the Unicode version and vice-versa */
htmldir "../holgif/";
althtmldir "../holuni/";


/******* Symbol definitions *******/

htmldef "wff" as '<FONT COLOR="#808080">wff </FONT>';
  althtmldef "wff" as '<FONT COLOR="#808080">wff </FONT>';
  latexdef "wff" as "\mathrm{wff}";
htmldef "var" as '<FONT COLOR="#808080">var </FONT>';
  althtmldef "var" as '<FONT COLOR="#808080">var </FONT>';
  latexdef "var" as "\mathrm{var}";
htmldef "type" as '<FONT COLOR="#808080">type </FONT>';
  althtmldef "type" as '<FONT COLOR="#808080">type </FONT>';
  latexdef "type" as "\mathrm{type}";
htmldef "term" as '<FONT COLOR="#808080">term </FONT>';
  althtmldef "term" as '<FONT COLOR="#808080">term </FONT>';
  latexdef "term" as "\mathrm{term}";
htmldef "|-" as
    "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 ALT='|-' ALIGN=TOP> ";
  althtmldef "|-" as
    '<FONT COLOR="#808080" FACE=sans-serif>&#8866; </FONT>'; /* &vdash; */
    /* Without sans-serif, way too big in FF3 */
  latexdef "|-" as "\vdash";
htmldef ":" as "<IMG SRC='colon.gif' WIDTH=4 HEIGHT=19 ALT=':' ALIGN=TOP>";
  althtmldef ":" as ':';
  latexdef ":" as ":";
htmldef "." as " ";
  althtmldef "." as ' ';
  latexdef "." as "\,";
htmldef "|=" as
    " <IMG SRC='models.gif' WIDTH=12 HEIGHT=19 ALT='|=' ALIGN=TOP> ";
  althtmldef "|=" as "&#8871;"; latexdef "|=" as "\models";
htmldef "bool" as
    "<IMG SRC='hexstar.gif' WIDTH=11 HEIGHT=19 ALT='*' ALIGN=TOP>";
  althtmldef "bool" as '&lowast;';
  latexdef "bool" as "\ast";
htmldef "ind" as
    "<IMG SRC='iota.gif' WIDTH=6 HEIGHT=19 ALT='iota' ALIGN=TOP>";
  althtmldef "ind" as '<FONT SIZE="+1">&iota;</FONT>';
  latexdef "ind" as "\iota";
htmldef "->" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 ALT='-&gt;' ALIGN=TOP> ";
  althtmldef "->" as ' &rarr; ';
  latexdef "->" as "\rightarrow";
htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT='(' ALIGN=TOP>";
  althtmldef "(" as "(";
  latexdef "(" as "(";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=')' ALIGN=TOP>";
  althtmldef ")" as ")";
  latexdef ")" as ")";
htmldef "," as "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=',' ALIGN=TOP> ";
  althtmldef "," as ', ';
  latexdef "," as ",";
htmldef "\" as "<IMG SRC='lambda.gif' WIDTH=9 HEIGHT=19 ALT='\' ALIGN=TOP>";
  althtmldef "\" as '<I>&lambda;</I>';
  latexdef "\" as "\lambda";
htmldef "=" as " <IMG SRC='eq.gif' WIDTH=12 HEIGHT=19 ALT='=' ALIGN=TOP> ";
  althtmldef "=" as ' = '; /* &equals; */
  latexdef "=" as "=";
htmldef "T." as "<IMG SRC='top.gif' WIDTH=11 HEIGHT=19 ALT='T.' ALIGN=TOP>";
  althtmldef "T." as '&#x22A4;';
  latexdef "T." as "\top";
htmldef "[" as "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT='[' ALIGN=TOP>";
  althtmldef "[" as '['; /* &lsqb; */
  latexdef "[" as "[";
htmldef "]" as "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=']' ALIGN=TOP>";
  althtmldef "]" as ']'; /* &rsqb; */
  latexdef "]" as "]";
htmldef "al" as
    "<IMG SRC='_alpha.gif' WIDTH=12 HEIGHT=19 ALT='al' ALIGN=TOP>";
  althtmldef "al" as '<FONT COLOR="#0000FF"><I>&alpha;</I></FONT>';
  latexdef "al" as "\alpha";
htmldef "be" as
    "<IMG SRC='_beta.gif' WIDTH=11 HEIGHT=19 ALT='be' ALIGN=TOP>";
  althtmldef "be" as '<FONT COLOR="#0000FF"><I>&beta;</I></FONT>';
  latexdef "be" as "\beta";
htmldef "ga" as
    "<IMG SRC='_gamma.gif' WIDTH=11 HEIGHT=19 ALT='ga' ALIGN=TOP>";
  althtmldef "ga" as '<FONT COLOR="#0000FF"><I>&gamma;</I></FONT>';
  latexdef "ga" as "\gamma";
htmldef "de" as
    "<IMG SRC='_delta.gif' WIDTH=9 HEIGHT=19 ALT='de' ALIGN=TOP>";
  althtmldef "de" as '<FONT COLOR="#0000FF"><I>&delta;</I></FONT>';
  latexdef "de" as "\delta";
htmldef "x" as "<IMG SRC='_x.gif' WIDTH=10 HEIGHT=19 ALT='x' ALIGN=TOP>";
  althtmldef "x" as '<I><FONT COLOR="#FF0000">x</FONT></I>';
  latexdef "x" as "x";
htmldef "y" as "<IMG SRC='_y.gif' WIDTH=9 HEIGHT=19 ALT='y' ALIGN=TOP>";
  althtmldef "y" as '<I><FONT COLOR="#FF0000">y</FONT></I>';
  latexdef "y" as "y";
htmldef "z" as "<IMG SRC='_z.gif' WIDTH=9 HEIGHT=19 ALT='z' ALIGN=TOP>";
  althtmldef "z" as '<I><FONT COLOR="#FF0000">z</FONT></I>';
  latexdef "z" as "z";
htmldef "f" as "<IMG SRC='_f.gif' WIDTH=9 HEIGHT=19 ALT='f' ALIGN=TOP>";
  althtmldef "f" as '<I><FONT COLOR="#FF0000">f</FONT></I>';
  latexdef "f" as "f";
htmldef "g" as "<IMG SRC='_g.gif' WIDTH=9 HEIGHT=19 ALT='g' ALIGN=TOP>";
  althtmldef "g" as '<I><FONT COLOR="#FF0000">g</FONT></I>';
  latexdef "g" as "g";
htmldef "p" as "<IMG SRC='_p.gif' WIDTH=10 HEIGHT=19 ALT='p' ALIGN=TOP>";
  althtmldef "p" as '<I><FONT COLOR="#FF0000">p</FONT></I>';
  latexdef "p" as "p";
htmldef "q" as "<IMG SRC='_q.gif' WIDTH=8 HEIGHT=19 ALT='q' ALIGN=TOP>";
  althtmldef "q" as '<I><FONT COLOR="#FF0000">q</FONT></I>';
  latexdef "q" as "q";
htmldef "A" as "<IMG SRC='_ca.gif' WIDTH=11 HEIGHT=19 ALT='A' ALIGN=TOP>";
  althtmldef "A" as '<I><FONT COLOR="#CC33CC">A</FONT></I>';
  latexdef "A" as "A";
htmldef "B" as "<IMG SRC='_cb.gif' WIDTH=12 HEIGHT=19 ALT='B' ALIGN=TOP>";
  althtmldef "B" as '<I><FONT COLOR="#CC33CC">B</FONT></I>';
  latexdef "B" as "B";
htmldef "C" as "<IMG SRC='_cc.gif' WIDTH=12 HEIGHT=19 ALT='C' ALIGN=TOP>";
  althtmldef "C" as '<I><FONT COLOR="#CC33CC">C</FONT></I>';
  latexdef "C" as "C";
htmldef "F" as "<IMG SRC='_cf.gif' WIDTH=13 HEIGHT=19 ALT='F' ALIGN=TOP>";
  althtmldef "F" as '<I><FONT COLOR="#CC33CC">F</FONT></I>';
  latexdef "F" as "F";
htmldef "R" as "<IMG SRC='_cr.gif' WIDTH=12 HEIGHT=19 ALT='R' ALIGN=TOP>";
  althtmldef "R" as '<I><FONT COLOR="#CC33CC">R</FONT></I>';
  latexdef "R" as "R";
htmldef "S" as "<IMG SRC='_cs.gif' WIDTH=11 HEIGHT=19 ALT='S' ALIGN=TOP>";
  althtmldef "S" as '<I><FONT COLOR="#CC33CC">S</FONT></I>';
  latexdef "S" as "S";
htmldef "T" as "<IMG SRC='_ct.gif' WIDTH=12 HEIGHT=19 ALT='T' ALIGN=TOP>";
  althtmldef "T" as '<I><FONT COLOR="#CC33CC">T</FONT></I>';
  latexdef "T" as "T";
htmldef "F." as "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT='F.' ALIGN=TOP>";
  althtmldef "F." as '&perp;';
  latexdef "F." as "\bot";
htmldef "/\" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 ALT='/\' ALIGN=TOP> ";
  althtmldef "/\" as ' <FONT FACE=sans-serif>&and;</FONT> ';
    /* althtmldef "/\" as ' <FONT FACE=sans-serif>&#8896;</FONT> '; */
    /* was &and; which is circle in Mozilla on WinXP Pro (but not Home) */
    /* Changed back 6-Mar-2012 NM */
  latexdef "/\" as "\wedge";
htmldef "~" as "<IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 ALT='~' ALIGN=TOP> ";
  althtmldef "~" as '&not; ';
  latexdef "~" as "\lnot";
htmldef "==>" as
    " <IMG SRC='bigto.gif' WIDTH=15 HEIGHT=19 ALT='==&gt;' ALIGN=TOP> ";
  althtmldef "==>" as ' &rArr; ';
  latexdef "==>" as "\Rightarrow";
htmldef "!" as "<IMG SRC='forall.gif' WIDTH=10 HEIGHT=19 ALT='A.' ALIGN=TOP>";
  althtmldef "!" as '<FONT FACE=sans-serif>&forall;</FONT>'; /* &#8704; */
  latexdef "!" as "\forall";
htmldef "?" as "<IMG SRC='exists.gif' WIDTH=9 HEIGHT=19 ALT='E.' ALIGN=TOP>";
  althtmldef "?" as '<FONT FACE=sans-serif>&exist;</FONT>'; /* &#8707; */
    /* Without sans-serif, bad in Opera and way too big in FF3 */
  latexdef "?" as "\exists";
htmldef "\/" as " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 ALT='\/' ALIGN=TOP> ";
  althtmldef "\/" as ' <FONT FACE=sans-serif> &or;</FONT> ' ;
    /* althtmldef "\/" as ' <FONT FACE=sans-serif>&#8897;</FONT> ' ; */
    /* was &or; - changed to match font of &and; replacement */
    /* Changed back 6-Mar-2012 NM */
  latexdef "\/" as "\vee";
htmldef "?!" as "<IMG SRC='_e1.gif' WIDTH=12 HEIGHT=19 ALT='E!' ALIGN=TOP>";
  althtmldef "?!" as '<FONT FACE=sans-serif>&exist;!</FONT>';
  latexdef "?!" as "\exists{!}";
htmldef "typedef" as "typedef ";
  althtmldef "typedef" as 'typedef ';
  latexdef "typedef" as "\text{ typedef }";
htmldef "1-1" as "1-1 ";
  althtmldef "1-1" as '1-1 ';
  latexdef "1-1" as "\mathrm{1-1}";
htmldef "onto" as "onto ";
  althtmldef "onto" as 'onto ';
  latexdef "onto" as "\mathrm{onto}";
htmldef "@" as
    "<IMG SRC='varepsilon.gif' WIDTH=8 HEIGHT=19 ALT='@' ALIGN=TOP>";
  althtmldef "@" as '&epsilon;';
  latexdef "@" as "\varepsilon";

/* End of typesetting definition section */
$)

$( 456789012345 (79-character line to adjust text window width) 567890123456 $)
