(* ITP course 2020 - Homework 2
 * Karl Norrman 2020-01-31
 *)

(* FEEDBACK: typos in exercie sheet:
 *
 * 1.4: FinalThm.sml, FinalTerm.sml etc seems to have changed names to
 * FinalThm-sig.sml etc.
 *
 * FEEDBACK: I will move the test code to a separate file once the solutions are
 * approved.  (That was feedback I received on Homework 1)
 *)

open HolKernel Parse boolLib bossLib
val _ = new_theory "homework2-sol"

(* 2.3 Constructing Terms
 * Write an SML function mk_imp_conj_term : int -> term that constructs, for
 * inputs n greater than 0, the term
 * !A1 ... An. A1 ==> ... ==> An ==> (A1 /\ ... /\ An). If n is 0 or less,
 * raise a HOL ERR exception (use failwith). You might want to read up on
 * boolSyntax for this task. You can use list-make functions such as
 * mk_list_conj, but also use non-list functions.
 *)

(* FEEDBACK: typo in exercise sheet: function is named list_mk_conj *)

(* First create list of As. Try different options to see which are fast
 * and clean
 *)

(* Straight forward: create term list of As in reverse order *)
fun mk_revAs 0 = []
  | mk_revAs n = mk_var ("A" ^ (Int.toString n), bool) :: mk_revAs (n - 1)


(* Tail recursive version, gives correct order of indices directly, presumably
 * faster but also messier code
 *)
fun mk_As2 0 = []
  | mk_As2 n =
    let fun mk_tr 0 _ xs = xs : term list
          | mk_tr m i xs =
              mk_tr (m - 1) (i - 1) (mk_var ("A" ^ Int.toString i, bool) :: xs)
    in
        mk_tr n n []
    end


(* The Parse.Term function may be useful for creating more complex terms *)
fun mk_As3 0 = []
  | mk_As3 n = Parse.Term [QUOTE ("A" ^ Int.toString n ^":bool")] :: mk_As3 (n - 1)


(* A more sml-Basis based version *)
fun mk_As4 n =
  let fun t i = mk_var ("A" ^ Int.toString i, bool)
  in
      List.drop (List.tabulate (n + 1, t), 1)
  end

(* Performance measurements are fluctuating wildely. How to measure? *)
val tim = Timer.startRealTimer ();
val n = 3500000;
mk_As4 n;
val measure = Timer.checkRealTimer tim; (* return time in seconds since created*)


fun mk_imp_conj_term n =
  if n <= 0 then failwith "mk_imp_conj_term: n <= 0"
  else
    let
      fun mk_As n =
        let fun t i = mk_var ("A" ^ Int.toString i, bool)
        in
            List.drop (List.tabulate (n + 1, t), 1)
        end
      val vars = mk_As n
      val conjTerm = list_mk_conj vars
      val impTerm = list_mk_imp (vars, conjTerm)
    in
      list_mk_forall (vars, impTerm)
    end


(* 3.1 Commutativity of Conjunction
 * Prove the theorem !A B. (A /\ B) <=> (B /\ A) using only inference rules
 * presented in lecture 2.
 *)
val commThm =
  let val a = mk_var ("A", bool)
      val b = mk_var ("B", bool)
      val tl = mk_conj (a, b)
      val assuml = ASSUME tl
      val fwdDir = CONJ (CONJUNCT2 assuml) (CONJUNCT1 assuml) |> DISCH tl
      val tr = mk_conj (b, a)
      val assumr = ASSUME tr
      val bwdDir = CONJ (CONJUNCT2 assumr) (CONJUNCT1 assumr) |> DISCH tr
  in
      IMP_ANTISYM_RULE fwdDir bwdDir |> GEN_ALL
  end


(* 3.2 Simplifying Conjunction
 * Prove the theorems !A. (A /\ ~A) <=> F and !A B. (A /\ ~A) /\ B <=> F.
 *)
val thm_32a =  (* !A. (A /\ ~A) <=> F *)
  let val tm_a = mk_var ("A", bool)
      (* Forward direction *)
      val tm_impcant = mk_conj (tm_a, mk_neg tm_a)
      val thm_impcant = ASSUME tm_impcant
      val thm_conjN = CONJUNCT2 thm_impcant
      val thm_conjP = CONJUNCT1 thm_impcant
      val thm_fwdDir =  thm_conjP
                     |> MP (NOT_ELIM thm_conjN)
                     |> DISCH tm_impcant
      (* Backward direction *)
      val thm_lemma = F_DEF |> EQ_IMP_RULE |> #1 |> UNDISCH
      val thm_bwdDir = CONJ
                         (SPEC tm_a thm_lemma)
                         (SPEC (mk_neg tm_a) thm_lemma)
                       |> DISCH F
  in
      IMP_ANTISYM_RULE thm_fwdDir thm_bwdDir |> GEN_ALL
  end

(* FIXME: Should be refactored. The two proofs are almost the same.
 * Make a rule that takes a list of terms and call that from both theorems
 *)
val thm_32b = (* !A B. (A /\ ~A) /\ B <=> F *)
  let val tm_a = mk_var ("A", bool)
      val tm_b = mk_var ("B", bool)
      (* Forward direction *)
      val tm_impcant = list_mk_conj [tm_a, mk_neg tm_a, tm_b]
      val thm_impcant = ASSUME tm_impcant
      val thm_conjN = CONJUNCT2 thm_impcant |> CONJUNCT1
      val thm_conjP = CONJUNCT1 thm_impcant
      val thm_fwdDir =  thm_conjP
                     |> MP (NOT_ELIM thm_conjN)
                     |> DISCH tm_impcant
      (* Backward direction *)
      val thm_lemma = F_DEF |> EQ_IMP_RULE |> #1 |> UNDISCH
      val thm_bwdDir = LIST_CONJ
                        [ SPEC tm_a thm_lemma
                        , SPEC (mk_neg tm_a) thm_lemma
                        , SPEC tm_b thm_lemma
                        ]
                        |> DISCH F
  in
      IMP_ANTISYM_RULE thm_fwdDir thm_bwdDir |> GEN tm_b |> GEN tm_a
  end


(*     4 Writing Your Own Automation
 *     4.1 Implications between Conjunctions
 *     Write a function show_big_conj_imp : term -> term -> thm that assumes that
 *     both terms are conjunctions and tries to prove that the first one implies
 *     the second one.  It should be clever enough to handle T and F.
 *
 * Note to self: It doesn't say in the description, but we assume there are
 * no quantifiers in the terms.
 *)

(* Create map from atoms in conjuction to thms proving they are derivable
 * from the conjunction
 *)
fun conjToThmMap tm =
  let fun recurse ctm rbt =
    let fun mapAdd m conclusion (proofStep, premise) =
      case Redblackmap.peek (m, conclusion) of
          SOME v => m
        | NONE => Redblackmap.insert (m, conclusion, (proofStep, premise))
    in
      if term_size ctm < 2 then
          failwith "conjToRBTree - Conjunctions require at least 2 operands"
      else if is_conj ctm then
        let val (t, ts) = dest_conj ctm
        in
          if (is_const ts)  orelse  (is_var ts) then
            (mapAdd (mapAdd rbt ts (CONJUNCT2, ctm))
                     t
                     (CONJUNCT1, ctm))
          else
            recurse ts
                    (mapAdd (mapAdd rbt ts (CONJUNCT2, ctm))
                            t
                            (CONJUNCT1, ctm))
        end
      else
          failwith "conjToRBTree - Term not a conjunction"
    end
  in
    recurse tm (Redblackmap.mkDict Term.compare)
  end

fun buildLitThm srcTm thmMap literal =
    if Term.compare (literal, srcTm) = EQUAL
    then
        ASSUME literal
    else case Redblackmap.peek (thmMap, literal) of
        SOME (thmBuilder, premise) => thmBuilder (buildLitThm srcTm thmMap premise)
      | NONE => failwith "buildLitThm - Implication does not hold"

fun buildConjThm srcTm thmMap trgTm =
  if is_conj trgTm then
    let val (t, ts) = dest_conj trgTm
    in
        CONJ (buildLitThm srcTm thmMap t) (buildConjThm srcTm thmMap ts)
    end
  else if (is_const trgTm)  orelse  (is_var trgTm) then
        buildLitThm srcTm thmMap trgTm
  else
        failwith "buildConjThm - Term not a conjunction"

fun show_big_conj_imp tm1 tm2 =
    buildConjThm tm1 (conjToThmMap tm1) tm2 |> DISCH_ALL

val x01 = ``x0 /\ x1``
val x02 = ``x0 /\ x2``
val x12 = ``x1 /\ x2``
val x02fa = ``x0 /\ fail``
val x012 = ``x0 /\ x1 /\ x2``
val x0123 = ``x0 /\ x1 /\ x2 /\ x3``

Redblackmap.listItems (conjToThmMap x0x1)

(* FIXME: Can't handle F and T properly yet *)
val tst_show_big_conj_imp = (
    show_big_conj_imp x01 x01;
    show_big_conj_imp x012 x01;
    show_big_conj_imp x012 x02;
    show_big_conj_imp x0123 x012
    )

(*     4.2 Equivalences between Conjunctions
 *     Use the function show_big_conj_imp to define a function
 *     show_big_conj_eq : term -> term -> thm that tries to shows the equivalence
 *     between the input terms. If both input terms are alpha-equivalent, it should
 *     raise an UNCHANGED exception. If the equivalence cannot be proved, a
 *     HOL_ERR exception should be raised.
 *
 * Note to self: Also here we assume that terms have no quantifiers. That makes
 * the test for alpha-equivalence superfluous since all variables are free.
 * Nontheless, we test for it just since the exercise asked for it.
 *)
fun show_big_conj_eq tm1 tm2 =
  if (Term.aconv tm1 tm2) then raise Conv.UNCHANGED
  else
    IMP_ANTISYM_RULE (show_big_conj_imp tm1 tm2) (show_big_conj_imp tm2 tm1)

val tst_show_big_conj_imp = (
    show_big_conj_eq ``x /\ y`` ``y /\ x``;
    show_big_conj_eq ``x /\ y /\ z`` ``y /\ z /\ x``
    )

(*     4.3 Duplicates in Conjunctions
 *     Use the function show_big_conj_eq to implement a conversion
 *     remove_dups_in_conj_CONV that replaces duplicate appearances of a term in a
 *     large conjunction with T.  Given the term a /\ (b /\ a) /\ c /\ b /\ a
 *     it should for example return
 *         |- (a /\ (b /\ a) /\ c /\ b /\ a) = (a /\ (b /\ T) /\ c /\ T /\ T).
 *     If no duplicates are found, UNCHANGED should be raised. If the input is not
 *     of type bool, a HOL ERR should be raised.
 *
 * Note to self: I'm not using the show_big_conj_eq function, so I'm probably
 * not providing the solution that was intended.
 *)
fun termToList tm =
  let val l = strip_conj tm   (* strip_conj is a fantastic function... *)
  in
    if exists (fn x => term_size x > 2) l then (* asm only lits have size < 3 *)
        failwith "termToList - not a conjunction"
    else
      l
  end

fun remove_dups_in_conj_CONV tm =
  let fun conv (lit, (m, trg)) =
          case (Redblackset.peek (m, lit)) of
               SOME _ => (m, T::trg)
             | NONE   => if Term.compare (lit, F) = EQUAL then
                    (m, F::trg) (* If F gets inserted, any duplicates of it
                                   will turn into T, which does not affect the
                                   boolean value of the term or violate
                                   the specification in the
                                   exercise, but feels very strange.
                                 *)
                else
                    (Redblackset.add (m, lit), lit::trg)
      val srcList = termToList tm
      val (m, l) = foldl conv (Redblackset.empty Term.compare, []) srcList
      val trgTm = list_mk_conj (rev l)
  in
    if (Term.compare (trgTm, tm) = EQUAL) then raise Conv.UNCHANGED else trgTm
  end

val tst_remove_dups_in_conj_CONV = (
    remove_dups_in_conj_CONV ``x/\y/\x/\y/\y``;
    remove_dups_in_conj_CONV ``T/\x/\y/\x/\T/\y``;
    remove_dups_in_conj_CONV ``x/\y/\F/\x/\F``;
    remove_dups_in_conj_CONV ``x/\y/\F/\T/\F``  (* UNCHANGED *)
    )

(*     4.4 Contradictions in Conjunctions
 *     Use the function show_big_conj_eq to implement a conversion
 *     find_contr_in_conj_CONV that searches for terms and their negations in a
 *     large conjunction. If such contradictions are found, the term should be
 *     converted to F. Given the term a /\ (b /\ ~a) /\ c it should for
 *     example return
 *               |- (a /\ (b /\ ~a) /\ c) = F.
 *     If no contradictions are found, UNCHANGED should be raised. If the
 *     input is not of type bool, a HOL ERR should be raised.
 *
 * FEEDBACK: the specification is unclear. Should the function convert a term
 * into another term (as described in the text) or should the function prove a
 * and return a theorem that the term
 * is equivalent to false as the example shows?
 * Suggestion: provide typing information for the function we should write.
 *
 * Note to self: I chose to do the former interpretation.
 * Note to self: Same as previous: I probably don't implement the intended
 * solution since I don't use the show_big_onj_eq function.
 *)
fun find_cont_in_conj_CONV tm =
  let val tmList = termToList tm
  in
    if exists (fn x =>
                   exists (fn y => Term.compare (mk_neg x, y) = EQUAL) tmList)
                   tmList
    then
        F
    else
        raise Conv.UNCHANGED
  end

val tst_find_cont_in_conj_CONV = (
    find_cont_in_conj_CONV ``x /\ ~x``;
    find_cont_in_conj_CONV ``x /\ y /\ ~x /\ z``;
    find_cont_in_conj_CONV ``x /\ y /\ ~x /\ z /\ ~y``;
    find_cont_in_conj_CONV ``x/\y`` (* UNCHANGED *)
    )
val _ = export_theory()

