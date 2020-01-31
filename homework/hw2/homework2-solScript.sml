(* ITP course 2020 - Homework 2
 * Karl Norrman 2020-01-31
 *)

(* FEEDBACK: typos in exercie sheet:
 *
 * 1.4: FinalThm.sml, FinalTerm.sml etc seems to have changed names to
 * FinalThm-sig.sml etc.
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

val _ = export_theory()


