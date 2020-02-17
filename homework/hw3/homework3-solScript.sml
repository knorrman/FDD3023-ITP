(* ITP course 2020 - Homework 3
 * Karl Norrman
 *)

open HolKernel Parse boolLib bossLib listTheory;
open arithmeticTheory;

val _ = new_theory "homework3-sol";

(* 2.2 Prove !l. l ++ [] = l by induction using the definition of APPEND (++) *)
(* Note to self: >| is an alias for THENL. It applies the first tac in the list
 * to the first goal, the second to the second goal and so on.
 *)
Theorem lAppendNullIsL_thm:
    !l. l ++ [] = l                 (* Inner language *)
Proof
    Induct_on `l` >| [
        REWRITE_TAC [APPEND],       (* base case *)
        ASM_REWRITE_TAC [APPEND]    (* induction step *)
    ]
QED

(* prove !l1 l2 l3. l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3 *)
Theorem appendAssoc_thm:
    !l1 l2 l3. l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3
Proof
    Induct >| [
        Induct >| [                      (* base case ind-on-l1 *)
            REWRITE_TAC [APPEND],        (* base case ind-on-l2 *)
            ASM_REWRITE_TAC [APPEND]     (* induction step ind-on-l2 *)
        ],
        ASM_REWRITE_TAC [APPEND]         (* induction step ind-on-l1 *)
    ]
QED


(* 2.3 Via any useful theorems you can find, prove the theorem
 * !l1 l2. LENGTH (REV l1 l2) = (LENGTH l1 + LENGTH l2)
 *)
Theorem lenRevApp_thm:
    !l1 l2. LENGTH (REV l1 l2) = (LENGTH l1 + LENGTH l2)
Proof
    Induct_on `l1` >| [
        REWRITE_TAC [REV_DEF, LENGTH, ADD],            (* base case *)
        ASM_REWRITE_TAC [REV_DEF, LENGTH, ADD_CLAUSES] (* induction step *)
    ]
QED

(* Prove !l1 l2. REV l1 l2 = REVERSE l1 ++ l2 *)
Theorem  revAppendEQReverseOfAppend_thm:
    !l1 l2. REV l1 l2 = REVERSE l1 ++ l2
Proof
    Induct >| [
        REWRITE_TAC [REV_DEF, REVERSE, APPEND],          (* base case *)
        ASM_REWRITE_TAC [REV_DEF, REVERSE, APPEND_SNOC1] (* induction step *)
    ]
QED

(* prove !l. REVERSE l = REV l [] using the theorem just above *)
Theorem revAppendHelperLemma_thm:
    !l. REVERSE l = REV l []
Proof
    GEN_TAC >>
    ACCEPT_TAC ( (* accepts proof-goal if given theorem is the same (up to alhpa *)
        Q.SPECL [`l:'a list`, `[]:'a list`]  (* Q.SPECL: types not necessary *)
                    revAppendEQReverseOfAppend_thm |>
        Thm.SYM |>  (* s = t   ==>  t = s *)
        PURE_ONCE_REWRITE_RULE [APPEND_NIL]
    )
QED

(* After completing the proof above, I discussed it with Jonas, who suggested
 * the following modifications. These make more explicit use of the sequent
 * calculus. I keep them here for my own reference. *)
Theorem revAppendHelperLemma_JonasSuggestions_thm:
    !l. REVERSE l = REV l []
Proof
    GEN_TAC >>
    ASSUME_TAC (
        Q.SPECL [`l:'a list`, `[]:'a list`]
                    revAppendEQReverseOfAppend_thm |>
        Thm.SYM |>  (* s = t   ==>  t = s *)
        PURE_ONCE_REWRITE_RULE [APPEND_NIL]
    ) >>
    ASM_REWRITE_TAC
QED


val _ = export_theory();

