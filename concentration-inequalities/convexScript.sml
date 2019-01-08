open HolKernel Parse boolLib bossLib;
open realLib;
open listTheory;
open pred_setTheory;
open realTheory;
open transcTheory;
open limTheory;

val _ = new_theory "convex";

fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;
val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);
val Suff = PARSE_TAC SUFF_TAC;

val convex_fn = Define
    `convex_fn = {f | ∀x y t. (0 <= t ∧ t <= 1) ==> f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y}`;

val exp_convex_lemma1 = store_thm
  ("exp_convex_lemma1",
   ``∀t. (t + (1 - t) * exp 0 - exp ((1 - t) * 0) = 0) ∧
     (t * exp 0 + (1 - t) - exp (t * 0) = 0)``,
   RW_TAC real_ss [EXP_0] >> REAL_ARITH_TAC);

val exp_convex_lemma2 = store_thm
  ("exp_convex_lemma2",
   ``∀t x. ((λx. (1 - t) * exp x - exp ((1 - t) * x)) diffl (λx. (1-t) * exp x - (1 - t)*exp ((1-t)*x)) x) x``,
   RW_TAC std_ss []
   >> `(λx. (1 - t) * exp x - exp ((1 - t) * x)) =
       (λx. (λx. (1 - t) * exp x) x - (λx. exp ((1 - t) * x)) x)`
    by RW_TAC std_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `((1 - t) * exp x - (1 - t) * exp ((1 - t) * x)) =
       (λx. (1 - t) * exp x) x - (λx. (1-t) * exp ((1- t) * x)) x`
    by RW_TAC std_ss []
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Suff `((λx. (1 - t) * exp x) diffl (λx. (1 - t) * exp x) x) x ∧
        ((λx. exp ((1 - t) * x)) diffl (λx. (1 - t) * exp ((1 - t) * x)) x) x`
   >- METIS_TAC [DIFF_SUB]
   >> CONJ_TAC
   >- (`(λx. (1 - t) * exp x) x = 0 * exp x + (exp x) * (λx. 1 - t) x` by RW_TAC real_ss [REAL_MUL_COMM]
       >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> Q.ABBREV_TAC `foo = (0 * exp x + exp x * (λx. 1 - t) x)`
       >> `(λx. (1 - t) * exp x) = (λx. (λx. 1 - t) x * exp x)` by RW_TAC std_ss [FUN_EQ_THM]
       >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> Q.UNABBREV_TAC `foo`
       >> MATCH_MP_TAC DIFF_MUL
       >> RW_TAC std_ss [DIFF_CONST, DIFF_EXP])
   >> `(λx. exp ((1 - t) * x)) = (λx. exp ((λx. (1-t)*x) x))` by RW_TAC std_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `(λx. (1 - t) * exp ((1 - t) * x)) x = exp ((λx. (1-t)*x) x) * (1-t)`
    by RW_TAC real_ss [REAL_MUL_COMM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Suff `((λx. (1 - t) * x) diffl (1-t)) x` >- METIS_TAC [DIFF_COMPOSITE]
   >> `(1 - t) = (1 - t) * 1` by RW_TAC real_ss []
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `(λx. (1 - t) * 1 * x) = (λx. (1-t) * (λx. x) x)` by RW_TAC real_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MATCH_MP_TAC DIFF_CMUL
   >> RW_TAC std_ss [DIFF_X]);

val exp_convex_lemma3 = store_thm
  ("exp_convex_lemma3",
   ``∀t x. (λx. (1-t) * exp x - exp ((1-t)*x)) contl x``,
   METIS_TAC [DIFF_CONT, exp_convex_lemma2]);

val exp_convex_lemma4 = store_thm
  ("exp_convex_lemma4",
   ``∀x. 0 < x ∧ 0 < t ∧ t < 1 ==> 0 < (λx. (1-t) * exp x - (1 - t)*exp ((1-t)*x)) x``,
   RW_TAC real_ss [REAL_LT_SUB_LADD] >> MATCH_MP_TAC REAL_LT_LMUL_IMP
   >> RW_TAC real_ss [REAL_LT_SUB_LADD, EXP_MONO_LT, REAL_SUB_RDISTRIB]
   >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR] >> MATCH_MP_TAC REAL_LT_MUL
   >> RW_TAC real_ss []);

val exp_convex_lemma5 = store_thm
  ("exp_convex_lemma5",
   ``∀f f' i j. (∀x. (f diffl f' x) x) ∧
        (∀x. f contl x) ∧
        (0 <= i ∧ i < j) ∧
        (∀x. i < x ∧ x < j ==> 0 < f' x) ==>
            f i < f j``,
   REPEAT STRIP_TAC
   >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `0 + f i` >> CONJ_TAC >- RW_TAC real_ss []
   >> RW_TAC real_ss [GSYM REAL_LT_SUB_LADD]
   >> `?l z. i < z ∧ z < j ∧ (f diffl l) z ∧ (f j - f i = (j - i) * l)`
    by (MATCH_MP_TAC MVT >> METIS_TAC [differentiable])
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MATCH_MP_TAC REAL_LT_MUL
   >> RW_TAC real_ss [REAL_LT_SUB_LADD]
   >> `l = f' z`
    by (MATCH_MP_TAC DIFF_UNIQ >> Q.EXISTS_TAC `f` >> Q.EXISTS_TAC `z` >> RW_TAC std_ss [])
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Q.PAT_X_ASSUM `∀x. i < x ∧ x < j ==> 0 < f' x` MATCH_MP_TAC >> RW_TAC std_ss []);

val exp_convex_lemma6 = store_thm
  ("exp_convex_lemma6",
   ``∀x y t. 0 < t ∧ t < 1 ∧ x < y ==>
        exp (t * x + (1 - t) * y) <= t * exp x + (1 - t) * exp y``,
   REPEAT STRIP_TAC
   >> Q.ABBREV_TAC `z = y - x`
   >> `0 < z` by (Q.UNABBREV_TAC `z` >> RW_TAC real_ss [REAL_LT_SUB_LADD])
   >> Suff `exp (t * x + (1 - t) * (x+z)) <= t * exp x + (1 - t) * exp (x+z)`
   >- (Q.UNABBREV_TAC `z` >> RW_TAC real_ss [])
   >> `t * x + (1 - t) * (x + z) = x + (1 - t) * z` by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> PURE_REWRITE_TAC [transcTheory.EXP_ADD]
   >> `t * exp x + (1 - t) * (exp x * exp z) = exp x * (t + (1 - t) * exp z)`
        by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> MATCH_MP_TAC REAL_LE_LMUL_IMP >> CONJ_TAC >- SIMP_TAC std_ss [EXP_POS_LE]
   >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `0 + exp ((1 - t) * z)` >> CONJ_TAC >- RW_TAC real_ss []
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_SUB_LADD]
   >> MATCH_MP_TAC REAL_LT_IMP_LE
   >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `t + (1 - t) * exp 0 - exp ((1 - t) * 0)`
   >> CONJ_TAC >- RW_TAC real_ss [exp_convex_lemma1]
   >> `t + (1 - t) * exp 0 - exp ((1 - t) * 0) = ((1 - t) * exp 0 - exp ((1 - t) * 0)) + t`
        by REAL_ARITH_TAC >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> ONCE_REWRITE_TAC [REAL_LT_ADD_SUB]
   >> `t + (1 - t) * exp z - exp ((1 - t) * z) - t = (1 - t) * exp z - exp ((1 - t) * z)`
        by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> Q.ABBREV_TAC `f = (λx. (1-t) * exp x - exp ((1-t)*x))`
   >> Suff `f 0 < f z` >- (Q.UNABBREV_TAC `f` >> RW_TAC std_ss [])
   >> MATCH_MP_TAC exp_convex_lemma5
   >> Q.EXISTS_TAC `(λx. (1-t) * exp x - (1 - t)*exp ((1-t)*x))`
   >> Q.UNABBREV_TAC `f`
   >> RW_TAC real_ss [exp_convex_lemma2, exp_convex_lemma3, exp_convex_lemma4]);

val exp_in_convex = store_thm
  ("exp_in_convex",
   ``exp IN convex_fn``,
   RW_TAC std_ss [convex_fn, EXTENSION, MEM, NOT_IN_EMPTY, GSPECIFICATION]
   >> Cases_on `t = 0` >- RW_TAC real_ss []
   >> Cases_on `t = 1` >- RW_TAC real_ss []
   >> `0 < t ∧ t < 1` by METIS_TAC [REAL_LT_LE]
   >> Cases_on `x = y` >- RW_TAC real_ss []
   >> (MP_TAC o Q.SPECL [`x`, `y`]) REAL_LT_TOTAL >> RW_TAC std_ss []
   >- (MATCH_MP_TAC exp_convex_lemma6 >> RW_TAC std_ss [])
   >> Q.ABBREV_TAC `t' = 1 - t`
   >> `t = 1 - t'` by (Q.UNABBREV_TAC `t'` >> REAL_ARITH_TAC)
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `0 < t'` by (Q.UNABBREV_TAC `t'` >> RW_TAC real_ss [REAL_LT_SUB_LADD])
   >> `t' < 1` by (Q.UNABBREV_TAC `t'` >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR])
   >> ONCE_REWRITE_TAC [REAL_ADD_COMM]
   >> MATCH_MP_TAC exp_convex_lemma6 >> RW_TAC std_ss []);

val exp_convex = store_thm(
  "exp_convex",
  ``∀x y l. (0 ≤ l) ∧ (l ≤ 1) ⇒ exp (l * x + (1 - l) * y) ≤ l * exp x + (1 - l) * exp y``,
  rpt strip_tac >> ASSUME_TAC exp_in_convex >> fs[convex_fn]
);

val _ = export_theory();
