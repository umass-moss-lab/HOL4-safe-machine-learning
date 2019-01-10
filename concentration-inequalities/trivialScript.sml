open HolKernel Parse boolLib bossLib;
open listTheory;
open pred_setTheory;
open realTheory;
open realLib;
open limTheory;
open transcTheory;
open extrealTheory;
open measureTheory;
open lebesgueTheory;
open probabilityTheory;

val _ = new_theory "trivial";

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Pred Set *)
(*---------------------------------------------------------------------------*)

val UNIV_FUN = store_thm(
    "UNIV_FUN",
    ``𝕌(:α) -> 𝕌(:β) = 𝕌(:α -> β)``,
    `∀f. (𝕌(:α) -> 𝕌(:β)) f = 𝕌(:α -> β) f` suffices_by metis_tac[] >> strip_tac >> fs[]
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Reals *)
(*---------------------------------------------------------------------------*)

val REAL_XOR_LT_GT_EQ = store_thm(
    "REAL_XOR_LT_GT_EQ",
    ``∀(x:real) y.
        ((x = y) ⇒ ¬(x < y) ∧ ¬(y < x)) ∧
        ((x < y) ⇒ (x ≠ y) ∧ ¬(y < x) ∧ ¬(y ≤ x)) ∧
        ((x ≤ y) ⇒ ¬(y < x))``,
    rpt strip_tac >> fs[REAL_LT_GT,REAL_LT_IMP_NE,real_lte]
);

val ADD_POS = store_thm(
    "ADD_POS",
    ``∀x y. ((0:real) ≤ x) ∧ (0 ≤ y) ∧ (x + y = 0) ⇒ (x = 0) ∧ (y = 0)``,
    rpt strip_tac >> Cases_on `x = 0` >> Cases_on `y = 0` >> fs[] >>
    `0 < x` by fs[REAL_LT_LE] >> `0 < y` by fs[REAL_LT_LE] >>
    `0 < x + y` by fs[REAL_LT_ADD] >> fs[REAL_XOR_LT_GT_EQ]
);

val SUM_GE0 = store_thm(
    "SUM_GE0",
    ``∀f n. (∀i. (i < n) ⇒ 0 ≤ f i) ⇒ 0 ≤ sum (0,n) f``,
    Induct_on `n` >> rpt strip_tac >> fs[sum] >>
    `0 ≤ sum (0,n) f` by fs[] >> `0 ≤ f n` by fs[] >>
    fs[REAL_LE_ADD]
);

val SUM_OF_POS_EQ_0 = store_thm(
    "SUM_OF_POS_EQ_0",
    ``∀f n. (sum (0,n) f = 0) ∧ (∀i. (i < n) ⇒ (0 ≤ f i)) ⇒
        (∀i. (i < n) ⇒ (f i = 0)) ∧ (∀m. (m < n) ⇒ (sum (0,m) f = 0))``,
    Induct_on `n` >> strip_tac >> fs[sum] >> strip_tac >>
    `0 ≤ sum (0,n) f` by fs[SUM_GE0] >> `0 ≤ f n` by fs[] >>
    `(sum (0,n) f = 0) ∧ (f n = 0)` by (strip_tac >> imp_res_tac ADD_POS) >>
    `(∀i. i < n ⇒ 0 ≤ f i)` by fs[] >> RES_TAC >> rpt strip_tac
    >- (Cases_on `i = n` >> fs[])
    >- (Cases_on `m = n` >> fs[])
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Limits/Derivatives *)
(*---------------------------------------------------------------------------*)

val DIFF_CADD = store_thm(
    "DIFF_CADD",
    ``∀f (c:real) l (x:real). (f diffl l) x ⇒ ((λx. c + f x) diffl l) x``,
    rpt strip_tac >>
    (ASSUME_TAC o ISPECL [``c:real``,``x:real``]) DIFF_CONST >>
    imp_res_tac DIFF_ADD >> fs[]
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Extended Reals *)
(*---------------------------------------------------------------------------*)

val sumfin_def = Define `(sumfin (n,0) f = 0) ∧
    (sumfin (n,SUC m) f = sumfin (n,m) f + f (n + m))`;
    
val prodfin_def = Define `(prodfin (n,0) f = 1) ∧
    (prodfin (n,SUC m) f = prodfin (n,m) f * f (n + m))`;

val sumfinfun_def = Define `(sumfinfun (n,0) f x = 0) ∧
    (sumfinfun (n,SUC m) f x = sumfinfun (n,m) f x + f (n + m) x)`;
    
val prodfinfun_def = Define `(prodfinfun (n,0) f x = 1) ∧
    (prodfinfun (n,SUC m) f x = prodfinfun (n,m) f x * f (n + m) x)`;

val closed_interval_def = Define `closed_interval a b = {x | a ≤ x ∧ x ≤ b}`;

val extreal_ln_def = Define
    `(extreal_ln (Normal x) = (if (x ≤ 0) then NegInf else Normal (ln x))) ∧
    (extreal_ln PosInf = PosInf) ∧ (extreal_ln NegInf = NegInf)`;
    
val _ = overload_on ("ln", Term `extreal_ln`);

val sumfinfun_alt = store_thm(
    "sumfinfun_alt",
    ``(∀n f. sumfinfun (n,0) f = (λx. 0)) ∧
        ∀n m f. sumfinfun (n,SUC m) f = (λx. sumfinfun (n,m) f x + f (n + m) x)``,
    rpt strip_tac
    >- (`∀x. sumfinfun (n,0) f x = (λx. 0) x` suffices_by metis_tac[] >>
        fs[sumfinfun_def])
    >- (`∀x. sumfinfun (n,SUC m) f x = (λx. sumfinfun (n,m) f x + f (n + m) x) x`
            suffices_by metis_tac[] >>
        fs[sumfinfun_def])
);

val prodfinfun_alt = store_thm(
    "prodfinfun_alt",
    ``(∀n f. prodfinfun (n,0) f = (λx. 1)) ∧
        ∀n m f. prodfinfun (n,SUC m) f = (λx. prodfinfun (n,m) f x * f (n + m) x)``,
    rpt strip_tac
    >- (`∀x. prodfinfun (n,0) f x = (λx. 1) x` suffices_by metis_tac[] >>
        fs[prodfinfun_def])
    >- (`∀x. prodfinfun (n,SUC m) f x = (λx. prodfinfun (n,m) f x * f (n + m) x) x`
            suffices_by metis_tac[] >>
        fs[prodfinfun_def])
);

val closed_interval_point = store_thm(
    "closed_interval_point",
    ``∀y. closed_interval y y = {y}``,
    strip_tac >> fs[closed_interval_def,EXTENSION,le_antisym]
);

val extreal_lt_alt = store_thm(
    "extreal_lt_alt",
    ``(Normal x < Normal y ⇔ x < y) ∧ (NegInf < PosInf ⇔ T) ∧
        (a < NegInf ⇔ F) ∧ (PosInf < b ⇔ F) ∧
        (NegInf < Normal r1 ⇔ T) ∧ (Normal r2 < PosInf ⇔ T)``,
    fs[extreal_lt_def,extreal_le_def,real_lte] >>
    Cases_on `b` >> fs[extreal_le_def]
);

val xor_lt_gt_eq = store_thm(
    "xor_lt_gt_eq",
    ``∀(x:extreal) y.
        ((x = y) ⇒ ¬(x < y) ∧ ¬(y < x)) ∧
        ((x < y) ⇒ (x ≠ y) ∧ ¬(y < x) ∧ ¬(y ≤ x)) ∧
        ((x ≤ y) ⇒ ¬(y < x))``,
    rpt strip_tac >> Cases_on `x` >> Cases_on `y` >> fs[extreal_le_def,extreal_lt_alt] >>
    fs[REAL_XOR_LT_GT_EQ]
);

val N0_EQ_0 = store_thm(
    "N0_EQ_0",
    ``Normal 0 = 0``,
    fs[extreal_eq_zero]
);

val N1_EQ_1 = store_thm(
    "N1_EQ_1",
    ``Normal 1 = 1``,
    fs[extreal_of_num_def]
);

val LE_NE_POSINF_IMP_NE_POSINF = store_thm(
    "LE_NE_POSINF_IMP_NE_POSINF",
    ``∀x y. (x ≤ y) ∧ (y ≠ PosInf) ⇒ (x ≠ PosInf)``,
    rpt strip_tac >> rw[] >> Cases_on `y` >> fs[extreal_le_def]
);

val NORM_REAL_NEG1 = store_thm(
    "NORM_REAL_NEG1",
    ``Normal (real (-1)) = -1``,
    ASSUME_TAC (ISPEC ``-1:extreal`` normal_real) >>
    `-1 ≠ NegInf ∧ -1 ≠ PosInf` suffices_by fs[] >> pop_assum kall_tac >>
    `-1 ≠ -PosInf ∧ -1 ≠ -NegInf` suffices_by fs[extreal_ainv_def] >>
    `1 ≠ PosInf ∧ 1 ≠ NegInf` suffices_by fs[eq_neg] >> Cases_on `1`
    >- (`inv 1 = inv NegInf` by fs[] >> fs[extreal_inv_def,inv_one])
    >- (`inv 1 = inv PosInf` by fs[] >> fs[extreal_inv_def,inv_one])
    >- (fs[])
);

val NORM_REAL_POS1 = store_thm(
    "NORM_REAL_POS1",
    ``Normal (real 1) = 1``,
    ASSUME_TAC (ISPEC ``1:extreal`` normal_real) >>
    `1 ≠ NegInf ∧ 1 ≠ PosInf` suffices_by fs[] >>
    pop_assum kall_tac >> Cases_on `1`
    >- (`inv 1 = inv NegInf` by fs[] >> fs[extreal_inv_def,inv_one])
    >- (`inv 1 = inv PosInf` by fs[] >> fs[extreal_inv_def,inv_one])
    >- (fs[])
);

val le_mul2 = store_thm(
    "le_mul2",
    ``∀x1 x2 y1 y2. (0:extreal) ≤ x1 ∧ 0 ≤ y1 ∧ x1 ≤ x2 ∧ y1 ≤ y2 ⇒ x1 * y1 ≤ x2 * y2``,
    rpt strip_tac >> `0 ≤ x2` by imp_res_tac le_trans >> `0 ≤ y2` by imp_res_tac le_trans >>
    `0 = Normal 0` by fs[N0_EQ_0] >> fs[] >> pop_assum kall_tac >>
    Cases_on `x1` >> Cases_on `y1` >> Cases_on `x2` >> Cases_on `y2` >>
    fs[extreal_mul_def,extreal_le_def] >> rw[] >> fs[extreal_le_def] >> rw[]
    >- (metis_tac[REAL_XOR_LT_GT_EQ,real_lte,REAL_LT_LE])
    >- (metis_tac[REAL_XOR_LT_GT_EQ,real_lte,REAL_LT_LE])
    >- (metis_tac[REAL_XOR_LT_GT_EQ,real_lte,REAL_LT_LE])
    >- (metis_tac[REAL_XOR_LT_GT_EQ,real_lte,REAL_LT_LE])
    >- (metis_tac[REAL_XOR_LT_GT_EQ,real_lte,REAL_LT_LE])
    >- (metis_tac[REAL_XOR_LT_GT_EQ,real_lte,REAL_LT_LE])
    >- (`r' = 0` by metis_tac[REAL_LE_ANTISYM] >> fs[])
    >- (metis_tac[REAL_XOR_LT_GT_EQ,real_lte,REAL_LT_LE])
    >- (`r = 0` by metis_tac[REAL_LE_ANTISYM] >> fs[])
    >- (metis_tac[REAL_XOR_LT_GT_EQ,real_lte,REAL_LT_LE])
    >- (fs[REAL_LE_MUL2])
);

val sumfin_replace = store_thm(
    "sumfin_replace",
    ``∀n f g. (∀i. i < n ⇒ (f i = g i)) ⇒ (sumfin (0,n) f = sumfin (0,n) g)``,
    Induct_on `n` >> rpt strip_tac >> fs[sumfin_def] >>
    `sumfin (0,n) f = sumfin (0,n) g` suffices_by (strip_tac >> fs[]) >> fs[]
);

val EXTR_MUL_CANCEL_LEFT = store_thm(
    "EXTR_MUL_CANCEL_LEFT",
    ``∀x y c. (c ≠ 0) ⇒ ((Normal c * x = Normal c * y) ⇔ (x = y))``,
    rpt strip_tac >> eq_tac >> strip_tac >> fs[] >>
    Cases_on `x` >> Cases_on `y` >> Cases_on `0 < c` >> fs[extreal_mul_def]
    >- (`NegInf=PosInf` by metis_tac[]>>fs[])
    >- (`PosInf=NegInf` by metis_tac[]>>fs[])
    >- (`NegInf=Normal (c * r)` by metis_tac[]>>fs[])
    >- (`PosInf=Normal (c * r)` by metis_tac[]>>fs[])
    >- (`PosInf=NegInf` by metis_tac[]>>fs[])
    >- (`NegInf=PosInf` by metis_tac[]>>fs[])
    >- (`PosInf=Normal (c * r)` by metis_tac[]>>fs[])
    >- (`NegInf=Normal (c * r)` by metis_tac[]>>fs[])
    >- (`Normal (c * r)=NegInf` by metis_tac[]>>fs[])
    >- (`Normal (c * r)=PosInf` by metis_tac[]>>fs[])
    >- (`Normal (c * r)=PosInf` by metis_tac[]>>fs[])
    >- (`Normal (c * r)=NegInf` by metis_tac[]>>fs[])
    >- (fs[])
    >- (fs[])
);

val EXTR_MUL_CANCEL_RIGHT = store_thm(
    "EXTR_MUL_CANCEL_RIGHT",
    ``∀x y c. (c ≠ 0) ⇒ ((x * Normal c = y * Normal c) ⇔ (x = y))``,
    rpt strip_tac >> eq_tac >> strip_tac >> fs[] >>
    `Normal c * x = Normal c * y` by fs[mul_comm] >>
    imp_res_tac EXTR_MUL_CANCEL_LEFT
);

val le_lmul_real = store_thm(
    "le_lmul_real",
    ``∀x y z. 0 < z ⇒ (x ≤ y ⇔ Normal z * x ≤ Normal z * y)``,
    rpt strip_tac >> eq_tac >> strip_tac
    >- (
        `Normal 0 < Normal z` by fs[extreal_lt_alt] >>
        fs[N0_EQ_0,le_lt,le_lmul_imp]
    )
    >- (
        `Normal 0 < Normal z` by fs[extreal_lt_alt] >> fs[N0_EQ_0] >>
        `Normal z ≠ PosInf` by fs[] >>
        imp_res_tac inv_pos >> `0 < inv (Normal z)` by fs[inv_1over] >>
        `0 ≤ inv (Normal z)` by fs[lt_le] >>
        `inv (Normal z) * (Normal z * x) ≤ inv (Normal z) * (Normal z * y)`
            by imp_res_tac le_lmul_imp >>
        `z ≠ 0` by fs[REAL_POS_NZ] >>
        fs[extreal_inv_def,mul_assoc,extreal_mul_def,REAL_MUL_LINV,N1_EQ_1,mul_lone]
    )
);

val ext_exp_pos_le = store_thm(
    "ext_exp_pos_le",
    ``∀(x:extreal). 0 ≤ exp x``,
    strip_tac >> `Normal 0 ≤ exp x` suffices_by fs[N0_EQ_0] >>
    Cases_on `x` >> fs[extreal_exp_def]
    >- (fs[le_refl])
    >- (fs[extreal_le_def])
    >- (fs[extreal_le_def,EXP_POS_LE])
);

val ext_exp_mono_le = store_thm(
    "ext_exp_mono_le",
    ``∀x y. exp x ≤ exp y ⇔ x ≤ y``,
    rpt strip_tac >> eq_tac >> strip_tac >>
    Cases_on `x` >> Cases_on `y` >>
    fs[extreal_le_def,extreal_exp_def,EXP_MONO_LE]
    >- (fs[EXP_POS_LT,real_lte])
    >- (fs[EXP_POS_LT,REAL_LT_IMP_LE])
);

val ext_exp_mono_lt = store_thm(
    "ext_exp_mono_lt",
    ``∀x y. exp x < exp y ⇔ x < y``,
    rpt strip_tac >> eq_tac >> strip_tac >>
    Cases_on `x` >> Cases_on `y` >>
    fs[extreal_lt_alt,extreal_exp_def,EXP_MONO_LT]
    >- ((qspec_then `r` assume_tac) EXP_POS_LT >> metis_tac[REAL_LT_ANTISYM])
    >- (fs[EXP_POS_LT])
);

val sumfin_normal = store_thm(
    "sumfin_normal",
    ``∀f n. sumfin (0,n) (λi. Normal (f i)) = Normal (sum (0,n) f)``,
    Induct_on `n` >> rpt strip_tac >> fs[sum,sumfin_def,N0_EQ_0,extreal_add_def]
);

val prodfin_le = store_thm(
    "prodfin_le",
    ``∀f g n. (∀i. i < n ⇒ 0 ≤ f i ∧ f i ≤ g i) ⇒
        0 ≤ prodfin (0,n) f ∧ prodfin (0,n) f ≤ prodfin (0,n) g``,
    NTAC 4 strip_tac >> Induct_on `n` >> fs[prodfin_def,le_refl]
    >- (`Normal 0 ≤ Normal 1` suffices_by fs[N0_EQ_0,N1_EQ_1] >>
        fs[extreal_le_def])
    >- (strip_tac >> fs[] >> `0 ≤ f n` by fs[] >> fs[le_mul] >>
        `f n ≤ g n` by fs[] >> fs[le_mul2])
);

val exp_sum = store_thm(
    "exp_sum",
    ``∀f n. prodfin (0,n) (λi. Normal (exp (f i))) = exp (sumfin (0,n) (λi. Normal (f i)))``,
    Induct_on `n` >> rpt strip_tac >> fs[prodfin_def,sumfin_def]
    >- (`Normal 1 = exp (Normal 0)` suffices_by fs[N0_EQ_0,N1_EQ_1] >>
        fs[extreal_exp_def,EXP_0])
    >- (fs[sumfin_normal,extreal_exp_def,extreal_mul_def,extreal_add_def,EXP_ADD])
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Measurable Sets and Functions *)
(*---------------------------------------------------------------------------*)

val EXP_MBL = store_thm(
    "EXP_MBL",
    ``exp ∈ measurable Borel Borel``,
    fs[IN_MEASURABLE_BOREL,SIGMA_ALGEBRA_BOREL,Borel_def,sigma_def,space_def,subsets_def,UNIV_FUN] >>
    rpt strip_tac >>
    `{x | exp x < c} ∈ IMAGE (λa. {x | x < a}) 𝕌(:extreal)`
        suffices_by (strip_tac >> metis_tac[SUBSET_DEF]) >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >>
    `{x | exp x < c} = {x | x < ln c}` suffices_by metis_tac[] >>
    fs[EXTENSION] >> strip_tac >>
    Cases_on `c` >> EQ_TAC >> strip_tac >> fs[extreal_ln_def] >>
    Cases_on `x` >> fs[extreal_exp_def,extreal_lt_alt] >>
    Cases_on `r ≤ 0` >> fs[extreal_lt_def,extreal_le_def,real_lte]
    >- (`0 < exp r'` by fs[EXP_POS_LT] >> imp_res_tac REAL_LT_TRANS)
    >- (
        `0 < exp r'` by fs[EXP_POS_LT] >>
        `ln (exp r') < ln r` by fs[LN_MONO_LT] >>
        fs[LN_EXP]
    )
    >- (
        `exp r' < exp (ln r)` by fs[EXP_MONO_LT] >>
        `exp (ln r) = r` by fs[EXP_LN] >> fs[]
    )
);

val IN_MEASURABLE_BOREL_CONST_ALT = store_thm(
    "IN_MEASURABLE_BOREL_CONST_ALT",
    ``∀a k. sigma_algebra a ⇒ (λx. k) ∈ measurable a Borel``,
    rpt strip_tac >>
    `∀x. (λx. k) x = k` suffices_by (strip_tac >>
        (qspecl_then [`a`,`k`,`(λx. k)`] assume_tac) IN_MEASURABLE_BOREL_CONST >>
        RES_TAC >> fs[]) >>
    fs[]
);

val IN_MEASURABLE_BOREL_ADD_ALT = store_thm(
    "IN_MEASURABLE_BOREL_ADD_ALT",
    ``∀a f g. sigma_algebra a ∧
        (f ∈ measurable a Borel) ∧ (g ∈ measurable a Borel) ⇒
        (λx. f x + g x) ∈ measurable a Borel``,
    rpt strip_tac >>
    `∀x. (λx. f x + g x) x = f x + g x` suffices_by (strip_tac >>
        (qspecl_then [`a`,`f`,`g`,`(λx. f x + g x)`] assume_tac) IN_MEASURABLE_BOREL_ADD >>
        RES_TAC >> fs[]) >>
    fs[]
);

val IN_MEASURABLE_BOREL_SUB_ALT = store_thm(
    "IN_MEASURABLE_BOREL_SUB_ALT",
    ``∀a f g. sigma_algebra a ∧
        (f ∈ measurable a Borel) ∧ (g ∈ measurable a Borel) ⇒
        (λx. f x - g x) ∈ measurable a Borel``,
    rpt strip_tac >>
    `∀x. (λx. f x - g x) x = f x - g x` suffices_by (strip_tac >>
        (qspecl_then [`a`,`f`,`g`,`(λx. f x - g x)`] assume_tac) IN_MEASURABLE_BOREL_SUB >>
        RES_TAC >> fs[]) >>
    fs[]
);

val IN_MEASURABLE_BOREL_CMUL_ALT = store_thm(
    "IN_MEASURABLE_BOREL_CMUL_ALT",
    ``∀a f c. sigma_algebra a ∧ (f ∈ measurable a Borel) ⇒
        (λx. Normal c * f x) ∈ measurable a Borel``,
    rpt strip_tac >>
    `∀x. (λx. Normal c * f x) x = Normal c * f x` suffices_by (strip_tac >>
        (qspecl_then [`a`,`f`,`(λx. Normal c * f x)`,`c`] assume_tac) IN_MEASURABLE_BOREL_CMUL >>
        RES_TAC >> fs[]) >>
    fs[]
);

val IN_MEASURABLE_BOREL_SUMFINFUN = store_thm(
    "IN_MEASURABLE_BOREL_SUMFINFUN",
    ``∀a X n. sigma_algebra a ∧ (∀i. i < n ⇒ X i ∈ measurable a Borel) ⇒
        sumfinfun (0,n) X ∈ measurable a Borel``,
    rpt strip_tac >> Induct_on `n` >> strip_tac >> fs[] >> rw[]
    >- (`(λx. 0) ∈ measurable a Borel` by fs[IN_MEASURABLE_BOREL_CONST_ALT] >>
        `sumfinfun (0,0) X = (λx. 0)` suffices_by fs[] >>
        `∀x. sumfinfun (0,0) X x = (λx. 0) x` suffices_by metis_tac[] >>
        strip_tac >> fs[sumfinfun_def])
    >- (`X n ∈ measurable a Borel` by fs[] >>
        `(λx. sumfinfun (0,n) X x + X n x) ∈ measurable a Borel`
            by imp_res_tac IN_MEASURABLE_BOREL_ADD_ALT >>
        `sumfinfun (0,SUC n) X = (λx. sumfinfun (0,n) X x + X n x)` suffices_by fs[] >>
        `∀x. sumfinfun (0,SUC n) X x = (λx. sumfinfun (0,n) X x + X n x) x`
            suffices_by metis_tac[] >>
        strip_tac >> fs[sumfinfun_def])
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Integrals *)
(*---------------------------------------------------------------------------*)

val INTEGRAL_FN_PLUS_POS = store_thm(
    "INTEGRAL_FN_PLUS_POS",
    ``∀m f. (measure_space m) ⇒ (0 ≤ pos_fn_integral m (fn_plus f))``,
    rpt strip_tac >>
    `pos_fn_integral m (λx. 0) ≤ pos_fn_integral m (fn_plus f)` by
        (`(∀x. 0 ≤ (λx. 0) x ∧ (λx. 0) x ≤ fn_plus f x)` suffices_by fs[pos_fn_integral_mono] >>
        fs[le_refl,FN_PLUS_POS]) >>
    imp_res_tac pos_fn_integral_zero >> fs[]
);

val INTEGRAL_FN_PLUS_NOT_NEGINF = store_thm(
    "INTEGRAL_FN_PLUS_NOT_NEGINF",
    ``∀m f. (measure_space m) ⇒ (pos_fn_integral m (fn_plus f) ≠ NegInf)``,
    rpt strip_tac >> imp_res_tac INTEGRAL_FN_PLUS_POS >>
    pop_assum (qspec_then `f` assume_tac) >> rfs[] >>
    `Normal 0 ≤ NegInf` by fs[N0_EQ_0] >> fs[extreal_le_def]
);

val INTEGRAL_FN_MINUS_POS = store_thm(
    "INTEGRAL_FN_MINUS_POS",
    ``∀m f. (measure_space m) ⇒ (0 ≤ pos_fn_integral m (fn_minus f))``,
    rpt strip_tac >>
    `pos_fn_integral m (λx. 0) ≤ pos_fn_integral m (fn_minus f)` by
        (`(∀x. 0 ≤ (λx. 0) x ∧ (λx. 0) x ≤ fn_minus f x)` suffices_by fs[pos_fn_integral_mono] >>
        fs[le_refl,FN_MINUS_POS]) >>
    imp_res_tac pos_fn_integral_zero >> fs[]
);

val INTEGRAL_FN_MINUS_NOT_NEGINF = store_thm(
    "INTEGRAL_FN_MINUS_NOT_NEGINF",
    ``∀m f. (measure_space m) ⇒ (pos_fn_integral m (fn_minus f) ≠ NegInf)``,
    rpt strip_tac >> imp_res_tac INTEGRAL_FN_MINUS_POS >>
    pop_assum (qspec_then `f` assume_tac) >> rfs[] >>
    `Normal 0 ≤ NegInf` by fs[N0_EQ_0] >> fs[extreal_le_def]
);

val INTEGRAL_NOT_INF_IMP_IBL = store_thm(
    "INTEGRAL_NOT_INF_IMP_IBL",
    ``∀m f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel
        ∧ (integral m f ≠ PosInf) ∧ (integral m f ≠ NegInf) ⇒ integrable m f``,
    rpt strip_tac >> fs[integral_def,integrable_def] >>
    Cases_on `pos_fn_integral m (fn_plus f)` >> Cases_on `pos_fn_integral m (fn_minus f)` >>
    fs[extreal_sub_def]
);

val INTEGRAL_FINITE_IMP_IBL = store_thm(
    "INTEGRAL_FINITE_IMP_IBL",
    ``∀m f a. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel
        ∧ (integral m f = Normal a) ⇒ integrable m f``,
    rpt strip_tac >> fs[integral_def,integrable_def] >>
    Cases_on `pos_fn_integral m (fn_plus f)` >> Cases_on `pos_fn_integral m (fn_minus f)` >>
    fs[extreal_sub_def]
);

val INTEGRAL_NULL_SET_INDIC = store_thm(
    "INTEGRAL_NULL_SET_INDIC",
    ``∀m s f. measure_space m ∧ null_set m s ⇒ (integral m (indicator_fn s) = 0)``,
    rpt strip_tac >> fs[null_set_def,integral_indicator,extreal_eq_zero]
);

val INTEGRAL_FN_PLUS_NULL_SET = store_thm(
    "INTEGRAL_FN_PLUS_NULL_SET",
    ``∀m s f. (measure_space m) ∧ (null_set m s) ⇒
        (pos_fn_integral m (fn_plus (λx. indicator_fn s x * f x)) = 0)``,
    rpt strip_tac >> fs[integral_def,null_set_def] >>
    imp_res_tac pos_fn_integral_cmul_infty >> rfs[] >> fs[N0_EQ_0,mul_rzero] >>
    `pos_fn_integral m (λx. 0) ≤ pos_fn_integral m (fn_plus (λx. indicator_fn s x * f x))` by
        (`∀x. 0 ≤ (λx. 0) x ∧ (λx. 0) x ≤ (fn_plus (λx. indicator_fn s x * f x)) x`
            suffices_by (strip_tac >> fs[pos_fn_integral_mono]) >> rw[]
        >- (fs[le_lt])
        >- (fs[FN_PLUS_POS])) >>
    imp_res_tac pos_fn_integral_zero >> fs[] >> pop_assum kall_tac >>
    `pos_fn_integral m (fn_plus (λx. indicator_fn s x * f x))
        ≤ pos_fn_integral m (λx. PosInf * indicator_fn s x)` by
        (`∀x. 0 ≤ (fn_plus (λx. indicator_fn s x * f x)) x ∧
            (fn_plus (λx. indicator_fn s x * f x)) x ≤ (λx. PosInf * indicator_fn s x) x`
            suffices_by (strip_tac >> fs[pos_fn_integral_mono]) >> rw[] >> fs[FN_PLUS_POS] >>
        Cases_on `x ∈ s` >>
        fs[indicator_fn_def,fn_plus_def,mul_lzero,mul_rzero,mul_lone,mul_rone,le_infty,le_refl]) >>
    rfs[] >> metis_tac[le_antisym]
);

val INTEGRAL_FN_MINUS_NULL_SET = store_thm(
    "INTEGRAL_FN_MINUS_NULL_SET",
    ``∀m s f. (measure_space m) ∧ (null_set m s) ⇒
        (pos_fn_integral m (fn_minus (λx. indicator_fn s x * f x)) = 0)``,
    rpt strip_tac >> fs[integral_def,null_set_def] >>
    imp_res_tac pos_fn_integral_cmul_infty >> rfs[] >> fs[N0_EQ_0,mul_rzero] >>
    `pos_fn_integral m (λx. 0) ≤ pos_fn_integral m (fn_minus (λx. indicator_fn s x * f x))` by
        (`∀x. 0 ≤ (λx. 0) x ∧ (λx. 0) x ≤ (fn_minus (λx. indicator_fn s x * f x)) x`
            suffices_by (strip_tac >> fs[pos_fn_integral_mono]) >> rw[]
        >- (fs[le_lt])
        >- (fs[FN_MINUS_POS])) >>
    imp_res_tac pos_fn_integral_zero >> fs[] >> pop_assum kall_tac >>
    `pos_fn_integral m (fn_minus (λx. indicator_fn s x * f x))
        ≤ pos_fn_integral m (λx. PosInf * indicator_fn s x)` by
        (`∀x. 0 ≤ (fn_minus (λx. indicator_fn s x * f x)) x ∧
            (fn_minus (λx. indicator_fn s x * f x)) x ≤ (λx. PosInf * indicator_fn s x) x`
            suffices_by (strip_tac >> fs[pos_fn_integral_mono]) >> rw[] >> fs[FN_MINUS_POS] >>
        Cases_on `x ∈ s` >>
        fs[indicator_fn_def,fn_minus_def,mul_lzero,mul_rzero,mul_lone,mul_rone,le_infty] >>
        `¬(0 < 0)` by (fs[extreal_lt_def] >> fs[le_lt]) >> fs[] >> fs[le_lt]) >>
    rfs[] >> metis_tac[le_antisym]
);

val INTEGRAL_NULL_SET = store_thm(
    "INTEGRAL_NULL_SET",
    ``∀m s f. (measure_space m) ∧ (null_set m s) ⇒ (integral m (λx. (indicator_fn s) x * f x) = 0)``,
    rpt strip_tac >> fs[integral_def] >>
    `(pos_fn_integral m (fn_plus (λx. indicator_fn s x * f x)) = 0) ∧
        (pos_fn_integral m (fn_minus (λx. indicator_fn s x * f x)) = 0)` suffices_by
        (rw[] >> fs[extreal_sub_add,add_lzero,neg_0]) >> rw[]
    >- (fs[INTEGRAL_FN_PLUS_NULL_SET])
    >- (fs[INTEGRAL_FN_MINUS_NULL_SET])
);

val IBL_TIMES_INDIC_IBL = store_thm(
    "IBL_TIMES_INDIC_IBL",
    ``∀m s f. (measure_space m) ∧ (s ∈ measurable_sets m) ∧ (integrable m f)
        ⇒ (integrable m (λx. (indicator_fn s) x * f x))``,
    rpt strip_tac >> fs[integrable_def] >>
    `(λx. indicator_fn s x * f x) ∈ measurable (m_space m,measurable_sets m) Borel` by
        (`sigma_algebra (m_space m,measurable_sets m)` by fs[measure_space_def] >>
        imp_res_tac IN_MEASURABLE_BOREL_MUL_INDICATOR >>
        (qspecl_then [`(m_space m,measurable_sets m)`,`f`,`s`] ASSUME_TAC) IN_MEASURABLE_BOREL_MUL_INDICATOR >>
        fs[subsets_def] >> pop_assum imp_res_tac >>
        `(λx. f x * indicator_fn s x) = (λx. indicator_fn s x * f x)` suffices_by (strip_tac >> fs[]) >>
        `∀x. (λx. f x * indicator_fn s x) x = (λx. indicator_fn s x * f x) x` suffices_by fs[] >>
        fs[mul_comm]) >> rw[]
    >- (
        `pos_fn_integral m (fn_plus (λx. indicator_fn s x * f x)) ≤ pos_fn_integral m (fn_plus f)`
            suffices_by (strip_tac >> metis_tac[LE_NE_POSINF_IMP_NE_POSINF]) >>
        `∀x. 0 ≤ (fn_plus (λx. indicator_fn s x * f x)) x ∧
            (fn_plus (λx. indicator_fn s x * f x)) x ≤ (fn_plus f) x` suffices_by
            (strip_tac >> fs[pos_fn_integral_mono]) >>
        rw[] >> Cases_on `x ∈ s` >> fs[indicator_fn_def,fn_plus_def,mul_lzero,mul_lone]
        >- (Cases_on `0 < f x` >> fs[le_lt,le_refl])
        >- (fs[le_refl])
        >- (fs[le_lt])
        >- (Cases_on `0 < f x` >> fs[le_lt,le_refl])
    )
    >- (
        `pos_fn_integral m (fn_minus (λx. indicator_fn s x * f x)) ≤ pos_fn_integral m (fn_minus f)`
            suffices_by (strip_tac >> metis_tac[LE_NE_POSINF_IMP_NE_POSINF]) >>
        `∀x. 0 ≤ (fn_minus (λx. indicator_fn s x * f x)) x ∧
            (fn_minus (λx. indicator_fn s x * f x)) x ≤ (fn_minus f) x` suffices_by
            (strip_tac >> fs[pos_fn_integral_mono]) >>
        rw[] >> Cases_on `x ∈ s` >> fs[indicator_fn_def,fn_minus_def,mul_lzero,mul_lone]
        >- (Cases_on `f x < 0`
            >- (fs[] >> `-0 ≤ -f x` suffices_by fs[neg_0] >> fs[le_neg] >> fs[le_lt])
            >- (fs[le_refl])
        )
        >- (`¬(0 < 0)` by (fs[extreal_lt_def] >> fs[le_lt]) >> fs[] >> fs[le_lt])
        >- (fs[le_lt])
        >- (
            `¬(0 < 0)` by (fs[extreal_lt_def] >> fs[le_lt]) >> fs[] >>
            pop_assum kall_tac >> Cases_on `f x < 0`
            >- (fs[] >> `-0 ≤ -f x` suffices_by fs[neg_0] >> fs[le_neg] >> fs[le_lt])
            >- (fs[le_refl])
        )
    )
);

val INT_FN_PLUS_INDIC_LE_FN_PLUS = store_thm(
    "INT_FN_PLUS_INDIC_LE_FN_PLUS",
    ``∀m f s. measure_space m ⇒
        pos_fn_integral m (fn_plus (λx. indicator_fn s x * f x)) ≤ pos_fn_integral m (fn_plus f)``,
    rpt strip_tac >>
    `(∀x. 0 ≤ (fn_plus (λx. indicator_fn s x * f x)) x ∧
        (fn_plus (λx. indicator_fn s x * f x)) x ≤ (fn_plus f) x)` suffices_by
        (strip_tac >> fs[pos_fn_integral_mono]) >> rw[]
    >- (fs[FN_PLUS_POS])
    >- (
        Cases_on `x ∈ s` >> Cases_on `0 < f x` >>
        fs[fn_plus_def,indicator_fn_def,mul_lzero,mul_lone,le_lt]
    )
);

val INT_FN_MINUS_INDIC_LE_FN_MINUS = store_thm(
    "INT_FN_MINUS_INDIC_LE_FN_MINUS",
    ``∀m f s. measure_space m ⇒
        pos_fn_integral m (fn_minus (λx. indicator_fn s x * f x)) ≤ pos_fn_integral m (fn_minus f)``,
    rpt strip_tac >>
    `(∀x. 0 ≤ (fn_minus (λx. indicator_fn s x * f x)) x ∧
        (fn_minus (λx. indicator_fn s x * f x)) x ≤ (fn_minus f) x)` suffices_by
        (strip_tac >> fs[pos_fn_integral_mono]) >> rw[]
    >- (fs[FN_MINUS_POS])
    >- (
        Cases_on `x ∈ s` >> Cases_on `f x < 0` >>
        `¬(0 < 0)` by (fs[extreal_lt_def] >> fs[le_lt]) >>
        fs[fn_minus_def,indicator_fn_def,mul_lzero,mul_lone,le_refl] >>
        `-0 ≤ -f x` suffices_by fs[neg_0] >> fs[le_neg] >> fs[le_lt]
    )
);

val integrable_sumfinfun = store_thm(
    "integrable_sumfinfun",
    ``∀m n X. (measure_space m) ∧ (∀i. i < n ⇒ integrable m (X i)) ⇒
        (integrable m (sumfinfun (0,n) X))``,
    rpt strip_tac >> Induct_on `n` >> fs[sumfinfun_alt,sumfin_def,integrable_zero] >>
    rpt strip_tac >> fs[] >> `integrable m (X n)` by fs[] >>
    imp_res_tac integrable_add
);

val integral_sumfinfun = store_thm(
    "integral_sumfinfun",
    ``∀m n X. (measure_space m) ∧ (∀i. i < n ⇒ integrable m (X i)) ⇒
        (integral m (sumfinfun (0,n) X) = sumfin (0,n) (λi. integral m (X i)))``,
    rpt strip_tac >> Induct_on `n` >> fs[sumfinfun_alt,sumfin_def,integral_zero] >>
    rpt strip_tac >> fs[] >> `integrable m (X n)` by fs[] >>
    `integrable m (sumfinfun (0,n) X)` by fs[integrable_sumfinfun] >>
    imp_res_tac integral_add >> fs[]
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Probability *)
(*---------------------------------------------------------------------------*)

val PROB_SUBSET_PSPACE = store_thm(
    "PROB_SUBSET_PSPACE",
    ``∀p s. prob_space p ∧ s ∈ events p ⇒ s ⊆ p_space p``,
    rpt strip_tac >> fs[prob_space_def,p_space_def,events_def,prob_def] >>
    fs[MEASURE_SPACE_SUBSET_MSPACE]
);

val probably_subset = store_thm(
    "probably_subset",
    ``∀p s t. prob_space p ∧ probably p s ∧ t ∈ events p ∧ s ⊆ t ⇒ probably p t``,
    rpt strip_tac >> fs[probably_def] >> imp_res_tac PROB_LE_1 >>
    imp_res_tac PROB_INCREASING >> rfs[] >> rw[] >> imp_res_tac REAL_LE_ANTISYM
);

val propably_comp_null = store_thm(
    "propably_comp_null",
    ``∀p s. prob_space p ∧ probably p s ⇒ null_set p (p_space p DIFF s)``,
    rpt strip_tac >> fs[probably_def,null_set_def] >>
    `p_space p DIFF s ∈ events p ∧ (prob p (p_space p DIFF s) = 0)`
        suffices_by fs[events_def,prob_def] >>
    imp_res_tac EVENTS_COMPL >> imp_res_tac PROB_COMPL >> fs[]
);

val EXPECT_1 = store_thm(
    "EXPECT_1",
    ``∀p. prob_space p ⇒ (expectation p (indicator_fn (m_space p)) = 1)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >>
    imp_res_tac integral_indicator >> fs[extreal_of_num_def]
);

val EXPECT_CONST = store_thm(
    "EXPECT_CONST",
    ``∀p c. prob_space p ⇒ (expectation p (λx. Normal c) = Normal c)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    imp_res_tac integral_mspace >>
    pop_assum (fn a => ASSUME_TAC (ISPEC ``(λx. Normal c)`` a)) >> fs[] >>
    imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >>
    imp_res_tac integral_cmul_indicator >> fs[]
);

val PSPACE_IBL_IMP_EXP_EQ_EXP_AS = store_thm(
    "PSPACE_IBL_IMP_EXP_EQ_EXP_AS",
    ``∀p s f. (prob_space p) ∧ (probably p s) ∧ (integrable p f) ⇒
        (expectation p f = expectation p (λx. indicator_fn s x * f x))``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,probably_def,prob_def,p_space_def,events_def] >>
    `integrable p (λx. indicator_fn s x * f x)` by fs[IBL_TIMES_INDIC_IBL] >>
    `measure p (m_space p DIFF s) = 0` by
        (ASSUME_TAC PROB_COMPL >> fs[prob_space_def,events_def,prob_def,p_space_def]) >>
    `null_set p (m_space p DIFF s)` by
        (fs[null_set_def] >> (qspecl_then [`p`,`m_space p`,`s`] ASSUME_TAC) MEASURE_SPACE_DIFF >>
        imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >> RES_TAC) >>
    imp_res_tac INTEGRAL_NULL_SET >> pop_assum (qspec_then `f` ASSUME_TAC) >>
    `integrable p (λx. indicator_fn (m_space p DIFF s) x * f x)` by
        ((qspecl_then [`p`,`m_space p DIFF s`,`f`] ASSUME_TAC) IBL_TIMES_INDIC_IBL >>
        (qspecl_then [`p`,`m_space p`,`s`] ASSUME_TAC) MEASURE_SPACE_DIFF >>
        imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >> RES_TAC) >>
    `integral p (λx. indicator_fn s x * f x) = integral p (λx. indicator_fn s x * f x) + 0`
        by fs[add_rzero] >>
    `_ = integral p (λx. indicator_fn s x * f x) + integral p (λx. indicator_fn (m_space p DIFF s) x * f x)`
        by rw[] >>
    `_ = integral p (λx. (λx. indicator_fn s x * f x) x +
        (λx. indicator_fn (m_space p DIFF s) x * f x) x)` by
        ((qspecl_then [`p`,`(λx. indicator_fn s x * f x)`,`(λx. indicator_fn (m_space p DIFF s) x * f x)`]
            ASSUME_TAC) integral_add >>
        RES_TAC >> metis_tac[]) >>
    `_ = integral p (λx. indicator_fn s x * f x + indicator_fn (m_space p DIFF s) x * f x)` by fs[] >>
    `_ = integral p (λx. f x * indicator_fn (m_space p) x)` by
        (`(λx. indicator_fn s x * f x + indicator_fn (m_space p DIFF s) x * f x) =
            (λx. f x * indicator_fn (m_space p) x)` suffices_by fs[] >>
        `∀x. (λx. indicator_fn s x * f x + indicator_fn (m_space p DIFF s) x * f x) x =
            (λx. f x * indicator_fn (m_space p) x) x` suffices_by fs[] >> strip_tac >>
        fs[DIFF_DEF,indicator_fn_def] >>
        `s ⊆ m_space p` by fs[MEASURABLE_SETS_SUBSET_SPACE] >>
        `x ∈ s ⇒ x ∈ m_space p` by fs[SUBSET_DEF] >>
        Cases_on `x ∈ s` >> Cases_on `x ∈ m_space p` >>
        fs[mul_lzero,mul_lone,mul_rzero,mul_rone,add_lzero,add_rzero]) >>
    `_ = integral p f` by metis_tac[integral_mspace] >> fs[]
);

val PSPACE_AS_IMP_COMP_NULL = store_thm(
    "PSPACE_AS_IMP_COMP_NULL",
    ``∀p s. prob_space p ∧ probably p s ⇒ null_set p (m_space p DIFF s)``,
    rpt strip_tac >> imp_res_tac PROB_COMPL >>
    fs[null_set_def,prob_space_def,probably_def,prob_def,p_space_def,events_def] >>
    fs[MEASURE_SPACE_MSPACE_MEASURABLE,MEASURE_SPACE_DIFF]
);

val PSPACE_INT_FN_PLUS_EQ_INT_FN_PLUS_INDIC = store_thm(
    "PSPACE_INT_FN_PLUS_EQ_INT_FN_PLUS_INDIC",
    ``∀p s f. (prob_space p) ∧ (probably p s) ∧ f ∈ measurable (m_space p,measurable_sets p) Borel ⇒
        (pos_fn_integral p (fn_plus f) = pos_fn_integral p (fn_plus (λx. indicator_fn s x * f x)))``,
    rpt strip_tac >> imp_res_tac PSPACE_AS_IMP_COMP_NULL >>
    fs[prob_space_def,probably_def,prob_def,p_space_def,events_def] >>
    `pos_fn_integral p (fn_plus f) = pos_fn_integral p (λx. (fn_plus f) x * indicator_fn (m_space p) x)` by
        fs[pos_fn_integral_mspace,FN_PLUS_POS] >>
    `_ = pos_fn_integral p (λx. fn_plus f x * indicator_fn (s ∪ (m_space p DIFF s)) x)` by
        (`s ⊆ m_space p` by fs[MEASURABLE_SETS_SUBSET_SPACE] >> fs[UNION_DIFF]) >>
    `_ = pos_fn_integral p (λx. fn_plus f x * indicator_fn s x)
        + pos_fn_integral p (λx. fn_plus f x * indicator_fn (m_space p DIFF s) x)` by
        (`DISJOINT s (m_space p DIFF s)` by fs[DISJOINT_DIFF] >>
        `(m_space p DIFF s) ∈ measurable_sets p` by fs[MEASURE_SPACE_MSPACE_MEASURABLE,MEASURE_SPACE_DIFF] >>
        imp_res_tac IN_MEASURABLE_BOREL_FN_PLUS >> (qspec_then `f` assume_tac) FN_PLUS_POS >>
        imp_res_tac pos_fn_integral_disjoint_sets) >>
    `_ = pos_fn_integral p (λx. fn_plus f x * indicator_fn s x)` by
        (`pos_fn_integral p (λx. fn_plus f x * indicator_fn (m_space p DIFF s) x) = 0`
            suffices_by fs[add_rzero] >>
        `pos_fn_integral p (λx. fn_plus f x * indicator_fn (m_space p DIFF s) x) =
            pos_fn_integral p (fn_plus (λx. indicator_fn (m_space p DIFF s) x * f x))`
            suffices_by (strip_tac >> fs[INTEGRAL_FN_PLUS_NULL_SET]) >>
        `(λx. fn_plus f x * indicator_fn (m_space p DIFF s) x) =
            (fn_plus (λx. indicator_fn (m_space p DIFF s) x * f x))` suffices_by fs[] >>
        `∀x. (λx. fn_plus f x * indicator_fn (m_space p DIFF s) x) x =
            (fn_plus (λx. indicator_fn (m_space p DIFF s) x * f x)) x` suffices_by metis_tac[] >>
        strip_tac >> fs[fn_plus_def,indicator_fn_def] >>
        Cases_on `0 < f x` >> Cases_on `x ∈ m_space p ∧ x ∉ s` >>
        fs[mul_lzero,mul_rzero,mul_lone,mul_rone]) >>
    `fn_plus (λx. indicator_fn s x * f x) = (λx. fn_plus f x * indicator_fn s x)` suffices_by fs[] >>
    `∀x. fn_plus (λx. indicator_fn s x * f x) x = (λx. fn_plus f x * indicator_fn s x) x`
        suffices_by metis_tac[] >> strip_tac >> fs[fn_plus_def,indicator_fn_def] >>
    Cases_on `0 < f x` >> Cases_on `x ∈ s` >> fs[mul_lzero,mul_rzero,mul_lone,mul_rone]
);

val PSPACE_INT_FN_MINUS_EQ_INT_FN_MINUS_INDIC = store_thm(
    "PSPACE_INT_FN_MINUS_EQ_INT_FN_MINUS_INDIC",
    ``∀p s f. (prob_space p) ∧ (probably p s) ∧ f ∈ measurable (m_space p,measurable_sets p) Borel ⇒
        (pos_fn_integral p (fn_minus f) = pos_fn_integral p (fn_minus (λx. indicator_fn s x * f x)))``,
    rpt strip_tac >> imp_res_tac PSPACE_AS_IMP_COMP_NULL >>
    fs[prob_space_def,probably_def,prob_def,p_space_def,events_def] >>
    `pos_fn_integral p (fn_minus f) = pos_fn_integral p (λx. (fn_minus f) x * indicator_fn (m_space p) x)` by
        fs[pos_fn_integral_mspace,FN_MINUS_POS] >>
    `_ = pos_fn_integral p (λx. fn_minus f x * indicator_fn (s ∪ (m_space p DIFF s)) x)` by
        (`s ⊆ m_space p` by fs[MEASURABLE_SETS_SUBSET_SPACE] >> fs[UNION_DIFF]) >>
    `_ = pos_fn_integral p (λx. fn_minus f x * indicator_fn s x)
        + pos_fn_integral p (λx. fn_minus f x * indicator_fn (m_space p DIFF s) x)` by
        (`DISJOINT s (m_space p DIFF s)` by fs[DISJOINT_DIFF] >>
        `(m_space p DIFF s) ∈ measurable_sets p` by fs[MEASURE_SPACE_MSPACE_MEASURABLE,MEASURE_SPACE_DIFF] >>
        imp_res_tac IN_MEASURABLE_BOREL_FN_MINUS >> (qspec_then `f` assume_tac) FN_MINUS_POS >>
        imp_res_tac pos_fn_integral_disjoint_sets) >>
    `_ = pos_fn_integral p (λx. fn_minus f x * indicator_fn s x)` by
        (`pos_fn_integral p (λx. fn_minus f x * indicator_fn (m_space p DIFF s) x) = 0`
            suffices_by fs[add_rzero] >>
        `pos_fn_integral p (λx. fn_minus f x * indicator_fn (m_space p DIFF s) x) =
            pos_fn_integral p (fn_minus (λx. indicator_fn (m_space p DIFF s) x * f x))`
            suffices_by (strip_tac >> fs[INTEGRAL_FN_MINUS_NULL_SET]) >>
        `(λx. fn_minus f x * indicator_fn (m_space p DIFF s) x) =
            (fn_minus (λx. indicator_fn (m_space p DIFF s) x * f x))` suffices_by fs[] >>
        `∀x. (λx. fn_minus f x * indicator_fn (m_space p DIFF s) x) x =
            (fn_minus (λx. indicator_fn (m_space p DIFF s) x * f x)) x` suffices_by metis_tac[] >>
        strip_tac >> fs[fn_minus_def,indicator_fn_def] >>
        `¬(0 < 0)` by (fs[extreal_lt_def] >> fs[le_lt]) >>
        Cases_on `f x < 0` >> Cases_on `x ∈ m_space p ∧ x ∉ s` >>
        fs[mul_lzero,mul_rzero,mul_lone,mul_rone]) >>
    `fn_minus (λx. indicator_fn s x * f x) = (λx. fn_minus f x * indicator_fn s x)` suffices_by fs[] >>
    `∀x. fn_minus (λx. indicator_fn s x * f x) x = (λx. fn_minus f x * indicator_fn s x) x`
        suffices_by metis_tac[] >> strip_tac >> fs[fn_minus_def,indicator_fn_def] >>
    `¬(0 < 0)` by (fs[extreal_lt_def] >> fs[le_lt]) >>
    Cases_on `f x < 0` >> Cases_on `x ∈ s` >> fs[mul_lzero,mul_rzero,mul_lone,mul_rone]
);

val PSPACE_MBL_IMP_EXP_EQ_EXP_AS = store_thm(
    "PSPACE_MBL_IMP_EXP_EQ_EXP_AS",
    ``∀p s f. (prob_space p) ∧ (probably p s) ∧ f ∈ measurable (m_space p,measurable_sets p) Borel ⇒
        (expectation p f = expectation p (λx. indicator_fn s x * f x))``,
    rpt strip_tac >> Cases_on `integrable p f` >> fs[PSPACE_IBL_IMP_EXP_EQ_EXP_AS] >>
    imp_res_tac PSPACE_INT_FN_PLUS_EQ_INT_FN_PLUS_INDIC >>
    imp_res_tac PSPACE_INT_FN_MINUS_EQ_INT_FN_MINUS_INDIC >>
    fs[expectation_def,prob_space_def,probably_def,prob_def,p_space_def,events_def] >>
    Cases_on `pos_fn_integral p (fn_plus f)` >>
    Cases_on `pos_fn_integral p (fn_minus f)` >>
    Cases_on `pos_fn_integral p (fn_plus (λx. indicator_fn s x * f x))` >>
    Cases_on `pos_fn_integral p (fn_minus (λx. indicator_fn s x * f x))` >>
    fs[integrable_def,integral_def] >> fs[extreal_sub_def] >>
    imp_res_tac INTEGRAL_FN_PLUS_NOT_NEGINF >> imp_res_tac INTEGRAL_FN_MINUS_NOT_NEGINF >>
    rw[] >> NTAC 2 (pop_assum kall_tac) >>
    imp_res_tac INT_FN_PLUS_INDIC_LE_FN_PLUS >>
    pop_assum (qspecl_then [`s`,`f`] assume_tac) >> rfs[] >>
    imp_res_tac INT_FN_MINUS_INDIC_LE_FN_MINUS >>
    pop_assum (qspecl_then [`s`,`f`] assume_tac) >> rfs[] >> fs[extreal_le_def] >>
    NTAC 2 (pop_assum kall_tac)
);

val probably_inter = store_thm(
    "probably_inter",
    ``∀p s t. prob_space p ∧ probably p s ∧ probably p t ⇒ probably p (s ∩ t)``,
    rpt strip_tac >> fs[probably_def] >> imp_res_tac PROB_COMPL >> rfs[] >>
    Q.ABBREV_TAC `tc = p_space p DIFF t` >> Q.ABBREV_TAC `sc = p_space p DIFF s` >>
    imp_res_tac EVENTS_COMPL >> rfs[] >>
    `(tc ∪ sc) ∈ events p` by imp_res_tac EVENTS_UNION >>
    `prob p (tc ∪ sc) = 0` by (
        (qspecl_then [`p`,`(tc ∪ sc)`,`tc`,`sc`] assume_tac) PROB_SUBADDITIVE >>
        rfs[] >> imp_res_tac PROB_POSITIVE >> imp_res_tac REAL_LE_ANTISYM) >>
    Q.ABBREV_TAC `tusc = p_space p DIFF (tc ∪ sc)` >>
    `tusc ∈ events p` by (imp_res_tac EVENTS_COMPL >> rfs[]) >>
    `prob p tusc = 1` by (imp_res_tac PROB_COMPL >> rfs[]) >>
    `tusc = s ∩ t` suffices_by (strip_tac >> fs[]) >>
    Q.UNABBREV_TAC `tusc` >> Q.UNABBREV_TAC `tc` >> Q.UNABBREV_TAC `sc` >>
    fs[DIFF_DEF,INTER_DEF,UNION_DEF,EXTENSION] >>
    strip_tac >> EQ_TAC >> strip_tac >> fs[] >>
    `s ⊆ p_space p` by fs[PROB_SUBSET_PSPACE] >> fs[SUBSET_DEF]
);

val probably_interval = store_thm(
    "probably_interval",
    ``∀p X a b. prob_space p ∧ probably p {x | X x ∈ closed_interval (Normal a) (Normal b)} ⇒ (a ≤ b)``,
    rpt strip_tac >> Cases_on `a ≤ b` >> fs[] >>
    fs[prob_space_def,p_space_def,events_def,prob_def,probably_def,closed_interval_def] >>
    `{x | Normal a ≤ X x ∧ X x ≤ Normal b} = ∅` by (fs[EXTENSION] >> strip_tac >>
        fs[REAL_NOT_LE] >> `Normal b < Normal a` by fs[extreal_lt_alt] >>
        Cases_on `Normal a ≤ X x` >> fs[] >> imp_res_tac lte_trans >> fs[extreal_lt_def]) >>
    imp_res_tac MEASURE_EMPTY >> fs[]
);

val sumfinfun_probably = store_thm(
    "sumfinfun_probably",
    ``∀p n X a. (prob_space p) ∧ (∀i. i < n ⇒ real_random_variable (X i) p) ∧
        (∀i. i < n ⇒ probably p {x | X i x = Normal (a i)}) ⇒
        (probably p {x | (sumfinfun (0,n) X x = Normal (sum (0,n) a)) ∧ x ∈ m_space p})``,
    Induct_on `n` >> rpt strip_tac >> fs[sumfinfun_def,sum]
    >- (fs[N0_EQ_0] >> rw[] >>
        fs[prob_space_def,probably_def,p_space_def,events_def,prob_def,MEASURE_SPACE_MSPACE_MEASURABLE])
    >- (`probably p {x | (sumfinfun (0,n) X x = Normal (sum (0,n) a)) ∧ x ∈ m_space p}`
            by (RES_TAC >> fs[]) >>
        `probably p {x | X n x = Normal (a n)}` by fs[] >>
        `sigma_algebra (m_space p,measurable_sets p)` by fs[prob_space_def,measure_space_def] >>
        `sumfinfun (0,SUC n) X ∈ measurable (m_space p,measurable_sets p) Borel` by (
            imp_res_tac IN_MEASURABLE_BOREL_SUMFINFUN >>
            fs[real_random_variable_def,p_space_def,events_def]) >>
        qpat_x_assum `∀p X a. _` kall_tac >> NTAC 2 (qpat_x_assum `∀i. _` kall_tac) >>
        fs[probably_def,events_def,prob_def,sumfinfun_alt] >>
        `{x | (sumfinfun (0,n) X x + X n x = Normal (sum (0,n) a + a n)) ∧
            x ∈ m_space p} ∈ measurable_sets p` by (imp_res_tac IN_MEASURABLE_BOREL_ALL >>
            fs[space_def,subsets_def,INTER_DEF]) >>
        fs[prob_space_def,p_space_def] >>
        (qspecl_then [`p`,`{x | X n x = Normal (a n)}`,
            `{x | (sumfinfun (0,n) X x = Normal (sum (0,n) a)) ∧ x ∈ m_space p}`]
            assume_tac) MEASURE_SPACE_INTER >>
        rfs[INTER_DEF] >> Q.ABBREV_TAC `SX = sumfinfun (0,n) X` >> Q.ABBREV_TAC `Sa = sum (0,n) a` >>
        `measure p {x | (X n x = Normal (a n)) ∧ (SX x = Normal Sa) ∧ x ∈ m_space p} = 1`
            suffices_by (strip_tac >>
            `{x | (X n x = Normal (a n)) ∧ (SX x = Normal Sa) ∧ x ∈ m_space p} ⊆
                {x | (SX x + X n x = Normal (Sa + a n)) ∧ x ∈ m_space p}` by (
                fs[SUBSET_DEF] >> rpt strip_tac >> fs[extreal_add_def]) >>
            imp_res_tac MEASURE_SPACE_INCREASING >>
            (qspecl_then [`p`,
                `{x | (X n x = Normal (a n)) ∧ (SX x = Normal Sa) ∧ x ∈ m_space p}`,
                `{x | (SX x + X n x = Normal (Sa + a n)) ∧ x ∈ m_space p}`] assume_tac) INCREASING >>
            rfs[] >>
            `measure p {x | (SX x + X n x = Normal (Sa + a n)) ∧ x ∈ m_space p} ≤ 1` by (
                (qspecl_then [`p`,`{x | (SX x + X n x = Normal (Sa + a n)) ∧ x ∈ m_space p}`]
                    assume_tac) PROB_LE_1 >>
                rfs[prob_space_def,p_space_def,events_def,prob_def]) >>
            imp_res_tac REAL_LE_ANTISYM) >>
        `{x | (X n x = Normal (a n)) ∧ (SX x = Normal Sa) ∧ x ∈ m_space p} =
            {x | (SX x = Normal Sa) ∧ x ∈ m_space p} ∩ {x | X n x = Normal (a n)}` by (
            fs[INTER_DEF,EXTENSION] >> strip_tac >> EQ_TAC >> fs[]) >>
        fs[] >> pop_assum kall_tac >>
        (qspecl_then [`p`,`{x | (SX x = Normal Sa) ∧ x ∈ m_space p}`,
            `{x | X n x = Normal (a n)}`] assume_tac) probably_inter >>
        rfs[prob_space_def,probably_def,p_space_def,events_def,prob_def]
    )
);

val _ = export_theory();
