open HolKernel Parse boolLib bossLib;
open realLib;

open arithmeticTheory;
open pred_setTheory;
open realTheory;
open transcTheory;
open seqTheory;
open limTheory;
open extrealTheory;
open measureTheory;
open lebesgueTheory;
open probabilityTheory;

open trivialTheory;
open convexTheory;
open markovTheory;

val _ = new_theory "hoeffding";

val L_def = Define `L (p : real) = (λh. - h * p + ln (1 - p + p * exp h))`;
val L'_def = Define `L' (p : real) = (λh. - p + p * exp h/(1 - p + p * exp h))`;
val L''_def = Define `L'' (p : real) =
    (λh. p * exp h/(1 - p + p * exp h) * (1 - p * exp h/(1 - p + p * exp h)))`;
val dL_def = Define `(dL p (0:num) = L p) ∧ (dL p (1:num) = L' p) ∧ (dL p (2:num) = L'' p)`;

val L_0_EQ_0 = store_thm(
    "L_0_EQ_0",
    ``∀p. L p 0 = 0``,
    strip_tac >> fs[L_def,EXP_0,real_sub] >>
    `ln (1 + (-p + p)) = 0` suffices_by fs[REAL_ADD_ASSOC] >>
    fs[REAL_MUL_RID,LN_1]
);

val L'_0_EQ_0 = store_thm(
    "L'_0_EQ_0",
    ``∀p. L' p 0 = 0``,
    strip_tac >> fs[L'_def,EXP_0,real_sub,real_div] >>
    `-p + p * (1 + (-p + p))⁻¹ = 0` suffices_by fs[REAL_ADD_ASSOC] >>
    fs[REAL_MUL_RID,REAL_INV1]
);

val T1MT_LE_QUARTER = store_thm(
    "T1MT_LE_QUARTER",
    ``∀t:real. t * (1 - t) ≤ 1 / 4``,
    strip_tac >> `∃a. a = t - 1/2` by fs[] >> fs[REAL_EQ_SUB_LADD] >> rw[] >>
    `1 − (a + 1 / 2) = -a + 1 / 2` by (fs[real_sub] >>
        `1 + -1 * (a + 1 / 2) = -a + 1 / 2` suffices_by metis_tac[REAL_NEG_MINUS1] >>
        fs[REAL_ADD_LDISTRIB,REAL_ADD_ASSOC,real_div] >>
        `1 + -1 * 2⁻¹ + -a = 2⁻¹ + -a` suffices_by metis_tac[REAL_NEG_MINUS1,REAL_ADD_ASSOC,REAL_ADD_COMM] >>
        fs[] >> `1 - 2⁻¹ = 2⁻¹` suffices_by metis_tac[REAL_NEG_MINUS1,real_sub] >>
        fs[REAL_EQ_SUB_RADD,REAL_INV_1OVER,REAL_HALF_DOUBLE]) >>
    rw[] >> pop_assum kall_tac >>
    fs[REAL_ADD_LDISTRIB,REAL_ADD_RDISTRIB,REAL_ADD_ASSOC,real_div] >>
    `-a * a + (a * 2⁻¹ + -a * 2⁻¹) + 4⁻¹ ≤ 4⁻¹` suffices_by metis_tac[REAL_MUL_COMM,REAL_ADD_ASSOC] >>
    fs[REAL_MUL_LNEG] >>
    `4⁻¹ - a * a ≤ 4⁻¹` suffices_by metis_tac[REAL_ADD_COMM,real_sub] >>
    fs[REAL_LE_SUB_RADD,REAL_LE_ADDR,REAL_LE_SQUARE]
);

val L''_LE_QUARTER = store_thm(
    "L''_LE_QUARTER",
    ``∀p h. L'' p h ≤ 1/4``,
    rpt strip_tac >> fs[L''_def,EXP_0] >>
    `∃t. t = p * exp h / (1 − p + p * exp h)` by fs[] >>
    `t * (1 - t) ≤ 1 / 4` suffices_by fs[] >>
    fs[T1MT_LE_QUARTER]
);

val L'_EQ_L' = store_thm(
    "L'_EQ_L'",
    ``∀p h. (0 < p) ∧ (p < 1) ⇒ (L p diffl L' p h) h``,
    rpt strip_tac >> fs[L_def,L'_def] >>
    `((λh. -h * p) diffl -p) h ∧ ((λh. ln (1 − p + p * exp h)) diffl (p * exp h / (1 − p + p * exp h))) h`
        suffices_by (strip_tac >> fs[DIFF_ADD]) >> rw[]
    >- (
        `((λh. h * p) diffl p) h` suffices_by
            (strip_tac >> imp_res_tac DIFF_NEG >> fs[REAL_MUL_LNEG]) >>
        (ASSUME_TAC o ISPEC ``h:real``) DIFF_X >>
        imp_res_tac DIFF_CMUL >>
        first_x_assum (ASSUME_TAC o ISPEC ``p:real``) >> fs[] >>
        `(λx. p * x) = (λh. h * p)` suffices_by (strip_tac >> fs[]) >>
        metis_tac[REAL_MUL_COMM]
    )
    >- (
        `((λh. ln h) diffl (1 / (1 − p + p * exp h))) ((λh. 1 − p + p * exp h) h)
            ∧ ((λh. 1 − p + p * exp h) diffl (p * exp h)) h` suffices_by
            (strip_tac >> imp_res_tac DIFF_CHAIN >>
            pop_assum kall_tac >> fs[real_div,REAL_MUL_COMM]) >> rw[]
        >- (
            fs[real_div] >>
            `0 < 1 − p + p * exp h` suffices_by metis_tac[DIFF_LN] >>
            `0 < 1 - p` by fs[REAL_LT_SUB_LADD] >>
            `0 < exp h` by fs[EXP_POS_LT] >>
            `0 < p * exp h` by fs[REAL_LT_MUL] >>
            fs[REAL_LT_ADD]
        )
        >- (
            (ASSUME_TAC o ISPECL [``1:real``,``h:real``]) DIFF_CONST >>
            (ASSUME_TAC o ISPECL [``p:real``,``h:real``]) DIFF_CONST >>
            (ASSUME_TAC o ISPEC ``h:real``) DIFF_EXP >>
            `((λx. (λx. 1) x - (λx. p) x) diffl (0 - 0)) h` by imp_res_tac DIFF_SUB >> fs[] >>
            `((λx. p * exp x) diffl (p * exp h)) h` by
                (imp_res_tac DIFF_CMUL >>
                qpat_x_assum `∀c. ( _ diffl (c * exp h)) _` (qspec_then `p` ASSUME_TAC) >> fs[]) >>
            `((λx. (λx. 1 − p) x + (λx. p * exp x) x) diffl (0 + p * exp h)) h`
                by imp_res_tac DIFF_ADD >>
            fs[]
        )
    )
);

val L''_EQ_L'' = store_thm(
    "L''_EQ_L''",
    ``∀p h. (0 < p) ∧ (p < 1) ⇒ (L' p diffl L'' p h) h``,
    rpt strip_tac >> fs[L'_def,L''_def,real_div,real_sub,REAL_ADD_LDISTRIB] >>
    fs[REAL_MUL_RNEG,REAL_MUL_ASSOC] >>
    `((λh. p * exp h * (1 + -p + p * exp h)⁻¹) diffl
        (p * exp h * (1 + -p + p * exp h)⁻¹ +
        -(p * exp h * (1 + -p + p * exp h)⁻¹ *
        p * exp h * (1 + -p + p * exp h)⁻¹))) h`
        suffices_by (strip_tac >> fs[DIFF_CADD]) >>
    `((λh. p * exp h) diffl (p * exp h)) h` by
        ((ASSUME_TAC o ISPECL [``p:real``,``h:real``]) DIFF_CONST >>
        (ASSUME_TAC o ISPEC ``h:real``) DIFF_EXP >>
        imp_res_tac DIFF_CMUL >>
        qpat_x_assum `∀c. ( _ diffl (c * exp h)) _` (qspec_then `p` ASSUME_TAC) >>
        fs[]) >>
    `((λh. (1 + -p + p * exp h)⁻¹) diffl
        -(p * exp h * (1 + -p + p * exp h)⁻¹ * (1 + -p + p * exp h)⁻¹)) h`
        suffices_by (rpt strip_tac >>
        (ASSUME_TAC o ISPECL [``(λh. p * exp h):real->real``,
            ``(λh. (1 + -p + p * exp h)⁻¹):real->real``]) DIFF_MUL >>
        pop_assum imp_res_tac >> fs[REAL_MUL_ASSOC,REAL_MUL_RNEG,REAL_MUL_LNEG] >>
        `-(p * exp h * (1 + -p + p * exp h)⁻¹ * p * exp h * (1 + -p + p * exp h)⁻¹) =
            -(p * exp h * (1 + -p + p * exp h)⁻¹ * (1 + -p + p * exp h)⁻¹ * p * exp h)`
            suffices_by fs[] >>
        metis_tac[REAL_MUL_COMM,REAL_MUL_ASSOC]) >>
    `((λh. 1 + -p + p * exp h) diffl (p * exp h)) h` by fs[DIFF_CADD] >>
    `1 + -p + p * exp h ≠ 0` by
        (`0 < 1 - p` by fs[REAL_LT_SUB_LADD] >>
        `0 < exp h` by fs[EXP_POS_LT] >>
        `0 < p * exp h` by fs[REAL_LT_MUL] >>
        `0 < 1 − p + p * exp h` by fs[REAL_LT_ADD] >>
        fs[real_sub,REAL_LT_IMP_NE]) >>
    imp_res_tac DIFF_INV >> NTAC 2 (pop_assum kall_tac) >> fs[] >>
    pop_assum imp_res_tac >>
    `-(p * exp h * (1 + -p + p * exp h)⁻¹ * (1 + -p + p * exp h)⁻¹) =
        -(p * exp h / (1 + -p + p * exp h) pow 2)` suffices_by fs[] >>
    fs[POW_2,real_div,REAL_MUL_ASSOC,REAL_INV_MUL]
);

val L_LE_EIGTH_HH = store_thm(
    "L_LE_EIGTH_HH",
    ``∀p h. (0 < p) ∧ (p < 1) ⇒ (L p h ≤ h * h / 8)``,
    rpt strip_tac >> (qspecl_then [`h:real`,`0:real`] ASSUME_TAC) REAL_LT_TOTAL >> rw[]
    >-(fs[L_0_EQ_0]) >>
    `∀h. (L p diffl L' p h) h` by imp_res_tac L'_EQ_L' >>
    `∀h. (L' p diffl L'' p h) h` by imp_res_tac L''_EQ_L''
    >-(
        (ASSUME_TAC o ISPECL [``L p``,``dL p``,``h:real``,``2:num``]) MCLAURIN_NEG >>
        fs[dL_def] >> pop_assum imp_res_tac >>
        `(∀m t. m < 2 ∧ h ≤ t ∧ t ≤ 0 ⇒ (dL p m diffl dL p (SUC m) t) t)` suffices_by
            (rpt strip_tac >> fs[] >>
            NTAC 2 (pop_assum kall_tac) >>
            `∀n m f. sum (n,SUC m) f = sum (n,m) f + f (n + m)` by fs[sum] >>
            qpat_assum `∀n m f. _ `
                (qspecl_then [`0`, `1`, `(λm. dL p m 0 / &FACT m * h pow m)`] assume_tac) >>
            qpat_x_assum `∀n m f. _ `
                (qspecl_then [`0`, `0`, `(λm. dL p m 0 / &FACT m * h pow m)`] assume_tac) >>
            fs[dL_def] >> fs[sum,L_0_EQ_0,L'_0_EQ_0,real_div,POW_2,REAL_MUL_ASSOC] >>
            fs[EVAL ``FACT 2``] >> NTAC 6 (pop_assum kall_tac) >>
            (qspecl_then [`p`,`t`] assume_tac) L''_LE_QUARTER >> fs[real_div] >>
            imp_res_tac REAL_LE_LMUL_IMP >>
            `0:real ≤ 2` by fs[] >> imp_res_tac REAL_LE_INV_EQ >>
            `0 ≤ h * h` by fs[REAL_LE_SQUARE] >>
            `0 ≤ 2⁻¹ * (h * h)` by imp_res_tac REAL_LE_MUL >> fs[REAL_MUL_ASSOC] >>
            
            `2⁻¹ * h * h * L'' p t ≤ 2⁻¹ * h * h * 4⁻¹` by RES_TAC >>
            `2⁻¹ * h * h * L'' p t ≤ 2⁻¹ * 4⁻¹ * h * h` by metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM] >>
            `0:real ≠ 2` by fs[] >> `0:real ≠ 4` by fs[] >>
            `0:real ≠ 2⁻¹` by metis_tac[REAL_INV_EQ_0] >>
            `0:real ≠ 4⁻¹` by metis_tac[REAL_INV_EQ_0] >>
            `2⁻¹ * h * h * L'' p t ≤ (2 * 4)⁻¹ * h * h` by metis_tac[REAL_INV_MUL] >>
            `2:real * 4 = 8` by fs[] >> fs[] >> rw[] >>
            metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM]) >>
        pop_assum kall_tac >> rpt strip_tac >>
        Cases_on `m` >> fs[dL_def] >> Cases_on `n` >> fs[dL_def]
    )
    >-(
        (ASSUME_TAC o ISPECL [``L p``,``dL p``,``h:real``,``2:num``]) MCLAURIN >>
        fs[dL_def] >> pop_assum imp_res_tac >>
        `(∀m t. m < 2 ∧ 0 ≤ t ∧ t ≤ h ⇒ (dL p m diffl dL p (SUC m) t) t)` suffices_by
            (rpt strip_tac >> fs[] >>
            NTAC 2 (pop_assum kall_tac) >>
            `∀n m f. sum (n,SUC m) f = sum (n,m) f + f (n + m)` by fs[sum] >>
            qpat_assum `∀n m f. _ `
                (qspecl_then [`0`, `1`, `(λm. dL p m 0 / &FACT m * h pow m)`] assume_tac) >>
            qpat_x_assum `∀n m f. _ `
                (qspecl_then [`0`, `0`, `(λm. dL p m 0 / &FACT m * h pow m)`] assume_tac) >>
            fs[dL_def] >> fs[sum,L_0_EQ_0,L'_0_EQ_0,real_div,POW_2,REAL_MUL_ASSOC] >>
            fs[EVAL ``FACT 2``] >> NTAC 6 (pop_assum kall_tac) >>
            (qspecl_then [`p`,`t`] assume_tac) L''_LE_QUARTER >> fs[real_div] >>
            imp_res_tac REAL_LE_LMUL_IMP >>
            `0:real ≤ 2` by fs[] >> imp_res_tac REAL_LE_INV_EQ >>
            `0 ≤ h` by fs[REAL_LT_IMP_LE] >>
            `0 ≤ 2⁻¹ * h * h` by imp_res_tac REAL_LE_MUL >>
            `2⁻¹ * h * h * L'' p t ≤ 2⁻¹ * h * h * 4⁻¹` by RES_TAC >>
            `2⁻¹ * h * h * L'' p t ≤ 2⁻¹ * 4⁻¹ * h * h` by metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM] >>
            `0:real ≠ 2` by fs[] >> `0:real ≠ 4` by fs[] >>
            `0:real ≠ 2⁻¹` by metis_tac[REAL_INV_EQ_0] >>
            `0:real ≠ 4⁻¹` by metis_tac[REAL_INV_EQ_0] >>
            `2⁻¹ * h * h * L'' p t ≤ (2 * 4)⁻¹ * h * h` by metis_tac[REAL_INV_MUL] >>
            `2:real * 4 = 8` by fs[] >> fs[] >> rw[] >>
            metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM]) >>
        pop_assum kall_tac >> rpt strip_tac >>
        Cases_on `m` >> fs[dL_def] >> Cases_on `n` >> fs[dL_def]
    )
);

val HOEF_LEM_ALG_LEM_1 = store_thm(
    "HOEF_LEM_ALG_LEM_1",
    ``∀p a b c g f. prob_space p ∧ integrable p f ⇒
        (expectation p (λx. 1 / (Normal b − Normal a) * exp (Normal g * Normal c) * f x) =
        Normal (exp (g * c) / (b − a)) * expectation p f)``,
    rpt strip_tac >> fs[extreal_mul_def,extreal_sub_def,extreal_exp_def] >>
    `expectation p (λx. inv (Normal (b − a)) * Normal (exp (g * c)) * f x) =
        Normal (exp (g * c) / (b − a)) * expectation p f` suffices_by fs[inv_1over] >>
    `expectation p (λx. Normal (exp (g * c)) * inv (Normal (b − a)) * f x) =
        Normal (exp (g * c) / (b − a)) * expectation p f` suffices_by metis_tac[mul_comm,mul_assoc] >>
    `expectation p (λx. (Normal (exp (g * c)) / (Normal (b − a))) * f x) =
        Normal (exp (g * c) / (b − a)) * expectation p f` suffices_by fs[extreal_div_def] >>
    `expectation p (λx. Normal (exp (g * c) / (b − a)) * f x) =
        Normal (exp (g * c) / (b − a)) * expectation p f` suffices_by fs[extreal_div_eq] >>
    fs[expectation_def,prob_space_def,integral_cmul]
);

val HOEF_LEM_ALG_LEM_2 = store_thm(
    "HOEF_LEM_ALG_LEM_2",
    ``∀p b f. prob_space p ∧ integrable p f ⇒
        (expectation p (λx. Normal b - f x) = Normal b - expectation p f)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >> fs[extreal_sub_add] >>
    imp_res_tac integrable_const >> imp_res_tac integrable_cmul >>
    qpat_x_assum `∀c. _` (fn a => ASSUME_TAC (ISPEC ``real (-1)`` a)) >>
    qpat_x_assum `∀c. _` (fn a => ASSUME_TAC (ISPEC ``b:real`` a)) >>
    fs[NORM_REAL_NEG1] >> `integrable p (λx. -f x)` by metis_tac[neg_minus1] >>
    qpat_x_assum `_ (λx. -1 * f x)` kall_tac >>
    `integral p (λx. (λx. Normal b) x + (λx. -f x) x) = Normal b + -integral p f` suffices_by fs[] >>
    fs[integral_add] >> ASSUME_TAC EXPECT_CONST >>
    fs[expectation_def,prob_space_def,p_space_def] >> pop_assum kall_tac >>
    `integral p (λx. -f x) = -integral p f` suffices_by fs[] >>
    `integral p (λx. -1 * f x) = -1 * integral p f` suffices_by metis_tac[neg_minus1] >>
    `integral p (λx. Normal (real (-1)) * f x) = Normal (real (-1)) * integral p f`
        suffices_by fs[NORM_REAL_NEG1] >>
    fs[integral_cmul]
);

val HOEF_LEM_ALG_LEM_3 = store_thm(
    "HOEF_LEM_ALG_LEM_3",
    ``∀p a f. prob_space p ∧ integrable p f ⇒
        (expectation p (λx. f x − Normal a) = expectation p f − Normal a)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    fs[extreal_sub_add,extreal_ainv_def] >> imp_res_tac integrable_const >>
    qpat_x_assum `∀c. _` (fn a => ASSUME_TAC (ISPEC ``-a:real`` a)) >>
    fs[integral_add] >> ASSUME_TAC EXPECT_CONST >>
    fs[expectation_def,prob_space_def,p_space_def]
);

val HOEF_LEM_IBL_LEM_1 = store_thm(
    "HOEF_LEM_IBL_LEM_1",
    ``∀p a b c g f. prob_space p ∧ integrable p f ⇒
         integrable p (λx. 1 / (Normal b − Normal a) * exp (Normal g * Normal c) * f x)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    fs[extreal_mul_def,extreal_sub_def,extreal_exp_def] >>
    `integrable p (λx. inv (Normal (b − a)) * Normal (exp (g * c)) * f x)` suffices_by fs[inv_1over] >>
    `integrable p (λx. Normal (exp (g * c)) * inv (Normal (b − a)) * f x)`
        suffices_by metis_tac[mul_comm,mul_assoc] >>
    `integrable p (λx. (Normal (exp (g * c)) / (Normal (b − a))) * f x)`
        suffices_by metis_tac[extreal_div_def] >>
    `integrable p (λx. Normal (exp (g * c) / (b − a)) * f x)` suffices_by metis_tac[extreal_div_eq] >>
    fs[integrable_cmul]
);

val HOEF_LEM_IBL_LEM_2 = store_thm(
    "HOEF_LEM_IBL_LEM_2",
    ``∀p b f. prob_space p ∧ integrable p f ⇒ integrable p (λx. Normal b − f x)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >> fs[extreal_sub_add] >>
    imp_res_tac integrable_const >> imp_res_tac integrable_cmul >>
    qpat_x_assum `∀c. _` (fn a => ASSUME_TAC (ISPEC ``real (-1)`` a)) >>
    qpat_x_assum `∀c. _` (fn a => ASSUME_TAC (ISPEC ``b:real`` a)) >>
    fs[NORM_REAL_NEG1] >> `integrable p (λx. -f x)` by metis_tac[neg_minus1] >>
    fs[integrable_add]
);

val HOEF_LEM_IBL_LEM_3 = store_thm(
    "HOEF_LEM_IBL_LEM_3",
    ``∀p a f. prob_space p ∧ integrable p f ⇒ integrable p (λx. f x − Normal a)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    fs[extreal_sub_add,extreal_ainv_def] >> imp_res_tac integrable_const >>
    qpat_x_assum `∀c. _` (fn a => ASSUME_TAC (ISPEC ``-a:real`` a)) >>
    fs[integrable_add]
);

val HOEF_LEM_ALG_LEM_4 = store_thm (
    "HOEF_LEM_ALG_LEM_4",
    ``∀p a b g f. prob_space p ∧ integrable p f ⇒
        (expectation p (λx. 1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b - f x) +
        1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (f x − Normal a) ) =
        (Normal (exp (g * a) / (b − a)) * (Normal b − expectation p f) +
        Normal (exp (g * b) / (b − a)) * (expectation p f − Normal a)))``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    imp_res_tac HOEF_LEM_IBL_LEM_2 >> imp_res_tac HOEF_LEM_IBL_LEM_3 >>
    fs[expectation_def,prob_space_def,p_space_def] >> RES_TAC >> fs[] >> rw[] >>
    qpat_x_assum `∀b. _` (fn asm => ASSUME_TAC (ISPEC ``b:real`` asm)) >>
    qpat_x_assum `∀a. _` (fn asm => ASSUME_TAC (ISPEC ``a:real`` asm)) >>
    imp_res_tac HOEF_LEM_IBL_LEM_1 >> pop_assum kall_tac >>
    fs[expectation_def,prob_space_def,p_space_def] >> RES_TAC >> fs[] >> rw[] >>
    qpat_x_assum `∀g c b a. _`
        (fn asm => ASSUME_TAC (ISPECL [``g:real``,``b:real``,``b:real``,``a:real``] asm)) >>
    qpat_x_assum `∀g c b a. _`
        (fn asm => ASSUME_TAC (ISPECL [``g:real``,``a:real``,``b:real``,``a:real``] asm)) >>
    `integral p (λx.
        (λx. 1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − f x)) x +
        (λx. 1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (f x − Normal a)) x) =
        integral p (λx. 1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − f x)) +
        integral p (λx. 1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (f x − Normal a))`
        by (imp_res_tac integral_add) >> fs[] >>
    NTAC 3 (pop_assum kall_tac) >> imp_res_tac HOEF_LEM_ALG_LEM_1 >>
    fs[expectation_def,prob_space_def,p_space_def] >> RES_TAC >> fs[] >> rw[] >>
    qpat_x_assum `∀g c b a. _`
        (fn asm => ASSUME_TAC (ISPECL [``g:real``,``b:real``,``b:real``,``a:real``] asm)) >>
    qpat_x_assum `∀g c b a. _`
        (fn asm => ASSUME_TAC (ISPECL [``g:real``,``a:real``,``b:real``,``a:real``] asm)) >>
    NTAC 5 (pop_assum kall_tac) >> imp_res_tac HOEF_LEM_ALG_LEM_2 >> imp_res_tac HOEF_LEM_ALG_LEM_3 >>
    fs[expectation_def,prob_space_def,p_space_def] >> RES_TAC >> fs[] >> rw[] >>
    qpat_x_assum `∀b. _` (fn asm => ASSUME_TAC (ISPEC ``b:real`` asm)) >>
    qpat_x_assum `∀a. _` (fn asm => ASSUME_TAC (ISPEC ``a:real`` asm))
);

val HOEF_LEM_ALG_LEM_5 = store_thm(
    "HOEF_LEM_ALG_LEM_5",
    ``∀p a b g f. prob_space p ∧ (expectation p f = 0) ∧
        f ∈ measurable (m_space p,measurable_sets p) Borel ⇒
        (expectation p (λx.
        1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − f x) +
        1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (f x − Normal a)) =
        Normal (b * exp (g * a) / (b − a) - a * exp (g * b) / (b − a)))``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    `integrable p f` by metis_tac[N0_EQ_0,INTEGRAL_FINITE_IMP_IBL] >>
    imp_res_tac HOEF_LEM_ALG_LEM_4 >>
    fs[expectation_def,prob_space_def,p_space_def] >> RES_TAC >> fs[] >> rw[] >>
    pop_assum kall_tac >>
    fs[sub_lzero,sub_rzero,extreal_ainv_def,extreal_mul_def,extreal_add_def] >>
    fs[REAL_MUL_ASSOC,REAL_MUL_COMM,real_sub,REAL_MUL_LNEG] >>
    fs[real_div,REAL_MUL_ASSOC]
);

val HOEF_LEM_ALG_LEM_6 = store_thm(
    "HOEF_LEM_ALG_LEM_6",
    ``∀a:real b g. (a < 0) ∧ (0 < b) ⇒
        ∃h p. (h = g * (b - a)) ∧ (p = -a / (b - a)) ∧ (0 < p) ∧ (p < 1) ∧
        (b * exp (g * a) / (b − a) - a * exp (g * b) / (b − a) = exp (L p h))``,
    rpt strip_tac >> fs[L_def] >>
    `0 < -a` by fs[REAL_NEG_GT0] >>
    `0 < b + -a` by fs[REAL_LT_ADD] >>
    `0 < (b + -a)⁻¹` by fs[REAL_LT_INV_EQ] >>
    `0 < -a * (b + -a)⁻¹` by fs[REAL_LT_MUL] >>
    `0 < b * (b + -a)⁻¹` by fs[REAL_LT_MUL] >>
    fs[real_sub,real_div,REAL_NEG_LMUL,REAL_NEG_NEG] >>
    `1 + a * (b + -a)⁻¹ = b * (b + -a)⁻¹` by
        (ASSUME_TAC REAL_EQ_RDIV_EQ >>
        fs[real_div,REAL_ADD_RDISTRIB,REAL_MUL_ASSOC] >>
        `(b + -a) ≠ 0` by fs[REAL_LT_IMP_NE] >>
        fs[REAL_MUL_LINV] >> imp_res_tac REAL_MUL_LINV >>
        `b + -a + a * 1 = b` suffices_by metis_tac[REAL_MUL_ASSOC] >> fs[] >>
        `b + 0 = b` suffices_by metis_tac[REAL_ADD_LINV,REAL_ADD_ASSOC] >> fs[]) >> rw[]
    >-(
        `0 < 1 - -a * (b + -a)⁻¹` suffices_by fs[REAL_LT_SUB_LADD] >>
        fs[real_sub,REAL_NEGNEG,REAL_MUL_LNEG]
    )
    >-(
        `0 < exp (g * (b + -a))` by fs[EXP_POS_LT] >>
        `0 < b * (b + -a)⁻¹ + -a * (b + -a)⁻¹ * exp (g * (b + -a))` by fs[REAL_LT_MUL,REAL_LT_ADD] >>
        fs[EXP_ADD] >>
        `b * exp (g * a) * (b + -a)⁻¹ + -a * exp (g * b) * (b + -a)⁻¹ =
            exp (-g * (b + -a) * (-a * (b + -a)⁻¹)) *
            (b * (b + -a)⁻¹ + -a * (b + -a)⁻¹ * exp (g * (b + -a)))` suffices_by metis_tac[EXP_LN] >>
        `-g * (b + -a) * (-a * (b + -a)⁻¹) = -g * (b + -a) * -a * (b + -a)⁻¹` by fs[REAL_MUL_ASSOC] >>
        `_ = -g * -a * (b + -a) * (b + -a)⁻¹` by metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM] >>
        `_ = -g * -a * ((b + -a) * (b + -a)⁻¹)` by fs[REAL_MUL_ASSOC] >>
        `_ = -g * -a` by fs[REAL_LT_IMP_NE,REAL_MUL_RINV] >>
        `_ = g * a` by fs[REAL_NEG_MUL2] >> rw[] >>
        fs[REAL_ADD_LDISTRIB,REAL_MUL_ASSOC] >>
        `exp (g * a) * b * (b + -a)⁻¹ = b * exp (g * a) * (b + -a)⁻¹`
            by metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM] >> rw[] >>
        NTAC 7 (pop_assum kall_tac) >>
        `exp (g * a) * -a * (b + -a)⁻¹ * exp (g * b + g * -a) =
            -a * exp (g * a) * exp (g * b + g * -a) * (b + -a)⁻¹`
            by metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM] >> rw[] >>
        fs[REAL_LT_IMP_NE] >>
        `exp (g * b) = exp (g * a) * exp (g * b + g * -a)` suffices_by metis_tac[REAL_MUL_ASSOC] >>
        `exp (g * b) = exp (g * a + g * b + g * -a)` suffices_by metis_tac[EXP_ADD,REAL_ADD_ASSOC] >>
        `g * b = g * a + g * b + g * -a` suffices_by metis_tac[] >>
        `g * b = g * a + g * -a + g * b` suffices_by metis_tac[REAL_ADD_ASSOC,REAL_ADD_COMM] >>
        `g * a + g * -a = a * g + -a * g` by fs[REAL_MUL_COMM] >>
        `_ = a * g + -(a * g)` by fs[REAL_MUL_LNEG] >>
        `_ = a * g - (a * g)` by fs[real_sub] >> fs[]
    )
);

val HOEF_LEM_ALG_LEM_7 = store_thm(
    "HOEF_LEM_ALG_LEM_7",
    ``∀a:real b g x. (a < 0) ∧ (0 < b) ∧ (a ≤ x) ∧ (x ≤ b) ⇒
        (exp (g * x) ≤ 1 / (b - a) * exp (g * a) * (b - x) + 1 / (b - a) * exp (g * b) * (x - a))``,
    rpt strip_tac >> fs[real_sub,real_div] >>
    `0 ≤ (b + -x) * (b + -a)⁻¹` by
        (`0 < -a` by fs[REAL_NEG_GT0] >>
        `0 < b + -a` by fs[REAL_LT_ADD] >>
        `0 ≤ (b + -a)⁻¹` by fs[REAL_LT_INV_EQ,REAL_LT_IMP_LE] >>
        `0 ≤ b - x` by fs[REAL_LE_SUB_LADD] >> fs[real_sub,REAL_LE_MUL]) >>
    `1 - (b + -x) * (b + -a)⁻¹ = (x + -a) * (b + -a)⁻¹` by
        (fs[REAL_EQ_SUB_RADD] >>
        `1 = ((x + -a) + (b + -x)) * (b + -a)⁻¹` suffices_by fs[REAL_ADD_RDISTRIB] >>
        `0 < -a` by fs[REAL_NEG_GT0] >>
        `0 < b + -a` by fs[REAL_LT_ADD] >>
        `1 = (x + -a + (b + -x)) / (b + -a)` suffices_by fs[real_div] >>
        `(b + -a) = x + -a + (b + -x)` suffices_by fs[REAL_EQ_RDIV_EQ] >>
        `b + -a = x + -x + b + -a` suffices_by metis_tac[REAL_ADD_ASSOC,REAL_ADD_COMM] >> fs[]) >>
    `(b + -x) * (b + -a)⁻¹ ≤ 1` by
        (`0 ≤ 1 - (b + -x) * (b + -a)⁻¹` suffices_by fs[REAL_LE_SUB_LADD] >> rw[] >>
        `0 < -a` by fs[REAL_NEG_GT0] >>
        `0 < b + -a` by fs[REAL_LT_ADD] >>
        `0 ≤ (b + -a)⁻¹` by fs[REAL_LT_INV_EQ,REAL_LT_IMP_LE] >>
        `0 ≤ x - a` by fs[REAL_LE_SUB_LADD] >> fs[real_sub,REAL_LE_MUL]) >>
    `exp ((b + -x) * (b + -a)⁻¹ * (g * a) + (x + -a) * (b + -a)⁻¹ * (g * b)) ≤
        (b + -x) * (b + -a)⁻¹ * exp (g * a) + (x + -a) * (b + -a)⁻¹ * exp (g * b)` by
        ((qspecl_then [`g * a`,`g * b`,`(b − x) / (b − a)`] assume_tac) exp_convex >>
        fs[real_sub,real_div,REAL_ADD_ASSOC] >> pop_assum imp_res_tac >> metis_tac[]) >>
    `(b + -x) * (b + -a)⁻¹ * (g * a) + (x + -a) * (b + -a)⁻¹ * (g * b) = g * x` by
        (`(b + -a)⁻¹ * (b + -x) * (g * a) + (b + -a)⁻¹ * (x + -a) * (g * b) = g * x`
            suffices_by metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM] >>
        `(b + -a)⁻¹ * ((b + -x) * (g * a) + (x + -a) * (g * b)) = g * x`
            suffices_by fs[REAL_ADD_LDISTRIB,REAL_MUL_ASSOC] >>
        `(b + -x) * (g * a) + (x + -a) * (g * b) = (b + -a) * g * x` by
            (fs[REAL_ADD_RDISTRIB,REAL_MUL_ASSOC,REAL_ADD_ASSOC] >>
            `b * g * a + -a * g * b + x * g * b + -x * g * a = b * g * x + -a * g * x`
                suffices_by metis_tac[REAL_ADD_ASSOC,REAL_ADD_COMM] >>
            `a * b * g + -a * b * g + x * g * b + -x * g * a = x * g * b + x * g * -a`
                suffices_by metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM] >>
            fs[REAL_MUL_LNEG,REAL_MUL_RNEG,REAL_EQ_RADD]) >> rw[] >>
        `0 < -a` by fs[REAL_NEG_GT0] >>
        `0 ≠ b + -a` by fs[REAL_LT_ADD,REAL_LT_IMP_NE] >>
        fs[REAL_MUL_ASSOC,REAL_MUL_LINV]) >>
    `exp (g * x) ≤ (b + -x) * (b + -a)⁻¹ * exp (g * a) + (x + -a) * (b +
        -a)⁻¹ * exp (g * b)` by metis_tac[] >>
    metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM]
);

val HOEF_LEM_ALG_LEM_8 = store_thm(
    "HOEF_LEM_ALG_LEM_8",
    ``∀p X a b g. (real_random_variable X p) ∧
        (probably p {x | X x ∈ (closed_interval (Normal a) (Normal b))}) ⇒
        (integral p (λx. exp (Normal g * X x)) = integral p
        (λx. indicator_fn {x | Normal a ≤ x ∧ x ≤ Normal b} (X x) * exp (Normal g * X x)))``,
    rpt strip_tac >>
    fs[real_random_variable_def,prob_space_def,probably_def,p_space_def,events_def,prob_def] >>
    `sigma_algebra (m_space p,measurable_sets p)` by fs[measure_space_def] >>
    `(λx. Normal g * X x) ∈ measurable (m_space p,measurable_sets p) Borel` by
        (`∀x. (λx. Normal g * X x) x = Normal g * X x` suffices_by
            (strip_tac >>
            (qspecl_then [`(m_space p,measurable_sets p)`,`X`,`(λx. Normal g * X x)`,`g`] assume_tac)
                IN_MEASURABLE_BOREL_CMUL >> pop_assum imp_res_tac >>
            NTAC 2 (pop_assum kall_tac) >> fs[]) >>
        fs[]) >>
    assume_tac EXP_MBL >>
    `(λx. exp (Normal g * X x)) ∈ measurable (m_space p,measurable_sets p) Borel` by
        (`exp ∘ (λx. Normal g * X x) ∈ measurable (m_space p,measurable_sets p) Borel`
            by imp_res_tac MEASURABLE_COMP >>
        `(λx. exp (Normal g * X x)) = exp ∘ (λx. Normal g * X x)` suffices_by fs[] >>
        `∀x. (λx. exp (Normal g * X x)) x = (exp ∘ (λx. Normal g * X x)) x` suffices_by metis_tac[] >>
        strip_tac >> fs[]) >>
    (qspecl_then [`p`,`{x | X x ∈ closed_interval (Normal a) (Normal b)}`,
        `(λx. exp (Normal g * X x))`] assume_tac) PSPACE_MBL_IMP_EXP_EQ_EXP_AS >>
    fs[expectation_def,prob_space_def,probably_def,p_space_def,events_def,prob_def] >>
    pop_assum imp_res_tac >>
    `∀x. indicator_fn {x | X x ∈ closed_interval (Normal a) (Normal b)} x =
        indicator_fn {x | Normal a ≤ x ∧ x ≤ Normal b} (X x)` suffices_by fs[] >>
    strip_tac >> fs[indicator_fn_def,closed_interval_def]
);

val HOEF_LEM_ALG_LEM_9 = store_thm(
    "HOEF_LEM_ALG_LEM_9",
    ``∀p X a b g. (real_random_variable X p) ∧
        (probably p {x | X x ∈ (closed_interval (Normal a) (Normal b))}) ⇒
        (integral p (λx. 1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − X x) +
        1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (X x − Normal a)) =
        integral p (λx. indicator_fn {x | Normal a ≤ x ∧ x ≤ Normal b} (X x) *
        (1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − X x) +
        1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (X x − Normal a))))``,
    rpt strip_tac >>
    fs[real_random_variable_def,prob_space_def,probably_def,p_space_def,events_def,prob_def] >>
    `sigma_algebra (m_space p,measurable_sets p)` by fs[measure_space_def] >>
    `∀c. Normal 1 / (Normal b − Normal a) * exp (Normal g * Normal c) =
        Normal (1 / (b − a) * exp (g * c))` by (strip_tac >>
        fs[extreal_sub_def,extreal_mul_def,extreal_div_eq,extreal_exp_def]) >>
    fs[N1_EQ_1] >> pop_assum kall_tac >>
    `(λx. Normal a) ∈ measurable (m_space p,measurable_sets p) Borel` by
        fs[IN_MEASURABLE_BOREL_CONST_ALT] >>
    `(λx. Normal b) ∈ measurable (m_space p,measurable_sets p) Borel` by
        fs[IN_MEASURABLE_BOREL_CONST_ALT] >>
    `(λx. (λx. Normal b) x − X x) ∈
        measurable (m_space p,measurable_sets p) Borel` by
        fs[IN_MEASURABLE_BOREL_SUB_ALT] >> fs[] >>
    `(λx. X x − (λx. Normal a) x) ∈
        measurable (m_space p,measurable_sets p) Borel` by
        fs[IN_MEASURABLE_BOREL_SUB_ALT] >> fs[] >>
    `(λx. Normal (1 / (b − a) * exp (g * a)) * (λx. Normal b − X x) x) ∈
        measurable (m_space p,measurable_sets p) Borel` by
        fs[IN_MEASURABLE_BOREL_CMUL_ALT] >> fs[] >>
    `(λx. Normal (1 / (b − a) * exp (g * b)) * (λx. X x − Normal a) x) ∈
        measurable (m_space p,measurable_sets p) Borel` by
        fs[IN_MEASURABLE_BOREL_CMUL_ALT] >> fs[] >>
    `(λx. (λx. Normal (1 / (b − a) * exp (g * a)) * (Normal b − X x)) x +
        (λx. Normal (1 / (b − a) * exp (g * b)) * (X x − Normal a)) x) ∈
        measurable (m_space p,measurable_sets p) Borel` by
        fs[IN_MEASURABLE_BOREL_ADD_ALT] >> fs[] >>
    (qspecl_then [`p`,`{x | X x ∈ closed_interval (Normal a) (Normal b)}`,
        `(λx. Normal (1 / (b − a) * exp (g * a)) * (Normal b − X x) +
        Normal (1 / (b − a) * exp (g * b)) * (X x − Normal a))`] assume_tac)
        PSPACE_MBL_IMP_EXP_EQ_EXP_AS >>
    fs[expectation_def,prob_space_def,probably_def,p_space_def,events_def,prob_def] >>
    pop_assum imp_res_tac >> NTAC 8 (pop_assum kall_tac) >>
    fs[indicator_fn_def,closed_interval_def]
);

val HOEFFDINGS_LEMMA = store_thm(
    "HOEFFDINGS_LEMMA",
    ``∀p a b g X. real_random_variable X p ∧ (expectation p X = 0) ∧ (a < 0) ∧ (0 < b) ∧
        probably p {x | X x ∈ closed_interval (Normal a) (Normal b)} ⇒
        expectation p (λx. (exp (Normal g * X x))) ≤ Normal (exp (g * g * (b - a) * (b - a) / 8))``,
    rpt strip_tac >>
    imp_res_tac HOEF_LEM_ALG_LEM_8 >> imp_res_tac HOEF_LEM_ALG_LEM_9 >>
    NTAC 2 (qpat_x_assum `∀g. _` (qspec_then `g` assume_tac)) >>
    fs[expectation_def,prob_space_def,p_space_def,real_random_variable_def,events_def] >>
    `∀t. t ∈ m_space p ⇒
        (λx. indicator_fn {x | Normal a ≤ X x ∧ X x ≤ Normal b} x * exp (Normal g * X x)) t ≤
        (λx. indicator_fn {x | Normal a ≤ X x ∧ X x ≤ Normal b} x *
        (1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − X x) +
        1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (X x − Normal a))) t` by
        (rpt strip_tac >> fs[indicator_fn_def] >> Cases_on `Normal a ≤ X t ∧ X t ≤ Normal b`
        >-(
            fs[mul_lone] >> RES_TAC >> ASSUME_TAC HOEF_LEM_ALG_LEM_7 >>
            pop_assum (qspecl_then [`a`, `b`, `g`, `real (X t)`] assume_tac) >>
            `Normal (real (X t)) = X t` by fs[normal_real] >>
            `a ≤ real (X t)` by
                (`Normal a ≤ Normal (real (X t))` suffices_by fs[extreal_le_def] >> fs[]) >>
            `real (X t) ≤ b` by
                (`Normal (real (X t)) ≤ Normal b` suffices_by fs[extreal_le_def] >> fs[]) >>
            qpat_x_assum `_ ∧ _ ∧ _ ∧ _ ⇒ _` imp_res_tac >>
            `Normal (exp (g * real (X t))) ≤
                Normal (1 / (b − a) * exp (g * a) * (b − real (X t)) +
                1 / (b − a) * exp (g * b) * (real (X t) − a))` by fs[extreal_le_def] >>
            `exp (Normal g * Normal (real (X t))) ≤
                Normal 1 / (Normal b − Normal a) *
                exp (Normal g * Normal a) * (Normal b − Normal (real (X t))) +
                Normal 1 / (Normal b − Normal a) *
                exp (Normal g * Normal b) * (Normal (real (X t)) − Normal a)`
                suffices_by fs[extreal_of_num_def] >>
            fs[extreal_div_eq,extreal_add_def,extreal_mul_def,extreal_sub_def,extreal_exp_def]
        )
        >-(fs[mul_lzero,le_refl])) >>
    `integral p (λx. indicator_fn {x | Normal a ≤ X x ∧ X x ≤ Normal b} x * exp (Normal g * X x))
        ≤ integral p (λx. indicator_fn {x | Normal a ≤ X x ∧ X x ≤ Normal b} x *
        (1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − X x) +
        1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (X x − Normal a)))`
        by fs[integral_mono] >>
    `integral p (λx. exp (Normal g * X x)) ≤ integral p (λx.
        1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − X x) +
        1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (X x − Normal a))` by
        fs[closed_interval_def,indicator_fn_def] >>
    ASSUME_TAC HOEF_LEM_ALG_LEM_5 >> fs[expectation_def,prob_space_def,p_space_def] >>
    `(integral p (λx.
        1 / (Normal b − Normal a) * exp (Normal g * Normal a) * (Normal b − X x) +
        1 / (Normal b − Normal a) * exp (Normal g * Normal b) * (X x − Normal a)) =
        Normal (b * exp (g * a) / (b − a) − a * exp (g * b) / (b − a)))`
        by (RES_TAC >> fs[]) >> qpat_x_assum `∀p a b g f. _` kall_tac >>
    `integral p (λx. exp (Normal g * X x)) ≤
        Normal (b * exp (g * a) / (b − a) − a * exp (g * b) / (b − a))`
        by fs[le_lt,le_trans] >>
    `Normal (b * exp (g * a) / (b − a) − a * exp (g * b) / (b − a)) ≤
        Normal (exp (g * g * (b − a) * (b − a) / 8))` suffices_by metis_tac[le_trans] >>
    NTAC 5 (pop_assum kall_tac) >>
    `b * exp (g * a) / (b − a) − a * exp (g * b) / (b − a) ≤
        exp (g * g * (b − a) * (b − a) / 8)` suffices_by fs[extreal_le_def] >>
    imp_res_tac HOEF_LEM_ALG_LEM_6 >> pop_assum (qspec_then `g` assume_tac) >>
    Q.ABBREV_TAC `h = g * (b − a)` >> Q.ABBREV_TAC `q = -a / (b − a)` >> fs[EXP_MONO_LE] >>
    `L q h ≤ h * h / 8` by fs[L_LE_EIGTH_HH] >>
    `h * h / 8 = g * g * (b − a) * (b − a) / 8` suffices_by (strip_tac >> fs[le_lt,le_trans]) >>
    Q.UNABBREV_TAC `q` >> Q.UNABBREV_TAC `h` >> fs[real_div] >>
    metis_tac[REAL_MUL_ASSOC,REAL_MUL_COMM]
);

val HOEF_INEQ_LEM_1 = store_thm(
    "HOEF_INEQ_LEM_1",
    ``∀mu sp (s:real) (t:real) f. (0 < s) ⇒
        (mu {x | Normal t ≤ f x ∧ x ∈ sp} =
        mu {x | Normal (exp (s * t)) ≤ exp (Normal s * (f x)) ∧ x ∈ sp})``,
    rpt strip_tac >>
    `{x | Normal t ≤ f x ∧ x ∈ sp} =
        {x | Normal (exp (s * t)) ≤ exp (Normal s * f x) ∧ x ∈ sp}` suffices_by fs[] >>
    `∀x. (Normal t ≤ f x ∧ x ∈ sp) ⇔
        (Normal (exp (s * t)) ≤ exp (Normal s * f x) ∧ x ∈ sp)` suffices_by fs[] >>
    strip_tac >> Cases_on `x ∈ sp` >> fs[] >> pop_assum kall_tac >>
    `Normal t ≤ f x ⇔ Normal s * (Normal t) ≤ Normal s * f x` by
        (imp_res_tac le_lmul_real >> metis_tac[]) >>
    fs[extreal_mul_def] >> pop_assum kall_tac >>
    (qspecl_then [`Normal (s * t)`,`Normal s * f x`] assume_tac) ext_exp_mono_le >>
    fs[extreal_exp_def]
);

val HOEF_INEQ_LEM_2 = store_thm(
    "HOEF_INEQ_LEM_2",
    ``∀sp sts mu n s t X. measure_space (sp,sts,mu) ∧
        (∀i. i < n ⇒ real_random_variable (X i) (sp,sts,mu)) ⇒
        (Normal (mu {x | Normal (exp (s * t)) ≤
        exp (Normal s * ((sumfinfun (0,n) X) x −
        integral (sp,sts,mu) (sumfinfun (0,n) X))) ∧ x ∈ sp}) ≤
        1 / Normal (exp (s * t)) * integral (sp,sts,mu)
        (λx. exp (Normal s * ((sumfinfun (0,n) X) x −
        integral (sp,sts,mu) (sumfinfun (0,n) X)))))``,
    NTAC 7 strip_tac >> Q.ABBREV_TAC `SX = sumfinfun (0,n) X` >>
    Q.ABBREV_TAC `ESX = integral (sp,sts,mu) SX` >> rpt strip_tac >>
    `0 < exp (s * t)` by fs[EXP_POS_LT] >>
    `∀x. 0 ≤ (λx. exp (Normal s * (SX x − ESX))) x` by (strip_tac >> fs[ext_exp_pos_le]) >>
    `measurable (sp,sts) Borel (λx. exp (Normal s * (SX x − ESX)))`
        suffices_by (strip_tac >> imp_res_tac MARKOVS_INEQUALITY >> fs[]) >>
    NTAC 2 (pop_assum kall_tac) >>
    `(λx. exp (Normal s * (SX x − ESX))) ∈ measurable (sp,sts) Borel`
        suffices_by (strip_tac >> fs[measurable_def]) >>
    `(λx. Normal s * (SX x − ESX)) ∈ measurable (sp,sts) Borel`
        suffices_by (strip_tac >> assume_tac EXP_MBL >> imp_res_tac MEASURABLE_COMP >>
        `(λx. exp (Normal s * (SX x − ESX))) = exp ∘ (λx. Normal s * (SX x − ESX))`
            suffices_by fs[] >>
        `∀x. (λx. exp (Normal s * (SX x − ESX))) x = (exp ∘ (λx. Normal s * (SX x − ESX))) x`
            suffices_by metis_tac[] >>
        strip_tac >> fs[]) >>
    `sigma_algebra (sp,sts)` by fs[measure_space_def,m_space_def,measurable_sets_def] >>
    `(λx. SX x − ESX) ∈ measurable (sp,sts) Borel` suffices_by (strip_tac >>
        imp_res_tac IN_MEASURABLE_BOREL_CMUL_ALT >> fs[]) >>
    `SX ∈ measurable (sp,sts) Borel` suffices_by (strip_tac >>
        `(λx. ESX) ∈ measurable (sp,sts) Borel` by fs[IN_MEASURABLE_BOREL_CONST_ALT] >>
        (qspecl_then [`(sp,sts)`,`SX`,`(λx. ESX)`] assume_tac) IN_MEASURABLE_BOREL_SUB_ALT >>
        pop_assum imp_res_tac >> fs[]) >>
    Q.UNABBREV_TAC `ESX` >> Q.UNABBREV_TAC `SX` >>
    `∀i. i < n ⇒ X i ∈ measurable (sp,sts) Borel` by (rpt strip_tac >> RES_TAC >>
        fs[real_random_variable_def,p_space_def,m_space_def,events_def,measurable_sets_def]) >>
    imp_res_tac IN_MEASURABLE_BOREL_SUMFINFUN
);

val HOEF_INEQ_LEM_5 = store_thm(
    "HOEF_INEQ_LEM_5",
    ``∀n X a b s t. Normal (exp (-(s * t))) *
        prodfin (0,n) (λi. Normal (exp (s * s * (b i − a i) * (b i − a i) / 8))) =
        Normal (exp (-(s * t) + s * s / 8 * sum (0,n) (λi. (b i − a i) * (b i − a i))))``,
    rpt strip_tac >>
    (qspecl_then [`λi. s * s * (b i − a i) * (b i − a i) / 8`,`n`] assume_tac) exp_sum >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`λi. s * s * (b i − a i) * (b i − a i) / 8`,`n`] assume_tac) sumfin_normal >>
    fs[extreal_exp_def,extreal_mul_def] >> pop_assum kall_tac >> fs[EXP_ADD] >>
    `sum (0,n) (λi. s * s * (b i − a i) * (b i − a i) / 8) =
        s * s / 8 * sum (0,n) (λi. (b i − a i) * (b i − a i))` suffices_by fs[] >>
    `(λi. s * s * (b i − a i) * (b i − a i) / 8) =
        (λi. s * s / 8 * (b i − a i) * (b i − a i))`
        by (fs[real_div] >> metis_tac[REAL_MUL_COMM,REAL_MUL_ASSOC]) >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`λi. (b i − a i) * (b i − a i)`,`s * s / 8`,`0`,`n`] assume_tac) SUM_CMUL >>
    fs[REAL_MUL_ASSOC]
);

val HOEF_INEQ_LEM_6 = store_thm(
    "HOEF_INEQ_LEM_6",
    ``∀p n X a b t. (prob_space p) ∧ (0 < t) ∧ (∀i. i < n ⇒ real_random_variable (X i) p) ∧
        (sum (0,n) (λi. (b i − a i) * (b i − a i)) = 0) ∧
        (∀i. i < n ⇒ (expectation p (X i) ≠ PosInf) ∧ (expectation p (X i) ≠ NegInf)) ∧
        (∀i. i < n ⇒ probably p {x | (X i) x ∈ closed_interval (Normal (a i)) (Normal (b i))}) ⇒
        (measure p {x | Normal t ≤
        (sumfinfun (0,n) X) x − (integral p (sumfinfun (0,n) X)) ∧ x ∈ m_space p} = 0)``,
    NTAC 6 strip_tac >> Q.ABBREV_TAC `sp = m_space p` >>
    Q.ABBREV_TAC `sts = measurable_sets p` >> Q.ABBREV_TAC `mu = measure p` >>
    Q.ABBREV_TAC `SX = sumfinfun (0,n) X` >> Q.ABBREV_TAC `ESX = integral p SX` >> strip_tac >>
    `∀i. (i < n) ⇒ (0 ≤ (λi. (b i − a i) * (b i − a i)) i)`
        by (rpt strip_tac >> fs[REAL_LE_SQUARE]) >>
    imp_res_tac SUM_OF_POS_EQ_0 >> pop_assum kall_tac >> fs[] >> rw[] >>
    qpat_x_assum `sum _ _ = _` kall_tac >> fs[closed_interval_point] >>
    `∀i. i < n ⇒ integrable p (X i)` by (rpt strip_tac >> RES_TAC >>
        fs[prob_space_def,expectation_def,real_random_variable_def,p_space_def,events_def] >>
        Cases_on `integral p (X i)` >> fs[] >> rw[] >>
        NTAC 4 (qpat_x_assum `∀i. i < n ⇒ _` kall_tac) >> rfs[] >>
        assume_tac INTEGRAL_FINITE_IMP_IBL >> rfs[]) >>
    `integral p (sumfinfun (0,n) X) = sumfin (0,n) (λi. integral p (X i))`
        by (fs[prob_space_def,p_space_def] >> imp_res_tac integral_sumfinfun >> rfs[]) >>
    Q.UNABBREV_TAC `SX` >> fs[] >> pop_assum kall_tac >>
    `∀i. i < n ⇒ (integral p (X i) = Normal (a i))` by (rpt strip_tac >> RES_TAC >>
        NTAC 5 (qpat_x_assum `∀i. i < n ⇒ _` kall_tac) >>
        fs[real_random_variable_def,p_space_def,events_def] >> rw[] >>
        imp_res_tac PSPACE_MBL_IMP_EXP_EQ_EXP_AS >>
        fs[expectation_def] >> pop_assum kall_tac >>
        `(λx. indicator_fn {x | X i x = Normal (a i)} x * X i x) =
            (λx.  Normal (a i) * indicator_fn {x | X i x = Normal (a i)} x)`
            by (`∀x. (λx. indicator_fn {x | X i x = Normal (a i)} x * X i x) x =
                (λx.  Normal (a i) * indicator_fn {x | X i x = Normal (a i)} x) x` suffices_by fs[] >>
            strip_tac >> fs[indicator_fn_def] >> Cases_on `X i x = Normal (a i)` >>
            fs[mul_lzero,mul_rzero,mul_lone,mul_rone]) >>
        fs[] >> pop_assum kall_tac >> rfs[probably_def,prob_def,events_def] >>
        (qspecl_then [`p`,`{x | X i x = Normal (a i)}`,`a i`] assume_tac) integral_cmul_indicator >>
        rfs[prob_space_def]) >>
    (qspecl_then [`n`,`(λi. integral p (X i))`,`(λi. Normal (a i))`] assume_tac) sumfin_replace >>
    fs[sumfin_normal] >> pop_assum kall_tac >> Q.UNABBREV_TAC `ESX` >>
    imp_res_tac sumfinfun_probably >> rfs[] >>
    Q.ABBREV_TAC `SX = sumfinfun (0,n) X` >> Q.ABBREV_TAC `Sa = sum (0,n) a` >>
    `{x | (SX x = Normal Sa) ∧ x ∈ sp} = {x | (SX x - Normal Sa = 0) ∧ x ∈ sp}` by (
        fs[EXTENSION] >> strip_tac >>
        `(SX x = Normal Sa) ⇔ (SX x − Normal Sa = 0)` suffices_by metis_tac[] >>
        EQ_TAC >> fs[sub_0] >> strip_tac >> fs[extreal_sub_def,N0_EQ_0]) >>
    fs[] >> pop_assum kall_tac >>
    `(λx. SX x − Normal Sa) ∈ measurable (sp,sts) Borel` by (
        `sigma_algebra (m_space p,measurable_sets p)` by fs[prob_space_def,measure_space_def] >>
        `sumfinfun (0,n) X ∈ measurable (m_space p,measurable_sets p) Borel` by (
            imp_res_tac IN_MEASURABLE_BOREL_SUMFINFUN >>
            fs[real_random_variable_def,p_space_def,events_def]) >>
        rfs[] >> `(λx. Normal Sa) ∈ measurable (sp,sts) Borel` by fs[IN_MEASURABLE_BOREL_CONST_ALT] >>
        (qspecl_then [`(sp,sts)`,`SX`,`(λx. Normal Sa)`] assume_tac) IN_MEASURABLE_BOREL_SUB_ALT >>
        rfs[]) >>
    `{x | SX x − Normal Sa < Normal t ∧ x ∈ sp} ∈ events p` by (fs[events_def] >>
        imp_res_tac IN_MEASURABLE_BOREL_ALL >> rfs[INTER_DEF,space_def,subsets_def]) >>
    `{x | (SX x − Normal Sa = 0) ∧ x ∈ sp} ⊆ {x | SX x − Normal Sa < Normal t ∧ x ∈ sp}` by (
        fs[SUBSET_DEF] >> rpt strip_tac >>
        `Normal 0 < Normal t` suffices_by fs[N0_EQ_0] >>
        fs[extreal_lt_alt]) >>
    imp_res_tac probably_subset >> pop_assum kall_tac >>
    imp_res_tac propably_comp_null >> pop_assum kall_tac >>
    rfs[null_set_def,p_space_def] >>
    `sp DIFF {x | SX x − Normal Sa < Normal t ∧ x ∈ sp} =
        {x | Normal t ≤ SX x − Normal Sa ∧ x ∈ sp}` suffices_by (strip_tac >> fs[]) >>
    fs[DIFF_DEF,EXTENSION] >> strip_tac >> rpt (pop_assum kall_tac) >>
    `¬(SX x − Normal Sa < Normal t) ⇔ Normal t ≤ SX x − Normal Sa`
        suffices_by (strip_tac >> metis_tac[]) >>
    Cases_on `SX x` >> fs[extreal_sub_def,extreal_lt_alt,extreal_le_def,real_lte]
);

val _ = export_theory();
