open HolKernel Parse boolLib bossLib;
open combinTheory;
open pairTheory;
open pred_setTheory;
open arithmeticTheory;
open realTheory;
open seqTheory;
open real_sigmaTheory;
open util_probTheory;
open c487306_extrealTheory;
open c487306_measureTheory;
open c487306_lebesgueTheory;
open c487306_probabilityTheory;
open trivialTheory;
open finiteTheory;
open roydenTheory;

val _ = new_theory "halmos";

(* Definitions *)

val x_slice_def = Define `x_slice s0 s = PREIMAGE (λs1. (s0,s1)) s`;

val y_slice_def = Define `y_slice s1 s = PREIMAGE (λs0. (s0,s1)) s`;

val x_sliceable_sets_def = Define `x_sliceable_sets m0 m1 =
    {s | s ∈ measurable_sets (prod_measure_space m0 m1) ∧ ∀s0. x_slice s0 s ∈ measurable_sets m1}`;

val y_sliceable_sets_def = Define `y_sliceable_sets m0 m1 =
    {s | s ∈ measurable_sets (prod_measure_space m0 m1) ∧ ∀s1. y_slice s1 s ∈ measurable_sets m0}`;

val x_slice_fun_def = Define `x_slice_fun m1 s s0 = Normal (measure m1 (x_slice s0 s))`;

val y_slice_fun_def = Define `y_slice_fun m0 s s1 = Normal (measure m0 (y_slice s1 s))`;

val x_slice_fun_measurable_sets_def = Define `x_slice_fun_measurable_sets m0 m1 = {s |
    s ∈ measurable_sets (prod_measure_space m0 m1) ∧
    x_slice_fun m1 s ∈ measurable (m_space m0,measurable_sets m0) Borel}`;

val y_slice_fun_measurable_sets_def = Define `y_slice_fun_measurable_sets m0 m1 = {s |
    s ∈ measurable_sets (prod_measure_space m0 m1) ∧
    y_slice_fun m0 s ∈ measurable (m_space m1,measurable_sets m1) Borel}`;

val x_fun_slice_def = Define `x_fun_slice f x y = f (x,y)`;

val y_fun_slice_def = Define `y_fun_slice f y x = f (x,y)`;

val prod_measure_hor_def = Define `prod_measure_hor m0 m1 =
    (λa. real (integral m1 (λs1. Normal (measure m0 (PREIMAGE (λs0. (s0,s1)) a)))))`;

val prod_measure_space_hor_def = Define `prod_measure_space_hor m0 m1 =
    (m_space m0 × m_space m1,
    subsets (sigma (m_space m0 × m_space m1) (prod_sets (measurable_sets m0) (measurable_sets m1))),
    prod_measure_hor m0 m1)`;

val monotone_class_def = Define `monotone_class a ⇔
    subset_class (space a) (subsets a) ∧
    (∀f. f ∈ (𝕌(:num) -> subsets a) ∧ (∀n. f n ⊆ f (SUC n)) ⇒
    BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a) ∧
    (∀f. f ∈ (𝕌(:num) -> subsets a) ∧ (∀n. f (SUC n) ⊆ f n) ⇒
    BIGINTER (IMAGE f 𝕌(:num)) ∈ subsets a)`;

val mono_class_gen_def = Define `mono_class_gen sp st =
    (sp,BIGINTER {s | st ⊆ s ∧ monotone_class (sp,s)})`;

val inv_meas_def = Define `inv_meas m f s = measure m (PREIMAGE f s ∩ m_space m)`

val pi_sys_def = Define `pi_sys a ⇔ subset_class (space a) (subsets a) ∧ (subsets a ≠ ∅) ∧
    ∀s t. s ∈ subsets a ∧ t ∈ subsets a ⇒ s ∩ t ∈ subsets a`;

val lambda_sys_def = Define `lambda_sys a ⇔ subset_class (space a) (subsets a) ∧ ∅ ∈ subsets a ∧
    (∀s. s ∈ subsets a ⇒ space a DIFF s ∈ subsets a) ∧ ∀f. f ∈ (𝕌(:num) -> subsets a) ∧
    (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒ BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a`;

val lambda_def = Define `∀sp st. lambda sp st = (sp,BIGINTER {s | st ⊆ s ∧ lambda_sys (sp,s)})`;

(* "Alternate definitions and simplifications" *)

val x_slice_fun_alt = store_thm(
    "x_slice_fun_alt",
    ``∀m1 s s0. x_slice_fun m1 s = (λs0. Normal (measure m1 (x_slice s0 s)))``,
    rw[FUN_EQ_THM,x_slice_fun_def]
);

val y_slice_fun_alt = store_thm(
    "y_slice_fun_alt",
    ``∀m0 s s1. y_slice_fun m0 s = (λs1. Normal (measure m0 (y_slice s1 s)))``,
    rw[FUN_EQ_THM,y_slice_fun_def]
);

val prod_measure_alt = store_thm(
    "prod_measure_alt",
    ``∀m0 m1. prod_measure m0 m1 = (λs. real (integral m0 (x_slice_fun m1 s)))``,
    rw[prod_measure_def,x_slice_fun_alt,x_slice_def]
);

val prod_measure_hor_alt = store_thm(
    "prod_measure_hor_alt",
    ``∀m0 m1. prod_measure_hor m0 m1 = (λs. real (integral m1 (y_slice_fun m0 s)))``,
    rw[prod_measure_hor_def,y_slice_fun_alt,y_slice_def]
);

val x_fun_slice_alt = store_thm(
    "x_fun_slice_alt",
    ``∀f x. x_fun_slice f x = (λy. f (x,y))``,
    rw[FUN_EQ_THM,x_fun_slice_def]
);

val y_fun_slice_alt = store_thm(
    "y_fun_slice_alt",
    ``∀f y. y_fun_slice f y = (λx. f (x,y))``,
    rw[FUN_EQ_THM,y_fun_slice_def]
);

val inv_meas_alt = store_thm(
    "inv_meas_alt",
    ``∀m f. inv_meas m f = (λs. measure m (PREIMAGE f s ∩ m_space m))``,
    rw[FUN_EQ_THM,inv_meas_def]
);

(***************************************************)
(* Trivial Results for horizontal product measures *)
(***************************************************)

val m_space_prod_measure_space_hor = store_thm(
    "m_space_prod_measure_space_hor",
    ``∀m0 m1. m_space (prod_measure_space_hor m0 m1) = m_space m0 × m_space m1``,
    rw[prod_measure_space_hor_def,m_space_def]
);

val measurable_sets_prod_measure_space_hor = store_thm(
    "measurable_sets_prod_measure_space_hor",
    ``∀m0 m1. measurable_sets (prod_measure_space_hor m0 m1) = subsets
        (sigma (m_space m0 × m_space m1) (prod_sets (measurable_sets m0) (measurable_sets m1)))``,
    rw[prod_measure_space_hor_def,measurable_sets_def]
);

val m_space_prod_hor_m_space_prod = store_thm(
    "m_space_prod_hor_m_space_prod",
    ``∀m0 m1. m_space (prod_measure_space_hor m0 m1) =
        m_space (prod_measure_space m0 m1)``,
    rw[m_space_prod_measure_space,m_space_prod_measure_space_hor]
);

val measurable_sets_prod_hor_measurable_sets_prod = store_thm(
    "measurable_sets_prod_hor_measurable_sets_prod",
    ``∀m0 m1. measurable_sets (prod_measure_space_hor m0 m1) =
        measurable_sets (prod_measure_space m0 m1)``,
    rw[measurable_sets_prod_measure_space,measurable_sets_prod_measure_space_hor]
);

val measure_prod_measure_space_hor = store_thm(
    "measure_prod_measure_space_hor",
    ``∀m0 m1. measure (prod_measure_space_hor m0 m1) = prod_measure_hor m0 m1``,
    rw[prod_measure_space_hor_def,measure_def]
);

(********************)
(* Monotone Classes *)
(********************)

(* Halmos 6.A, in parts *)
val sigma_algebra_monotone_class = store_thm(
    "sigma_algebra_monotone_class",
    ``∀a. sigma_algebra a ⇒ monotone_class a``,
    rw[monotone_class_def]
    >- (fs[SIGMA_ALGEBRA])
    >- (fs[SIGMA_ALGEBRA_FN])
    >- (fs[SIGMA_ALGEBRA_FN_BIGINTER])
);

val monotone_algebra_sigma_algebra = store_thm(
    "monotone_algebra_sigma_algebra",
    ``∀a. algebra a ∧ monotone_class a ⇒ sigma_algebra a``,
    rw[SIGMA_ALGEBRA_ALT] >>
    `BIGUNION (IMAGE f 𝕌(:num)) =
        BIGUNION (IMAGE (λn. BIGUNION (IMAGE f (count (SUC n)))) 𝕌(:num))` by (
        Q.ABBREV_TAC `g = (λn. BIGUNION (IMAGE f (count (SUC n))))` >>
        rw[EXTENSION,IN_BIGUNION_IMAGE] >> eq_tac >> rw[]
        >- (EXISTS_TAC ``x' : num`` >> rw[] >>
            Q.UNABBREV_TAC `g` >> rw[IN_BIGUNION_IMAGE] >>
            EXISTS_TAC ``x' : num`` >> rw[])
        >- (Q.UNABBREV_TAC `g` >> fs[IN_BIGUNION_IMAGE] >>
            EXISTS_TAC ``x'' : num`` >> rw[])) >>
    rw[] >> pop_assum kall_tac >> fs[monotone_class_def] >>
    qpat_x_assum `∀f. _` irule >> rw[]
    >- (rw[SUBSET_DEF,IN_BIGUNION_IMAGE] >> EXISTS_TAC ``x' : num`` >> rw[])
    >- (rw[FUNSET] >> irule ALGEBRA_FINITE_UNION >>
        rw[IMAGE_FINITE,SUBSET_DEF] >> fs[FUNSET])
);

(* Various Monotone class results *)

val SPACE_MONO_CLASS_GEN = store_thm(
    "SPACE_MONO_CLASS_GEN",
    ``∀sp a. space (mono_class_gen sp a) = sp``,
    rw[space_def,mono_class_gen_def]
);

val POW_MONOTONE_CLASS = store_thm(
    "POW_MONOTONE_CLASS",
    ``∀sp. monotone_class (sp,POW sp)``,
    rw[monotone_class_def,space_def,subsets_def]
    >- (fs[POW_SUBSET_CLASS])
    >- (rw[POW_DEF,SUBSET_DEF,IN_BIGUNION_IMAGE] >>
        fs[FUNSET,POW_DEF,SUBSET_DEF] >> metis_tac[])
    >- (rw[POW_DEF,SUBSET_DEF,IN_BIGINTER_IMAGE] >>
        fs[FUNSET,POW_DEF,SUBSET_DEF])
);

val MONOTONE_CLASS_MONO_CLASS_GEN = store_thm(
    "MONOTONE_CLASS_MONO_CLASS_GEN",
    ``∀sp sts. subset_class sp sts ⇒ monotone_class (mono_class_gen sp sts)``,
    rw[monotone_class_def] >> rw[mono_class_gen_def,space_def,subsets_def]
    >- (fs[subset_class_def] >> rw[] >>
        pop_assum (qspec_then `POW sp` assume_tac) >> fs[POW_MONOTONE_CLASS] >>
        fs[POW_DEF] >> pop_assum irule >> rw[SUBSET_DEF]) >>
    `f ∈ (𝕌(:num) -> P)` suffices_by (rw[] >> fs[monotone_class_def,subsets_def]) >>
    fs[FUNSET] >> rw[] >> qpat_x_assum `∀x. _ ∈ _` (qspec_then `x` assume_tac) >>
    fs[mono_class_gen_def,subsets_def]
);

val MONO_CLASS_GEN_PINCH = store_thm(
    "MONO_CLASS_GEN_PINCH",
    ``∀sp stsa stsb. stsa ⊆ stsb ∧ stsb ⊆ subsets (mono_class_gen sp stsa) ∧
        monotone_class (sp,stsb) ⇒ (stsb = subsets (mono_class_gen sp stsa))``,
    rw[SET_EQ_SUBSET] >> rw[mono_class_gen_def,subsets_def,SUBSET_DEF,IN_BIGINTER] >>
    pop_assum (qspec_then `stsb` assume_tac) >> rfs[SUBSET_DEF]
);

val MONO_CLASS_GEN_SMALLEST = store_thm(
    "MONO_CLASS_GEN_SMALLEST",
    ``∀sp stsa stsb. stsa ⊆ stsb ∧ monotone_class (sp,stsb) ⇒
        subsets (mono_class_gen sp stsa) ⊆ stsb``,
    rw[mono_class_gen_def,subsets_def,SUBSET_DEF]
);

val MONO_CLASS_GEN_SUBSET_SUBSETS = store_thm(
    "MONO_CLASS_GEN_SUBSET_SUBSETS",
    ``∀sp a. a ⊆ subsets (mono_class_gen sp a)``,
    rw[mono_class_gen_def,subsets_def,SUBSET_DEF]
);

val MONOTONE_CLASS_INCREASING_DIFF_SUFFICIENT = store_thm(
    "MONOTONE_CLASS_INCREASING_DIFF_SUFFICIENT",
    ``∀a. subset_class (space a) (subsets a) ∧
        (∀s. s ∈ subsets a ⇒ space a DIFF s ∈ subsets a) ∧
        (∀f. f ∈ (𝕌(:num) -> subsets a) ∧ (∀n. f n ⊆ f (SUC n)) ⇒
        BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a) ⇒
        monotone_class a``,
    rw[monotone_class_def] >>
    `BIGUNION (IMAGE (λu. (space a) DIFF f u) 𝕌(:num)) ∈ subsets a` by (
        qpat_x_assum `∀f. _` irule >> rw[SUBSET_IMP_DIFFS_SUBSET] >> fs[FUNSET]) >>
    qpat_x_assum `∀(s : α -> bool). _` imp_res_tac >>
    (assume_tac o ISPECL [``space a``,``𝕌(:num)``,
        ``(λu. space a DIFF f u) : num -> α -> bool``]) DIFF_BIGUNION_IMAGE >>
    rfs[FUNSET,subset_class_def,POW_DEF] >> fs[] >>
    `(λu. space a DIFF (space a DIFF f u)) = f` suffices_by (rw[] >> fs[]) >>
    `∀u. space a DIFF (space a DIFF f u) = f u` suffices_by rw[FUN_EQ_THM] >> rw[] >>
    irule DIFF_DIFF_SUBSET >> fs[]
);

(* Halmos 6.4 Lemmas *)

val ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_DIFF = store_thm(
    "ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_DIFF",
    ``∀sp sts. algebra (sp,sts) ⇒
        ({s | s ∈ subsets (mono_class_gen sp sts) ∧
        sp DIFF s ∈ subsets (mono_class_gen sp sts)} =
        subsets (mono_class_gen sp sts))``,
    rw[] >> irule MONO_CLASS_GEN_PINCH >> rw[]
    >- (fs[algebra_def,space_def,subsets_def] >>
        drule_then assume_tac MONOTONE_CLASS_MONO_CLASS_GEN >>
        rw[monotone_class_def,space_def,subsets_def]
        >- (fs[monotone_class_def] >> fs[subset_class_def] >> rw[] >>
            fs[mono_class_gen_def,space_def,subsets_def])
        >- (fs[monotone_class_def,space_def,subsets_def] >>
            qpat_x_assum `∀f. _` irule >> rw[] >> fs[FUNSET])
        >- (`sp DIFF BIGUNION (IMAGE f 𝕌(:num)) = BIGINTER (IMAGE (λu. sp DIFF f u) 𝕌(:num))` by (
                irule DIFF_BIGUNION_IMAGE >> rw[] >> fs[FUNSET,POW_DEF] >>
                fs[monotone_class_def,space_def,subsets_def] >>
                fs[mono_class_gen_def,space_def,subsets_def] >> rw[] >>
                NTAC 2 (qpat_x_assum `∀x. _` (qspec_then `x` assume_tac)) >> fs[] >>
                NTAC 2 (qpat_x_assum `∀P. _` (qspec_then `POW sp` assume_tac)) >>
                fs[POW_MONOTONE_CLASS] >> rfs[subset_class_def,SUBSET_DEF,POW_DEF] >>
                metis_tac[]) >>
            rw[] >> pop_assum kall_tac >> fs[monotone_class_def,space_def,subsets_def] >>
            qpat_x_assum `∀f. _` irule >> rw[] >> fs[FUNSET] >>
            fs[SUBSET_IMP_DIFFS_SUBSET])
        >- (fs[monotone_class_def,space_def,subsets_def] >>
            qpat_x_assum `∀f. _` irule >> rw[] >> fs[FUNSET])
        >- (`sp DIFF BIGINTER (IMAGE f 𝕌(:num)) = BIGUNION (IMAGE (λu. sp DIFF f u) 𝕌(:num))` by (
                irule DIFF_BIGINTER_IMAGE >> rw[] >> fs[FUNSET,POW_DEF] >>
                fs[monotone_class_def,space_def,subsets_def] >>
                fs[mono_class_gen_def,space_def,subsets_def] >> rw[] >>
                NTAC 2 (qpat_x_assum `∀x. _` (qspec_then `x` assume_tac)) >> fs[] >>
                NTAC 2 (qpat_x_assum `∀P. _` (qspec_then `POW sp` assume_tac)) >>
                fs[POW_MONOTONE_CLASS] >> rfs[subset_class_def,SUBSET_DEF,POW_DEF] >>
                metis_tac[]) >>
            rw[] >> pop_assum kall_tac >> fs[monotone_class_def,space_def,subsets_def] >>
            qpat_x_assum `∀f. _` irule >> rw[] >> fs[FUNSET] >>
            fs[SUBSET_IMP_DIFFS_SUBSET]))
    >- (rw[SUBSET_DEF]
        >- (rw[subsets_def,mono_class_gen_def] >> rfs[SUBSET_DEF])
        >- (rw[subsets_def,mono_class_gen_def] >>
            `sp DIFF x ∈ sts` by fs[algebra_def,space_def,subsets_def] >> fs[SUBSET_DEF]))
    >- (rw[SUBSET_DEF])
);

val ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION_MONO = store_thm(
    "ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION_MONO",
    ``∀sp sts s. algebra (sp,sts) ⇒ monotone_class (sp,
        {t | t ∈ subsets (mono_class_gen sp sts) ∧
        s ∪ t ∈ subsets (mono_class_gen sp sts)})``,
    rw[] >> fs[algebra_def,space_def,subsets_def] >>
    drule_then assume_tac MONOTONE_CLASS_MONO_CLASS_GEN >>
    rw[monotone_class_def,space_def,subsets_def]
    >- (fs[monotone_class_def] >> fs[subset_class_def] >> rw[] >>
        fs[mono_class_gen_def,space_def,subsets_def])
    >- (fs[monotone_class_def,space_def,subsets_def] >>
        qpat_x_assum `∀f. _` irule >> rw[] >> fs[FUNSET])
    >- (rw[GSYM UNION_BIGUNION_IMAGE] >> fs[monotone_class_def,space_def,subsets_def] >>
        qpat_x_assum `∀f. _` irule >> rw[] >> fs[FUNSET] >>
        `f (SUC n) ⊆ s ∪ f (SUC n)` by fs[SUBSET_UNION] >> metis_tac[SUBSET_TRANS])
    >- (fs[monotone_class_def,space_def,subsets_def] >>
        qpat_x_assum `∀f. _` irule >> rw[] >> fs[FUNSET])
    >- (rw[GSYM UNION_BIGINTER_IMAGE] >> fs[monotone_class_def,space_def,subsets_def] >>
        qpat_x_assum `∀f. _` irule >> rw[] >> fs[FUNSET] >>
        `f n ⊆ s ∪ f n` by fs[SUBSET_UNION] >> metis_tac[SUBSET_TRANS])
);

val ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION_ALG = store_thm(
    "ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION_ALG",
    ``∀sp sts s. algebra (sp,sts) ∧ s ∈ sts ⇒
        ({t | t ∈ subsets (mono_class_gen sp sts) ∧
        s ∪ t ∈ subsets (mono_class_gen sp sts)} =
        subsets (mono_class_gen sp sts))``,
    rw[] >> irule MONO_CLASS_GEN_PINCH >> rw[]
    >- (fs[ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION_MONO])
    >- (rw[SUBSET_DEF,mono_class_gen_def,subsets_def] >>
        fs[algebra_def,space_def,subsets_def])
    >- (rw[SUBSET_DEF])
);

val ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION = store_thm(
    "ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION",
    ``∀sp sts s. algebra (sp,sts) ∧ s ∈ subsets (mono_class_gen sp sts) ⇒
        ({t | t ∈ subsets (mono_class_gen sp sts) ∧
        s ∪ t ∈ subsets (mono_class_gen sp sts)} =
        subsets (mono_class_gen sp sts))``,
    rw[] >> irule MONO_CLASS_GEN_PINCH >> rw[]
    >- (fs[ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION_MONO])
    >- (rw[SUBSET_DEF]
        >- (rw[mono_class_gen_def,space_def,subsets_def] >>
            fs[SUBSET_DEF,algebra_def,space_def,subsets_def])
        >- (`x ∪ s ∈ subsets (mono_class_gen sp sts)` suffices_by fs[UNION_COMM] >>
            drule_all_then assume_tac (GSYM ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION_ALG) >>
            rfs[EXTENSION] >> metis_tac[]))
    >- (rw[SUBSET_DEF])
);

val ALGEBRA_MONO_CLASS_GEN_ALGEBRA = store_thm(
    "ALGEBRA_MONO_CLASS_GEN_ALGEBRA",
    ``∀a. algebra a ⇒ algebra (mono_class_gen (space a) (subsets a))``,
    rw[] >> rw[algebra_def]
    >- (fs[algebra_def] >> imp_res_tac MONOTONE_CLASS_MONO_CLASS_GEN >> fs[monotone_class_def]) >>
    fs[mono_class_gen_def,space_def,subsets_def] >> rw[]
    >- (fs[algebra_def,SUBSET_DEF])
    >- (`∃sp sts. a = (sp,sts)` by fs[ABS_PAIR_THM] >> fs[space_def,subsets_def] >>
        pop_assum kall_tac >>
        drule_then assume_tac (GSYM ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_DIFF) >>
        fs[EXTENSION,mono_class_gen_def,space_def,subsets_def] >>
        pop_assum (qspec_then `s` assume_tac) >> rfs[])
    >- (`∃sp sts. a = (sp,sts)` by fs[ABS_PAIR_THM] >> fs[space_def,subsets_def] >>
        pop_assum kall_tac >>
        drule_then assume_tac (GSYM ALGEBRA_MONO_CLASS_GEN_ALGEBRA_LEMMA_UNION) >>
        pop_assum (qspec_then `s` assume_tac) >>
        rfs[EXTENSION,mono_class_gen_def,space_def,subsets_def] >>
        pop_assum (qspec_then `t` assume_tac) >> rfs[])
);

(* Halmos 6.4 *)

val SIGMA_ALGEBRA_EQ_MONO_CLASS_GEN_ALGEBRA = store_thm(
    "SIGMA_ALGEBRA_EQ_MONO_CLASS_GEN_ALGEBRA",
    ``∀a. algebra a ⇒ (sigma (space a) (subsets a) = mono_class_gen (space a) (subsets a))``,
    rw[] >>
    `subsets (sigma (space a) (subsets a)) = subsets (mono_class_gen (space a) (subsets a))`
        suffices_by rw[sigma_def,mono_class_gen_def,space_def,subsets_def] >>
    rw[SET_EQ_SUBSET]
    >- (irule SIGMA_SMALLEST >> rw[MONO_CLASS_GEN_SUBSET_SUBSETS] >>
        `sigma_algebra (mono_class_gen (space a) (subsets a))`
            suffices_by rw[mono_class_gen_def,space_def,subsets_def] >>
        irule monotone_algebra_sigma_algebra >>
        rw[ALGEBRA_MONO_CLASS_GEN_ALGEBRA] >> irule MONOTONE_CLASS_MONO_CLASS_GEN >>
        fs[algebra_def])
    >- (irule MONO_CLASS_GEN_SMALLEST >> rw[SIGMA_SUBSET_SUBSETS] >>
        `monotone_class (sigma (space a) (subsets a))`
            suffices_by rw[sigma_def,space_def,subsets_def] >>
        irule sigma_algebra_monotone_class >> irule SIGMA_ALGEBRA_SIGMA >>
        fs[algebra_def])
);

(*******************)
(* (X,Σ) σ-algebra *)
(*******************)

val prod_measure_space_subset_class = store_thm(
    "prod_measure_space_subset_class",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ subset_class (m_space m0 × m_space m1)
        (subsets (sigma (m_space m0 × m_space m1)
        (prod_sets (measurable_sets m0) (measurable_sets m1))))``,
    rpt strip_tac >> fs[subset_class_def,subsets_def,sigma_def] >> rpt strip_tac >>
    pop_assum (qspec_then `POW (m_space m0 × m_space m1)` assume_tac) >>
    rfs[POW_SIGMA_ALGEBRA,prod_sets_def,POW_DEF] >>
    `{s × t | s ∈ measurable_sets m0 ∧ t ∈ measurable_sets m1} ⊆
        {s | s ⊆ m_space m0 × m_space m1}` suffices_by fs[] >>
    fs[SUBSET_DEF] >> rpt strip_tac >> imp_res_tac MEASURE_SPACE_SUBSET_MSPACE >> rfs[SUBSET_DEF]
);

val prod_sets_subset_class = store_thm(
    "prod_sets_subset_class",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ subset_class (m_space m0 × m_space m1)
        (prod_sets (measurable_sets m0) (measurable_sets m1))``,
    rpt strip_tac >> fs[subset_class_def,prod_sets_def] >> rpt strip_tac >>
    fs[SUBSET_DEF] >> rpt strip_tac >> imp_res_tac MEASURE_SPACE_SUBSET_MSPACE >> rfs[SUBSET_DEF]
);

val prod_measure_space_sigma_algebra = store_thm(
    "prod_measure_space_sigma_algebra",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ sigma_algebra
        (m_space (prod_measure_space m0 m1),
        measurable_sets (prod_measure_space m0 m1))``,
    rpt strip_tac >> imp_res_tac prod_sets_subset_class >>
    fs[prod_measure_space_def,m_space_def,measurable_sets_def,SIGMA_REDUCE] >>
    imp_res_tac SIGMA_ALGEBRA_SIGMA
);

val prod_measure_space_hor_sigma_algebra = store_thm(
    "prod_measure_space_hor_sigma_algebra",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ sigma_algebra
        (m_space (prod_measure_space_hor m0 m1),
        measurable_sets (prod_measure_space_hor m0 m1))``,
    rpt strip_tac >> imp_res_tac prod_sets_subset_class >>
    fs[prod_measure_space_hor_def,m_space_def,measurable_sets_def,SIGMA_REDUCE] >>
    imp_res_tac SIGMA_ALGEBRA_SIGMA
);

(* Some Corollaries Thereof *)

val prod_measure_prod_set = store_thm(
    "prod_measure_prod_set",
    ``∀m0 m1 A B. measure_space m0 ∧ measure_space m1 ∧
        A ∈ measurable_sets m0 ∧ B ∈ measurable_sets m1 ⇒
        (measure (prod_measure_space m0 m1) (A × B) =
        (measure m0 A) * (measure m1 B))``,
    rpt strip_tac >> fs[measure_def,prod_measure_space_def,prod_measure_def] >>
    `∀s0. PREIMAGE (λs1. (s0,s1)) (A × B) = if s0 ∈ A then B else ∅`
        by (strip_tac >> Cases_on `s0 ∈ A` >> fs[PREIMAGE_def]) >>
    fs[] >> pop_assum kall_tac >>
    `∀s0. measure m1 (if s0 ∈ A then B else ∅) = if s0 ∈ A then (measure m1 B) else 0`
        by (strip_tac >> Cases_on `s0 ∈ A` >> fs[measure_space_def,positive_def]) >>
    fs[] >> pop_assum kall_tac >>
    `(λs0. Normal (if s0 ∈ A then measure m1 B else 0)) =
        (λx. Normal (measure m1 B) * indicator_fn A x)` by (
        fs[FUN_EQ_THM] >> strip_tac >> Cases_on `x ∈ A` >>
        fs[indicator_fn_def,mul_rzero,mul_rone,N0_EQ_0]) >>
    fs[] >> pop_assum kall_tac >>
    fs[integral_cmul_indicator,real_normal,REAL_MUL_COMM]
);

val prod_measure_hor_prod_set = store_thm(
    "prod_measure_hor_prod_set",
    ``∀m0 m1 A B. measure_space m0 ∧ measure_space m1 ∧
        A ∈ measurable_sets m0 ∧ B ∈ measurable_sets m1 ⇒
        (measure (prod_measure_space_hor m0 m1) (A × B) =
        (measure m0 A) * (measure m1 B))``,
    rw[] >> fs[measure_def,prod_measure_space_hor_def,prod_measure_hor_def] >>
    `∀s1. PREIMAGE (λs0. (s0,s1)) (A × B) = if s1 ∈ B then A else ∅`
        by (strip_tac >> Cases_on `s1 ∈ B` >> fs[PREIMAGE_def]) >>
    fs[] >> pop_assum kall_tac >>
    `∀s1. measure m0 (if s1 ∈ B then A else ∅) = if s1 ∈ B then (measure m0 A) else 0`
        by (strip_tac >> Cases_on `s1 ∈ B` >> fs[measure_space_def,positive_def]) >>
    fs[] >> pop_assum kall_tac >>
    `(λs1. Normal (if s1 ∈ B then measure m0 A else 0)) =
        (λx. Normal (measure m0 A) * indicator_fn B x)` by (
        fs[FUN_EQ_THM] >> strip_tac >> Cases_on `x ∈ B` >>
        fs[indicator_fn_def,mul_rzero,mul_rone,N0_EQ_0]) >>
    fs[] >> pop_assum kall_tac >>
    fs[integral_cmul_indicator,real_normal,REAL_MUL_COMM]
);

val prod_measure_m_space_measure = store_thm(
    "prod_measure_m_space_measure",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        (measure (prod_measure_space m0 m1) (m_space (prod_measure_space m0 m1)) =
        (measure m0 (m_space m0)) * (measure m1 (m_space m1)))``,
    rpt strip_tac >>
    `(m_space m0) ∈ measurable_sets m0` by fs[MEASURE_SPACE_MSPACE_MEASURABLE] >>
    `(m_space m1) ∈ measurable_sets m1` by fs[MEASURE_SPACE_MSPACE_MEASURABLE] >>
    imp_res_tac prod_measure_prod_set >>
    fs[prod_measure_space_def,m_space_def,measurable_sets_def,measure_def]
);

val prod_measure_hor_m_space_measure = store_thm(
    "prod_measure_hor_m_space_measure",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        (measure (prod_measure_space_hor m0 m1) (m_space (prod_measure_space_hor m0 m1)) =
        (measure m0 (m_space m0)) * (measure m1 (m_space m1)))``,
    rw[] >>
    `(m_space m0) ∈ measurable_sets m0` by fs[MEASURE_SPACE_MSPACE_MEASURABLE] >>
    `(m_space m1) ∈ measurable_sets m1` by fs[MEASURE_SPACE_MSPACE_MEASURABLE] >>
    imp_res_tac prod_measure_hor_prod_set >>
    fs[prod_measure_space_hor_def,m_space_def,measurable_sets_def,measure_def]
);

val prod_measure_space_empty = store_thm(
    "prod_measure_space_empty",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        ∅ ∈ measurable_sets (prod_measure_space m0 m1)``,
    rw[] >> imp_res_tac prod_measure_space_sigma_algebra >>
    fs[sigma_algebra_def,algebra_def,space_def,subsets_def]
);

val prod_measure_space_hor_empty = store_thm(
    "prod_measure_space_hor_empty",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        ∅ ∈ measurable_sets (prod_measure_space_hor m0 m1)``,
    rw[measurable_sets_prod_hor_measurable_sets_prod,prod_measure_space_empty]
);

val prod_measure_space_diff = store_thm(
    "prod_measure_space_diff",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        m_space (prod_measure_space m0 m1) DIFF s ∈ measurable_sets (prod_measure_space m0 m1)``,
    rw[] >> imp_res_tac prod_measure_space_sigma_algebra >>
    fs[sigma_algebra_def,algebra_def,space_def,subsets_def]
);

val prod_measure_space_hor_diff = store_thm(
    "prod_measure_space_hor_diff",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space_hor m0 m1) ⇒
        m_space (prod_measure_space_hor m0 m1) DIFF s ∈
        measurable_sets (prod_measure_space_hor m0 m1)``,
    rw[m_space_prod_hor_m_space_prod,measurable_sets_prod_hor_measurable_sets_prod,
        prod_measure_space_diff]
);

val prod_measure_space_union = store_thm(
    "prod_measure_space_union",
    ``∀m0 m1 s t. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ∧
        t ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        s ∪ t ∈ measurable_sets (prod_measure_space m0 m1)``,
    rw[] >> imp_res_tac prod_measure_space_sigma_algebra >>
    fs[sigma_algebra_def,algebra_def,space_def,subsets_def]
);

val prod_measure_space_hor_union = store_thm(
    "prod_measure_space_hor_union",
    ``∀m0 m1 s t. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space_hor m0 m1) ∧
        t ∈ measurable_sets (prod_measure_space_hor m0 m1) ⇒
        s ∪ t ∈ measurable_sets (prod_measure_space_hor m0 m1)``,
    rw[m_space_prod_hor_m_space_prod,measurable_sets_prod_hor_measurable_sets_prod,
        prod_measure_space_union]
);

val prod_measure_space_bigunion = store_thm(
    "prod_measure_space_bigunion",
    ``∀m0 m1 c. measure_space m0 ∧ measure_space m1 ∧
        countable c ∧ c ⊆ measurable_sets (prod_measure_space m0 m1) ⇒
        BIGUNION c ∈ measurable_sets (prod_measure_space m0 m1)``,
    rw[] >> imp_res_tac prod_measure_space_sigma_algebra >>
    fs[sigma_algebra_def,algebra_def,space_def,subsets_def]
);

val prod_measure_space_hor_bigunion = store_thm(
    "prod_measure_space_hor_bigunion",
    ``∀m0 m1 c. measure_space m0 ∧ measure_space m1 ∧
        countable c ∧ c ⊆ measurable_sets (prod_measure_space_hor m0 m1) ⇒
        BIGUNION c ∈ measurable_sets (prod_measure_space_hor m0 m1)``,
    rw[m_space_prod_hor_m_space_prod,measurable_sets_prod_hor_measurable_sets_prod,
        prod_measure_space_bigunion]
);

(**********)
(* Slices *)
(**********)

val x_slice_rect = store_thm(
    "x_slice_rect",
    ``∀x s t. x_slice x (s × t) = if x ∈ s then t else ∅``,
    rw[] >> fs[x_slice_def,PREIMAGE_def]
);

val y_slice_rect = store_thm(
    "y_slice_rect",
    ``∀y s t. y_slice y (s × t) = if y ∈ t then s else ∅``,
    rw[] >> fs[y_slice_def,PREIMAGE_def]
);

val x_slice_diff = store_thm(
    "x_slice_diff",
    ``∀x s t. x_slice x (s DIFF t) = (x_slice x s) DIFF (x_slice x t)``,
    rpt strip_tac >> fs[x_slice_def,PREIMAGE_def,DIFF_DEF,EXTENSION]
);

val y_slice_diff = store_thm(
    "y_slice_diff",
    ``∀y s t. y_slice y (s DIFF t) = (y_slice y s) DIFF (y_slice y t)``,
    rpt strip_tac >> fs[y_slice_def,PREIMAGE_def,DIFF_DEF,EXTENSION]
);

val x_slice_union = store_thm(
    "x_slice_union",
    ``∀x s t. x_slice x (s ∪ t) = (x_slice x s) ∪ (x_slice x t)``,
    rpt strip_tac >> fs[x_slice_def,PREIMAGE_def,UNION_DEF,EXTENSION]
);

val y_slice_union = store_thm(
    "y_slice_union",
    ``∀y s t. y_slice y (s ∪ t) = (y_slice y s) ∪ (y_slice y t)``,
    rpt strip_tac >> fs[y_slice_def,PREIMAGE_def,UNION_DEF,EXTENSION]
);

val x_slice_inter = store_thm(
    "x_slice_inter",
    ``∀x s t. x_slice x (s ∩ t) = (x_slice x s) ∩ (x_slice x t)``,
    rpt strip_tac >> fs[x_slice_def,PREIMAGE_def,INTER_DEF,EXTENSION]
);

val y_slice_inter = store_thm(
    "y_slice_inter",
    ``∀y s t. y_slice y (s ∩ t) = (y_slice y s) ∩ (y_slice y t)``,
    rpt strip_tac >> fs[y_slice_def,PREIMAGE_def,INTER_DEF,EXTENSION]
);

val x_slice_bigunion = store_thm(
    "x_slice_bigunion",
    ``∀x c. x_slice x (BIGUNION c) = BIGUNION (IMAGE (λs. x_slice x s) c)``,
    rpt strip_tac >> fs[x_slice_def,PREIMAGE_def,BIGUNION,IMAGE_DEF,EXTENSION] >>
    rpt strip_tac >> eq_tac >> rpt strip_tac >> fs[]
    >- (EXISTS_TAC ``{s1 | (x,s1) ∈ (s: α # β -> bool)}`` >> fs[] >>
        EXISTS_TAC ``s: α # β -> bool`` >> fs[])
    >- (EXISTS_TAC ``s': α # β -> bool`` >> fs[])
);

val y_slice_bigunion = store_thm(
    "y_slice_bigunion",
    ``∀y c. y_slice y (BIGUNION c) = BIGUNION (IMAGE (λs. y_slice y s) c)``,
    rpt strip_tac >> fs[y_slice_def,PREIMAGE_def,BIGUNION,IMAGE_DEF,EXTENSION] >>
    rpt strip_tac >> eq_tac >> rpt strip_tac >> fs[]
    >- (EXISTS_TAC ``{s0 | (s0,y) ∈ (s: β # α -> bool)}`` >> fs[] >>
        EXISTS_TAC ``s: β # α -> bool`` >> fs[])
    >- (EXISTS_TAC ``s': β # α -> bool`` >> fs[])
);

val x_sliceable_sigma_algebra = store_thm(
    "x_sliceable_sigma_algebra",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        sigma_algebra (m_space m0 × m_space m1,x_sliceable_sets m0 m1)``,
    rpt strip_tac >> fs[x_sliceable_sets_def] >>
    `sigma_algebra (m_space m0 × m_space m1, measurable_sets (prod_measure_space m0 m1))` by (
        imp_res_tac prod_measure_space_sigma_algebra >> fs[prod_measure_space_def,m_space_def]) >>
    fs[sigma_algebra_def,subsets_def] >> rpt strip_tac >> fs[]
    >- (fs[algebra_def,subsets_def,space_def] >> rpt strip_tac >> fs[]
        >- (fs[subset_class_def] >> rpt strip_tac >> fs[])
        >- (fs[x_slice_def,PREIMAGE_def,MEASURE_SPACE_EMPTY_MEASURABLE])
        >- (fs[x_slice_diff] >> pop_assum (qspec_then `s0` assume_tac) >>
            fs[x_slice_def,PREIMAGE_def] >> Cases_on `s0 ∈ m_space m0` >> fs[]
            >- (imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >>
                fs[measure_space_def,sigma_algebra_def,algebra_def,space_def,subsets_def])
            >- (fs[MEASURE_SPACE_EMPTY_MEASURABLE]))
        >- (fs[x_slice_union] >> NTAC 2 (qpat_x_assum `∀s0. _` (qspec_then `s0` assume_tac)) >>
            fs[measure_space_def,sigma_algebra_def,algebra_def,space_def,subsets_def]))
    >- (qpat_x_assum `∀c. _` (qspec_then `c` assume_tac) >> rfs[SUBSET_DEF])
    >- (fs[x_slice_bigunion] >>
        `countable (IMAGE (λs. x_slice s0 s) c)` by fs[image_countable] >>
        `IMAGE (λs. x_slice s0 s) c ⊆ measurable_sets m1` by (fs[SUBSET_DEF] >>
            rpt strip_tac >> RES_TAC >> fs[]) >>
        fs[measure_space_def,sigma_algebra_def,algebra_def,space_def,subsets_def])
);

val y_sliceable_sigma_algebra = store_thm(
    "y_sliceable_sigma_algebra",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        sigma_algebra (m_space m0 × m_space m1,y_sliceable_sets m0 m1)``,
    rpt strip_tac >> fs[y_sliceable_sets_def] >>
    `sigma_algebra (m_space m0 × m_space m1, measurable_sets (prod_measure_space m0 m1))` by (
        imp_res_tac prod_measure_space_sigma_algebra >> fs[prod_measure_space_def,m_space_def]) >>
    fs[sigma_algebra_def,subsets_def] >> rpt strip_tac >> fs[]
    >- (fs[algebra_def,subsets_def,space_def] >> rpt strip_tac >> fs[]
        >- (fs[subset_class_def] >> rpt strip_tac >> fs[])
        >- (fs[y_slice_def,PREIMAGE_def,MEASURE_SPACE_EMPTY_MEASURABLE])
        >- (fs[y_slice_diff] >> pop_assum (qspec_then `s1` assume_tac) >>
            fs[y_slice_def,PREIMAGE_def] >> Cases_on `s1 ∈ m_space m1` >> fs[]
            >- (imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >>
                fs[measure_space_def,sigma_algebra_def,algebra_def,space_def,subsets_def])
            >- (fs[MEASURE_SPACE_EMPTY_MEASURABLE]))
        >- (fs[y_slice_union] >> NTAC 2 (qpat_x_assum `∀s1. _` (qspec_then `s1` assume_tac)) >>
            fs[measure_space_def,sigma_algebra_def,algebra_def,space_def,subsets_def]))
    >- (qpat_x_assum `∀c. _` (qspec_then `c` assume_tac) >> rfs[SUBSET_DEF])
    >- (fs[y_slice_bigunion] >>
        `countable (IMAGE (λs. y_slice s1 s) c)` by fs[image_countable] >>
        `IMAGE (λs. y_slice s1 s) c ⊆ measurable_sets m0` by (fs[SUBSET_DEF] >>
            rpt strip_tac >> RES_TAC >> fs[]) >>
        fs[measure_space_def,sigma_algebra_def,algebra_def,space_def,subsets_def])
);

val direct_products_x_sliceable = store_thm(
    "direct_products_x_sliceable",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        prod_sets (measurable_sets m0) (measurable_sets m1) ⊆ x_sliceable_sets m0 m1``,
    rpt strip_tac >> fs[SUBSET_DEF,x_sliceable_sets_def] >> rpt strip_tac >>
    fs[prod_measure_space_def,prod_sets_def,measurable_sets_def,sigma_def,subsets_def]
    >- (rpt strip_tac >> fs[SUBSET_DEF] >>
        qpat_x_assum `∀x. _` (qspec_then `x` assume_tac) >>
        `∃s t. (x = s × t) ∧ s ∈ measurable_sets m0 ∧ t ∈ measurable_sets m1`
            suffices_by (strip_tac >> RES_TAC >> rfs[]) >>
        map_every exists_tac [``s: α -> bool``, ``t: β -> bool``] >> fs[])
    >- (Cases_on `s0 ∈ s` >> fs[x_slice_def,PREIMAGE_def,MEASURE_SPACE_EMPTY_MEASURABLE])
);

val direct_products_y_sliceable = store_thm(
    "direct_products_y_sliceable",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        prod_sets (measurable_sets m0) (measurable_sets m1) ⊆ y_sliceable_sets m0 m1``,
    rpt strip_tac >> fs[SUBSET_DEF,y_sliceable_sets_def] >> rpt strip_tac >>
    fs[prod_measure_space_def,prod_sets_def,measurable_sets_def,sigma_def,subsets_def]
    >- (rpt strip_tac >> fs[SUBSET_DEF] >>
        qpat_x_assum `∀x. _` (qspec_then `x` assume_tac) >>
        `∃s t. (x = s × t) ∧ s ∈ measurable_sets m0 ∧ t ∈ measurable_sets m1`
            suffices_by (strip_tac >> RES_TAC >> rfs[]) >>
        map_every exists_tac [``s: α -> bool``, ``t: β -> bool``] >> fs[])
    >- (Cases_on `s1 ∈ t` >> fs[y_slice_def,PREIMAGE_def,MEASURE_SPACE_EMPTY_MEASURABLE])
);

val product_measure_space_x_slice_measurable = store_thm(
    "product_measure_space_x_slice_measurable",
    ``∀m0 m1 s s0. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        x_slice s0 s ∈ measurable_sets m1``,
    rpt strip_tac >> fs[measurable_sets_def,prod_measure_space_def,sigma_def,subsets_def] >>
    imp_res_tac direct_products_x_sliceable >> imp_res_tac x_sliceable_sigma_algebra >>
    RES_TAC >> fs[x_sliceable_sets_def]
);

val product_measure_space_y_slice_measurable = store_thm(
    "product_measure_space_y_slice_measurable",
    ``∀m0 m1 s s1. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        y_slice s1 s ∈ measurable_sets m0``,
    rpt strip_tac >> fs[measurable_sets_def,prod_measure_space_def,sigma_def,subsets_def] >>
    imp_res_tac direct_products_y_sliceable >> imp_res_tac y_sliceable_sigma_algebra >>
    RES_TAC >> fs[y_sliceable_sets_def]
);

(*******************)
(* positivity of μ *)
(*******************)

val product_measure_space_bounded = store_thm(
    "product_measure_space_bounded",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧ s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (0 ≤ measure (prod_measure_space m0 m1) s) ∧ (measure (prod_measure_space m0 m1) s ≤
        measure (prod_measure_space m0 m1) (m_space (prod_measure_space m0 m1)))``,
    NTAC 4 strip_tac >> fs[prod_measure_m_space_measure] >>
    `∀x. x ∈ m_space m0 ⇒ (PREIMAGE (λy. (x,y)) s) ∈ measurable_sets m1` by (
        rpt strip_tac >>
        (qspecl_then [`m0`,`m1`,`s`,`x`] assume_tac) product_measure_space_x_slice_measurable >>
        rfs[x_slice_def]) >>
    fs[prod_measure_space_def,m_space_def,measurable_sets_def,measure_def,prod_measure_def] >>
    `(∀t. t ∈ m_space m0 ⇒ 0 ≤ Normal (measure m1 (PREIMAGE (λs1. (t,s1)) s)))` by (
        rpt strip_tac >> RES_TAC >> imp_res_tac MEASURE_SPACE_POSITIVE >>
        fs[positive_def] >> RES_TAC >> fs[GSYM N0_EQ_0,extreal_le_def]) >>
    `(∀t. t ∈ m_space m0 ⇒ Normal (measure m1 (PREIMAGE (λs1. (t,s1)) s)) ≤
        Normal (measure m1 (m_space m1)))` by (rpt strip_tac >> RES_TAC >>
        fs[extreal_le_def,MEASURE_MAXIMUM]) >>
    (qspecl_then [`m0`,`(λx. 0)`,
        `(λs0. Normal (measure m1 (PREIMAGE (λs1. (s0,s1)) s)))`]
        assume_tac) integral_mono >>
    (qspecl_then [`m0`,`(λs0. Normal (measure m1 (PREIMAGE (λs1. (s0,s1)) s)))`,
        `(λs0. Normal (measure m1 (m_space m1)))`] assume_tac) integral_mono >>
    rfs[integral_zero,integral_const,GSYM N0_EQ_0] >>
    Cases_on `integral m0 (λs0. Normal (measure m1 (PREIMAGE (λs1. (s0,s1)) s)))` >>
    fs[extreal_le_def,real_normal] >> fs[REAL_MUL_COMM]
);

val product_measure_space_hor_bounded = store_thm(
    "product_measure_space_hor_bounded",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space_hor m0 m1) ⇒
        (0 ≤ measure (prod_measure_space_hor m0 m1) s) ∧
        (measure (prod_measure_space_hor m0 m1) s ≤
        measure (prod_measure_space_hor m0 m1) (m_space (prod_measure_space_hor m0 m1)))``,
    NTAC 4 strip_tac >> fs[prod_measure_hor_m_space_measure] >>
    `∀y. y ∈ m_space m1 ⇒ (PREIMAGE (λx. (x,y)) s) ∈ measurable_sets m0` by (
        rw[] >> fs[measurable_sets_prod_hor_measurable_sets_prod] >>
        drule_all_then assume_tac product_measure_space_y_slice_measurable >>
        rfs[y_slice_def]) >>
    fs[prod_measure_space_hor_def,m_space_def,measurable_sets_def,measure_def,prod_measure_hor_def] >>
    `(∀t. t ∈ m_space m1 ⇒ 0 ≤ Normal (measure m0 (PREIMAGE (λs0. (s0,t)) s)))` by (
        rw[] >> RES_TAC >> imp_res_tac MEASURE_SPACE_POSITIVE >>
        fs[positive_def] >> RES_TAC >> fs[GSYM N0_EQ_0,extreal_le_def]) >>
    `(∀t. t ∈ m_space m1 ⇒ Normal (measure m0 (PREIMAGE (λs0. (s0,t)) s)) ≤
        Normal (measure m0 (m_space m0)))` by (rw[] >> RES_TAC >>
        fs[extreal_le_def,MEASURE_MAXIMUM]) >>
    (qspecl_then [`m1`,`(λy. 0)`,
        `(λs1. Normal (measure m0 (PREIMAGE (λs0. (s0,s1)) s)))`]
        assume_tac) (INST_TYPE [alpha |-> ``:β``] integral_mono) >>
    (qspecl_then [`m1`,`(λs1. Normal (measure m0 (PREIMAGE (λs0. (s0,s1)) s)))`,
        `(λs1. Normal (measure m0 (m_space m0)))`] assume_tac)
        (INST_TYPE [alpha |-> ``:β``] integral_mono) >>
    rfs[integral_zero,integral_const,GSYM N0_EQ_0] >>
    Cases_on `integral m1 (λs1. Normal (measure m0 (PREIMAGE (λs0. (s0,s1)) s)))` >>
    fs[extreal_le_def,real_normal] >> fs[REAL_MUL_COMM]
);

val product_measure_space_normal_measure = store_thm(
    "product_measure_space_normal_measure",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (Normal (measure (prod_measure_space m0 m1) s) =
        integral m0 (λs0. Normal (measure m1 (PREIMAGE (λs1. (s0,s1)) s))))``,
    rw[] >> `∀x. x ∈ m_space m0 ⇒ (PREIMAGE (λy. (x,y)) s) ∈ measurable_sets m1` by (
        rpt strip_tac >>
        (qspecl_then [`m0`,`m1`,`s`,`x`] assume_tac) product_measure_space_x_slice_measurable >>
        rfs[x_slice_def]) >>
    fs[prod_measure_space_def,m_space_def,measurable_sets_def,measure_def,prod_measure_def] >>
    `(∀t. t ∈ m_space m0 ⇒ 0 ≤ Normal (measure m1 (PREIMAGE (λs1. (t,s1)) s)))` by (
        rpt strip_tac >> RES_TAC >> imp_res_tac MEASURE_SPACE_POSITIVE >>
        fs[positive_def] >> RES_TAC >> fs[GSYM N0_EQ_0,extreal_le_def]) >>
    `(∀t. t ∈ m_space m0 ⇒ Normal (measure m1 (PREIMAGE (λs1. (t,s1)) s)) ≤
        Normal (measure m1 (m_space m1)))` by (rpt strip_tac >> RES_TAC >>
        fs[extreal_le_def,MEASURE_MAXIMUM]) >>
    (qspecl_then [`m0`,`(λx. 0)`,
        `(λs0. Normal (measure m1 (PREIMAGE (λs1. (s0,s1)) s)))`]
        assume_tac) integral_mono >>
    (qspecl_then [`m0`,`(λs0. Normal (measure m1 (PREIMAGE (λs1. (s0,s1)) s)))`,
        `(λs0. Normal (measure m1 (m_space m1)))`] assume_tac) integral_mono >>
    rfs[integral_zero,integral_const,GSYM N0_EQ_0] >>
    Q.ABBREV_TAC `mnus = integral m0 (λs0. Normal (measure m1 (PREIMAGE (λs1. (s0,s1)) s)))` >>
    Cases_on `mnus = PosInf` >> Cases_on `mnus = NegInf` >> fs[extreal_le_def] >>
    fs[normal_real]
);

val product_measure_space_hor_normal_measure = store_thm(
    "product_measure_space_hor_normal_measure",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space_hor m0 m1) ⇒
        (Normal (measure (prod_measure_space_hor m0 m1) s) =
        integral m1 (λs1. Normal (measure m0 (PREIMAGE (λs0. (s0,s1)) s))))``,
    rw[] >> `∀y. y ∈ m_space m1 ⇒ (PREIMAGE (λx. (x,y)) s) ∈ measurable_sets m0` by (
        rw[] >> fs[measurable_sets_prod_hor_measurable_sets_prod] >>
        drule_all_then assume_tac product_measure_space_y_slice_measurable >>
        rfs[y_slice_def]) >>
    fs[prod_measure_space_hor_def,m_space_def,measurable_sets_def,measure_def,prod_measure_hor_def] >>
    `(∀t. t ∈ m_space m1 ⇒ 0 ≤ Normal (measure m0 (PREIMAGE (λs0. (s0,t)) s)))` by (
        rw[] >> RES_TAC >> imp_res_tac MEASURE_SPACE_POSITIVE >>
        fs[positive_def] >> RES_TAC >> fs[GSYM N0_EQ_0,extreal_le_def]) >>
    `(∀t. t ∈ m_space m1 ⇒ Normal (measure m0 (PREIMAGE (λs0. (s0,t)) s)) ≤
        Normal (measure m0 (m_space m0)))` by (rw[] >> RES_TAC >>
        fs[extreal_le_def,MEASURE_MAXIMUM]) >>
    (qspecl_then [`m1`,`(λy. 0)`,
        `(λs1. Normal (measure m0 (PREIMAGE (λs0. (s0,s1)) s)))`]
        assume_tac) (INST_TYPE [alpha |-> ``:β``] integral_mono) >>
    (qspecl_then [`m1`,`(λs1. Normal (measure m0 (PREIMAGE (λs0. (s0,s1)) s)))`,
        `(λs1. Normal (measure m0 (m_space m0)))`] assume_tac)
        (INST_TYPE [alpha |-> ``:β``] integral_mono) >>
    rfs[integral_zero,integral_const,GSYM N0_EQ_0] >>
    Q.ABBREV_TAC `mnus = integral m1 (λs1. Normal (measure m0 (PREIMAGE (λs0. (s0,s1)) s)))` >>
    Cases_on `mnus = PosInf` >> Cases_on `mnus = NegInf` >> fs[extreal_le_def] >>
    fs[normal_real]
);

val product_measure_space_positive = store_thm(
    "product_measure_space_positive",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ positive (prod_measure_space m0 m1)``,
    rpt strip_tac >> fs[positive_def] >> rw[]
    >- (fs[prod_measure_space_def,prod_measure_def,measure_def] >>
        fs[PREIMAGE_def,integral_const,real_normal,measure_space_def,positive_def])
    >- (imp_res_tac product_measure_space_bounded)
);

val product_measure_space_hor_positive = store_thm(
    "product_measure_space_hor_positive",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ positive (prod_measure_space_hor m0 m1)``,
    rw[] >> fs[positive_def] >> rw[]
    >- (fs[prod_measure_space_hor_def,prod_measure_hor_def,measure_def] >>
        fs[PREIMAGE_def,integral_const,real_normal,measure_space_def,positive_def])
    >- (imp_res_tac product_measure_space_hor_bounded)
);

(***************************)
(* Slice Measure Functions *)
(***************************)

val x_slice_fun_measurable_sets_empty = store_thm(
    "x_slice_fun_measurable_sets_empty",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        x_slice_fun m1 ∅ ∈ measurable (m_space m0,measurable_sets m0) Borel``,
    rw[] >> `x_slice_fun m1 ∅ = (λs0. 0)` by (rw[FUN_EQ_THM] >>
        fs[x_slice_fun_def,x_slice_def,PREIMAGE_def,MEASURE_EMPTY,N0_EQ_0]) >>
    fs[] >> irule IN_MEASURABLE_BOREL_CONST_ALT >> fs[measure_space_def]
);

val y_slice_fun_measurable_sets_empty = store_thm(
    "y_slice_fun_measurable_sets_empty",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        y_slice_fun m0 ∅ ∈ measurable (m_space m1,measurable_sets m1) Borel``,
    rw[] >> `y_slice_fun m0 ∅ = (λs1. 0)` by (rw[FUN_EQ_THM] >>
        fs[y_slice_fun_def,y_slice_def,PREIMAGE_def,MEASURE_EMPTY,N0_EQ_0]) >>
    fs[] >> irule IN_MEASURABLE_BOREL_CONST_ALT >> fs[measure_space_def]
);

val direct_products_x_slice_fun_measurable = store_thm(
    "direct_products_x_slice_fun_measurable",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        prod_sets (measurable_sets m0) (measurable_sets m1) ⊆ x_slice_fun_measurable_sets m0 m1``,
    rw[] >> fs[SUBSET_DEF,x_slice_fun_measurable_sets_def] >> rw[] >>
    fs[prod_measure_space_def,prod_sets_def,measurable_sets_def,sigma_def,subsets_def]
    >- (rw[SUBSET_DEF] >>
        qpat_x_assum `∀x. _` (qspec_then `s × t` assume_tac) >> pop_assum irule >>
        map_every exists_tac [``s: α -> bool``, ``t: β -> bool``] >> fs[])
    >- (rw[IN_MEASURABLE_BOREL_ALT1]
        >- (fs[measure_space_def])
        >- (rw[FUNSET])
        >- (fs[x_slice_fun_def,subsets_def,space_def,x_slice_rect] >>
            (qspecl_then [`c`,`0`,`Normal (measure m1 (t : β -> bool))`] assume_tac)
                interval_3_right_closed_total >> fs[]
            >- (`{x | c ≤ Normal (measure m1 (if x ∈ s then t else ∅))} = 𝕌(:α)` by (
                    rw[EXTENSION] >> Cases_on `x ∈ s` >> fs[]
                    >- (imp_res_tac MEASURE_POSITIVE >> fs[GSYM extreal_le_def,N0_EQ_0] >>
                        imp_res_tac le_trans)
                    >- (fs[MEASURE_EMPTY,N0_EQ_0])) >>
                fs[MEASURE_SPACE_MSPACE_MEASURABLE])
            >- (`{x | c ≤ Normal (measure m1 (if x ∈ s then t else ∅))} = s` by (
                    rw[EXTENSION] >> Cases_on `x ∈ s` >>
                    fs[extreal_lt_def,MEASURE_EMPTY,N0_EQ_0]) >>
                imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >> fs[MEASURE_SPACE_INTER])
            >- (`{x | c ≤ Normal (measure m1 (if x ∈ s then t else ∅))} = ∅` by (
                    rw[EXTENSION] >> Cases_on `x ∈ s` >> fs[GSYM extreal_lt_def] >>
                    fs[MEASURE_EMPTY,N0_EQ_0] >> imp_res_tac MEASURE_POSITIVE >>
                    fs[GSYM extreal_le_def,N0_EQ_0] >> imp_res_tac let_trans) >>
                fs[MEASURE_SPACE_EMPTY_MEASURABLE])))
);

val direct_products_y_slice_fun_measurable = store_thm(
    "direct_products_y_slice_fun_measurable",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        prod_sets (measurable_sets m0) (measurable_sets m1) ⊆ y_slice_fun_measurable_sets m0 m1``,
    rw[] >> fs[SUBSET_DEF,y_slice_fun_measurable_sets_def] >> rw[] >>
    fs[prod_measure_space_def,prod_sets_def,measurable_sets_def,sigma_def,subsets_def]
    >- (rw[SUBSET_DEF] >>
        qpat_x_assum `∀x. _` (qspec_then `s × t` assume_tac) >> pop_assum irule >>
        map_every exists_tac [``s: α -> bool``, ``t: β -> bool``] >> fs[])
    >- (rw[IN_MEASURABLE_BOREL_ALT1]
        >- (fs[measure_space_def])
        >- (rw[FUNSET])
        >- (fs[y_slice_fun_def,subsets_def,space_def,y_slice_rect] >>
            (qspecl_then [`c`,`0`,`Normal (measure m0 (s : α -> bool))`] assume_tac)
                interval_3_right_closed_total >> fs[]
            >- (`{x | c ≤ Normal (measure m0 (if x ∈ t then s else ∅))} = 𝕌(:β)` by (
                    rw[EXTENSION] >> Cases_on `x ∈ t` >> fs[]
                    >- (imp_res_tac MEASURE_POSITIVE >> fs[GSYM extreal_le_def,N0_EQ_0] >>
                        imp_res_tac le_trans)
                    >- (fs[MEASURE_EMPTY,N0_EQ_0])) >>
                fs[MEASURE_SPACE_MSPACE_MEASURABLE])
            >- (`{x | c ≤ Normal (measure m0 (if x ∈ t then s else ∅))} = t` by (
                    rw[EXTENSION] >> Cases_on `x ∈ t` >>
                    fs[extreal_lt_def,MEASURE_EMPTY,N0_EQ_0]) >>
                imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >> fs[MEASURE_SPACE_INTER])
            >- (`{x | c ≤ Normal (measure m0 (if x ∈ t then s else ∅))} = ∅` by (
                    rw[EXTENSION] >> Cases_on `x ∈ t` >> fs[GSYM extreal_lt_def] >>
                    fs[MEASURE_EMPTY,N0_EQ_0] >> imp_res_tac MEASURE_POSITIVE >>
                    fs[GSYM extreal_le_def,N0_EQ_0] >> imp_res_tac let_trans) >>
                fs[MEASURE_SPACE_EMPTY_MEASURABLE])))
);

val x_slice_fun_diff = store_thm(
    "x_slice_fun_diff",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (x_slice_fun m1 (m_space (prod_measure_space m0 m1) DIFF s) =
        (λx. (Normal (measure m1 (m_space m1)) - x_slice_fun m1 s x) *
        indicator_fn (m_space m0) x))``,
    rw[FUN_EQ_THM,x_slice_fun_def,extreal_sub_def] >>
    rw[m_space_prod_measure_space,x_slice_diff,x_slice_rect,indicator_fn_def]
    >- (rw[GSYM N1_EQ_1,extreal_mul_def] >> irule MEASURE_COMPL >> rw[] >>
        irule product_measure_space_x_slice_measurable >> rw[] >> metis_tac[])
    >- (rw[GSYM N0_EQ_0,extreal_mul_def,MEASURE_EMPTY])
);

val y_slice_fun_diff = store_thm(
    "y_slice_fun_diff",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (y_slice_fun m0 (m_space (prod_measure_space m0 m1) DIFF s) =
        (λy. (Normal (measure m0 (m_space m0)) - y_slice_fun m0 s y) *
        indicator_fn (m_space m1) y))``,
    rw[FUN_EQ_THM,y_slice_fun_def,extreal_sub_def] >>
    rw[m_space_prod_measure_space,y_slice_diff,y_slice_rect,indicator_fn_def]
    >- (rw[GSYM N1_EQ_1,extreal_mul_def] >> irule MEASURE_COMPL >> rw[] >>
        irule product_measure_space_y_slice_measurable >> rw[] >> metis_tac[])
    >- (rw[GSYM N0_EQ_0,extreal_mul_def,MEASURE_EMPTY])
);

val x_slice_fun_measurable_sets_diff = store_thm(
    "x_slice_fun_measurable_sets_diff",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ x_slice_fun_measurable_sets m0 m1 ⇒
        x_slice_fun m1 (m_space (prod_measure_space m0 m1) DIFF s) ∈
        measurable (m_space m0,measurable_sets m0) Borel``,
    rw[] >> fs[x_slice_fun_measurable_sets_def] >>
    drule_all_then assume_tac x_slice_fun_diff >> rw[] >> pop_assum kall_tac >>
    `sigma_algebra (m_space m0,measurable_sets m0)` by fs[measure_space_def] >>
    Q.ABBREV_TAC `xsls = x_slice_fun m1 s` >>
    Q.ABBREV_TAC `ma0 = (m_space m0,measurable_sets m0)` >>
    `(λx. Normal (measure m1 (m_space m1))) ∈ measurable ma0 Borel`
        by fs[IN_MEASURABLE_BOREL_CONST_ALT] >>
    Q.ABBREV_TAC `Nmsp1 = (λx. Normal (measure m1 (m_space m1)))` >>
    `(λx. Nmsp1 x − xsls x) ∈ measurable ma0 Borel` by fs[IN_MEASURABLE_BOREL_SUB_ALT] >>
    Q.ABBREV_TAC `sp_m_sl = (λx. Nmsp1 x − xsls x)` >>
    (qspecl_then [`ma0`,`sp_m_sl`,`m_space m0`] assume_tac) IN_MEASURABLE_BOREL_MUL_INDICATOR >>
    map_every Q.UNABBREV_TAC [`ma0`,`xsls`,`Nmsp1`,`sp_m_sl`] >>
    rfs[subsets_def,MEASURE_SPACE_MSPACE_MEASURABLE]
);

val y_slice_fun_measurable_sets_diff = store_thm(
    "y_slice_fun_measurable_sets_diff",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ y_slice_fun_measurable_sets m0 m1 ⇒
        y_slice_fun m0 (m_space (prod_measure_space m0 m1) DIFF s) ∈
        measurable (m_space m1,measurable_sets m1) Borel``,
    rw[] >> fs[y_slice_fun_measurable_sets_def] >>
    drule_all_then assume_tac y_slice_fun_diff >> rw[] >> pop_assum kall_tac >>
    `sigma_algebra (m_space m1,measurable_sets m1)` by fs[measure_space_def] >>
    Q.ABBREV_TAC `ysls = y_slice_fun m0 s` >>
    Q.ABBREV_TAC `ma1 = (m_space m1,measurable_sets m1)` >>
    `(λy. Normal (measure m0 (m_space m0))) ∈ measurable ma1 Borel`
        by fs[IN_MEASURABLE_BOREL_CONST_ALT] >>
    Q.ABBREV_TAC `Nmsp0 = (λy. Normal (measure m0 (m_space m0)))` >>
    `(λy. Nmsp0 y − ysls y) ∈ measurable ma1 Borel` by fs[IN_MEASURABLE_BOREL_SUB_ALT] >>
    Q.ABBREV_TAC `sp_m_sl = (λy. Nmsp0 y − ysls y)` >>
    (qspecl_then [`ma1`,`sp_m_sl`,`m_space m1`] assume_tac)
        (INST_TYPE [alpha |-> ``:β``] IN_MEASURABLE_BOREL_MUL_INDICATOR) >>
    map_every Q.UNABBREV_TAC [`ma1`,`ysls`,`Nmsp0`,`sp_m_sl`] >>
    rfs[subsets_def,MEASURE_SPACE_MSPACE_MEASURABLE]
);

val x_slice_fun_monotone_bigunion = store_thm(
    "x_slice_fun_monotone_bigunion",
    ``∀m0 m1 f n. measure_space m0 ∧ measure_space m1 ∧ (∀n. f n ⊆ f (SUC n)) ∧
        f ∈ (𝕌(:num) -> measurable_sets (prod_measure_space m0 m1)) ⇒
        (x_slice_fun m1 (BIGUNION (IMAGE f 𝕌(:num))) =
        (λs0. sup (IMAGE (λi. x_slice_fun m1 (f i) s0) 𝕌(:num))))``,
    rw[FUN_EQ_THM,x_slice_fun_def] >>
    `∀i. (x_slice s0 ∘ f) i ⊆ (x_slice s0 ∘ f) (SUC i)` by (fs[SUBSET_DEF] >>
        rw[x_slice_def,PREIMAGE_def]) >> 
    `mono_increasing (measure m1 ∘ x_slice s0 ∘ f)` by (rw[mono_increasing_suc] >>
        irule MEASURE_INCREASING >> rw[]
        >- (`f n ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
            irule product_measure_space_x_slice_measurable >> fs[] >> metis_tac[])
        >- (`f (SUC n) ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
            irule product_measure_space_x_slice_measurable >> fs[] >> metis_tac[])
        >- (fs[SUBSET_DEF])) >>
    `measure m1 ∘ x_slice s0 ∘ f -->
        measure m1 (x_slice s0 (BIGUNION (IMAGE f 𝕌(:num))))` suffices_by (rw[] >>
        drule_then assume_tac sup_seq >> fs[]) >>
    irule MONOTONE_CONVERGENCE >> rw[]
    >- (rw[x_slice_bigunion,IMAGE_IMAGE,o_DEF])
    >- (fs[FUNSET] >> rw[] >> irule product_measure_space_x_slice_measurable >>
        rw[] >> metis_tac[])
);

val y_slice_fun_monotone_bigunion = store_thm(
    "y_slice_fun_monotone_bigunion",
    ``∀m0 m1 f n. measure_space m0 ∧ measure_space m1 ∧ (∀n. f n ⊆ f (SUC n)) ∧
        f ∈ (𝕌(:num) -> measurable_sets (prod_measure_space m0 m1)) ⇒
        (y_slice_fun m0 (BIGUNION (IMAGE f 𝕌(:num))) =
        (λs1. sup (IMAGE (λi. y_slice_fun m0 (f i) s1) 𝕌(:num))))``,
    rw[FUN_EQ_THM,y_slice_fun_def] >>
    `∀i. (y_slice s1 ∘ f) i ⊆ (y_slice s1 ∘ f) (SUC i)` by (fs[SUBSET_DEF] >>
        rw[y_slice_def,PREIMAGE_def]) >> 
    `mono_increasing (measure m0 ∘ y_slice s1 ∘ f)` by (rw[mono_increasing_suc] >>
        irule MEASURE_INCREASING >> rw[]
        >- (`f n ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
            irule product_measure_space_y_slice_measurable >> fs[] >> metis_tac[])
        >- (`f (SUC n) ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
            irule product_measure_space_y_slice_measurable >> fs[] >> metis_tac[])
        >- (fs[SUBSET_DEF])) >>
    `measure m0 ∘ y_slice s1 ∘ f -->
        measure m0 (y_slice s1 (BIGUNION (IMAGE f 𝕌(:num))))` suffices_by (rw[] >>
        drule_then assume_tac sup_seq >> fs[]) >>
    irule MONOTONE_CONVERGENCE >> rw[]
    >- (rw[y_slice_bigunion,IMAGE_IMAGE,o_DEF])
    >- (fs[FUNSET] >> rw[] >> irule product_measure_space_y_slice_measurable >>
        rw[] >> metis_tac[])
);

val x_slice_fun_measurable_sets_monotone_bigunion = store_thm(
    "x_slice_fun_measurable_sets_monotone_bigunion",
    ``∀m0 m1 f n. measure_space m0 ∧ measure_space m1 ∧ (∀n. f n ⊆ f (SUC n)) ∧
        f ∈ (𝕌(:num) -> x_slice_fun_measurable_sets m0 m1) ⇒
        (x_slice_fun m1 (BIGUNION (IMAGE f 𝕌(:num))) ∈
        measurable (m_space m0,measurable_sets m0) Borel)``,
    rw[] >> fs[x_slice_fun_measurable_sets_def,FUNSET] >>
    `x_slice_fun m1 (BIGUNION (IMAGE f 𝕌(:num))) =
        (λs0. sup (IMAGE (λi. x_slice_fun m1 (f i) s0) 𝕌(:num)))` by (
        irule x_slice_fun_monotone_bigunion >> rw[FUNSET] >> metis_tac[]) >>
    rw[] >> pop_assum kall_tac >>
    `(λs0. sup (IMAGE (λi. (λi s0. x_slice_fun m1 (f i) s0) i s0) 𝕌(:num))) ∈
        measurable (m_space m0,measurable_sets m0) Borel` suffices_by rw[] >>
    irule IN_MEASURABLE_BOREL_MONO_SUP_ALT >> rw[]
    >- (rw[x_slice_fun_def,extreal_le_def] >> irule MEASURE_INCREASING >> rw[]
        >- (`f n ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
            irule product_measure_space_x_slice_measurable >> fs[] >> metis_tac[])
        >- (`f (SUC n) ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
            irule product_measure_space_x_slice_measurable >> fs[] >> metis_tac[])
        >- (fs[SUBSET_DEF,x_slice_def,PREIMAGE_def]))
    >- (fs[GSYM o_DEF,GSYM I_ALT])
    >- (fs[MEASURE_SPACE_SIGMA_ALGEBRA])
);

val y_slice_fun_measurable_sets_monotone_bigunion = store_thm(
    "y_slice_fun_measurable_sets_monotone_bigunion",
    ``∀m0 m1 f n. measure_space m0 ∧ measure_space m1 ∧ (∀n. f n ⊆ f (SUC n)) ∧
        f ∈ (𝕌(:num) -> y_slice_fun_measurable_sets m0 m1) ⇒
        (y_slice_fun m0 (BIGUNION (IMAGE f 𝕌(:num))) ∈
        measurable (m_space m1,measurable_sets m1) Borel)``,
    rw[] >> fs[y_slice_fun_measurable_sets_def,FUNSET] >>
    `y_slice_fun m0 (BIGUNION (IMAGE f 𝕌(:num))) =
        (λs1. sup (IMAGE (λi. y_slice_fun m0 (f i) s1) 𝕌(:num)))` by (
        irule y_slice_fun_monotone_bigunion >> rw[FUNSET] >> metis_tac[]) >>
    rw[] >> pop_assum kall_tac >>
    `(λs1. sup (IMAGE (λi. (λi s1. y_slice_fun m0 (f i) s1) i s1) 𝕌(:num))) ∈
        measurable (m_space m1,measurable_sets m1) Borel` suffices_by rw[] >>
    irule IN_MEASURABLE_BOREL_MONO_SUP_ALT >> rw[]
    >- (rw[y_slice_fun_def,extreal_le_def] >> irule MEASURE_INCREASING >> rw[]
        >- (`f n ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
            irule product_measure_space_y_slice_measurable >> fs[] >> metis_tac[])
        >- (`f (SUC n) ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
            irule product_measure_space_y_slice_measurable >> fs[] >> metis_tac[])
        >- (fs[SUBSET_DEF,y_slice_def,PREIMAGE_def]))
    >- (fs[GSYM o_DEF,GSYM I_ALT])
    >- (fs[MEASURE_SPACE_SIGMA_ALGEBRA])
);

val finite_disj_unions_rects_x_slice_fun_measurable = store_thm(
    "finite_disj_unions_rects_x_slice_fun_measurable",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        finite_disjoint_unions (prod_sets (measurable_sets m0) (measurable_sets m1)) ⊆
        x_slice_fun_measurable_sets m0 m1``,
    rw[SUBSET_DEF,x_slice_fun_measurable_sets_def]
    >- (fs[finite_disjoint_unions_dir] >> irule prod_measure_space_bigunion >>
        rw[finite_countable,measurable_sets_prod_measure_space] >>
        metis_tac[SIGMA_SUBSET_SUBSETS,SUBSET_TRANS])
    >- (fs[finite_disjoint_unions_alt_dir,x_slice_fun_alt] >> rw[] >>
        irule (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM) >>
        rw[MEASURE_SPACE_SIGMA_ALGEBRA,space_def] >>
        Q.ABBREV_TAC `f = (λi x. Normal (measure m1 (x_slice x (b i))))` >>
        map_every EXISTS_TAC [``f : num -> α -> extreal``,``count n``] >>
        Q.UNABBREV_TAC `f` >> rw[]
        >- (rw[EXTREAL_SUM_IMAGE_NORMAL,GSYM REAL_SUM_IMAGE_EQ_sum] >>
            rw[x_slice_bigunion,IMAGE_IMAGE] >> rw[o_DEF] >> rw[GSYM o_DEF] >>
            irule (GSYM MEASURE_ADDITIVE_SUM) >> rw[]
            >- (`DISJOINT (b i) (b j)` by (RES_TAC >> fs[]) >>
                fs[x_slice_def,PREIMAGE_def,DISJOINT_DEF,EXTENSION])
            >- (fs[FUNSET] >> rw[] >>
                `b x' ∈ prod_sets (measurable_sets m0) (measurable_sets m1)` by (RES_TAC >> fs[]) >>
                (qspecl_then [`m0`,`m1`] assume_tac) direct_products_x_sliceable >>
                rfs[x_sliceable_sets_def,SUBSET_DEF]))
        >- (rw[GSYM x_slice_fun_alt] >> fs[FUNSET] >> rw[] >>
            `b i ∈ prod_sets (measurable_sets m0) (measurable_sets m1)` by (RES_TAC >> fs[]) >>
            (qspecl_then [`m0`,`m1`] assume_tac) direct_products_x_slice_fun_measurable >>
            rfs[x_slice_fun_measurable_sets_def,SUBSET_DEF]))
);

val finite_disj_unions_rects_y_slice_fun_measurable = store_thm(
    "finite_disj_unions_rects_y_slice_fun_measurable",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        finite_disjoint_unions (prod_sets (measurable_sets m0) (measurable_sets m1)) ⊆
        y_slice_fun_measurable_sets m0 m1``,
    rw[SUBSET_DEF,y_slice_fun_measurable_sets_def]
    >- (fs[finite_disjoint_unions_dir] >> irule prod_measure_space_bigunion >>
        rw[finite_countable,measurable_sets_prod_measure_space] >>
        metis_tac[SIGMA_SUBSET_SUBSETS,SUBSET_TRANS])
    >- (fs[finite_disjoint_unions_alt_dir,y_slice_fun_alt] >> rw[] >>
        irule (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM) >>
        rw[MEASURE_SPACE_SIGMA_ALGEBRA,space_def] >>
        Q.ABBREV_TAC `f = (λi y. Normal (measure m0 (y_slice y (b i))))` >>
        map_every qexists_tac [`f`,`count n`] >> Q.UNABBREV_TAC `f` >> rw[]
        >- (rw[EXTREAL_SUM_IMAGE_NORMAL,GSYM REAL_SUM_IMAGE_EQ_sum] >>
            rw[y_slice_bigunion,IMAGE_IMAGE] >> rw[o_DEF] >> rw[GSYM o_DEF] >>
            irule (GSYM MEASURE_ADDITIVE_SUM) >> rw[]
            >- (`DISJOINT (b i) (b j)` by (RES_TAC >> fs[]) >>
                fs[y_slice_def,PREIMAGE_def,DISJOINT_DEF,EXTENSION])
            >- (fs[FUNSET] >> rw[] >>
                `b x' ∈ prod_sets (measurable_sets m0) (measurable_sets m1)` by (RES_TAC >> fs[]) >>
                (qspecl_then [`m0`,`m1`] assume_tac) direct_products_y_sliceable >>
                rfs[y_sliceable_sets_def,SUBSET_DEF]))
        >- (rw[GSYM y_slice_fun_alt] >> fs[FUNSET] >> rw[] >>
            `b i ∈ prod_sets (measurable_sets m0) (measurable_sets m1)` by (RES_TAC >> fs[]) >>
            (qspecl_then [`m0`,`m1`] assume_tac) direct_products_y_slice_fun_measurable >>
            rfs[y_slice_fun_measurable_sets_def,SUBSET_DEF]))
);

(* Halmos 35.A *)

val product_measure_space_x_slice_fun_measurable = store_thm(
    "product_measure_space_x_slice_fun_measurable",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        x_slice_fun m1 s ∈ measurable (m_space m0,measurable_sets m0) Borel``,
    rw[] >>
    `measurable_sets (prod_measure_space m0 m1) ⊆ x_slice_fun_measurable_sets m0 m1`
        suffices_by (rw[x_slice_fun_measurable_sets_def] >> rfs[SUBSET_DEF]) >>
    pop_assum kall_tac >> rw[measurable_sets_prod_measure_space] >>
    map_every Q.ABBREV_TAC [`XYsp = m_space m0 × m_space m1`,
        `XYsts = prod_sets (measurable_sets m0) (measurable_sets m1)`,
        `E = x_slice_fun_measurable_sets m0 m1`] >>
    `subsets (sigma XYsp (finite_disjoint_unions XYsts)) ⊆ E`
        suffices_by rw[sigma_finite_disj_unions] >>
    (qspecl_then [`m0`,`m1`] assume_tac) prod_sets_finite_union_algebra >> rfs[] >>
    drule_then assume_tac SIGMA_ALGEBRA_EQ_MONO_CLASS_GEN_ALGEBRA >>
    fs[space_def,subsets_def] >> irule MONO_CLASS_GEN_SMALLEST >>
    map_every Q.UNABBREV_TAC [`XYsp`,`XYsts`,`E`] >>
    rw[finite_disj_unions_rects_x_slice_fun_measurable] >> NTAC 2 (pop_assum kall_tac) >>
    irule MONOTONE_CLASS_INCREASING_DIFF_SUFFICIENT >> rw[space_def,subsets_def]
    >- (rw[x_slice_fun_measurable_sets_def,GSYM m_space_prod_measure_space]
        >- (fs[x_slice_fun_measurable_sets_def,prod_measure_space_diff])
        >- (fs[x_slice_fun_measurable_sets_diff]))
    >- (rw[x_slice_fun_measurable_sets_def]
        >- (irule prod_measure_space_bigunion >>
            fs[x_slice_fun_measurable_sets_def,SUBSET_DEF] >>
            rw[] >> fs[FUNSET])
        >- (irule x_slice_fun_measurable_sets_monotone_bigunion >> rw[]))
    >- (imp_res_tac prod_measure_space_subset_class >>
        rw[subset_class_def,x_slice_fun_measurable_sets_def] >>
        fs[subset_class_def,prod_measure_space_def,measurable_sets_def,subsets_def])
);

val product_measure_space_y_slice_fun_measurable = store_thm(
    "product_measure_space_y_slice_fun_measurable",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        y_slice_fun m0 s ∈ measurable (m_space m1,measurable_sets m1) Borel``,
    rw[] >>
    `measurable_sets (prod_measure_space m0 m1) ⊆ y_slice_fun_measurable_sets m0 m1`
        suffices_by (rw[y_slice_fun_measurable_sets_def] >> rfs[SUBSET_DEF]) >>
    pop_assum kall_tac >> rw[measurable_sets_prod_measure_space] >>
    map_every Q.ABBREV_TAC [`XYsp = m_space m0 × m_space m1`,
        `XYsts = prod_sets (measurable_sets m0) (measurable_sets m1)`,
        `E = y_slice_fun_measurable_sets m0 m1`] >>
    `subsets (sigma XYsp (finite_disjoint_unions XYsts)) ⊆ E`
        suffices_by rw[sigma_finite_disj_unions] >>
    (qspecl_then [`m0`,`m1`] assume_tac) prod_sets_finite_union_algebra >> rfs[] >>
    drule_then assume_tac SIGMA_ALGEBRA_EQ_MONO_CLASS_GEN_ALGEBRA >>
    fs[space_def,subsets_def] >> irule MONO_CLASS_GEN_SMALLEST >>
    map_every Q.UNABBREV_TAC [`XYsp`,`XYsts`,`E`] >>
    rw[finite_disj_unions_rects_y_slice_fun_measurable] >> NTAC 2 (pop_assum kall_tac) >>
    irule MONOTONE_CLASS_INCREASING_DIFF_SUFFICIENT >> rw[space_def,subsets_def]
    >- (rw[y_slice_fun_measurable_sets_def,GSYM m_space_prod_measure_space]
        >- (fs[y_slice_fun_measurable_sets_def,prod_measure_space_diff])
        >- (fs[y_slice_fun_measurable_sets_diff]))
    >- (rw[y_slice_fun_measurable_sets_def]
        >- (irule prod_measure_space_bigunion >>
            fs[y_slice_fun_measurable_sets_def,SUBSET_DEF] >>
            rw[] >> fs[FUNSET])
        >- (irule y_slice_fun_measurable_sets_monotone_bigunion >> rw[]))
    >- (imp_res_tac prod_measure_space_subset_class >>
        rw[subset_class_def,y_slice_fun_measurable_sets_def] >>
        fs[subset_class_def,prod_measure_space_def,measurable_sets_def,subsets_def])
);

(*********************************)
(* μ countably additive in (X,Σ) *)
(*********************************)

(* 20B : measurable_sequence *)
(* 27B : lebesgue_monotone_convergence *)

(* Halmos 27.2 *)
val halmos_27_2_pos = store_thm(
    "halmos_27_2_pos",
    ``∀m fi. measure_space m ∧ (∀i x. 0 ≤ fi i x) ∧ (∀i. integrable m (fi i)) ∧
        suminf (λi. pos_fn_integral m (fi i)) < PosInf ⇒
        ∃f. (∀x. x ∈ m_space m ⇒ (suminf (λi. fi i x) = f x)) ∧ integrable m f ∧
        (pos_fn_integral m f = suminf (λi. pos_fn_integral m (fi i)))``,
    rw[] >> EXISTS_TAC ``λx. suminf (λi. (fi : num -> α -> extreal) i x)`` >> fs[] >>
    `pos_fn_integral m (λx. suminf (λi. fi i x)) = suminf (λi. pos_fn_integral m (fi i))` by (
        (qspecl_then [`m`,`λx. suminf (λi. fi i x)`,
            `λn x. SIGMA (λi. fi i x) (count n)`] assume_tac) lebesgue_monotone_convergence >>
        rfs[] >> fs[ext_suminf_def] >>
        `sup (IMAGE (λn. SIGMA (λi. pos_fn_integral m (fi i)) (count n)) 𝕌(:num)) =
            sup (IMAGE (λi. pos_fn_integral m (λx. SIGMA (λi. fi i x) (count i))) 𝕌(:num))` by (
            `(λn. SIGMA (λi. pos_fn_integral m (fi i)) (count n)) =
                (λi. pos_fn_integral m (λx. SIGMA (λi. fi i x) (count i)))` suffices_by fs[] >>
            fs[FUN_EQ_THM] >> rw[] >> irule (GSYM pos_fn_integral_sum) >>
            rw[] >> fs[integrable_def]) >>
        fs[] >> pop_assum kall_tac >> pop_assum irule >> rw[]
        >- (rw[ext_mono_increasing_def] >> irule EXTREAL_SUM_IMAGE_MONO_SET >>
            rw[] >> fs[count_def,SUBSET_DEF])
        >- (fs[GSYM ext_suminf_def] >> irule ext_suminf_pos >> rw[])
        >- (irule EXTREAL_SUM_IMAGE_POS >> fs[])
        >- (irule IN_MEASURABLE_BOREL_SUM_ALT >> rw[] >> fs[integrable_def,measure_space_def])) >>
    fs[integrable_def] >> rw[]
    >- (irule IN_MEASURABLE_BOREL_POS_SUMINF_ALT >> rw[] >> fs[measure_space_def])
    >- (`fn_plus (λx. suminf (λi. fi i x)) = (λx. suminf (λi. fi i x))` by (
            irule FN_PLUS_POS_ID >> rw[] >> irule ext_suminf_pos >> rw[]) >>
        fs[] >> CCONTR_TAC >> fs[extreal_lt_alt])
    >- (`fn_minus (λx. suminf (λi. fi i x)) = (λx. 0)` by (
            irule FN_MINUS_POS_ZERO >> rw[] >> irule ext_suminf_pos >> rw[]) >>
        fs[pos_fn_integral_zero] >> fs[GSYM N0_EQ_0])
);

(* Halmos 35B ish : 27B 27.2 13A *)
val product_measure_space_countably_additive = store_thm(
    "product_measure_space_countably_additive",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        countably_additive (prod_measure_space m0 m1)``,
    rw[] >> fs[countably_additive_def] >> rw[] >>
    map_every Q.ABBREV_TAC [`mnufi = measure (prod_measure_space m0 m1) ∘ f`,
        `mnuf = measure (prod_measure_space m0 m1) (BIGUNION (IMAGE f 𝕌(:num)))`] >>
    `(suminf (λi. Normal (mnufi i)) = Normal mnuf)` suffices_by (rw[] >>
        `∀i. 0 ≤ mnufi i` suffices_by metis_tac[sums_to_ext_suminf] >>
        Q.UNABBREV_TAC `mnufi` >>
        `positive (prod_measure_space m0 m1)` by fs[product_measure_space_positive] >>
        fs[positive_def] >> rfs[FUNSET]) >>
    map_every Q.UNABBREV_TAC [`mnufi`,`mnuf`] >>
    `∀n. f n ∈ measurable_sets (prod_measure_space m0 m1)` by fs[FUNSET] >>
    fs[product_measure_space_normal_measure,GSYM x_slice_def] >>
    Q.ABBREV_TAC `mxsl = (λs s0. Normal (measure m1 (x_slice s0 s)))` >>
    `integral m0 (mxsl (BIGUNION (IMAGE f 𝕌(:num)))) =
        suminf (λi. integral m0 (mxsl (f i)))` suffices_by (
        Q.UNABBREV_TAC `mxsl` >> rw[]) >>
    `integral m0 (mxsl (BIGUNION (IMAGE f 𝕌(:num)))) =
        pos_fn_integral m0 (mxsl (BIGUNION (IMAGE f 𝕌(:num))))` by (irule integral_pos_fn >>
        rw[] >> Q.UNABBREV_TAC `mxsl` >> fs[GSYM N0_EQ_0,extreal_le_def] >>
        `x_slice x (BIGUNION (IMAGE f 𝕌(:num))) ∈ measurable_sets m1` suffices_by (rw[] >>
            fs[measure_space_def,positive_def]) >>
        drule_all_then assume_tac product_measure_space_x_slice_measurable >> fs[]) >>
    `(λi. integral m0 (mxsl (f i))) = (λi. pos_fn_integral m0 (mxsl (f i)))` by (
        rw[FUN_EQ_THM] >> irule integral_pos_fn >> rw[] >>
        Q.UNABBREV_TAC `mxsl` >> fs[GSYM N0_EQ_0,extreal_le_def] >>
        `x_slice x (f i) ∈ measurable_sets m1` suffices_by fs[measure_space_def,positive_def] >>
        `f i ∈ measurable_sets (prod_measure_space m0 m1)` by fs[] >>
        drule_all_then assume_tac product_measure_space_x_slice_measurable >> fs[]) >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >> fs[ext_suminf_def] >>
    `(λn. SIGMA (λi. pos_fn_integral m0 (mxsl (f i))) (count n)) =
        (λn. pos_fn_integral m0 (λx. SIGMA (λi. mxsl (f i) x) (count n)))` by (rw[FUN_EQ_THM] >>
        (assume_tac o ISPECL
            [``m0 : (α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real)``,
            ``((mxsl : (α # β -> bool) -> α -> extreal) ∘ (f : num -> α # β -> bool))``,
            ``count n``]) (GSYM pos_fn_integral_sum) >>
        rfs[] >> pop_assum irule >> rw[] >> Q.UNABBREV_TAC `mxsl` >> fs[]
        >- (fs[GSYM N0_EQ_0,extreal_le_def] >>
            `x_slice x (f i) ∈ measurable_sets m1` suffices_by
                fs[measure_space_def,positive_def] >>
            `f i ∈ measurable_sets (prod_measure_space m0 m1)` by fs[] >>
            drule_all_then assume_tac product_measure_space_x_slice_measurable >> fs[])
        >- (rw[GSYM x_slice_fun_alt] >> fs[product_measure_space_x_slice_fun_measurable])) >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`m0`,`mxsl (BIGUNION (IMAGE f 𝕌(:num)))`,
        `λn x. SIGMA (λi. mxsl (f i) x) (count n)`]
        assume_tac) lebesgue_monotone_convergence >>
    fs[] >> pop_assum irule >>
    `∀s x. s ∈ measurable_sets (prod_measure_space m0 m1) ⇒ 0 ≤ mxsl s x` by (rw[] >>
        Q.UNABBREV_TAC `mxsl` >> rw[GSYM N0_EQ_0,extreal_le_def] >>
        `x_slice x s ∈ measurable_sets m1` suffices_by fs[measure_space_def,positive_def] >>
        imp_res_tac product_measure_space_x_slice_measurable >> rfs[]) >> rw[]
    >- (rw[ext_mono_increasing_def] >> irule EXTREAL_SUM_IMAGE_MONO_SET >> rw[count_def,SUBSET_DEF])
    >- (Q.UNABBREV_TAC `mxsl` >> rw[GSYM ext_suminf_def] >> fs[] >>
        (qspecl_then [`λi. measure m1 (x_slice x (f i))`] assume_tac) sums_to_ext_suminf >>
        `∀i. 0 ≤ measure m1 (x_slice x (f i))` by rw[GSYM extreal_le_def,N0_EQ_0] >>
        fs[] >> NTAC 2 (pop_assum kall_tac) >>
        `(λi. measure m1 (x_slice x (f i))) = measure m1 ∘ (λi. x_slice x (f i))`
            by rw[FUN_EQ_THM] >>
        fs[] >> pop_assum kall_tac >> irule MEASURE_COUNTABLY_ADDITIVE >> rw[]
        >- (RES_TAC >> fs[DISJOINT_DEF,EXTENSION] >> rw[x_slice_def,PREIMAGE_def])
        >- (fs[x_slice_bigunion] >> rw[GSYM IMAGE_COMPOSE] >> rw[o_DEF])
        >- (rw[FUNSET] >> metis_tac[product_measure_space_x_slice_measurable]))
    >- (irule EXTREAL_SUM_IMAGE_POS >> fs[])
    >- ((assume_tac o ISPECL [``(m_space m0,measurable_sets m0)``,
            ``λ(i :num). (mxsl : (α # β -> bool) -> α -> extreal) (f i)``,
            ``count i``]) IN_MEASURABLE_BOREL_SUM_ALT >>
        fs[] >> pop_assum irule >>
        `sigma_algebra (m_space m0,measurable_sets m0)` by fs[measure_space_def] >>
        rw[] >> Q.UNABBREV_TAC `mxsl` >> rw[] >> rw[GSYM x_slice_fun_alt] >>
        fs[product_measure_space_x_slice_fun_measurable])
);

val product_measure_space_hor_countably_additive = store_thm(
    "product_measure_space_hor_countably_additive",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        countably_additive (prod_measure_space_hor m0 m1)``,
    rw[] >> fs[countably_additive_def] >> rw[] >>
    map_every Q.ABBREV_TAC [`mnufi = measure (prod_measure_space_hor m0 m1) ∘ f`,
        `mnuf = measure (prod_measure_space_hor m0 m1) (BIGUNION (IMAGE f 𝕌(:num)))`] >>
    `(suminf (λi. Normal (mnufi i)) = Normal mnuf)` suffices_by (rw[] >>
        `∀i. 0 ≤ mnufi i` suffices_by metis_tac[sums_to_ext_suminf] >>
        Q.UNABBREV_TAC `mnufi` >>
        `positive (prod_measure_space_hor m0 m1)` by fs[product_measure_space_hor_positive] >>
        fs[positive_def] >> rfs[FUNSET]) >>
    map_every Q.UNABBREV_TAC [`mnufi`,`mnuf`] >>
    `∀n. f n ∈ measurable_sets (prod_measure_space_hor m0 m1)` by fs[FUNSET] >>
    fs[product_measure_space_hor_normal_measure,GSYM y_slice_def] >>
    fs[measurable_sets_prod_hor_measurable_sets_prod] >>
    Q.ABBREV_TAC `mysl = (λs s1. Normal (measure m0 (y_slice s1 s)))` >>
    `integral m1 (mysl (BIGUNION (IMAGE f 𝕌(:num)))) =
        suminf (λi. integral m1 (mysl (f i)))` suffices_by (
        Q.UNABBREV_TAC `mysl` >> rw[]) >>
    `integral m1 (mysl (BIGUNION (IMAGE f 𝕌(:num)))) =
        pos_fn_integral m1 (mysl (BIGUNION (IMAGE f 𝕌(:num))))` by (irule integral_pos_fn >>
        rw[] >> Q.UNABBREV_TAC `mysl` >> fs[GSYM N0_EQ_0,extreal_le_def] >>
        `y_slice x (BIGUNION (IMAGE f 𝕌(:num))) ∈ measurable_sets m0` suffices_by (rw[] >>
            fs[measure_space_def,positive_def]) >>
        drule_all_then assume_tac product_measure_space_y_slice_measurable >> fs[]) >>
    `(λi. integral m1 (mysl (f i))) = (λi. pos_fn_integral m1 (mysl (f i)))` by (
        rw[FUN_EQ_THM] >> irule integral_pos_fn >> rw[] >>
        Q.UNABBREV_TAC `mysl` >> fs[GSYM N0_EQ_0,extreal_le_def] >>
        `y_slice x (f i) ∈ measurable_sets m0` suffices_by fs[measure_space_def,positive_def] >>
        `f i ∈ measurable_sets (prod_measure_space m0 m1)` by fs[] >>
        drule_all_then assume_tac product_measure_space_y_slice_measurable >> fs[]) >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >> fs[ext_suminf_def] >>
    `(λn. SIGMA (λi. pos_fn_integral m1 (mysl (f i))) (count n)) =
        (λn. pos_fn_integral m1 (λx. SIGMA (λi. mysl (f i) x) (count n)))` by (rw[FUN_EQ_THM] >>
        (qspecl_then [`m1`,
            `(mysl : (α # β -> bool) -> β -> extreal) ∘ (f : num -> α # β -> bool)`,
            `count n`] assume_tac)
            (INST_TYPE [alpha |-> ``:β``,beta |-> ``:num``] (GSYM pos_fn_integral_sum)) >>
        rfs[] >> pop_assum irule >> rw[] >> Q.UNABBREV_TAC `mysl` >> fs[]
        >- (fs[GSYM N0_EQ_0,extreal_le_def] >>
            `y_slice x (f i) ∈ measurable_sets m0` suffices_by
                fs[measure_space_def,positive_def] >>
            `f i ∈ measurable_sets (prod_measure_space m0 m1)` by fs[] >>
            drule_all_then assume_tac product_measure_space_y_slice_measurable >> fs[])
        >- (rw[GSYM y_slice_fun_alt] >> fs[product_measure_space_y_slice_fun_measurable])) >>
    fs[measurable_sets_prod_hor_measurable_sets_prod] >> pop_assum kall_tac >>
    (qspecl_then [`m1`,`mysl (BIGUNION (IMAGE f 𝕌(:num)))`,
        `λn x. SIGMA (λi. mysl (f i) x) (count n)`]
        assume_tac) (INST_TYPE [alpha |-> ``:β``] lebesgue_monotone_convergence) >>
    fs[] >> pop_assum irule >>
    `∀s x. s ∈ measurable_sets (prod_measure_space m0 m1) ⇒ 0 ≤ mysl s x` by (rw[] >>
        Q.UNABBREV_TAC `mysl` >> rw[GSYM N0_EQ_0,extreal_le_def] >>
        `y_slice x s ∈ measurable_sets m0` suffices_by fs[measure_space_def,positive_def] >>
        imp_res_tac product_measure_space_y_slice_measurable >> rfs[]) >> rw[]
    >- (rw[ext_mono_increasing_def] >> irule EXTREAL_SUM_IMAGE_MONO_SET >> rw[count_def,SUBSET_DEF])
    >- (Q.UNABBREV_TAC `mysl` >> rw[GSYM ext_suminf_def] >> fs[] >>
        (qspecl_then [`λi. measure m0 (y_slice x (f i))`] assume_tac) sums_to_ext_suminf >>
        `∀i. 0 ≤ measure m0 (y_slice x (f i))` by rw[GSYM extreal_le_def,N0_EQ_0] >>
        fs[] >> NTAC 2 (pop_assum kall_tac) >>
        `(λi. measure m0 (y_slice x (f i))) = measure m0 ∘ (λi. y_slice x (f i))`
            by rw[FUN_EQ_THM] >>
        fs[] >> pop_assum kall_tac >> irule MEASURE_COUNTABLY_ADDITIVE >> rw[]
        >- (RES_TAC >> fs[DISJOINT_DEF,EXTENSION] >> rw[y_slice_def,PREIMAGE_def])
        >- (fs[y_slice_bigunion] >> rw[GSYM IMAGE_COMPOSE] >> rw[o_DEF])
        >- (rw[FUNSET] >> metis_tac[product_measure_space_y_slice_measurable]))
    >- (irule EXTREAL_SUM_IMAGE_POS >> fs[])
    >- ((qspecl_then [`(m_space m1,measurable_sets m1)`,`λ(i :num). mysl (f i)`,`count i`] assume_tac)
            (INST_TYPE [alpha |-> ``:β``,beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM_ALT) >>
        fs[] >> pop_assum irule >>
        `sigma_algebra (m_space m1,measurable_sets m1)` by fs[measure_space_def] >>
        rw[] >> Q.UNABBREV_TAC `mysl` >> rw[] >> rw[GSYM y_slice_fun_alt] >>
        fs[product_measure_space_y_slice_fun_measurable])
);

(***************************************************)
(* product measure space is indeed a measure space *)
(***************************************************)

val prod_measure_space_measure_space = store_thm(
    "prod_measure_space_measure_space",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ measure_space (prod_measure_space m0 m1)``,
    rw[] >> map_every imp_res_tac [prod_measure_space_sigma_algebra,
        product_measure_space_positive,product_measure_space_countably_additive] >>
    fs[measure_space_def]
);

val prod_measure_space_hor_measure_space = store_thm(
    "prod_measure_space_hor_measure_space",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ measure_space (prod_measure_space_hor m0 m1)``,
    rw[] >> map_every imp_res_tac [prod_measure_space_hor_sigma_algebra,
        product_measure_space_hor_positive,product_measure_space_hor_countably_additive] >>
    fs[measure_space_def]
);

(***************************)
(* Equivalence of Measures *)
(***************************)

val measure_eq_algebra_imp_measure_eq = store_thm(
    "measure_eq_algebra_imp_measure_eq",
    ``∀a mu nu. measure_space (space a,subsets (sigma (space a) (subsets a)),mu) ∧
        measure_space (space a,subsets (sigma (space a) (subsets a)),nu) ∧
        algebra a ∧ (∀s. s ∈ subsets a ⇒ (mu s = nu s)) ⇒
        ∀s. s ∈ subsets (sigma (space a) (subsets a)) ⇒ (mu s = nu s)``,
    NTAC 4 strip_tac >>
    Q.ABBREV_TAC `E = {s | s ∈ subsets (sigma (space a) (subsets a)) ∧ (mu s = nu s)}` >>
    `subsets (sigma (space a) (subsets a)) ⊆ E` suffices_by (
        rw[] >> Q.UNABBREV_TAC `E` >> fs[SUBSET_DEF]) >>
    `subsets a ⊆ E` by (Q.UNABBREV_TAC `E` >> rw[SUBSET_DEF] >> fs[IN_SIGMA]) >>
    `sigma_algebra (sigma (space a) (subsets a))` by fs[algebra_def,SIGMA_ALGEBRA_SIGMA] >>
    fs[SIGMA_ALGEBRA_EQ_MONO_CLASS_GEN_ALGEBRA] >>
    rfs[SIGMA_ALGEBRA_EQ_MONO_CLASS_GEN_ALGEBRA] >>
    irule MONO_CLASS_GEN_SMALLEST >> Q.UNABBREV_TAC `E` >> fs[] >>
    irule MONOTONE_CLASS_INCREASING_DIFF_SUFFICIENT >>
    fs[SIGMA_ALGEBRA_FN,space_def,subsets_def,SPACE_MONO_CLASS_GEN] >> rw[]
    >- (NTAC 2 (dxrule_then assume_tac MEASURE_COMPL) >>
        NTAC 2 (qpat_x_assum `∀s. _` (qspec_then `s` assume_tac)) >>
        rfs[m_space_def,measurable_sets_def,measure_def] >>
        `space a ∈ subsets a` by fs[ALGEBRA_SPACE] >> fs[])
    >- (qpat_x_assum `∀f. _` irule >> fs[FUNSET])
    >- ((qspecl_then [`(space a,subsets (mono_class_gen (space a) (subsets a)),mu)`,`f`]
            assume_tac) MEASURE_COUNTABLE_INCREASING_ALT >>
        (qspecl_then [`(space a,subsets (mono_class_gen (space a) (subsets a)),nu)`,`f`]
            assume_tac) MEASURE_COUNTABLE_INCREASING_ALT >>
        rfs[FUNSET,measurable_sets_def,measure_def] >>
        `mu ∘ f = nu ∘ f` by rw[FUN_EQ_THM] >> fs[] >> pop_assum kall_tac >>
        dxrule_all_then assume_tac SEQ_UNIQ >> rw[])
    >- (fs[subset_class_def])
);

val measure_eq_semi_alg_imp_measure_eq = store_thm(
    "measure_eq_semi_alg_imp_measure_eq",
    ``∀a mu nu. measure_space (space a,subsets (sigma (space a) (subsets a)),mu) ∧
        measure_space (space a,subsets (sigma (space a) (subsets a)),nu) ∧
        semi_algebra a ∧ (∀s. s ∈ subsets a ⇒ (mu s = nu s)) ⇒
        ∀s. s ∈ subsets (sigma (space a) (subsets a)) ⇒ (mu s = nu s)``,
    NTAC 4 strip_tac >>
    (qspecl_then [`(space a,finite_disjoint_unions (subsets a))`,`mu`,`nu`] assume_tac)
        measure_eq_algebra_imp_measure_eq >>
    rfs[space_def,subsets_def,sigma_finite_disj_unions,semi_alg_ext] >>
    `∀s. s ∈ finite_disjoint_unions (subsets a) ⇒ (mu s = nu s)` suffices_by (rw[] >> fs[]) >>
    pop_assum kall_tac >> rw[finite_disjoint_unions_alt_dir] >>
    (qspecl_then [`(space a,subsets (sigma (space a) (subsets a)),mu)`,`b`,`n`]
        assume_tac) ADDITIVE_SUM_ALT >>
    (qspecl_then [`(space a,subsets (sigma (space a) (subsets a)),nu)`,`b`,`n`]
        assume_tac) ADDITIVE_SUM_ALT >>
    rfs[MEASURE_SPACE_ALGEBRA,MEASURE_SPACE_POSITIVE,MEASURE_SPACE_ADDITIVE] >>
    rfs[measurable_sets_def,measure_def] >> rfs[FUNSET,IN_SIGMA] >>
    NTAC 2 (pop_assum (assume_tac o GSYM) >> rw[] >> pop_assum kall_tac) >>
    irule SUM_EQ >> rw[]
);

val prod_measures_equiv_hor = store_thm(
    "prod_measures_equiv_hor",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ subsets (sigma (m_space m0 × m_space m1)
        (prod_sets (measurable_sets m0) (measurable_sets m1))) ⇒
        (prod_measure_hor m0 m1 s = prod_measure m0 m1 s)``,
    NTAC 2 strip_tac >> Cases_on `measure_space m0 ∧ measure_space m1` >> fs[] >>
    (qspecl_then [`(m_space m0 × m_space m1,prod_sets (measurable_sets m0) (measurable_sets m1))`,
        `prod_measure_hor m0 m1`,`prod_measure m0 m1`] assume_tac)
        (INST_TYPE [alpha |-> ``:α # β``] measure_eq_semi_alg_imp_measure_eq) >>
    rfs[space_def,subsets_def] >> rfs[GSYM prod_measure_space_def,GSYM prod_measure_space_hor_def] >>
    rfs[prod_sets_semi_alg,prod_measure_space_measure_space,prod_measure_space_hor_measure_space] >>
    `∀r. r ∈ prod_sets (measurable_sets m0) (measurable_sets m1) ⇒
        (prod_measure_hor m0 m1 r = prod_measure m0 m1 r)` suffices_by (rw[] >> fs[]) >>
    pop_assum kall_tac >> rw[prod_sets_def] >>
    `measure (prod_measure_space m0 m1) (s × t) = measure m0 s * measure m1 t` by
        fs[prod_measure_prod_set] >>
    `measure (prod_measure_space_hor m0 m1) (s × t) = measure m0 s * measure m1 t` by
        fs[prod_measure_hor_prod_set] >>
    fs[prod_measure_space_def,prod_measure_space_hor_def,measure_def]
);

(*********************)
(* Tonelli's Theorem *)
(*********************)

(* Function Slice Properties *)

val x_fun_slice_fn_plus = store_thm(
    "x_fun_slice_fn_plus",
    ``∀f x. x_fun_slice (fn_plus f) x = fn_plus (x_fun_slice f x)``,
    rw[FUN_EQ_THM,x_fun_slice_def,fn_plus_def]
);

val y_fun_slice_fn_plus = store_thm(
    "y_fun_slice_fn_plus",
    ``∀f y. y_fun_slice (fn_plus f) y = fn_plus (y_fun_slice f y)``,
    rw[FUN_EQ_THM,y_fun_slice_def,fn_plus_def]
);

val x_fun_slice_fn_minus = store_thm(
    "x_fun_slice_fn_minus",
    ``∀f x. x_fun_slice (fn_minus f) x = fn_minus (x_fun_slice f x)``,
    rw[FUN_EQ_THM,x_fun_slice_def,fn_minus_def]
);

val y_fun_slice_fn_minus = store_thm(
    "y_fun_slice_fn_minus",
    ``∀f y. y_fun_slice (fn_minus f) y = fn_minus (y_fun_slice f y)``,
    rw[FUN_EQ_THM,y_fun_slice_def,fn_minus_def]
);

val x_fun_slice_indicator_fn = store_thm(
    "x_fun_slice_indicator_fn",
    ``∀s x. x_fun_slice (indicator_fn s) x = indicator_fn (x_slice x s)``,
    rw[x_fun_slice_alt,indicator_fn_def,x_slice_def,PREIMAGE_def]
);

val y_fun_slice_indicator_fn = store_thm(
    "y_fun_slice_indicator_fn",
    ``∀s y. y_fun_slice (indicator_fn s) y = indicator_fn (y_slice y s)``,
    rw[y_fun_slice_alt,indicator_fn_def,y_slice_def,PREIMAGE_def]
);

val x_fun_slice_pos_simple_fn = store_thm(
    "x_fun_slice_pos_simple_fn",
    ``∀m0 m1 f s e a x. measure_space m0 ∧ measure_space m1 ∧ x ∈ m_space m0 ∧
        pos_simple_fn (prod_measure_space m0 m1) f s e a ⇒
        pos_simple_fn m1 (x_fun_slice f x) s (λi. x_slice x (e i)) a``,
    rw[pos_simple_fn_def,x_fun_slice_def]
    >- (`(x,t) ∈ m_space (prod_measure_space m0 m1)` by rw[m_space_prod_measure_space] >>
        rw[] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[] >>
        `indicator_fn (e x') (x,t) = indicator_fn (x_slice x (e x')) t`
            suffices_by (rw[] >> fs[]) >>
        rw[indicator_fn_def,x_slice_def,PREIMAGE_def])
    >- (irule product_measure_space_x_slice_measurable >> rw[] >> qexists_tac `m0` >> rw[])
    >- (`DISJOINT (e i) (e i')` by rw[] >> fs[DISJOINT_DEF,x_slice_def,PREIMAGE_def,EXTENSION])
    >- ((qspecl_then [`x`,`IMAGE e s`] assume_tac) (GSYM x_slice_bigunion) >>
        fs[GSYM IMAGE_COMPOSE,o_DEF] >>
        rw[m_space_prod_measure_space,x_slice_def,PREIMAGE_def,EXTENSION])
);

val y_fun_slice_pos_simple_fn = store_thm(
    "y_fun_slice_pos_simple_fn",
    ``∀m0 m1 f s e a y. measure_space m0 ∧ measure_space m1 ∧ y ∈ m_space m1 ∧
        pos_simple_fn (prod_measure_space m0 m1) f s e a ⇒
        pos_simple_fn m0 (y_fun_slice f y) s (λi. y_slice y (e i)) a``,
    rw[pos_simple_fn_def,y_fun_slice_def]
    >- (qpat_x_assum `∀t. _` (qspec_then `(t,y)` assume_tac) >>
        rfs[m_space_prod_measure_space] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[] >>
        `indicator_fn (e x) (t,y) = indicator_fn (y_slice y (e x)) t`
            suffices_by (rw[] >> fs[]) >>
        rw[indicator_fn_def,y_slice_def,PREIMAGE_def])
    >- (irule product_measure_space_y_slice_measurable >> rw[] >> qexists_tac `m1` >> rw[])
    >- (`DISJOINT (e i) (e i')` by rw[] >> fs[DISJOINT_DEF,y_slice_def,PREIMAGE_def,EXTENSION])
    >- ((qspecl_then [`y`,`IMAGE e s`] assume_tac)
            (INST_TYPE [alpha |-> ``:β``,beta |-> ``:α``] (GSYM y_slice_bigunion)) >>
        fs[GSYM IMAGE_COMPOSE,o_DEF] >>
        rw[m_space_prod_measure_space,y_slice_def,PREIMAGE_def,EXTENSION])
);

(* Part One of Tonelli's *)

(*product_measure_space_x_fun_slice_measurable*)
val tonelli_1x = store_thm(
    "tonelli_1x",
    ``∀m0 m1 a f x. measure_space m0 ∧ measure_space m1 ∧ x ∈ m_space m0 ∧
        f ∈ measurable (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) a ⇒
        x_fun_slice f x ∈ measurable (m_space m1,measurable_sets m1) a``,
    rw[measurable_def,space_def,subsets_def]
    >- (fs[measure_space_def])
    >- (fs[FUNSET] >> rw[x_fun_slice_def] >> Q.RENAME_TAC [`y ∈ m_space m1`] >>
        qpat_x_assum `∀x. _` irule >> rw[m_space_prod_measure_space])
    >- (qpat_x_assum `∀x. _` (dxrule_all_then assume_tac) >>
        dxrule_all_then assume_tac product_measure_space_x_slice_measurable >>
        pop_assum (qspec_then `x` assume_tac) >>
        rfs[x_slice_inter,m_space_prod_measure_space,x_slice_rect] >>
        `x_slice x (PREIMAGE f s) = PREIMAGE (x_fun_slice f x) s` suffices_by (rw[] >> fs[]) >>
        rw[EXTENSION,x_slice_def,x_fun_slice_def,PREIMAGE_def])
);

(*product_measure_space_y_fun_slice_measurable*)
val tonelli_1y = store_thm(
    "tonelli_1y",
    ``∀m0 m1 a f y. measure_space m0 ∧ measure_space m1 ∧ y ∈ m_space m1 ∧
        f ∈ measurable (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) a ⇒
        y_fun_slice f y ∈ measurable (m_space m0,measurable_sets m0) a``,
    rw[measurable_def,space_def,subsets_def]
    >- (fs[measure_space_def])
    >- (fs[FUNSET] >> rw[y_fun_slice_def] >>
        qpat_x_assum `∀x. _` irule >> rw[m_space_prod_measure_space])
    >- (qpat_x_assum `∀x. _` (dxrule_all_then assume_tac) >>
        dxrule_all_then assume_tac product_measure_space_y_slice_measurable >>
        pop_assum (qspec_then `y` assume_tac) >>
        rfs[y_slice_inter,m_space_prod_measure_space,y_slice_rect] >>
        `y_slice y (PREIMAGE f s) = PREIMAGE (y_fun_slice f y) s` suffices_by (rw[] >> fs[]) >>
        rw[EXTENSION,y_slice_def,y_fun_slice_def,PREIMAGE_def])
);

(* Buildup to Part Two of Tonelli *)

val product_measure_space_x_fun_slice_fun_measurable_indicator_fn = store_thm(
    "product_measure_space_x_fun_slice_fun_measurable_indicator_fn",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (λx. pos_fn_integral m1 (x_fun_slice (indicator_fn s) x)) ∈
        measurable (m_space m0,measurable_sets m0) Borel``,
    rw[x_fun_slice_indicator_fn] >>
    drule_all_then assume_tac product_measure_space_x_slice_measurable >>
    rw[pos_fn_integral_indicator,GSYM x_slice_fun_alt,product_measure_space_x_slice_fun_measurable]
);

val product_measure_space_y_fun_slice_fun_measurable_indicator_fn = store_thm(
    "product_measure_space_y_fun_slice_fun_measurable_indicator_fn",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (λy. pos_fn_integral m0 (y_fun_slice (indicator_fn s) y)) ∈
        measurable (m_space m1,measurable_sets m1) Borel``,
    rw[y_fun_slice_indicator_fn] >>
    drule_all_then assume_tac product_measure_space_y_slice_measurable >>
    rw[pos_fn_integral_indicator,GSYM y_slice_fun_alt,product_measure_space_y_slice_fun_measurable]
);

val product_measure_space_x_fun_slice_fun_measurable_pos_simple_fn = store_thm(
    "product_measure_space_x_fun_slice_fun_measurable_pos_simple_fn",
    ``∀m0 m1 f s e a. measure_space m0 ∧ measure_space m1 ∧
        pos_simple_fn (prod_measure_space m0 m1) f s e a ⇒
        (λx. pos_fn_integral m1 (x_fun_slice f x)) ∈
        measurable (m_space m0,measurable_sets m0) Borel``,
    rw[] >> irule (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM) >>
    fs[MEASURE_SPACE_SIGMA_ALGEBRA,space_def] >>
    map_every qexists_tac
        [`(λi x. Normal (a i) * pos_fn_integral m1 (indicator_fn (x_slice x (e i))))`,`s`] >> rw[]
    >- (drule_all_then assume_tac x_fun_slice_pos_simple_fn >>
        rw[pos_fn_integral_pos_simple_fn_as_sum])
    >- (irule IN_MEASURABLE_BOREL_CMUL >> fs[MEASURE_SPACE_SIGMA_ALGEBRA,space_def] >>
        map_every qexists_tac
            [`(λx. pos_fn_integral m1 (indicator_fn (x_slice x (e i))))`,`a i`] >>
        rw[GSYM x_fun_slice_indicator_fn] >>
        irule product_measure_space_x_fun_slice_fun_measurable_indicator_fn >>
        fs[pos_simple_fn_def])
    >- (fs[pos_simple_fn_def])
);

val product_measure_space_y_fun_slice_fun_measurable_pos_simple_fn = store_thm(
    "product_measure_space_y_fun_slice_fun_measurable_pos_simple_fn",
    ``∀m0 m1 f s e a. measure_space m0 ∧ measure_space m1 ∧
        pos_simple_fn (prod_measure_space m0 m1) f s e a ⇒
        (λy. pos_fn_integral m0 (y_fun_slice f y)) ∈
        measurable (m_space m1,measurable_sets m1) Borel``,
    rw[] >> irule (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM) >>
    fs[MEASURE_SPACE_SIGMA_ALGEBRA,space_def] >>
    map_every qexists_tac
        [`(λi y. Normal (a i) * pos_fn_integral m0 (indicator_fn (y_slice y (e i))))`,`s`] >> rw[]
    >- (drule_all_then assume_tac y_fun_slice_pos_simple_fn >>
        rw[pos_fn_integral_pos_simple_fn_as_sum])
    >- (irule IN_MEASURABLE_BOREL_CMUL >> fs[MEASURE_SPACE_SIGMA_ALGEBRA,space_def] >>
        map_every qexists_tac
            [`(λy. pos_fn_integral m0 (indicator_fn (y_slice y (e i))))`,`a i`] >>
        rw[GSYM y_fun_slice_indicator_fn] >>
        irule product_measure_space_y_fun_slice_fun_measurable_indicator_fn >>
        fs[pos_simple_fn_def])
    >- (fs[pos_simple_fn_def])
);

val product_measure_space_x_fun_slice_fun_measurable_pos_mbl_fn = store_thm(
    "product_measure_space_x_fun_slice_fun_measurable_pos_mbl_fn",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ (∀z. 0 ≤ f z) ∧
        f ∈ measurable (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel ⇒
        (λx. pos_fn_integral m1 (x_fun_slice f x)) ∈
        measurable (m_space m0,measurable_sets m0) Borel``,
    rw[] >> irule (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_MONO_SUP) >>
    `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    drule_all_then assume_tac measurable_sequence_pos >> fs[MEASURE_SPACE_SIGMA_ALGEBRA] >>
    qexists_tac `(λi x. pos_fn_integral m1 (x_fun_slice (fi i) x))` >> rw[space_def]
    >- ((qspecl_then [`m1`,`(x_fun_slice f x)`,`(λi. x_fun_slice (fi i) x)`] assume_tac)
            (INST_TYPE [alpha |-> ``:β``] lebesgue_monotone_convergence) >> rfs[] >>
        pop_assum irule >> rw[x_fun_slice_def] >> Q.ABBREV_TAC `y = x'` >> pop_assum kall_tac
        >- (qpat_x_assum `∀x. _` irule >> rw[m_space_prod_measure_space])
        >- (irule tonelli_1x >> rw[] >> qexists_tac `m0` >> rw[] >>
            irule IN_MEASURABLE_BOREL_POS_SIMPLE_FN >> rw[]))
    >- (irule pos_fn_integral_mono >> rw[x_fun_slice_def] >> fs[ext_mono_increasing_def])
    >- (irule product_measure_space_x_fun_slice_fun_measurable_pos_simple_fn >> rw[] >>
        qpat_x_assum `∀i:num. _` (qspec_then `n` assume_tac) >> fs[] >>
        map_every qexists_tac [`x`,`a`,`s`] >> rw[])
);

val product_measure_space_y_fun_slice_fun_measurable_pos_mbl_fn = store_thm(
    "product_measure_space_y_fun_slice_fun_measurable_pos_mbl_fn",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ (∀z. 0 ≤ f z) ∧
        f ∈ measurable (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel ⇒
        (λy. pos_fn_integral m0 (y_fun_slice f y)) ∈
        measurable (m_space m1,measurable_sets m1) Borel``,
    rw[] >> irule (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_MONO_SUP) >>
    `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    drule_all_then assume_tac measurable_sequence_pos >> fs[MEASURE_SPACE_SIGMA_ALGEBRA] >>
    qexists_tac `(λi y. pos_fn_integral m0 (y_fun_slice (fi i) y))` >> rw[space_def] >>
     Q.ABBREV_TAC `y = x` >> pop_assum kall_tac
    >- ((qspecl_then [`m0`,`(y_fun_slice f y)`,`(λi. y_fun_slice (fi i) y)`] assume_tac)
            lebesgue_monotone_convergence >> rfs[] >>
        pop_assum irule >> rw[y_fun_slice_def]
        >- (qpat_x_assum `∀x. _` irule >> rw[m_space_prod_measure_space])
        >- (irule tonelli_1y >> rw[] >> qexists_tac `m1` >> rw[] >>
            irule IN_MEASURABLE_BOREL_POS_SIMPLE_FN >> rw[]))
    >- (irule pos_fn_integral_mono >> rw[y_fun_slice_def] >> fs[ext_mono_increasing_def])
    >- (irule product_measure_space_y_fun_slice_fun_measurable_pos_simple_fn >> rw[] >>
        qpat_x_assum `∀i:num. _` (qspec_then `n` assume_tac) >> fs[] >>
        map_every qexists_tac [`x`,`a`,`s`] >> rw[])
);

(* Part Two of Tonelli *)

(*product_measure_space_x_fun_slice_fun_measurable*)
val tonelli_2x = store_thm(
    "tonelli_2x",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧
        f ∈ measurable (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel ⇒
        (λx. integral m1 (x_fun_slice f x)) ∈
        measurable (m_space m0,measurable_sets m0) Borel``,
    rw[integral_def] >> irule IN_MEASURABLE_BOREL_SUB >> fs[MEASURE_SPACE_SIGMA_ALGEBRA] >>
    map_every qexists_tac [`(λx. pos_fn_integral m1 (fn_plus (x_fun_slice f x)))`,
        `(λx. pos_fn_integral m1 (fn_minus (x_fun_slice f x)))`] >> rw[]
    >- (`∀x. fn_plus (x_fun_slice f x) = x_fun_slice (fn_plus f) x`
            by rw[FUN_EQ_THM,x_fun_slice_def,fn_plus_def] >>
        rw[] >> irule product_measure_space_x_fun_slice_fun_measurable_pos_mbl_fn >>
        rw[FN_PLUS_POS,IN_MEASURABLE_BOREL_FN_PLUS])
    >- (`∀x. fn_minus (x_fun_slice f x) = x_fun_slice (fn_minus f) x`
            by rw[FUN_EQ_THM,x_fun_slice_def,fn_minus_def] >>
        rw[] >> irule product_measure_space_x_fun_slice_fun_measurable_pos_mbl_fn >>
        rw[FN_MINUS_POS,IN_MEASURABLE_BOREL_FN_MINUS])
);

(*product_measure_space_y_fun_slice_fun_measurable*)
val tonelli_2y = store_thm(
    "tonelli_2y",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧
        f ∈ measurable (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel ⇒
        (λy. integral m0 (y_fun_slice f y)) ∈
        measurable (m_space m1,measurable_sets m1) Borel``,
    rw[integral_def] >> irule IN_MEASURABLE_BOREL_SUB >> fs[MEASURE_SPACE_SIGMA_ALGEBRA] >>
    map_every qexists_tac [`(λy. pos_fn_integral m0 (fn_plus (y_fun_slice f y)))`,
        `(λy. pos_fn_integral m0 (fn_minus (y_fun_slice f y)))`] >> rw[]
    >- (`∀y. fn_plus (y_fun_slice f y) = y_fun_slice (fn_plus f) y`
            by rw[FUN_EQ_THM,y_fun_slice_def,fn_plus_def] >>
        rw[] >> irule product_measure_space_y_fun_slice_fun_measurable_pos_mbl_fn >>
        rw[FN_PLUS_POS,IN_MEASURABLE_BOREL_FN_PLUS])
    >- (`∀y. fn_minus (y_fun_slice f y) = y_fun_slice (fn_minus f) y`
            by rw[FUN_EQ_THM,y_fun_slice_def,fn_minus_def] >>
        rw[] >> irule product_measure_space_y_fun_slice_fun_measurable_pos_mbl_fn >>
        rw[FN_MINUS_POS,IN_MEASURABLE_BOREL_FN_MINUS])
);

(* Halmos 36.A : 27.B *)

val prod_meas_zero_iff_x_slice_fun_zero_a_e = store_thm(
    "prod_meas_zero_iff_x_slice_fun_zero_a_e",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (a_e m0 {x | x_slice_fun m1 s x = 0} ⇔ (measure (prod_measure_space m0 m1) s = 0))``,
    rw[] >>
    drule_all_then assume_tac product_measure_space_x_slice_fun_measurable >>
    `(∀x. x ∈ m_space m0 ⇒ 0 ≤ x_slice_fun m1 s x)` by (rw[x_slice_fun_def] >>
        rw[GSYM N0_EQ_0,extreal_le_def] >>
        drule_all_then assume_tac product_measure_space_x_slice_measurable >>
        NTAC 2 (dxrule_then assume_tac MEASURE_SPACE_POSITIVE) >> fs[positive_def]) >>
    drule_all_then assume_tac integral_pos_eq_zero_iff_zero_a_e >>
    rw[] >> pop_assum kall_tac >>
    `(integral m0 (x_slice_fun m1 s) = 0) ⇔
        (Normal (measure (prod_measure_space m0 m1) s) = 0)`
        suffices_by (rw[] >> fs[GSYM N0_EQ_0]) >>
    rw[product_measure_space_normal_measure,x_slice_fun_alt,x_slice_def]
);

val prod_meas_zero_iff_y_slice_fun_zero_a_e = store_thm(
    "prod_meas_zero_iff_y_slice_fun_zero_a_e",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (a_e m1 {y | y_slice_fun m0 s y = 0} ⇔ (measure (prod_measure_space m0 m1) s = 0))``,
    rw[] >>
    `measure (prod_measure_space m0 m1) s = measure (prod_measure_space_hor m0 m1) s` by (
        fs[prod_measure_space_def,prod_measure_space_hor_def,measurable_sets_def,measure_def] >>
        irule (GSYM prod_measures_equiv_hor) >> rw[]) >>
    rw[] >> pop_assum kall_tac >>
    drule_all_then assume_tac product_measure_space_y_slice_fun_measurable >>
    `(∀y. y ∈ m_space m1 ⇒ 0 ≤ y_slice_fun m0 s y)` by (rw[y_slice_fun_def] >>
        rw[GSYM N0_EQ_0,extreal_le_def] >>
        drule_all_then assume_tac product_measure_space_y_slice_measurable >>
        NTAC 2 (dxrule_then assume_tac MEASURE_SPACE_POSITIVE) >> fs[positive_def]) >>
    drule_all_then assume_tac integral_pos_eq_zero_iff_zero_a_e >>
    rw[] >> pop_assum kall_tac >>
    `(integral m1 (y_slice_fun m0 s) = 0) ⇔
        (Normal (measure (prod_measure_space_hor m0 m1) s) = 0)`
        suffices_by (rw[] >> fs[GSYM N0_EQ_0]) >>
    `s ∈ measurable_sets (prod_measure_space_hor m0 m1)` by
        fs[measurable_sets_def,prod_measure_space_hor_def,prod_measure_space_def] >>
    rw[product_measure_space_hor_normal_measure,y_slice_fun_alt,y_slice_def]
);

(* Buildup to Part Three of Tonelli's *)

val integral_dA_eq_integral_dy_dx_indicator_fn = store_thm(
    "integral_dA_eq_integral_dy_dx_indicator_fn",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (integral (prod_measure_space m0 m1) (indicator_fn s) =
        integral m0 (λx. integral m1 (x_fun_slice (indicator_fn s) x)))``,
    rw[x_fun_slice_alt] >>
    `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    rw[integral_indicator,product_measure_space_normal_measure] >>
    irule integral_eq_fun_eq_mspace >> rw[GSYM x_slice_def] >>
    `(λy. indicator_fn s (x,y)) = indicator_fn (x_slice x s)`
        by rw[FUN_EQ_THM,indicator_fn_def,x_slice_def,PREIMAGE_def] >>
    `x_slice x s ∈ measurable_sets m1` by (irule product_measure_space_x_slice_measurable >>
        rw[] >> qexists_tac `m0` >> rw[]) >>
    rw[integral_indicator]
);

val integral_dA_eq_integral_dx_dy_indicator_fn = store_thm(
    "integral_dA_eq_integral_dx_dy_indicator_fn",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (integral (prod_measure_space m0 m1) (indicator_fn s) =
        integral m1 (λy. integral m0 (y_fun_slice (indicator_fn s) y)))``,
    rw[y_fun_slice_alt] >>
    `s ∈ measurable_sets (prod_measure_space_hor m0 m1)`
        by fs[prod_measure_space_def,prod_measure_space_hor_def,measurable_sets_def] >>
    `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    `measure_space (prod_measure_space_hor m0 m1)` by rw[prod_measure_space_hor_measure_space] >>
    rw[integral_indicator] >>
    `measure (prod_measure_space m0 m1) s = measure (prod_measure_space_hor m0 m1) s` by (
        fs[prod_measure_space_def,prod_measure_space_hor_def,measurable_sets_def,measure_def] >>
        irule (GSYM prod_measures_equiv_hor) >> rw[]) >>
    rw[product_measure_space_hor_normal_measure] >>
    irule integral_eq_fun_eq_mspace >> rw[GSYM y_slice_def] >>
    Q.RENAME_TAC [`y ∈ m_space m1`] >>
    `(λx. indicator_fn s (x,y)) = indicator_fn (y_slice y s)`
        by rw[FUN_EQ_THM,indicator_fn_def,y_slice_def,PREIMAGE_def] >>
    `y_slice y s ∈ measurable_sets m0` by (irule product_measure_space_y_slice_measurable >>
        rw[] >> qexists_tac `m1` >> rw[]) >>
    rw[integral_indicator]
);

val pos_fn_integral_dA_eq_pos_fn_integral_dy_dx_indicator_fn = store_thm(
    "pos_fn_integral_dA_eq_pos_fn_integral_dy_dx_indicator_fn",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (pos_fn_integral (prod_measure_space m0 m1) (indicator_fn s) =
        pos_fn_integral m0 (λx. pos_fn_integral m1 (x_fun_slice (indicator_fn s) x)))``,
    rw[x_fun_slice_alt] >>
    `pos_fn_integral (prod_measure_space m0 m1) (indicator_fn s) =
        integral (prod_measure_space m0 m1) (indicator_fn s)` by (irule (GSYM integral_pos_fn) >>
        rw[prod_measure_space_measure_space,indicator_fn_def,le_01,le_refl]) >>
    `pos_fn_integral m0 (λx. pos_fn_integral m1 (λy. indicator_fn s (x,y))) =
        integral m0 (λx. pos_fn_integral m1 (λy. indicator_fn s (x,y)))` by (
        irule (GSYM integral_pos_fn) >> rw[] >> irule pos_fn_integral_pos >>
        rw[prod_measure_space_measure_space,indicator_fn_def,le_01,le_refl]) >>
    `(λx. pos_fn_integral m1 (λy. indicator_fn s (x,y))) =
        (λx. integral m1 (λy. indicator_fn s (x,y)))` by (rw[FUN_EQ_THM] >>
        irule (GSYM integral_pos_fn) >>
        rw[prod_measure_space_measure_space,indicator_fn_def,le_01,le_refl]) >>
    fs[GSYM x_fun_slice_alt] >>
    rw[integral_dA_eq_integral_dy_dx_indicator_fn]
);

val pos_fn_integral_dA_eq_pos_fn_integral_dx_dy_indicator_fn = store_thm(
    "pos_fn_integral_dA_eq_pos_fn_integral_dx_dy_indicator_fn",
    ``∀m0 m1 s. measure_space m0 ∧ measure_space m1 ∧
        s ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        (pos_fn_integral (prod_measure_space m0 m1) (indicator_fn s) =
        pos_fn_integral m1 (λy. pos_fn_integral m0 (y_fun_slice (indicator_fn s) y)))``,
    rw[y_fun_slice_alt] >>
    `pos_fn_integral (prod_measure_space m0 m1) (indicator_fn s) =
        integral (prod_measure_space m0 m1) (indicator_fn s)` by (irule (GSYM integral_pos_fn) >>
        rw[prod_measure_space_measure_space,indicator_fn_def,le_01,le_refl]) >>
    `pos_fn_integral m1 (λy. pos_fn_integral m0 (λx. indicator_fn s (x,y))) =
        integral m1 (λy. pos_fn_integral m0 (λx. indicator_fn s (x,y)))` by (
        irule (GSYM integral_pos_fn) >> rw[] >> irule pos_fn_integral_pos >>
        rw[prod_measure_space_measure_space,indicator_fn_def,le_01,le_refl]) >>
    `(λy. pos_fn_integral m0 (λx. indicator_fn s (x,y))) =
        (λy. integral m0 (λx. indicator_fn s (x,y)))` by (rw[FUN_EQ_THM] >>
        irule (GSYM integral_pos_fn) >>
        rw[prod_measure_space_measure_space,indicator_fn_def,le_01,le_refl]) >>
    fs[GSYM y_fun_slice_alt] >>
    rw[integral_dA_eq_integral_dx_dy_indicator_fn]
);

val pos_fn_integral_dA_eq_pos_fn_integral_dy_dx_pos_simple_fn = store_thm(
    "pos_fn_integral_dA_eq_pos_fn_integral_dy_dx_pos_simple_fn",
    ``∀m0 m1 f s e a. measure_space m0 ∧ measure_space m1 ∧
        pos_simple_fn (prod_measure_space m0 m1) f s e a ⇒
        (pos_fn_integral (prod_measure_space m0 m1) f =
        pos_fn_integral m0 (λx. pos_fn_integral m1 (x_fun_slice f x)))``,
    rw[x_fun_slice_alt] >>
    `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    drule_all_then assume_tac pos_fn_integral_pos_simple_fn_as_sum >>
    rw[] >> NTAC 2 (pop_assum kall_tac) >>
    `∀x. x ∈ m_space m0 ⇒ pos_simple_fn m1 (λy. f (x,y)) s (λi. x_slice x (e i)) a` by (
        fs[pos_simple_fn_def] >> rw[]
        >- (qpat_x_assum `∀t. _` (qspec_then `(x,y)` assume_tac) >>
            rfs[m_space_prod_measure_space] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[] >>
            `indicator_fn (e x') (x,y) = indicator_fn (x_slice x (e x')) y`
                suffices_by (rw[] >> fs[]) >>
            rw[indicator_fn_def,x_slice_def,PREIMAGE_def])
        >- (irule product_measure_space_x_slice_measurable >> rw[] >>
            qexists_tac `m0` >> rw[])
        >- (`DISJOINT (e i) (e i')` by rw[] >>
            fs[DISJOINT_DEF,x_slice_def,PREIMAGE_def,EXTENSION])
        >- ((qspecl_then [`x`,`IMAGE e s`] assume_tac) (GSYM x_slice_bigunion) >>
            fs[GSYM IMAGE_COMPOSE,o_DEF] >>
            rw[m_space_prod_measure_space,x_slice_def,PREIMAGE_def,EXTENSION])) >>
    `∀x. x ∈ m_space m0 ⇒ (pos_fn_integral m1 (λy. f (x,y)) =
        SIGMA (λi. Normal (a i) * pos_fn_integral m1 (indicator_fn (x_slice x (e i)))) s)` by (
        rw[] >> qpat_x_assum `∀x. _` (qspec_then `x` assume_tac) >> rfs[] >>
        drule_all_then assume_tac pos_fn_integral_pos_simple_fn_as_sum >> rw[]) >>
    `∀x. 0 ≤ pos_fn_integral m1 (λy. f (x,y))` by (rw[] >> irule pos_fn_integral_pos >>
        rw[] >> fs[pos_simple_fn_def]) >>
    `∀x. 0 ≤ SIGMA (λi. Normal (a i) * pos_fn_integral m1 (indicator_fn (x_slice x (e i)))) s` by (
        rw[] >> irule EXTREAL_SUM_IMAGE_POS >> fs[pos_simple_fn_def] >> rw[] >>
        irule le_mul >> rw[GSYM N0_EQ_0,extreal_le_def] >> rw[N0_EQ_0] >>
        irule pos_fn_integral_pos >> rw[indicator_fn_def,le_01,le_refl]) >>
    `pos_fn_integral m0 (λx. pos_fn_integral m1 (λy. f (x,y))) =
        pos_fn_integral m0 (λx. SIGMA (λi. Normal (a i) *
        pos_fn_integral m1 (indicator_fn (x_slice x (e i)))) s)`
        by (irule pos_fn_integral_eq_fun_eq_mspace >> rw[]) >>
    rw[] >> pop_assum kall_tac >>
    Q.ABBREV_TAC `g = (λi x. Normal (a i) * pos_fn_integral m1 (indicator_fn (x_slice x (e i))))` >>
    `pos_fn_integral m0 (λx. SIGMA (λi. g i x) s) = SIGMA (λi. pos_fn_integral m0 (g i)) s` by (
        irule pos_fn_integral_sum >> fs[pos_simple_fn_def] >> Q.UNABBREV_TAC `g` >> rw[]
        >- (irule le_mul >> rw[GSYM N0_EQ_0,extreal_le_def] >> rw[N0_EQ_0] >>
            irule pos_fn_integral_pos >> rw[indicator_fn_def,le_01,le_refl])
        >- (irule IN_MEASURABLE_BOREL_CMUL >> rw[MEASURE_SPACE_SIGMA_ALGEBRA,space_def] >>
            map_every qexists_tac
                [`(λx. pos_fn_integral m1 (indicator_fn (x_slice x (e i))))`,`a i`] >> rw[] >>
            `(λx. pos_fn_integral m1 (indicator_fn (x_slice x (e i)))) = x_slice_fun m1 (e i)` by (
                rw[FUN_EQ_THM,x_slice_fun_alt] >> irule pos_fn_integral_indicator >> rw[] >>
                irule product_measure_space_x_slice_measurable >> rw[] >>
                qexists_tac `m0` >> rw[]) >>
            rw[] >> irule product_measure_space_x_slice_fun_measurable >> rw[])) >>
    Q.UNABBREV_TAC `g` >> fs[] >> NTAC 3 (pop_assum kall_tac) >>
    irule EXTREAL_SUM_IMAGE_EQ >> fs[pos_simple_fn_def] >> rw[] >> Q.RENAME_TAC [`z ∈ s`] >>
    `pos_fn_integral m0 (λx. Normal (a z) *
        (λx. pos_fn_integral m1 (indicator_fn (x_slice x (e z)))) x) =
        Normal (a z) * pos_fn_integral m0
        (λx. pos_fn_integral m1 (indicator_fn (x_slice x (e z))))` by (
        irule pos_fn_integral_cmul >> rw[] >>
        irule pos_fn_integral_pos >> rw[indicator_fn_def,le_01,le_refl]) >>
    fs[GSYM x_fun_slice_alt,pos_fn_integral_dA_eq_pos_fn_integral_dy_dx_indicator_fn] >>
    fs[x_fun_slice_alt] >>
    `(λx. pos_fn_integral m1 (λy. indicator_fn (e z) (x,y))) =
        (λx. pos_fn_integral m1 (indicator_fn (x_slice x (e z))))` suffices_by (rw[] >> fs[]) >>
    rw[FUN_EQ_THM] >>
    `(λy. indicator_fn (e z) (x,y)) = (indicator_fn (x_slice x (e z)))` suffices_by (rw[] >> fs[]) >>
    rw[FUN_EQ_THM,indicator_fn_def,x_slice_def,PREIMAGE_def]
);

val pos_fn_integral_dA_eq_pos_fn_integral_dx_dy_pos_simple_fn = store_thm(
    "pos_fn_integral_dA_eq_pos_fn_integral_dx_dy_pos_simple_fn",
    ``∀m0 m1 f s e a. measure_space m0 ∧ measure_space m1 ∧
        pos_simple_fn (prod_measure_space m0 m1) f s e a ⇒
        (pos_fn_integral (prod_measure_space m0 m1) f =
        pos_fn_integral m1 (λy. pos_fn_integral m0 (y_fun_slice f y)))``,
    rw[y_fun_slice_alt] >>
    `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    drule_all_then assume_tac pos_fn_integral_pos_simple_fn_as_sum >>
    rw[] >> NTAC 2 (pop_assum kall_tac) >>
    `∀y. y ∈ m_space m1 ⇒ pos_simple_fn m0 (λx. f (x,y)) s (λi. y_slice y (e i)) a` by (
        fs[pos_simple_fn_def] >> rw[]
        >- (qpat_x_assum `∀t. _` (qspec_then `(x',y)` assume_tac) >>
            rfs[m_space_prod_measure_space] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[] >>
            `indicator_fn (e x) (x',y) = indicator_fn (y_slice y (e x)) x'`
                suffices_by (rw[] >> fs[]) >>
            rw[indicator_fn_def,y_slice_def,PREIMAGE_def])
        >- (irule product_measure_space_y_slice_measurable >> rw[] >>
            qexists_tac `m1` >> rw[])
        >- (`DISJOINT (e i) (e i')` by rw[] >>
            fs[DISJOINT_DEF,y_slice_def,PREIMAGE_def,EXTENSION])
        >- ((qspecl_then [`y`,`IMAGE e s`] assume_tac)
                (INST_TYPE [alpha |-> ``:β``,beta |-> ``:α``] (GSYM y_slice_bigunion)) >>
            fs[GSYM IMAGE_COMPOSE,o_DEF] >>
            rw[m_space_prod_measure_space,y_slice_def,PREIMAGE_def,EXTENSION])) >>
    `∀y. y ∈ m_space m1 ⇒ (pos_fn_integral m0 (λx. f (x,y)) =
        SIGMA (λi. Normal (a i) * pos_fn_integral m0 (indicator_fn (y_slice y (e i)))) s)` by (
        rw[] >> qpat_x_assum `∀y. _` (qspec_then `y` assume_tac) >> rfs[] >>
        drule_all_then assume_tac pos_fn_integral_pos_simple_fn_as_sum >> rw[]) >>
    `∀y. 0 ≤ pos_fn_integral m0 (λx. f (x,y))` by (rw[] >> irule pos_fn_integral_pos >>
        rw[] >> fs[pos_simple_fn_def]) >>
    `∀y. 0 ≤ SIGMA (λi. Normal (a i) * pos_fn_integral m0 (indicator_fn (y_slice y (e i)))) s` by (
        rw[] >> irule EXTREAL_SUM_IMAGE_POS >> fs[pos_simple_fn_def] >> rw[] >>
        irule le_mul >> rw[GSYM N0_EQ_0,extreal_le_def] >> rw[N0_EQ_0] >>
        irule pos_fn_integral_pos >> rw[indicator_fn_def,le_01,le_refl]) >>
    `pos_fn_integral m1 (λy. pos_fn_integral m0 (λx. f (x,y))) =
        pos_fn_integral m1 (λy. SIGMA (λi. Normal (a i) *
        pos_fn_integral m0 (indicator_fn (y_slice y (e i)))) s)`
        by (irule pos_fn_integral_eq_fun_eq_mspace >> rw[]) >>
    rw[] >> pop_assum kall_tac >>
    Q.ABBREV_TAC `g = (λi y. Normal (a i) * pos_fn_integral m0 (indicator_fn (y_slice y (e i))))` >>
    `pos_fn_integral m1 (λy. SIGMA (λi. g i y) s) = SIGMA (λi. pos_fn_integral m1 (g i)) s` by (
        irule pos_fn_integral_sum >> fs[pos_simple_fn_def] >> Q.UNABBREV_TAC `g` >> rw[]
        >- (irule le_mul >> rw[GSYM N0_EQ_0,extreal_le_def] >> rw[N0_EQ_0] >>
            irule pos_fn_integral_pos >> rw[indicator_fn_def,le_01,le_refl])
        >- (irule IN_MEASURABLE_BOREL_CMUL >> rw[MEASURE_SPACE_SIGMA_ALGEBRA,space_def] >>
            map_every qexists_tac
                [`(λy. pos_fn_integral m0 (indicator_fn (y_slice y (e i))))`,`a i`] >> rw[] >>
            `(λy. pos_fn_integral m0 (indicator_fn (y_slice y (e i)))) = y_slice_fun m0 (e i)` by (
                rw[FUN_EQ_THM,y_slice_fun_alt] >> irule pos_fn_integral_indicator >> rw[] >>
                irule product_measure_space_y_slice_measurable >> rw[] >>
                qexists_tac `m1` >> rw[]) >>
            rw[] >> irule product_measure_space_y_slice_fun_measurable >> rw[])) >>
    Q.UNABBREV_TAC `g` >> fs[] >> NTAC 3 (pop_assum kall_tac) >>
    irule EXTREAL_SUM_IMAGE_EQ >> fs[pos_simple_fn_def] >> rw[] >> Q.RENAME_TAC [`z ∈ s`] >>
    `pos_fn_integral m1 (λy. Normal (a z) *
        (λy. pos_fn_integral m0 (indicator_fn (y_slice y (e z)))) y) =
        Normal (a z) * pos_fn_integral m1
        (λy. pos_fn_integral m0 (indicator_fn (y_slice y (e z))))` by (
        irule pos_fn_integral_cmul >> rw[] >>
        irule pos_fn_integral_pos >> rw[indicator_fn_def,le_01,le_refl]) >>
    fs[GSYM y_fun_slice_alt,pos_fn_integral_dA_eq_pos_fn_integral_dx_dy_indicator_fn] >>
    fs[y_fun_slice_alt] >>
    `(λy. pos_fn_integral m0 (λx. indicator_fn (e z) (x,y))) =
        (λy. pos_fn_integral m0 (indicator_fn (y_slice y (e z))))` suffices_by (rw[] >> fs[]) >>
    rw[FUN_EQ_THM] >>
    `(λx. indicator_fn (e z) (x,y)) = (indicator_fn (y_slice y (e z)))` suffices_by (rw[] >> fs[]) >>
    rw[FUN_EQ_THM,indicator_fn_def,y_slice_def,PREIMAGE_def]
);

(* Halmos 36.B (aka Tonelli Part Three) : 20.B 27.B 35.B *)

(*pos_fn_integral_dA_eq_pos_fn_integral_dy_dx_pos_mbl_fn*)
val tonelli_3x = store_thm(
    "tonelli_3x",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ (∀z. 0 ≤ f z) ∧
        f ∈ measurable (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel ⇒
        (pos_fn_integral (prod_measure_space m0 m1) f =
        pos_fn_integral m0 (λx. pos_fn_integral m1 (x_fun_slice f x)))``,
    rw[] >> `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    drule_all_then assume_tac measurable_sequence_pos >> fs[] >>
    `∀x. x ∈ m_space m0 ⇒ (pos_fn_integral m1 (x_fun_slice f x) = sup
        (IMAGE (λi. pos_fn_integral m1 ((λi. x_fun_slice (fi i) x) i)) 𝕌(:num)))` by (
        NTAC 2 strip_tac >> irule lebesgue_monotone_convergence >> rw[] >>
        Q.ABBREV_TAC `y = x'` >> pop_assum kall_tac >> fs[ext_mono_increasing_def,x_fun_slice_def]
        >- (qpat_x_assum `∀x. _` irule >> rw[m_space_prod_measure_space])
        >- (irule tonelli_1x >> rw[] >> qexists_tac `m0` >> rw[] >>
            irule IN_MEASURABLE_BOREL_POS_SIMPLE_FN >> rw[])) >>
    `pos_fn_integral m0 (λx. pos_fn_integral m1 (x_fun_slice f x)) = pos_fn_integral m0
        (λx. (sup (IMAGE (λi. pos_fn_integral m1 ((λi. x_fun_slice (fi i) x) i)) 𝕌(:num))))` by (
        irule pos_fn_integral_eq_fun_eq_mspace >> rw[]
        >- (irule pos_fn_integral_pos >> rw[x_fun_slice_def])
        >- (rw[le_sup] >>
            pop_assum (qspec_then `pos_fn_integral m1 (x_fun_slice (fi 0) x)` assume_tac) >>
            `pos_fn_integral m1 (x_fun_slice (fi 0) x) ≤ y` by (pop_assum irule >>
                qexists_tac `0` >> rw[]) >>
            `0 ≤ pos_fn_integral m1 (x_fun_slice (fi 0) x)` suffices_by (rw[] >> imp_res_tac le_trans) >>
            irule pos_fn_integral_pos >> rw[x_fun_slice_def])) >> fs[] >>
    `pos_fn_integral m0 (λx. sup (IMAGE (λi. pos_fn_integral m1 (x_fun_slice (fi i) x)) 𝕌(:num))) =
        sup (IMAGE (λi. pos_fn_integral m0
        ((λi. (λx. pos_fn_integral m1 (x_fun_slice (fi i) x))) i)) 𝕌(:num))` by (
        irule lebesgue_monotone_convergence >> rw[]
        >- (fs[ext_mono_increasing_def] >> rw[] >> irule pos_fn_integral_mono >>
            rw[x_fun_slice_def])
        >- (rw[le_sup] >>
            pop_assum (qspec_then `pos_fn_integral m1 (x_fun_slice (fi 0) x)` assume_tac) >>
            `pos_fn_integral m1 (x_fun_slice (fi 0) x) ≤ y` by (pop_assum irule >>
                qexists_tac `0` >> rw[]) >>
            `0 ≤ pos_fn_integral m1 (x_fun_slice (fi 0) x)` suffices_by (rw[] >> imp_res_tac le_trans) >>
            irule pos_fn_integral_pos >> rw[x_fun_slice_def])
        >- (irule pos_fn_integral_pos >> rw[x_fun_slice_def])
        >- (irule product_measure_space_x_fun_slice_fun_measurable_pos_simple_fn >> rw[] >>
            qpat_x_assum `∀i:num. _` (qspec_then `i` assume_tac) >> fs[] >>
            map_every qexists_tac [`x`,`a`,`s`] >> rw[])) >> rw[] >>
    `IMAGE (λi. pos_fn_integral (prod_measure_space m0 m1) (fi i)) 𝕌(:num) =
        IMAGE (λi. pos_fn_integral m0 (λx. pos_fn_integral m1 (x_fun_slice (fi i) x))) 𝕌(:num)`
        suffices_by (rw[] >> fs[]) >>
    irule IMAGE_CONG >> rw[] >>
    irule pos_fn_integral_dA_eq_pos_fn_integral_dy_dx_pos_simple_fn >> rw[] >>
    qpat_x_assum `∀i:num. _` (qspec_then `x` assume_tac) >> fs[] >>
    map_every qexists_tac [`x'`,`a`,`s`] >> rw[]
);

(*pos_fn_integral_dA_eq_pos_fn_integral_dx_dy_pos_mbl_fn*)
val tonelli_3y = store_thm(
    "tonelli_3y",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ (∀z. 0 ≤ f z) ∧
        f ∈ measurable (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel ⇒
        (pos_fn_integral (prod_measure_space m0 m1) f =
        pos_fn_integral m1 (λy. pos_fn_integral m0 (y_fun_slice f y)))``,
    rw[] >> `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    drule_all_then assume_tac measurable_sequence_pos >> fs[] >>
    `∀y. y ∈ m_space m1 ⇒ (pos_fn_integral m0 (y_fun_slice f y) = sup
        (IMAGE (λi. pos_fn_integral m0 ((λi. y_fun_slice (fi i) y) i)) 𝕌(:num)))` by (
        NTAC 2 strip_tac >> irule lebesgue_monotone_convergence >> rw[] >>
        fs[ext_mono_increasing_def,y_fun_slice_def]
        >- (qpat_x_assum `∀x. _` irule >> rw[m_space_prod_measure_space])
        >- (irule tonelli_1y >> rw[] >> qexists_tac `m1` >> rw[] >>
            irule IN_MEASURABLE_BOREL_POS_SIMPLE_FN >> rw[])) >>
    `pos_fn_integral m1 (λy. pos_fn_integral m0 (y_fun_slice f y)) = pos_fn_integral m1
        (λy. (sup (IMAGE (λi. pos_fn_integral m0 ((λi. y_fun_slice (fi i) y) i)) 𝕌(:num))))` by (
        irule pos_fn_integral_eq_fun_eq_mspace >> rw[]
        >- (irule pos_fn_integral_pos >> rw[y_fun_slice_def])
        >- (rw[le_sup] >>
            pop_assum (qspec_then `pos_fn_integral m0 (y_fun_slice (fi 0) x)` assume_tac) >>
            `pos_fn_integral m0 (y_fun_slice (fi 0) x) ≤ y` by (pop_assum irule >>
                qexists_tac `0` >> rw[]) >>
            `0 ≤ pos_fn_integral m0 (y_fun_slice (fi 0) x)` suffices_by (rw[] >> imp_res_tac le_trans) >>
            irule pos_fn_integral_pos >> rw[y_fun_slice_def])) >> fs[] >>
    `pos_fn_integral m1 (λy. sup (IMAGE (λi. pos_fn_integral m0 (y_fun_slice (fi i) y)) 𝕌(:num))) =
        sup (IMAGE (λi. pos_fn_integral m1
        ((λi. (λy. pos_fn_integral m0 (y_fun_slice (fi i) y))) i)) 𝕌(:num))` by (
        irule lebesgue_monotone_convergence >> rw[]
        >- (fs[ext_mono_increasing_def] >> rw[] >> irule pos_fn_integral_mono >>
            rw[y_fun_slice_def])
        >- (rw[le_sup] >>
            pop_assum (qspec_then `pos_fn_integral m0 (y_fun_slice (fi 0) x)` assume_tac) >>
            `pos_fn_integral m0 (y_fun_slice (fi 0) x) ≤ y` by (pop_assum irule >>
                qexists_tac `0` >> rw[]) >>
            `0 ≤ pos_fn_integral m0 (y_fun_slice (fi 0) x)` suffices_by (rw[] >> imp_res_tac le_trans) >>
            irule pos_fn_integral_pos >> rw[y_fun_slice_def])
        >- (irule pos_fn_integral_pos >> rw[y_fun_slice_def])
        >- (irule product_measure_space_y_fun_slice_fun_measurable_pos_simple_fn >> rw[] >>
            qpat_x_assum `∀i:num. _` (qspec_then `i` assume_tac) >> fs[] >>
            map_every qexists_tac [`x`,`a`,`s`] >> rw[])) >> rw[] >>
    `IMAGE (λi. pos_fn_integral (prod_measure_space m0 m1) (fi i)) 𝕌(:num) =
        IMAGE (λi. pos_fn_integral m1 (λy. pos_fn_integral m0 (y_fun_slice (fi i) y))) 𝕌(:num)`
        suffices_by (rw[] >> fs[]) >>
    irule IMAGE_CONG >> rw[] >>
    irule pos_fn_integral_dA_eq_pos_fn_integral_dx_dy_pos_simple_fn >> rw[] >>
    qpat_x_assum `∀i:num. _` (qspec_then `x` assume_tac) >> fs[] >>
    map_every qexists_tac [`x'`,`a`,`s`] >> rw[]
);

(********************)
(* Fubini's Theorem *)
(********************)

val fubini_1x = store_thm(
    "fubini_1x",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ integrable (prod_measure_space m0 m1) f ⇒
        a_e m0 {x | integrable m1 (x_fun_slice f x)}``,
    rw[a_e_def,integrable_def] >>
    map_every (fn tm => (qspecl_then [`m0`,`m1`,tm] assume_tac) tonelli_3x)
        [`fn_plus f`,`fn_minus f`] >>
    rfs[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    fs[x_fun_slice_fn_plus,x_fun_slice_fn_minus] >> NTAC 2 (pop_assum kall_tac) >>
    map_every Q.ABBREV_TAC [`ipf = (λx. pos_fn_integral m1 (fn_plus (x_fun_slice f x)))`,
        `imf = (λx. pos_fn_integral m1 (fn_minus (x_fun_slice f x)))`] >>
    `integrable m0 ipf` by ((qspecl_then [`m0`,`ipf`] assume_tac) integrable_pos >> rfs[] >>
        `(∀x. 0 ≤ ipf x) ∧ ipf ∈ measurable (m_space m0,measurable_sets m0) Borel`
            suffices_by (rw[] >> fs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `ipf` >> rw[]
        >- (irule pos_fn_integral_pos >> rw[FN_PLUS_POS]) >>
        `(λx. pos_fn_integral m1 (fn_plus (x_fun_slice f x))) =
            (λx. integral m1 (x_fun_slice (fn_plus f) x))` by (rw[FUN_EQ_THM,x_fun_slice_fn_plus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_PLUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2x >> rw[IN_MEASURABLE_BOREL_FN_PLUS]) >>
    `integrable m0 imf` by ((qspecl_then [`m0`,`imf`] assume_tac) integrable_pos >> rfs[] >>
        `(∀x. 0 ≤ imf x) ∧ imf ∈ measurable (m_space m0,measurable_sets m0) Borel`
            suffices_by (rw[] >> fs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `imf` >> rw[]
        >- (irule pos_fn_integral_pos >> rw[FN_MINUS_POS]) >>
        `(λx. pos_fn_integral m1 (fn_minus (x_fun_slice f x))) =
            (λx. integral m1 (x_fun_slice (fn_minus f) x))` by (rw[FUN_EQ_THM,x_fun_slice_fn_minus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_MINUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2x >> rw[IN_MEASURABLE_BOREL_FN_MINUS]) >>
    `null_set m0 {x | x ∈ m_space m0 ∧ (ipf x = PosInf)}` by rw[integrable_infty_null] >>
    `null_set m0 {x | x ∈ m_space m0 ∧ (imf x = PosInf)}` by rw[integrable_infty_null] >> fs[] >>
    `(m_space m0 DIFF {x | x_fun_slice f x ∈ measurable (m_space m1,measurable_sets m1) Borel ∧
        ipf x ≠ PosInf ∧ imf x ≠ PosInf}) = {x | x ∈ m_space m0 ∧ (ipf x = PosInf)} ∪
        {x | x ∈ m_space m0 ∧ (imf x = PosInf)}` by (rw[EXTENSION] >>
        Cases_on `x ∈ m_space m0` >> rw[] >>
        drule_all_then assume_tac (INST_TYPE [gamma |-> ``:extreal``] tonelli_1x) >> rw[]) >>
    rw[] >> pop_assum kall_tac >> fs[null_set_def] >>
    map_every Q.ABBREV_TAC [`ipfs = {x | x ∈ m_space m0 ∧ (ipf x = PosInf)}`,
        `imfs = {x | x ∈ m_space m0 ∧ (imf x = PosInf)}`] >>
    `ipfs ∪ imfs ∈ measurable_sets m0` by rw[MEASURE_SPACE_UNION] >> rw[] >>
    (qspecl_then [`m0`,`ipfs`,`imfs`,`ipfs ∪ imfs`] assume_tac) SUBADDITIVE >>
    rfs[MEASURE_SPACE_SUBADDITIVE] >>
    `positive m0` by rw[ MEASURE_SPACE_POSITIVE] >> fs[positive_def] >>
    pop_assum (drule_then assume_tac) >> rw[GSYM REAL_LE_ANTISYM]
);

val fubini_1y = store_thm(
    "fubini_1y",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ integrable (prod_measure_space m0 m1) f ⇒
        a_e m1 {y | integrable m0 (y_fun_slice f y)}``,
    rw[a_e_def,integrable_def] >>
    map_every (fn tm => (qspecl_then [`m0`,`m1`,tm] assume_tac) tonelli_3y)
        [`fn_plus f`,`fn_minus f`] >>
    rfs[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    fs[y_fun_slice_fn_plus,y_fun_slice_fn_minus] >> NTAC 2 (pop_assum kall_tac) >>
    map_every Q.ABBREV_TAC [`ipf = (λy. pos_fn_integral m0 (fn_plus (y_fun_slice f y)))`,
        `imf = (λy. pos_fn_integral m0 (fn_minus (y_fun_slice f y)))`] >>
    `integrable m1 ipf` by (
        (qspecl_then [`m1`,`ipf`] assume_tac) (INST_TYPE [alpha |-> ``:β``] integrable_pos) >> rfs[] >>
        `(∀y. 0 ≤ ipf y) ∧ ipf ∈ measurable (m_space m1,measurable_sets m1) Borel`
            suffices_by (rw[] >> fs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `ipf` >> rw[]
        >- (irule pos_fn_integral_pos >> rw[FN_PLUS_POS]) >>
        `(λy. pos_fn_integral m0 (fn_plus (y_fun_slice f y))) =
            (λy. integral m0 (y_fun_slice (fn_plus f) y))` by (rw[FUN_EQ_THM,y_fun_slice_fn_plus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_PLUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2y >> rw[IN_MEASURABLE_BOREL_FN_PLUS]) >>
    `integrable m1 imf` by (
        (qspecl_then [`m1`,`imf`] assume_tac) (INST_TYPE [alpha |-> ``:β``] integrable_pos) >> rfs[] >>
        `(∀y. 0 ≤ imf y) ∧ imf ∈ measurable (m_space m1,measurable_sets m1) Borel`
            suffices_by (rw[] >> fs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `imf` >> rw[]
        >- (irule pos_fn_integral_pos >> rw[FN_MINUS_POS]) >>
        `(λy. pos_fn_integral m0 (fn_minus (y_fun_slice f y))) =
            (λy. integral m0 (y_fun_slice (fn_minus f) y))` by (rw[FUN_EQ_THM,y_fun_slice_fn_minus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_MINUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2y >> rw[IN_MEASURABLE_BOREL_FN_MINUS]) >>
    `null_set m1 {y | y ∈ m_space m1 ∧ (ipf y = PosInf)}` by rw[integrable_infty_null] >>
    `null_set m1 {y | y ∈ m_space m1 ∧ (imf y = PosInf)}` by rw[integrable_infty_null] >> fs[] >>
    `(m_space m1 DIFF {y | y_fun_slice f y ∈ measurable (m_space m0,measurable_sets m0) Borel ∧
        ipf y ≠ PosInf ∧ imf y ≠ PosInf}) = {y | y ∈ m_space m1 ∧ (ipf y = PosInf)} ∪
        {y | y ∈ m_space m1 ∧ (imf y = PosInf)}` by (rw[EXTENSION] >>
        Q.RENAME_TAC [`y ∈ _ ∧ _ ⇔ _`] >> Cases_on `y ∈ m_space m1` >> rw[] >>
        drule_all_then assume_tac (INST_TYPE [gamma |-> ``:extreal``] tonelli_1y) >> rw[]) >>
    rw[] >> pop_assum kall_tac >> fs[null_set_def] >>
    map_every Q.ABBREV_TAC [`ipfs = {y | y ∈ m_space m1 ∧ (ipf y = PosInf)}`,
        `imfs = {y | y ∈ m_space m1 ∧ (imf y = PosInf)}`] >>
    `ipfs ∪ imfs ∈ measurable_sets m1` by rw[MEASURE_SPACE_UNION] >> rw[] >>
    (qspecl_then [`m1`,`ipfs`,`imfs`,`ipfs ∪ imfs`] assume_tac)
        (INST_TYPE [alpha |-> ``:β``] SUBADDITIVE) >>
    rfs[MEASURE_SPACE_SUBADDITIVE] >>
    `positive m1` by rw[ MEASURE_SPACE_POSITIVE] >> fs[positive_def] >>
    pop_assum (drule_then assume_tac) >> rw[GSYM REAL_LE_ANTISYM]
);

val fubini_2x = store_thm(
    "fubini_2x",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ integrable (prod_measure_space m0 m1) f ⇒
        integrable m0 (λx. integral m1 (x_fun_slice f x))``,
    rw[integrable_def]
    >- (fs[tonelli_2x]) >>
    map_every (fn tm => (qspecl_then [`m0`,`m1`,tm] assume_tac) tonelli_3x)
        [`fn_plus f`,`fn_minus f`] >>
    rfs[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >> rw[integral_def] >>
    fs[x_fun_slice_fn_plus,x_fun_slice_fn_minus] >>
    map_every Q.ABBREV_TAC [`ipf = (λx. pos_fn_integral m1 (fn_plus (x_fun_slice f x)))`,
        `imf = (λx. pos_fn_integral m1 (fn_minus (x_fun_slice f x)))`] >>
    `integrable m0 ipf` by ((qspecl_then [`m0`,`ipf`] assume_tac) integrable_pos >> rfs[] >>
        `(∀x. 0 ≤ ipf x) ∧ ipf ∈ measurable (m_space m0,measurable_sets m0) Borel`
            suffices_by (rw[] >> fs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `ipf` >> rw[]
        >- (irule pos_fn_integral_pos >> rw[FN_PLUS_POS]) >>
        `(λx. pos_fn_integral m1 (fn_plus (x_fun_slice f x))) =
            (λx. integral m1 (x_fun_slice (fn_plus f) x))` by (rw[FUN_EQ_THM,x_fun_slice_fn_plus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_PLUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2x >> rw[IN_MEASURABLE_BOREL_FN_PLUS]) >>
    `integrable m0 imf` by ((qspecl_then [`m0`,`imf`] assume_tac) integrable_pos >> rfs[] >>
        `(∀x. 0 ≤ imf x) ∧ imf ∈ measurable (m_space m0,measurable_sets m0) Borel`
            suffices_by (rw[] >> fs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `imf` >> rw[]
        >- (irule pos_fn_integral_pos >> rw[FN_MINUS_POS]) >>
        `(λx. pos_fn_integral m1 (fn_minus (x_fun_slice f x))) =
            (λx. integral m1 (x_fun_slice (fn_minus f) x))` by (rw[FUN_EQ_THM,x_fun_slice_fn_minus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_MINUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2x >> rw[IN_MEASURABLE_BOREL_FN_MINUS]) >>
    `integrable m0 (λx. ipf x − imf x)` by rw[integrable_sub] >>
    map_every Q.UNABBREV_TAC [`ipf`,`imf`] >> fs[integrable_def]
);

val fubini_2y = store_thm(
    "fubini_2y",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ integrable (prod_measure_space m0 m1) f ⇒
        integrable m1 (λy. integral m0 (y_fun_slice f y))``,
    rw[integrable_def]
    >- (fs[tonelli_2y]) >>
    map_every (fn tm => (qspecl_then [`m0`,`m1`,tm] assume_tac) tonelli_3y)
        [`fn_plus f`,`fn_minus f`] >>
    rfs[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >> rw[integral_def] >>
    fs[y_fun_slice_fn_plus,y_fun_slice_fn_minus] >>
    map_every Q.ABBREV_TAC [`ipf = (λy. pos_fn_integral m0 (fn_plus (y_fun_slice f y)))`,
        `imf = (λy. pos_fn_integral m0 (fn_minus (y_fun_slice f y)))`] >>
    `integrable m1 ipf` by (
        (qspecl_then [`m1`,`ipf`] assume_tac) (INST_TYPE [alpha |-> ``:β``] integrable_pos) >> rfs[] >>
        `(∀y. 0 ≤ ipf y) ∧ ipf ∈ measurable (m_space m1,measurable_sets m1) Borel`
            suffices_by (rw[] >> fs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `ipf` >> rw[]
        >- (irule pos_fn_integral_pos >> rw[FN_PLUS_POS]) >>
        `(λy. pos_fn_integral m0 (fn_plus (y_fun_slice f y))) =
            (λy. integral m0 (y_fun_slice (fn_plus f) y))` by (rw[FUN_EQ_THM,y_fun_slice_fn_plus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_PLUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2y >> rw[IN_MEASURABLE_BOREL_FN_PLUS]) >>
    `integrable m1 imf` by (
        (qspecl_then [`m1`,`imf`] assume_tac) (INST_TYPE [alpha |-> ``:β``] integrable_pos) >> rfs[] >>
        `(∀y. 0 ≤ imf y) ∧ imf ∈ measurable (m_space m1,measurable_sets m1) Borel`
            suffices_by (rw[] >> fs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `imf` >> rw[]
        >- (irule pos_fn_integral_pos >> rw[FN_MINUS_POS]) >>
        `(λy. pos_fn_integral m0 (fn_minus (y_fun_slice f y))) =
            (λy. integral m0 (y_fun_slice (fn_minus f) y))` by (rw[FUN_EQ_THM,y_fun_slice_fn_minus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_MINUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2y >> rw[IN_MEASURABLE_BOREL_FN_MINUS]) >>
    `integrable m1 (λy. ipf y − imf y)` by rw[integrable_sub] >>
    map_every Q.UNABBREV_TAC [`ipf`,`imf`] >> fs[integrable_def]
);

(* Halmos 36.C : 36.B *)

val fubini_3x = store_thm(
    "fubini_3x",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ integrable (prod_measure_space m0 m1) f ⇒
        (integral (prod_measure_space m0 m1) f = integral m0 (λx. integral m1 (x_fun_slice f x)))``,
    rw[integral_def,integrable_def] >>
    map_every (fn tm => (qspecl_then [`m0`,`m1`,tm] assume_tac) tonelli_3x)
        [`fn_plus f`,`fn_minus f`] >>
    rfs[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >> rw[integral_def] >>
    fs[x_fun_slice_fn_plus,x_fun_slice_fn_minus] >>
    map_every Q.ABBREV_TAC [`ipf = (λx. pos_fn_integral m1 (fn_plus (x_fun_slice f x)))`,
        `imf = (λx. pos_fn_integral m1 (fn_minus (x_fun_slice f x)))`] >>
    `∀x. 0 ≤ ipf x` by (Q.UNABBREV_TAC `ipf` >> rw[] >>
        irule pos_fn_integral_pos >> rw[FN_PLUS_POS]) >>
    `∀x. 0 ≤ imf x` by (Q.UNABBREV_TAC `imf` >> rw[] >>
        irule pos_fn_integral_pos >> rw[FN_MINUS_POS]) >>
    `integrable m0 ipf` by (rw[integrable_pos] >> Q.UNABBREV_TAC `ipf` >>
        `(λx. pos_fn_integral m1 (fn_plus (x_fun_slice f x))) =
            (λx. integral m1 (x_fun_slice (fn_plus f) x))` by (rw[FUN_EQ_THM,x_fun_slice_fn_plus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_PLUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2x >> rw[IN_MEASURABLE_BOREL_FN_PLUS]) >>
    `integrable m0 imf` by (rw[integrable_pos] >> Q.UNABBREV_TAC `imf` >>
        `(λx. pos_fn_integral m1 (fn_minus (x_fun_slice f x))) =
            (λx. integral m1 (x_fun_slice (fn_minus f) x))` by (rw[FUN_EQ_THM,x_fun_slice_fn_minus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_MINUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2x >> rw[IN_MEASURABLE_BOREL_FN_MINUS]) >>
    `(integral m0 (λx. ipf x − imf x) = integral m0 ipf − integral m0 imf)` by rw[integral_sub] >>
    `pos_fn_integral m0 ipf = integral m0 ipf` by rw[GSYM integral_pos_fn] >>
    `pos_fn_integral m0 imf = integral m0 imf` by rw[GSYM integral_pos_fn] >>
    map_every Q.UNABBREV_TAC [`ipf`,`imf`] >> fs[] >> fs[integral_def]
);

val fubini_3y = store_thm(
    "fubini_3y",
    ``∀m0 m1 f. measure_space m0 ∧ measure_space m1 ∧ integrable (prod_measure_space m0 m1) f ⇒
        (integral (prod_measure_space m0 m1) f = integral m1 (λy. integral m0 (y_fun_slice f y)))``,
    rw[integral_def,integrable_def] >>
    map_every (fn tm => (qspecl_then [`m0`,`m1`,tm] assume_tac) tonelli_3y)
        [`fn_plus f`,`fn_minus f`] >>
    rfs[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >> rw[integral_def] >>
    fs[y_fun_slice_fn_plus,y_fun_slice_fn_minus] >>
    map_every Q.ABBREV_TAC [`ipf = (λy. pos_fn_integral m0 (fn_plus (y_fun_slice f y)))`,
        `imf = (λy. pos_fn_integral m0 (fn_minus (y_fun_slice f y)))`] >>
    `∀y. 0 ≤ ipf y` by (Q.UNABBREV_TAC `ipf` >> rw[] >>
        irule pos_fn_integral_pos >> rw[FN_PLUS_POS]) >>
    `∀y. 0 ≤ imf y` by (Q.UNABBREV_TAC `imf` >> rw[] >>
        irule pos_fn_integral_pos >> rw[FN_MINUS_POS]) >>
    `integrable m1 ipf` by (rw[integrable_pos] >> Q.UNABBREV_TAC `ipf` >>
        `(λy. pos_fn_integral m0 (fn_plus (y_fun_slice f y))) =
            (λy. integral m0 (y_fun_slice (fn_plus f) y))` by (rw[FUN_EQ_THM,y_fun_slice_fn_plus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_PLUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2y >> rw[IN_MEASURABLE_BOREL_FN_PLUS]) >>
    `integrable m1 imf` by (rw[integrable_pos] >> Q.UNABBREV_TAC `imf` >>
        `(λy. pos_fn_integral m0 (fn_minus (y_fun_slice f y))) =
            (λy. integral m0 (y_fun_slice (fn_minus f) y))` by (rw[FUN_EQ_THM,y_fun_slice_fn_minus] >>
            irule (GSYM integral_pos_fn) >> rw[FN_MINUS_POS]) >>
        rw[] >> pop_assum kall_tac >> irule tonelli_2y >> rw[IN_MEASURABLE_BOREL_FN_MINUS]) >>
    `(integral m1 (λy. ipf y − imf y) = integral m1 ipf − integral m1 imf)` by rw[integral_sub] >>
    `pos_fn_integral m1 ipf = integral m1 ipf` by rw[GSYM integral_pos_fn] >>
    `pos_fn_integral m1 imf = integral m1 imf` by rw[GSYM integral_pos_fn] >>
    map_every Q.UNABBREV_TAC [`ipf`,`imf`] >> fs[] >> fs[integral_def]
);

(***********************)
(* Integral of Product *)
(***********************)

(* Leadup to 45.A *)

val IN_MEASURABLE_BOREL_POS_PROD = store_thm(
    "IN_MEASURABLE_BOREL_POS_PROD",
    ``∀m0 m1 f0 f1. measure_space m0 ∧ measure_space m1 ∧ (∀x. 0 ≤ f0 x) ∧ (∀y. 0 ≤ f1 y) ∧
        f0 ∈ measurable (m_space m0,measurable_sets m0) Borel ∧
        f1 ∈ measurable (m_space m1,measurable_sets m1) Borel ⇒
        (λ(x,y). f0 x * f1 y) ∈ measurable
        (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel``,
    rw[] >> `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    (qspecl_then [`m0`,`f0`] assume_tac) measurable_sequence_pos >> rfs[] >>
    Q.RENAME_TAC [`∀i x. 0 ≤ fi0 i x`] >>
    (qspecl_then [`m1`,`f1`] assume_tac) (INST_TYPE [alpha |-> ``:β``] measurable_sequence_pos) >>
    rfs[] >> Q.RENAME_TAC [`∀i x. 0 ≤ fi1 i x`] >>
    irule IN_MEASURABLE_BOREL_MONO_SUP >> rw[MEASURE_SPACE_SIGMA_ALGEBRA] >>
    qexists_tac `λi. (λ(x,y). fi0 i x * fi1 i y)` >> rw[]
    >- ((qspec_then `x` assume_tac) ABS_PAIR_THM >> rw[] >> fs[] >> Q.RENAME_TAC [`(x,y) ∈ _`] >>
        fs[space_def,m_space_prod_measure_space] >>
        (qspecl_then [`λn. fi0 n x`,`λn. fi1 n y`] assume_tac) sup_mul_mono >> rfs[])
    >- ((qspec_then `x` assume_tac) ABS_PAIR_THM >> rw[] >> fs[] >> Q.RENAME_TAC [`(x,y) ∈ _`] >>
        fs[ext_mono_increasing_def] >> irule le_mul2 >> rw[])
    >- (irule IN_MEASURABLE_BOREL_POS_SIMPLE_FN >> rw[] >>
        irule pos_simple_fn_prod >> metis_tac[])
);

val IN_MEASURABLE_BOREL_PROD = store_thm(
    "IN_MEASURABLE_BOREL_PROD",
    ``∀m0 m1 f0 f1. measure_space m0 ∧ measure_space m1 ∧
        f0 ∈ measurable (m_space m0,measurable_sets m0) Borel ∧
        f1 ∈ measurable (m_space m1,measurable_sets m1) Borel ⇒
        (λ(x,y). f0 x * f1 y) ∈ measurable
        (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel``,
    rw[] >> `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    (qspecl_then [`(m_space m0,measurable_sets m0)`,`f0`] assume_tac)
        IN_MEASURABLE_BOREL_PLUS_MINUS >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`(m_space m1,measurable_sets m1)`,`f1`] assume_tac)
        (INST_TYPE [alpha |-> ``:β``] IN_MEASURABLE_BOREL_PLUS_MINUS) >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`(m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1))`,
        `(λ(x,y). f0 x * f1 y)`] assume_tac)
        (INST_TYPE [alpha |-> ``:α#β``] IN_MEASURABLE_BOREL_PLUS_MINUS) >>
    fs[] >> pop_assum kall_tac >>
    rw[FN_PLUS_PROD,FN_MINUS_PROD] >>
    irule IN_MEASURABLE_BOREL_ADD_ALT >> rw[MEASURE_SPACE_SIGMA_ALGEBRA] >>
    irule IN_MEASURABLE_BOREL_POS_PROD >> rw[FN_PLUS_POS,FN_MINUS_POS]
);

val IN_MEASURABLE_BOREL_UNPROD_X = store_thm(
    "IN_MEASURABLE_BOREL_UNPROD_X",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧
        (∃y c. (g y = Normal c) ∧ (y ∈ m_space m1) ∧ (c ≠ 0)) ∧
        (λ(x,y). f x * g y) ∈ measurable
        (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel ⇒
        f ∈ measurable (m_space m0,measurable_sets m0) Borel``,
    rw[] >> drule_all_then assume_tac tonelli_1y >> rfs[y_fun_slice_alt] >>
    `(λx. f x * Normal c) = (λx. Normal c * f x)` by rw[FUN_EQ_THM,mul_comm] >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`(m_space m0,measurable_sets m0)`,`(λx. Normal c * f x)`,`c⁻¹`] assume_tac)
        IN_MEASURABLE_BOREL_CMUL_ALT >>
    rfs[MEASURE_SPACE_SIGMA_ALGEBRA,mul_assoc,extreal_mul_def,REAL_INV_CANCEL,N1_EQ_1,mul_lone,F_SIMP]
);

val IN_MEASURABLE_BOREL_UNPROD_Y = store_thm(
    "IN_MEASURABLE_BOREL_UNPROD_Y",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧
        (∃x c. (f x = Normal c) ∧ (x ∈ m_space m0) ∧ (c ≠ 0)) ∧
        (λ(x,y). f x * g y) ∈ measurable
        (m_space (prod_measure_space m0 m1),measurable_sets (prod_measure_space m0 m1)) Borel ⇒
        g ∈ measurable (m_space m1,measurable_sets m1) Borel``,
    rw[] >> drule_all_then assume_tac tonelli_1x >> rfs[x_fun_slice_alt] >>
    (qspecl_then [`(m_space m1,measurable_sets m1)`,`(λy. Normal c * g y)`,`c⁻¹`] assume_tac)
        (INST_TYPE [alpha |-> ``:β``] IN_MEASURABLE_BOREL_CMUL_ALT) >>
    rfs[MEASURE_SPACE_SIGMA_ALGEBRA,mul_assoc,extreal_mul_def,REAL_INV_CANCEL,N1_EQ_1,mul_lone,F_SIMP]
);

val prod_measure_space_unrect = store_thm(
    "prod_measure_space_unrect",
    ``∀m0 m1 s0 s1. measure_space m0 ∧ measure_space m1 ∧ (s0 × s1 ≠ ∅) ∧
        (s0 × s1) ∈ measurable_sets (prod_measure_space m0 m1) ⇒
        s0 ∈ measurable_sets m0 ∧ s1 ∈ measurable_sets m1``,
    rw[]
    >- (`s1 ≠ ∅` by (CCONTR_TAC >> fs[CROSS_EMPTY]) >> fs[GSYM MEMBER_NOT_EMPTY] >>
        (qspecl_then [`m0`,`m1`,`s0 × s1`,`x'`] assume_tac)
            product_measure_space_y_slice_measurable >>
        rfs[y_slice_def,PREIMAGE_def])
    >- (`s0 ≠ ∅` by (CCONTR_TAC >> fs[CROSS_EMPTY]) >> fs[GSYM MEMBER_NOT_EMPTY] >>
        (qspecl_then [`m0`,`m1`,`s0 × s1`,`x'`] assume_tac)
            product_measure_space_x_slice_measurable >>
        rfs[x_slice_def,PREIMAGE_def])
);

val IN_MEASURABLE_BOREL_INTEGRABLE_UNPROD = store_thm(
    "IN_MEASURABLE_BOREL_INTEGRABLE_UNPROD",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧ ¬a_e m0 {x | f x = 0} ∧ ¬a_e m1 {y | g y = 0} ∧
        integrable (prod_measure_space m0 m1) (λ(x,y). f x * g y) ⇒
        f ∈ measurable (m_space m0,measurable_sets m0) Borel ∧
        g ∈ measurable (m_space m1,measurable_sets m1) Borel``,
    NTAC 5 strip_tac >>
    `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    fs[integrable_alt_abs] >>
    `∃x y a b. x ∈ m_space m0 ∧ (f x = Normal a) ∧ (a ≠ 0) ∧
        y ∈ m_space m1 ∧ (g y = Normal b) ∧ (b ≠ 0)` suffices_by (
        strip_tac >> rw[]
        >- (irule IN_MEASURABLE_BOREL_UNPROD_X >> rw[] >>
            map_every qexists_tac [`g`,`m1`] >> rw[] >>
            map_every qexists_tac [`y`,`b`] >> rw[])
        >- (irule IN_MEASURABLE_BOREL_UNPROD_Y >> rw[] >>
            map_every qexists_tac [`f`,`m0`] >> rw[] >>
            map_every qexists_tac [`x`,`a`] >> rw[])) >>
    `integrable (prod_measure_space m0 m1) (λ(x,y). f x * g y)` by rw[integrable_alt_abs] >>
    drule_then assume_tac integrable_abs_infty_null >> pop_assum (dxrule_then assume_tac) >>
    `{x | x ∈ m_space (prod_measure_space m0 m1) ∧ (abs ((λ(x,y). f x * g y) x) = PosInf)} =
        {x | x ∈ m_space (prod_measure_space m0 m1) ∧ ((λ(x,y). abs (f x) * abs (g y)) x = PosInf)}` by (
        rw[EXTENSION] >> (qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[abs_mul]) >>
    fs[] >> pop_assum kall_tac >>
    Cases_on `∃x a. x ∈ m_space m0 ∧ (f x = Normal a) ∧ a ≠ 0` >>
    Cases_on `∃y b. y ∈ m_space m1 ∧ (g y = Normal b) ∧ b ≠ 0` >> fs[]
    >- (map_every qexists_tac [`x`,`y`,`a`,`b`] >> rw[])
    >- (`∀y. y ∈ m_space m1 ⇒ (abs (g y) = PosInf) ∨ (g y = 0)` by (rw[] >>
            qpat_x_assum `∀y b. _` (qspec_then `y` assume_tac) >> rfs[] >>
            Cases_on `g y` >> fs[GSYM N0_EQ_0,extreal_abs_def]) >>
        qpat_x_assum `∀z c. _ ∨ _ ∨ _` kall_tac >>
        `{x | x ∈ m_space (prod_measure_space m0 m1) ∧ ((λ(x,y). abs (f x) * abs (g y)) x = PosInf)} =
            {x | x ∈ m_space m0 ∧ f x ≠ 0} × {y | y ∈ m_space m1 ∧ (abs (g y) = PosInf)}` by (
            rw[EXTENSION] >> (qspec_then `x'` assume_tac) ABS_PAIR_THM >> fs[] >>
            eq_tac >> rw[m_space_prod_measure_space]
            >- (CCONTR_TAC >> RES_TAC >> fs[abs_0,mul_lzero] >> fs[GSYM N0_EQ_0])
            >- (CCONTR_TAC >> RES_TAC >> fs[abs_0,mul_rzero])
            >- (fs[abs_nz] >> rw[extreal_mul_alt] >> fs[lt_refl])) >>
        fs[null_set_def] >> pop_assum kall_tac >>
        `{x | x ∈ m_space m0 ∧ f x ≠ 0} ≠ ∅` by (rw[GSYM MEMBER_NOT_EMPTY] >>
            qexists_tac `x` >> rw[GSYM N0_EQ_0]) >>
        `{y | y ∈ m_space m1 ∧ (abs (g y) = PosInf)} ≠ ∅` by (rw[EXTENSION] >> CCONTR_TAC >> fs[] >>
            `∀y. y ∈ m_space m1 ⇒ (g y = 0)` by (rw[] >> fs[DISJ_EQ_IMP]) >>
            `m_space m1 DIFF {y | g y = 0} = ∅` by (rw[EXTENSION] >> CCONTR_TAC >> fs[] >> RES_TAC) >>
            (qspecl_then [`m1`,`{y | g y = 0}`] assume_tac)
                (INST_TYPE [alpha |-> ``:β``] MEASURE_SPACE_TRIVIAL_A_E) >>
            rfs[MEASURE_SPACE_EMPTY_MEASURABLE] >> `a_e m1 {y | g y = 0}` suffices_by rw[] >>
            NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >> rw[a_e_def,MEASURE_SPACE_EMPTY_NULL]) >>
        (qspecl_then [`m0`,`m1`,`{x | x ∈ m_space m0 ∧ f x ≠ 0}`,
            `{y | y ∈ m_space m1 ∧ (abs (g y) = PosInf)}`] assume_tac) prod_measure_space_unrect >>
        rfs[CROSS_EMPTY_EQN] >>
        (qspecl_then [`m0`,`m1`] assume_tac) (GSYM prod_measure_prod_set) >> rfs[] >>
        pop_assum (drule_all_then assume_tac) >> rfs[]
        >- (`m_space m0 DIFF {x | f x = 0} = {x | x ∈ m_space m0 ∧ f x ≠ 0}` by rw[EXTENSION] >>
            (qspecl_then [`m0`,`{x | f x = 0}`] assume_tac) MEASURE_SPACE_TRIVIAL_A_E >> rfs[] >>
            `a_e m0 {x | f x = 0}` suffices_by rw[] >> NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >>
            rw[a_e_def,null_set_def])
        >- (`m_space m1 DIFF {y | g y = 0} = {y | y ∈ m_space m1 ∧ (abs (g y) = PosInf)}` by (
                rw[EXTENSION] >> eq_tac >> rw[] >> CCONTR_TAC >> RES_TAC >>
                fs[abs_0] >> fs[GSYM N0_EQ_0]) >>
            (qspecl_then [`m1`,`{y | g y = 0}`] assume_tac)
                (INST_TYPE [alpha |-> ``:β``] MEASURE_SPACE_TRIVIAL_A_E) >> rfs[] >>
            `a_e m1 {y | g y = 0}` suffices_by rw[] >> NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >>
            rw[a_e_def,null_set_def]))
    >- (`∀x. x ∈ m_space m0 ⇒ (abs (f x) = PosInf) ∨ (f x = 0)` by (rw[] >>
            qpat_x_assum `∀x a. _` (qspec_then `x` assume_tac) >> rfs[] >>
            Cases_on `f x` >> fs[GSYM N0_EQ_0,extreal_abs_def]) >>
        qpat_x_assum `∀z c. _ ∨ _ ∨ _` kall_tac >>
        `{x | x ∈ m_space (prod_measure_space m0 m1) ∧ ((λ(x,y). abs (f x) * abs (g y)) x = PosInf)} =
            {x | x ∈ m_space m0 ∧ (abs (f x) = PosInf)} × {y | y ∈ m_space m1 ∧ g y ≠ 0}` by (
            rw[EXTENSION] >> (qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[] >>
            eq_tac >> rw[m_space_prod_measure_space]
            >- (CCONTR_TAC >> RES_TAC >> fs[abs_0,mul_lzero])
            >- (CCONTR_TAC >> RES_TAC >> fs[abs_0,mul_rzero] >> fs[GSYM N0_EQ_0])
            >- (fs[abs_nz] >> rw[extreal_mul_alt] >> fs[lt_refl])) >>
        fs[null_set_def] >> pop_assum kall_tac >>
        `{x | x ∈ m_space m0 ∧ (abs (f x) = PosInf)} ≠ ∅` by (rw[EXTENSION] >> CCONTR_TAC >> fs[] >>
            `∀x. x ∈ m_space m0 ⇒ (f x = 0)` by (rw[] >> fs[DISJ_EQ_IMP]) >>
            `m_space m0 DIFF {x | f x = 0} = ∅` by (rw[EXTENSION] >> CCONTR_TAC >> fs[] >> RES_TAC) >>
            (qspecl_then [`m0`,`{x | f x = 0}`] assume_tac) MEASURE_SPACE_TRIVIAL_A_E >>
            rfs[MEASURE_SPACE_EMPTY_MEASURABLE] >> `a_e m0 {x | f x = 0}` suffices_by rw[] >>
            NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >> rw[a_e_def,MEASURE_SPACE_EMPTY_NULL]) >>
        `{y | y ∈ m_space m1 ∧ g y ≠ 0} ≠ ∅` by (rw[GSYM MEMBER_NOT_EMPTY] >>
            qexists_tac `y` >> rw[GSYM N0_EQ_0]) >>
        (qspecl_then [`m0`,`m1`,`{x | x ∈ m_space m0 ∧ (abs (f x) = PosInf)}`,
            `{y | y ∈ m_space m1 ∧ g y ≠ 0}`] assume_tac) prod_measure_space_unrect >>
        rfs[CROSS_EMPTY_EQN] >>
        (qspecl_then [`m0`,`m1`] assume_tac) (GSYM prod_measure_prod_set) >> rfs[] >>
        pop_assum (drule_all_then assume_tac) >> rfs[]
        >- (`m_space m0 DIFF {x | f x = 0} = {x | x ∈ m_space m0 ∧ (abs (f x) = PosInf)}` by (
                rw[EXTENSION] >> eq_tac >> rw[] >> CCONTR_TAC >> RES_TAC >>
                fs[abs_0] >> fs[GSYM N0_EQ_0]) >>
            (qspecl_then [`m0`,`{x | f x = 0}`] assume_tac) MEASURE_SPACE_TRIVIAL_A_E >> rfs[] >>
            `a_e m0 {x | f x = 0}` suffices_by rw[] >> NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >>
            rw[a_e_def,null_set_def])
        >- (`m_space m1 DIFF {y | g y = 0} = {y | y ∈ m_space m1 ∧ g y ≠ 0}` by rw[EXTENSION] >>
            (qspecl_then [`m1`,`{y | g y = 0}`] assume_tac)
                (INST_TYPE [alpha |-> ``:β``] MEASURE_SPACE_TRIVIAL_A_E) >> rfs[] >>
            `a_e m1 {y | g y = 0}` suffices_by rw[] >> NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >>
            rw[a_e_def,null_set_def]))
    >- (`∀x. x ∈ m_space m0 ⇒ (abs (f x) = PosInf) ∨ (f x = 0)` by (rw[] >>
            qpat_x_assum `∀x a. _` (qspec_then `x` assume_tac) >> rfs[] >>
            Cases_on `f x` >> fs[GSYM N0_EQ_0,extreal_abs_def]) >>
        `∀y. y ∈ m_space m1 ⇒ (abs (g y) = PosInf) ∨ (g y = 0)` by (rw[] >>
            qpat_x_assum `∀y b. _` (qspec_then `y` assume_tac) >> rfs[] >>
            Cases_on `g y` >> fs[GSYM N0_EQ_0,extreal_abs_def]) >>
        NTAC 2 (qpat_x_assum `∀z c. _ ∨ _ ∨ _` kall_tac) >>
        `{x | x ∈ m_space (prod_measure_space m0 m1) ∧ ((λ(x,y). abs (f x) * abs (g y)) x = PosInf)} =
            {x | x ∈ m_space m0 ∧ (abs (f x) = PosInf)} ×
            {y | y ∈ m_space m1 ∧ (abs (g y) = PosInf)}` by (rw[EXTENSION] >>
            (qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[] >>
            eq_tac >> rw[m_space_prod_measure_space]
            >- (CCONTR_TAC >> RES_TAC >> fs[abs_0,mul_lzero])
            >- (CCONTR_TAC >> RES_TAC >> fs[abs_0,mul_rzero])
            >- (rw[extreal_mul_def])) >>
        fs[null_set_def] >> pop_assum kall_tac >>
        `{x | x ∈ m_space m0 ∧ (abs (f x) = PosInf)} ≠ ∅` by (rw[EXTENSION] >> CCONTR_TAC >> fs[] >>
            `∀x. x ∈ m_space m0 ⇒ (f x = 0)` by (rw[] >> fs[DISJ_EQ_IMP]) >>
            `m_space m0 DIFF {x | f x = 0} = ∅` by (rw[EXTENSION] >> CCONTR_TAC >> fs[] >> RES_TAC) >>
            (qspecl_then [`m0`,`{x | f x = 0}`] assume_tac) MEASURE_SPACE_TRIVIAL_A_E >>
            rfs[MEASURE_SPACE_EMPTY_MEASURABLE] >> `a_e m0 {x | f x = 0}` suffices_by rw[] >>
            NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >> rw[a_e_def,MEASURE_SPACE_EMPTY_NULL]) >>
        `{y | y ∈ m_space m1 ∧ (abs (g y) = PosInf)} ≠ ∅` by (rw[EXTENSION] >> CCONTR_TAC >> fs[] >>
            `∀y. y ∈ m_space m1 ⇒ (g y = 0)` by (rw[] >> fs[DISJ_EQ_IMP]) >>
            `m_space m1 DIFF {y | g y = 0} = ∅` by (rw[EXTENSION] >> CCONTR_TAC >> fs[] >> RES_TAC) >>
            (qspecl_then [`m1`,`{y | g y = 0}`] assume_tac)
                (INST_TYPE [alpha |-> ``:β``] MEASURE_SPACE_TRIVIAL_A_E) >>
            rfs[MEASURE_SPACE_EMPTY_MEASURABLE] >> `a_e m1 {y | g y = 0}` suffices_by rw[] >>
            NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >> rw[a_e_def,MEASURE_SPACE_EMPTY_NULL]) >>
        (qspecl_then [`m0`,`m1`,`{x | x ∈ m_space m0 ∧ (abs (f x) = PosInf)}`,
            `{y | y ∈ m_space m1 ∧ (abs (g y) = PosInf)}`] assume_tac) prod_measure_space_unrect >>
        rfs[CROSS_EMPTY_EQN] >>
        (qspecl_then [`m0`,`m1`] assume_tac) (GSYM prod_measure_prod_set) >> rfs[] >>
        pop_assum (drule_all_then assume_tac) >> rfs[]
        >- (`m_space m0 DIFF {x | f x = 0} = {x | x ∈ m_space m0 ∧ (abs (f x) = PosInf)}` by (
                rw[EXTENSION] >> eq_tac >> rw[] >> CCONTR_TAC >> RES_TAC >>
                fs[abs_0] >> fs[GSYM N0_EQ_0]) >>
            (qspecl_then [`m0`,`{x | f x = 0}`] assume_tac) MEASURE_SPACE_TRIVIAL_A_E >> rfs[] >>
            `a_e m0 {x | f x = 0}` suffices_by rw[] >> NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >>
            rw[a_e_def,null_set_def])
        >- (`m_space m1 DIFF {y | g y = 0} = {y | y ∈ m_space m1 ∧ (abs (g y) = PosInf)}` by (
                rw[EXTENSION] >> eq_tac >> rw[] >> CCONTR_TAC >> RES_TAC >>
                fs[abs_0] >> fs[GSYM N0_EQ_0]) >>
            (qspecl_then [`m1`,`{y | g y = 0}`] assume_tac)
                (INST_TYPE [alpha |-> ``:β``] MEASURE_SPACE_TRIVIAL_A_E) >> rfs[] >>
            `a_e m1 {y | g y = 0}` suffices_by rw[] >> NTAC 2 (qpat_x_assum `¬a_e _ _` kall_tac) >>
            rw[a_e_def,null_set_def]))
);

val pos_fn_integral_prod = store_thm(
    "pos_fn_integral_prod",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧ (∀x. 0 ≤ f x) ∧ (∀x. 0 ≤ g x) ∧
        f ∈ measurable (m_space m0,measurable_sets m0) Borel ∧
        g ∈ measurable (m_space m1,measurable_sets m1) Borel ⇒
        (pos_fn_integral (prod_measure_space m0 m1) (λ(x,y). f x * g y) =
        pos_fn_integral m0 f * pos_fn_integral m1 g)``,
    rw[] >> (qspecl_then [`m0`,`m1`] assume_tac) IN_MEASURABLE_BOREL_PROD >>
    rfs[] >> pop_assum (drule_all_then assume_tac) >>
    `∀z. 0 ≤ (λ(x,y). f x * g y) z` by (rw[] >>
        (qspec_then `z` assume_tac) ABS_PAIR_THM >> rw[] >> fs[] >>
        irule le_mul >> rw[]) >>
    rw[tonelli_3x,x_fun_slice_alt] >>
    `pos_fn_integral m0 (λx. pos_fn_integral m1 (λy. f x * g y)) =
        pos_fn_integral m0 (λx. f x * pos_fn_integral m1 (λy. g y))` by (
        irule pos_fn_integral_eq_fun_eq_mspace >> rw[F_SIMP]
        >- (`0 ≤ f x` by rw[] >> Cases_on `f x` >> fs[GSYM N0_EQ_0,extreal_le_def]
            >- (`Normal 0 ≤ PosInf` by rw[extreal_le_def] >> fs[N0_EQ_0] >>
                rw[pos_fn_integral_extcmul])
            >- (irule pos_fn_integral_cmul >> fs[N0_EQ_0]))
        >- (irule pos_fn_integral_pos >> rw[] >> irule le_mul >> rw[])
        >- (irule le_mul >> rw[] >> irule pos_fn_integral_pos >> rw[])) >>
    rw[F_SIMP] >> pop_assum kall_tac >>
    `0 ≤ pos_fn_integral m1 g` by (irule pos_fn_integral_pos >> rw[]) >>
    Q.ABBREV_TAC `int_g = pos_fn_integral m1 g` >>
    Cases_on `int_g` >> fs[GSYM N0_EQ_0,extreal_le_def]
    >- (`pos_fn_integral m0 f * PosInf = PosInf * pos_fn_integral m0 f` by rw[mul_comm] >>
        `(λx. f x * PosInf) = (λx. PosInf * f x)` by rw[FUN_EQ_THM,mul_comm] >>
        rw[] >> NTAC 2 (pop_assum kall_tac) >>
        `Normal 0 ≤ PosInf` by rw[extreal_le_def] >> fs[N0_EQ_0] >>
        rw[pos_fn_integral_extcmul])
    >- (`pos_fn_integral m0 (λx. Normal r * f x) = Normal r * pos_fn_integral m0 f` suffices_by (rw[] >>
            `(λx. f x * Normal r) = (λx. Normal r * f x)` suffices_by rw[mul_comm] >>
            rw[FUN_EQ_THM,mul_comm]) >>
        irule pos_fn_integral_cmul >> fs[N0_EQ_0])
);

val pos_fn_integral_unprod = store_thm(
    "pos_fn_integral_unprod",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧ (∀x. 0 ≤ f x) ∧ (∀x. 0 ≤ g x) ∧
        ¬a_e m0 {x | f x = 0} ∧ ¬a_e m1 {y | g y = 0} ∧
        integrable (prod_measure_space m0 m1) (λ(x,y). f x * g y) ⇒
        (pos_fn_integral (prod_measure_space m0 m1) (λ(x,y). f x * g y) =
        pos_fn_integral m0 f * pos_fn_integral m1 g)``,
    rw[] >> drule_all_then assume_tac IN_MEASURABLE_BOREL_INTEGRABLE_UNPROD >>
    irule pos_fn_integral_prod >> rw[]
);

(* Not Halmos 45.A *)

val integrable_prod = store_thm(
    "integrable_prod",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧
        integrable m0 f ∧ integrable m1 g ⇒
        integrable (prod_measure_space m0 m1) (λ(x,y). f x * g y)``,
    rw[] >> `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    rfs[integrable_alt_abs] >> rw[IN_MEASURABLE_BOREL_PROD] >>
    imp_res_tac MEASURE_SPACE_SIGMA_ALGEBRA >>
    NTAC 2 (dxrule_all_then assume_tac IN_MEASURABLE_BOREL_ABS_ALT) >>
    qpat_x_assum `sigma_algebra _` kall_tac >>
    (qspecl_then [`m0`,`m1`,`abs ∘ f`,`abs ∘ g`] assume_tac) pos_fn_integral_prod >>
    rfs[o_DEF,abs_pos,abs_zero,IN_MEASURABLE_BOREL_ABS_ALT] >>
    `(λx. abs ((λ(x,y). f x * g y) x)) = (λ(x,y). abs (f x) * abs (g y))` by (
        rw[FUN_EQ_THM] >> (qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[abs_mul]) >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >>
    `0 ≤ pos_fn_integral m1 (λx. abs (g x))` by (irule pos_fn_integral_pos >> rw[abs_pos]) >>
    `0 ≤ pos_fn_integral m0 (λx. abs (f x))` by (irule pos_fn_integral_pos >> rw[abs_pos]) >>
    Cases_on `pos_fn_integral m1 (λx. abs (g x))` >>
    Cases_on `pos_fn_integral m0 (λx. abs (f x))` >>
    fs[GSYM N0_EQ_0,extreal_le_def,extreal_mul_def]
);

val integrable_unprod = store_thm(
    "integrable_unprod",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧
        ¬a_e m0 {x | f x = 0} ∧ ¬a_e m1 {y | g y = 0} ∧
        integrable (prod_measure_space m0 m1) (λ(x,y). f x * g y) ⇒
        integrable m0 f ∧ integrable m1 g``,
    NTAC 5 strip_tac >>
    `measure_space (prod_measure_space m0 m1)` by rw[prod_measure_space_measure_space] >>
    drule_all_then assume_tac IN_MEASURABLE_BOREL_INTEGRABLE_UNPROD >>
    fs[integrable_alt_abs] >>
    imp_res_tac MEASURE_SPACE_SIGMA_ALGEBRA >>
    NTAC 2 (dxrule_all_then assume_tac IN_MEASURABLE_BOREL_ABS_ALT) >>
    qpat_x_assum `sigma_algebra _` kall_tac >>
    (qspecl_then [`m0`,`m1`,`abs ∘ f`,`abs ∘ g`] assume_tac) pos_fn_integral_prod >>
    rfs[o_DEF,abs_pos,abs_zero,IN_MEASURABLE_BOREL_ABS_ALT] >>
    `(λx. abs ((λ(x,y). f x * g y) x)) = (λ(x,y). abs (f x) * abs (g y))` by (
        rw[FUN_EQ_THM] >> (qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[abs_mul]) >>
    fs[] >> pop_assum kall_tac >>
    CCONTR_TAC >> fs[] >> fs[] >> NTAC 2 (pop_assum kall_tac)
    >- (`0 ≤ pos_fn_integral m1 (λx. abs (g x))` by (
            irule pos_fn_integral_pos >> rw[abs_pos]) >>
        fs[le_lt] >> fs[mul_infty] >> pop_assum (assume_tac o GSYM) >>
        fs[mul_infty,zero_not_infty] >> rw[] >>
        (qspecl_then [`m1`,`(λx. abs (g x))`] assume_tac)
            (INST_TYPE [alpha |-> ``:β``] (GSYM pos_fn_integral_eq_zero_iff_zero_a_e)) >>
        rfs[abs_pos,abs_zero])
    >- (`0 ≤ pos_fn_integral m0 (λx. abs (f x))` by (
            irule pos_fn_integral_pos >> rw[abs_pos]) >>
        fs[le_lt] >> fs[mul_infty] >> pop_assum (assume_tac o GSYM) >>
        fs[mul_infty,zero_not_infty] >> rw[] >>
        (qspecl_then [`m0`,`(λx. abs (f x))`] assume_tac)
            (GSYM pos_fn_integral_eq_zero_iff_zero_a_e) >>
        rfs[abs_pos,abs_zero])
);

val integrable_iff_prod = store_thm(
    "integrable_iff_prod",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧
        ¬a_e m0 {x | f x = 0} ∧ ¬a_e m1 {y | g y = 0} ⇒
        (integrable (prod_measure_space m0 m1) (λ(x,y). f x * g y) ⇔
        integrable m0 f ∧ integrable m1 g)``,
    rw[] >> eq_tac >> rw[]
    >- (dxrule_all_then assume_tac integrable_unprod >> fs[])
    >- (dxrule_all_then assume_tac integrable_unprod >> fs[])
    >- (dxrule_all_then assume_tac integrable_prod >> fs[])
);

val integral_prod = store_thm(
    "integral_prod",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧
        integrable m0 f ∧ integrable m1 g ⇒
        (integral (prod_measure_space m0 m1) (λ(x,y). f x * g y) = integral m0 f * integral m1 g)``,
    rw[] >> fs[integral_def,integrable_def,FN_PLUS_PROD,FN_MINUS_PROD] >>
    map_every (fn tms => (qspecl_then tms assume_tac) pos_fn_integral_prod)
        [[`m0`,`m1`,`fn_plus f`,`fn_plus g`],[`m0`,`m1`,`fn_plus f`,`fn_minus g`],
        [`m0`,`m1`,`fn_minus f`,`fn_plus g`],[`m0`,`m1`,`fn_minus f`,`fn_minus g`]] >>
    rfs[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    `pos_fn_integral (prod_measure_space m0 m1) (λz. (λ(x,y). fn_plus f x * fn_plus g y) z +
        (λ(x,y). fn_minus f x * fn_minus g y) z) =
        pos_fn_integral (prod_measure_space m0 m1) (λ(x,y). fn_plus f x * fn_plus g y) +
        pos_fn_integral (prod_measure_space m0 m1) (λ(x,y). fn_minus f x * fn_minus g y)` by (
        irule pos_fn_integral_add >> rw[]
        >- ((qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[] >>
            irule le_mul >> fs[FN_PLUS_POS,FN_MINUS_POS])
        >- ((qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[] >>
            irule le_mul >> fs[FN_PLUS_POS,FN_MINUS_POS])
        >- (rw[prod_measure_space_measure_space])
        >- (irule IN_MEASURABLE_BOREL_PROD >>
            rw[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS])
        >- (irule IN_MEASURABLE_BOREL_PROD >>
            rw[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS])) >>
    `pos_fn_integral (prod_measure_space m0 m1) (λz. (λ(x,y). fn_plus f x * fn_minus g y) z +
        (λ(x,y). fn_minus f x * fn_plus g y) z) =
        pos_fn_integral (prod_measure_space m0 m1) (λ(x,y). fn_plus f x * fn_minus g y) +
        pos_fn_integral (prod_measure_space m0 m1) (λ(x,y). fn_minus f x * fn_plus g y)` by (
        irule pos_fn_integral_add >> rw[]
        >- ((qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[] >>
            irule le_mul >> fs[FN_PLUS_POS,FN_MINUS_POS])
        >- ((qspec_then `x` assume_tac) ABS_PAIR_THM >> fs[] >>
            irule le_mul >> fs[FN_PLUS_POS,FN_MINUS_POS])
        >- (rw[prod_measure_space_measure_space])
        >- (irule IN_MEASURABLE_BOREL_PROD >>
            rw[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS])
        >- (irule IN_MEASURABLE_BOREL_PROD >>
            rw[IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS])) >>
    fs[] >> NTAC 6 (pop_assum kall_tac) >>
    map_every (fn tms => (qspecl_then tms assume_tac) pos_fn_integral_pos)
        [[`m0`,`fn_plus f`],[`m0`,`fn_minus f`]] >>
    map_every (fn tms => (qspecl_then tms assume_tac) (INST_TYPE [alpha |-> ``:β``] pos_fn_integral_pos))
        [[`m1`,`fn_plus g`],[`m1`,`fn_minus g`]] >>
    rfs[FN_PLUS_POS,FN_MINUS_POS] >>
    Cases_on `pos_fn_integral m0 (fn_plus f)` >> Cases_on `pos_fn_integral m0 (fn_minus f)` >>
    Cases_on `pos_fn_integral m1 (fn_plus g)` >> Cases_on `pos_fn_integral m1 (fn_minus g)` >>
    fs[GSYM N0_EQ_0,extreal_le_def] >> rw[extreal_mul_def,extreal_add_def,extreal_sub_def] >>
    rpt (pop_assum kall_tac) >> rw[REAL_SUB_LDISTRIB,REAL_SUB_RDISTRIB] >>
    rw[real_sub,REAL_ADD_ASSOC,REAL_NEG_ADD] >> metis_tac[REAL_ADD_COMM,REAL_ADD_ASSOC]
);

val integral_unprod = store_thm(
    "integral_unprod",
    ``∀m0 m1 f g. measure_space m0 ∧ measure_space m1 ∧
        ¬a_e m0 {x | f x = 0} ∧ ¬a_e m1 {y | g y = 0} ∧
        integrable (prod_measure_space m0 m1) (λ(x,y). f x * g y) ⇒
        (integral (prod_measure_space m0 m1) (λ(x,y). f x * g y) = integral m0 f * integral m1 g)``,
    rw[] >> (qspecl_then [`m0`,`m1`,`f`,`g`] assume_tac) integrable_unprod >> rfs[] >>
    irule integral_prod >> rw[]
);

(* Halmos 39 *)

val inv_meas_measure_space = store_thm(
    "inv_meas_measure_space",
    ``∀m a f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) a ⇒
        measure_space (space a,subsets a,inv_meas m f)``,
    rw[measurable_def,measure_space_def,inv_meas_def,sigma_algebra_def,algebra_def,subset_class_def,
        positive_def,countably_additive_def,
        m_space_def,measurable_sets_def,measure_def,space_def,subsets_def] >>
    rename [`inv_meas m f ∘ g sums _`] >>
    qpat_x_assum `∀f. _ ∧ _ ∧ _ ⇒ _` (qspec_then `(λn. PREIMAGE f (g n) ∩ m_space m)` assume_tac) >>
    `(λn. PREIMAGE f (g n) ∩ m_space m) ∈ (𝕌(:num) → measurable_sets m)` by fs[FUNSET] >>
    `(∀i j. i ≠ j ⇒
        DISJOINT ((λn. PREIMAGE f (g n) ∩ m_space m) i) ((λn. PREIMAGE f (g n) ∩ m_space m) j))` by (
        rw[] >> qpat_x_assum `∀i j. _` (dxrule_then assume_tac) >> fs[DISJOINT_DEF,EXTENSION] >>
        CCONTR_TAC >> fs[] >> first_x_assum (qspec_then `f x` assume_tac) >> rfs[]) >>
    `BIGUNION (IMAGE (λn. PREIMAGE f (g n) ∩ m_space m) 𝕌(:num)) ∈ measurable_sets m` by (
        first_x_assum irule >> rw[COUNTABLE_IMAGE_NUM,SUBSET_DEF] >>
        first_x_assum irule >> fs[FUNSET]) >>
    fs[] >> NTAC 3 (pop_assum kall_tac) >>
    `inv_meas m f ∘ g = measure m ∘ (λn. PREIMAGE f (g n) ∩ m_space m)`
        by rw[FUN_EQ_THM,inv_meas_def,o_DEF] >>
    `PREIMAGE f (BIGUNION (IMAGE g 𝕌(:num))) ∩ m_space m =
        BIGUNION (IMAGE (λn. PREIMAGE f (g n) ∩ m_space m) 𝕌(:num))` by (
        rw[PREIMAGE_BIGUNION] >> rw[INTER_BIGUNION_IMAGE_COMM] >>
        rw[GSYM IMAGE_COMPOSE] >> rw[o_DEF]) >>
    fs[]
);

val inv_meas_pos_simple_fn_o = store_thm(
    "inv_meas_pos_simple_fn_o",
    ``∀m a f g s e c. pos_simple_fn (space a,subsets a,inv_meas m f) g s e c ∧
        f ∈ measurable (m_space m,measurable_sets m) a ⇒
        pos_simple_fn m (g ∘ f) s (λi. (PREIMAGE f (e i) ∩ m_space m)) c``,
    rw[pos_simple_fn_def,measurable_def,space_def,subsets_def,m_space_def,measurable_sets_def]
    >- (fs[FUNSET] >> NTAC 2 (first_x_assum (drule_then assume_tac)) >> pop_assum kall_tac >>
        irule EXTREAL_SUM_IMAGE_EQ >> rw[] >> irule IRULER >> rw[indicator_fn_def,IN_PREIMAGE])
    >- (rename [`i ≠ j`] >> qpat_x_assum `∀i j. _` (dxrule_all_then assume_tac) >>
        fs[DISJOINT_DEF,EXTENSION,IN_PREIMAGE] >> CCONTR_TAC >> fs[] >>
        first_x_assum (qspec_then `f x` assume_tac) >> rfs[])
    >- (rw[EXTENSION,IN_BIGUNION_IMAGE] >> eq_tac >> rw[] >>
        `f x ∈ space a` by fs[FUNSET] >> `f x ∈ BIGUNION (IMAGE e s)` by fs[EXTENSION] >>
        fs[IN_BIGUNION_IMAGE] >> rename [`f x ∈ e n`] >> qexists_tac `n` >> simp[])
);

val inv_meas_pos_simple_fn_integral_o = store_thm(
    "inv_meas_pos_simple_fn_integral_o",
    ``∀m a f g s e c. pos_simple_fn (space a,subsets a,inv_meas m f) g s e c ∧
        f ∈ measurable (m_space m,measurable_sets m) a ⇒
        pos_simple_fn_integral (space a,subsets a,inv_meas m f) s e c =
        pos_simple_fn_integral m s (λi. (PREIMAGE f (e i) ∩ m_space m)) c``,
    rw[measurable_def,pos_simple_fn_integral_def,pos_simple_fn_def,inv_meas_def,
        space_def,subsets_def,m_space_def,measurable_sets_def,measure_def]
);

val inv_meas_pos_fn_integral_o = store_thm(
    "inv_meas_pos_fn_integral_o",
    ``∀m a f g. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) a ∧
        g ∈ measurable a Borel ∧ (∀x. 0 ≤ g x) ⇒
        pos_fn_integral (space a,subsets a,inv_meas m f) g = pos_fn_integral m (g ∘ f)``,
    rw[] >> (drule_all_then assume_tac) inv_meas_measure_space >>
    (drule_then assume_tac) measurable_sequence_pos >> fs[m_space_def,measurable_sets_def,SPACE] >>
    pop_assum (drule_all_then assume_tac) >> fs[] >> rename [`∀i x. 0 ≤ gi i x`] >>
    `pos_fn_integral m (g ∘ f) =
        sup (IMAGE (λi. pos_fn_integral m ((λi. gi i ∘ f) i)) 𝕌(:num))` suffices_by (rw[] >>
        irule IRULER >> irule IMAGE_CONG >> rw[] >> rename [`_ _ (gi n) = _`] >>
        qpat_x_assum `∀i. ∃s e c. _` (qspec_then `n` assume_tac) >> fs[] >>
        rename [`_ _ _ s e c`] >> (drule_all_then assume_tac) inv_meas_pos_simple_fn_o >>
        imp_res_tac pos_fn_integral_pos_simple_fn >> rw[] >> NTAC 2 (pop_assum kall_tac) >>
        irule inv_meas_pos_simple_fn_integral_o >> simp[] >>
        qexists_tac `gi n` >> simp[]) >>
    irule lebesgue_monotone_convergence >> rw[]
    >- (`f x ∈ space a` by fs[measurable_def,space_def,FUNSET] >>
        first_x_assum (dxrule_then assume_tac) >> simp[])
    >- (irule MEASURABLE_COMP >> qexists_tac `a` >> simp[] >>
        (qspecl_then [`(space a,subsets a,inv_meas m f)`,`gi i`] assume_tac)
            IN_MEASURABLE_BOREL_POS_SIMPLE_FN >>
        rfs[m_space_def,measurable_sets_def,SPACE])
);

val inv_meas_integral_o = store_thm(
    "inv_meas_integral_o",
    ``∀m a f g. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) a ∧
        g ∈ measurable a Borel ⇒ integral (space a,subsets a,inv_meas m f) g = integral m (g ∘ f)``,
    rw[integral_def,GSYM FN_PLUS_o,GSYM FN_MINUS_o] >>
    `fn_plus g ∈ measurable a Borel` by rw[IN_MEASURABLE_BOREL_FN_PLUS] >>
    `fn_minus g ∈ measurable a Borel` by rw[IN_MEASURABLE_BOREL_FN_MINUS] >>
    `(∀x. 0 ≤ fn_plus g x)` by rw[FN_PLUS_POS] >> `(∀x. 0 ≤ fn_minus g x)` by rw[FN_MINUS_POS] >>
    simp[inv_meas_pos_fn_integral_o]
);

val inv_meas_integrable_o = store_thm(
    "inv_meas_integrable_o",
    ``∀m a f g. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) a ∧
        g ∈ measurable a Borel ⇒ (integrable (space a,subsets a,inv_meas m f) g ⇔ integrable m (g ∘ f))``,
    rw[integrable_def,m_space_def,measurable_sets_def,GSYM FN_PLUS_o,GSYM FN_MINUS_o] >>
    (drule_all_then assume_tac) MEASURABLE_COMP >> simp[SPACE] >>
    `fn_plus g ∈ measurable a Borel` by rw[IN_MEASURABLE_BOREL_FN_PLUS] >>
    `fn_minus g ∈ measurable a Borel` by rw[IN_MEASURABLE_BOREL_FN_MINUS] >>
    `(∀x. 0 ≤ fn_plus g x)` by rw[FN_PLUS_POS] >> `(∀x. 0 ≤ fn_minus g x)` by rw[FN_MINUS_POS] >>
    simp[inv_meas_pos_fn_integral_o]
);

(* Halmos 45.A prep *)

val measure_eq_imp_pod_fn_integral_eq = store_thm(
    "measure_eq_imp_pod_fn_integral_eq",
    ``∀a mu nu f. (∀s. s ∈ subsets a ⇒ mu s = nu s) ∧ (∀x. 0 ≤ f x) ⇒
        pos_fn_integral (space a,subsets a,mu) f = pos_fn_integral (space a,subsets a,nu) f``,
    rw[pos_fn_integral_def] >> irule IRULER >> rw[EXTENSION] >> eq_tac >> rw[] >>
    qexists_tac `g` >> simp[] >> fs[psfis_def,psfs_def,IN_IMAGE] >> rw[] >>
    rename [`pos_simple_fn _ _ s e c`] >> qexists_tac `(s,e,c)` >> simp[] >>
    fs[pos_simple_fn_def,pos_simple_fn_integral_def,m_space_def,measurable_sets_def,measure_def] >>
    irule REAL_SUM_IMAGE_EQ >> rw[]
);

val measure_eq_imp_integral_eq = store_thm(
    "measure_eq_imp_integral_eq",
    ``∀a mu nu f. (∀s. s ∈ subsets a ⇒ mu s = nu s) ⇒
        integral (space a,subsets a,mu) f = integral (space a,subsets a,nu) f``,
    rw[integral_def] >> `(∀x. 0 ≤ fn_plus f x)` by rw[FN_PLUS_POS] >>
    `(∀x. 0 ≤ fn_minus f x)` by rw[FN_MINUS_POS] >>
    imp_res_tac measure_eq_imp_pod_fn_integral_eq >> rw[]
);

val measure_eq_semi_alg_imp_integral_eq = store_thm(
    "measure_eq_semi_alg_imp_integral_eq",
    ``∀a mu nu f. measure_space (space a,subsets (sigma (space a) (subsets a)),mu) ∧
        measure_space (space a,subsets (sigma (space a) (subsets a)),nu) ∧
        semi_algebra a ∧ (∀s. s ∈ subsets a ⇒ mu s = nu s) ⇒
        integral (space a,subsets (sigma (space a) (subsets a)),mu) f =
        integral (space a,subsets (sigma (space a) (subsets a)),nu) f``,
    rw[] >> (qspecl_then [`a`,`mu`,`nu`] assume_tac) measure_eq_semi_alg_imp_measure_eq >>
    rfs[] >> (dxrule_then assume_tac) measure_eq_imp_integral_eq >> fs[SPACE_SIGMA]
);

val prod_measure_inv_meas_rect = store_thm(
    "prod_measure_inv_meas_rect",
    ``∀m a b f g. measure_space m ∧ sigma_algebra a ∧ sigma_algebra b ∧ indep_rv m f g a b ∧
        f ∈ measurable (m_space m,measurable_sets m) a ∧
        g ∈ measurable (m_space m,measurable_sets m) b ⇒
        ∀s. s ∈ prod_sets (subsets a) (subsets b) ⇒
        prod_measure (space a,subsets a,inv_meas m f) (space b,subsets b,inv_meas m g) s =
        inv_meas m ((f ## g) ∘ DUP) s``,
    rw[prod_sets_def] >> rename [`indep_rv m f g a b`,`s ∈ subsets a`] >>
    imp_res_tac inv_meas_measure_space >>
    (qspecl_then [`(space a,subsets a,inv_meas m f)`,`(space b,subsets b,inv_meas m g)`,
        `s`,`t`] assume_tac) (INST_TYPE [alpha |-> ``:β``,beta |-> ``:γ``] prod_measure_prod_set) >>
    rfs[measure_prod_measure_space,measurable_sets_def,measure_def] >> pop_assum kall_tac >>
    simp[inv_meas_def] >> fs[indep_rv_alt] >> first_x_assum (drule_all_then assume_tac) >>
    fs[indep_alt] >> pop_assum (assume_tac o GSYM) >> simp[] >> pop_assum kall_tac >>
    irule IRULER >> rw[EXTENSION,DUP_DEF] >> eq_tac >> rw[]
);

val measure_eq_imp_measure_space = store_thm(
    "measure_eq_imp_measure_space",
    ``∀a mu nu. measure_space (space a,subsets a,nu) ∧ (∀s. s ∈ subsets a ⇒ mu s = nu s) ⇒
        measure_space (space a,subsets a,mu)``,
    rw[measure_space_def,positive_def,countably_additive_def,m_space_def,measurable_sets_def,measure_def]
    >- (fs[SPACE] >> `∅ ∈ subsets a` by fs[sigma_algebra_def,algebra_def] >> simp[])
    >- (first_x_assum (qspec_then `f` assume_tac) >> rfs[] >> `mu ∘ f = nu ∘ f` suffices_by rw[] >>
        rw[FUN_EQ_THM] >> first_x_assum irule >> fs[FUNSET])
);

(* Halmos 45.A *)

val integral_mul = store_thm(
    "integral_mul",
    ``∀m f g. measure_space m ∧ integrable m f ∧ integrable m g ∧ indep_rv m f g Borel Borel ⇒
        integral m (λx. f x * g x) = integral m f * integral m g``,
    `∀m f1 f2. measure_space m ∧ integrable m f1 ∧ integrable m f2 ∧ indep_rv m f1 f2 Borel Borel ⇒
        integral m (λz. f1 z * f2 z) = integral m f1 * integral m f2` suffices_by rw[] >>
    rw[] >>
    `(λz. f1 z * f2 z) = ((λ(x,y). x * y) ∘ (f1 ## f2) ∘ DUP)` by simp[FUN_EQ_THM,DUP_DEF] >>
    simp[] >> pop_assum kall_tac >>
    `integral m f1 = integral (space Borel,subsets Borel,inv_meas m f1) I ∧
        integral m f2 = integral (space Borel,subsets Borel,inv_meas m f2) I ∧
        integral m ((λ(x,y). x * y) ∘ (f1 ## f2) ∘ DUP) =
        integral (space Borel_2D,subsets Borel_2D,inv_meas m ((f1 ## f2) ∘ DUP)) (λ(x,y). x * y)` by (
        map_every (fn tms => (qspecl_then tms assume_tac) (GSYM inv_meas_integral_o))
            [[`m`,`Borel`,`f1`,`I`],[`m`,`Borel`,`f2`,`I`],
            [`m`,`Borel_2D`,`(f1 ## f2) ∘ DUP`,`(λ(x,y). x * y)`]] >>
        rfs[integrable_def] >> assume_tac SIGMA_ALGEBRA_BOREL >>
        fs[MEASURABLE_I] >> first_x_assum irule >> rw[]
        >- (irule IN_MEASURABLE_BOREL_2D_PAIR_MAP_DUP_ALT >> fs[measure_space_def,integrable_def]) >>
        `(λ(x,y). x * y) = (λz. FST z * SND z)` by simp[FUN_EQ_THM,PAIR_FUN] >>
        simp[] >> pop_assum kall_tac >> irule IN_MEASURABLE_BOREL_EXTMUL_ALT >>
        simp[SIGMA_ALGEBRA_BOREL_2D,FST_MBL,SND_MBL]) >>
    simp[] >> NTAC 3 (pop_assum kall_tac) >>
    `integrable (space Borel,subsets Borel,inv_meas m f1) I ∧
        integrable (space Borel,subsets Borel,inv_meas m f2) I` by (
        map_every (fn tms => (qspecl_then tms assume_tac) inv_meas_integrable_o)
            [[`m`,`Borel`,`f1`,`I`],[`m`,`Borel`,`f2`,`I`]] >>
        rfs[] >> assume_tac SIGMA_ALGEBRA_BOREL >>
        `f1 ∈ measurable (m_space m,measurable_sets m) Borel ∧
            f2 ∈ measurable (m_space m,measurable_sets m) Borel` by fs[integrable_def] >>
        fs[MEASURABLE_I]) >>
    `integral (space Borel,subsets Borel,inv_meas m f1) I *
        integral (space Borel,subsets Borel,inv_meas m f2) I =
        integral (prod_measure_space (space Borel,subsets Borel,inv_meas m f1)
        (space Borel,subsets Borel,inv_meas m f2)) (λ(x,y). I x * I y)` by (
        irule (GSYM integral_prod) >> simp[] >> fs[integrable_def,inv_meas_measure_space]) >>
    simp[] >> NTAC 3 (pop_assum kall_tac) >>
    `f1 ∈ measurable (m_space m,measurable_sets m) Borel ∧
        f2 ∈ measurable (m_space m,measurable_sets m) Borel` by fs[integrable_def] >>
    imp_res_tac inv_meas_measure_space >>
    `measure_space (prod_measure_space (space Borel,subsets Borel,inv_meas m f1)
        (space Borel,subsets Borel,inv_meas m f2))` by simp[prod_measure_space_measure_space] >>
    `prod_measure_space (space Borel,subsets Borel,inv_meas m f1)
        (space Borel,subsets Borel,inv_meas m f2) = (space Borel_2D,subsets Borel_2D,
        prod_measure (space Borel,subsets Borel,inv_meas m f1)
        (space Borel,subsets Borel,inv_meas m f2))` by (
        rw[prod_measure_space_def,m_space_def,measurable_sets_def] >>
        simp[Borel_2D_def,Borel_def,SPACE_SIGMA]) >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`(space Borel,subsets Borel,inv_meas m f1)`,
        `(space Borel,subsets Borel,inv_meas m f2)`] assume_tac) prod_sets_semi_alg >>
    rfs[m_space_def,measurable_sets_def] >>
    (qspecl_then [`m`,`Borel`,`Borel`,`f1`,`f2`] assume_tac) (GSYM prod_measure_inv_meas_rect) >>
    rfs[SIGMA_ALGEBRA_BOREL] >>
    (qspecl_then [`(space Borel × space Borel,prod_sets (subsets Borel) (subsets Borel))`,
        `inv_meas m ((f1 ## f2) ∘ DUP)`,`prod_measure (space Borel,subsets Borel,inv_meas m f1)
        (space Borel,subsets Borel,inv_meas m f2)`,`(λ(x,y). x * y)`] assume_tac)
        measure_eq_semi_alg_imp_integral_eq >>
    rfs[space_def,subsets_def] >>
    `space Borel × space Borel = space Borel_2D` by simp[Borel_def,Borel_2D_def,SPACE_SIGMA] >>
    `subsets (sigma (space Borel × space Borel) (prod_sets (subsets Borel) (subsets Borel))) =
        subsets Borel_2D` by simp[Borel_2D_def,Borel_def,SPACE_SIGMA] >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >> pop_assum irule >> simp[] >>
    irule inv_meas_measure_space >> simp[] >> irule IN_MEASURABLE_BOREL_2D_PAIR_MAP_DUP_ALT >>
    fs[measure_space_def]
);

(* π-λ theorem *)

val SIGMA_PI_LAMBDA = store_thm(
    "SIGMA_PI_LAMBDA",
    ``∀a. sigma_algebra a ⇔ pi_sys a ∧ lambda_sys a``,
    rw[pi_sys_def,lambda_sys_def,SIGMA_ALGEBRA_ALT_DISJOINT,ALGEBRA_ALT_INTER] >>
    eq_tac >> rw[EXTENSION] >> qexists_tac `∅` >> simp[]
);

val LAMBDA_SYS_DISJ_UNION = store_thm(
    "LAMBDA_SYS_DISJ_UNION",
    ``∀a s t. lambda_sys a ∧ s ∈ subsets a ∧ t ∈ subsets a ∧ DISJOINT s t ⇒ s ∪ t ∈ subsets a``,
    rw[lambda_sys_def] >>
    `∃(f: num -> α -> bool). ∀i. (i = 0 ⇒ f i = s) ∧ (i = SUC 0 ⇒ f i = t) ∧ (SUC 0 < i ⇒ f i = ∅)` by (
        rw[GSYM SKOLEM_THM] >> Cases_on `i` >> simp[] >> Cases_on `n` >> simp[]) >>
    first_x_assum (qspec_then `f` assume_tac) >>
    `s ∪ t = BIGUNION (IMAGE f 𝕌(:num))` by (rw[EXTENSION,IN_BIGUNION_IMAGE] >>
        eq_tac >> rw[]
        >- (qexists_tac `0` >> fs[])
        >- (qexists_tac `1` >> fs[])
        >- (rename [`x ∈ f n`] >> Cases_on `n` >> rfs[] >>
            rename [`x ∈ f (SUC n)`] >> Cases_on `n` >> rfs[])) >>
    simp[] >> pop_assum kall_tac >> pop_assum irule >> rw[]
    >- (Cases_on `n` >> fs[]
        >- (Cases_on `m` >> fs[] >> rw[] >> rename [`DISJOINT (f (SUC m)) s`] >>
            Cases_on `m` >> fs[] >> simp[DISJOINT_SYM]) >>
        rename [`m ≠ SUC n`] >> Cases_on `n` >> fs[] >> Cases_on `m` >> fs[])
    >- (rw[FUNSET] >> Cases_on `x` >> simp[] >> Cases_on `n` >> simp[])
);

val LAMBDA_SYS_DIFF_SUBSET = store_thm(
    "LAMBDA_SYS_DIFF_SUBSET",
    ``∀a s t. lambda_sys a ∧ s ∈ subsets a ∧ t ∈ subsets a ∧ t ⊆ s ⇒ s DIFF t ∈ subsets a``,
    rw[] >> (drule_then assume_tac) LAMBDA_SYS_DISJ_UNION >> fs[lambda_sys_def] >>
    `s DIFF t = space a DIFF ((space a DIFF s) ∪ t)` by (
        rw[EXTENSION] >> eq_tac >> rw[] >> fs[subset_class_def,SUBSET_DEF] >>
        last_x_assum (qspec_then `s` assume_tac) >> rfs[]) >>
    simp[] >> pop_assum kall_tac >> last_assum irule >>
    last_x_assum (qspec_then `s` assume_tac) >> rfs[] >>
    first_x_assum irule >> simp[] >> rw[DISJOINT_DEF,EXTENSION] >>
    CCONTR_TAC >> fs[SUBSET_DEF] >> first_x_assum (dxrule_then assume_tac) >> fs[]
);

val POW_LAMBDA_SYS = store_thm(
    "POW_LAMBDA_SYS",
    ``∀sp. lambda_sys (sp,POW sp)``,
    rw[] >> assume_tac POW_SIGMA_ALGEBRA >> fs[SIGMA_PI_LAMBDA]
);

val POW_PI_SYS = store_thm(
    "POW_PI_SYS",
    ``∀sp. pi_sys (sp,POW sp)``,
    rw[] >> assume_tac POW_SIGMA_ALGEBRA >> fs[SIGMA_PI_LAMBDA]
);

val LABMDA_SYS_LAMBDA = store_thm(
    "LABMDA_SYS_LAMBDA",
    ``∀sp sts. subset_class sp sts ⇒ lambda_sys (lambda sp sts)``,
    rw[lambda_sys_def,subset_class_def] >> fs[lambda_def,space_def,subsets_def] >> rw[]
    >- (pop_assum (qspec_then `POW sp` assume_tac) >> fs[POW_LAMBDA_SYS] >> fs[POW_DEF] >>
        pop_assum irule >> rw[SUBSET_DEF])
    >- (fs[lambda_sys_def,space_def,subsets_def])
    >- (fs[lambda_sys_def,space_def,subsets_def])
    >- (`f ∈ (𝕌(:num) → P)` by fs[FUNSET] >>
        fs[lambda_sys_def,space_def,subsets_def] >> first_x_assum irule >> simp[])
);

val SPACE_LAMBDA = store_thm(
    "SPACE_LAMBDA",
    ``∀sp sts. space (lambda sp sts) = sp``,
    rw[lambda_def,space_def]
);

val IN_LAMBDA = store_thm(
    "IN_LAMBDA",
    ``∀sp sts x. x ∈ sts ⇒ x ∈ subsets (lambda sp sts)``,
    rw[lambda_def,subsets_def] >> rfs[SUBSET_DEF]
);

val SIGMA_ALGEBRA_LAMBDA = store_thm(
    "SIGMA_ALGEBRA_LAMBDA",
    ``∀sp sts. pi_sys (sp,sts) ⇒ sigma_algebra (lambda sp sts)``,
    rw[pi_sys_def,space_def,subsets_def] >> (drule_then assume_tac) LABMDA_SYS_LAMBDA >>
    simp[SIGMA_PI_LAMBDA] >> fs[lambda_sys_def,pi_sys_def,SPACE_LAMBDA] >> rw[]
    >- (simp[EXTENSION] >> qexists_tac `∅` >> simp[]) >>
    `∀A. A ∈ subsets (lambda sp sts) ⇒
        lambda_sys (sp,{B | B ⊆ sp ∧ (A ∩ B) ∈ subsets (lambda sp sts)})` by (
        NTAC 2 (pop_assum kall_tac) >> rw[lambda_sys_def,space_def,subsets_def]
        >- (simp[subset_class_def])
        >- (`A ∩ (sp DIFF s) = A DIFF (A ∩ s)` by (rw[EXTENSION] >> eq_tac >> rw[] >> simp[] >>
                fs[subset_class_def] >> qpat_x_assum `A ∩ s ∈ _` kall_tac >>
                last_x_assum (dxrule_then assume_tac) >> rfs[SUBSET_DEF]) >>
            simp[] >> pop_assum kall_tac >> irule LAMBDA_SYS_DIFF_SUBSET >>
            simp[LABMDA_SYS_LAMBDA])
        >- (rw[BIGUNION_SUBSET,SUBSET_DEF] >> rename [`x ∈ f n`] >>
            fs[FUNSET,SUBSET_DEF] >> qpat_x_assum `∀x. _ ∧ _` (qspec_then `n` assume_tac) >> rfs[])
        >- (simp[GSYM INTER_BIGUNION_IMAGE] >> first_x_assum irule >> fs[FUNSET] >> rw[] >>
            first_x_assum (dxrule_then assume_tac) >> CCONTR_TAC >> fs[IN_DISJOINT] >>
            first_x_assum (qspec_then `x` assume_tac) >> rfs[])) >>
    `∀A B. A ∈ sts ∧ B ∈ subsets (lambda sp sts) ⇒ A ∩ B ∈ subsets (lambda sp sts)` by (
        NTAC 2 (qpat_x_assum `_ ∈ _` kall_tac) >>
        (qspecl_then [`sp`,`sts`] assume_tac) IN_LAMBDA >> rw[] >>
        first_assum (drule_then assume_tac) >>
        qpat_x_assum `∀A. _ ⇒ lambda_sys _` (dxrule_then assume_tac) >>
        `sts ⊆ {B | B ⊆ sp ∧ A ∩ B ∈ subsets (lambda sp sts)}` by (
            simp[SUBSET_DEF,lambda_def,subsets_def] >> fs[subset_class_def,SUBSET_DEF]) >>
        `B ∈ BIGINTER {s | sts ⊆ s ∧ lambda_sys (sp,s)}` by fs[lambda_def,subsets_def] >>
        fs[] >> pop_assum (dxrule_all_then assume_tac) >> fs[]) >>
    qpat_x_assum `∀A. _ ⇒ lambda_sys _` (drule_then assume_tac) >>
    `sts ⊆ {B | B ⊆ sp ∧ t ∩ B ∈ subsets (lambda sp sts)}` by (
        rw[SUBSET_DEF]
        >- (fs[subset_class_def,SUBSET_DEF] >> last_x_assum (dxrule_then assume_tac) >>
            pop_assum irule >> simp[])
        >- (first_x_assum (drule_all_then assume_tac) >> fs[INTER_COMM])) >>
    `s ∈ BIGINTER {r | sts ⊆ r ∧ lambda_sys (sp,r)}` by fs[lambda_def,subsets_def] >>
    fs[] >> pop_assum (dxrule_all_then assume_tac) >> fs[INTER_COMM]
);

val PI_LAMBDA_THM = store_thm(
    "PI_LAMBDA_THM",
    ``∀sp stsa stsb. stsa ⊆ stsb ∧ pi_sys (sp,stsa) ∧ lambda_sys (sp,stsb) ⇒
        subsets (sigma sp stsa) ⊆ stsb``,
    rw[] >> rw[SUBSET_DEF] >> fs[sigma_def,subsets_def] >>
    `stsa ⊆ subsets (lambda sp stsa)` by fs[SUBSET_DEF,IN_LAMBDA] >>
    (drule_then assume_tac) SIGMA_ALGEBRA_LAMBDA >> fs[lambda_def,subsets_def] >>
    first_x_assum (dxrule_all_then assume_tac) >> fs[]
);

(* 45.A for arbitrary products *)

val mut_indep_rv_indep_prod = store_thm(
    "mut_indep_rv_indep_prod",
    ``∀n p fs. 0 < n ∧ prob_space p ∧ mut_indep_rv (SUC n) p fs (λi. Borel) ∧
        (∀i. i < SUC n ⇒ (fs i) ∈ measurable (p_space p,events p) Borel) ⇒
        indep_rv p (λx. prod (0,n) (λi. fs i x)) (fs n) Borel Borel``,
    rw[] >>
    `sigma_algebra (p_space p,events p)` by (pop_assum (qspec_then `0` assume_tac) >>
        fs[measurable_def]) >>
    (qspecl_then [`n`,`(p_space p,events p)`,`fs`] assume_tac)
        IN_MEASURABLE_BOREL_EXTPROD_PREIMAGE_SIGMA >>
    rfs[space_def] >>
    Q.ABBREV_TAC `sts = {BIGINTER (IMAGE (λi. PREIMAGE (fs i) (ss i) ∩ p_space p) (count n)) |
        ss ∈ (𝕌(:num) → subsets Borel)}` >>
    `sts ⊆ {s | ∀t. t ∈ subsets Borel ⇒ indep p s (PREIMAGE (fs n) t ∩ p_space p)}` by (
        rw[SUBSET_DEF,indep_def] >> Q.UNABBREV_TAC `sts` >> fs[]
        >- ((qspec_then `(p_space p,events p)` assume_tac) SIGMA_ALGEBRA_COUNTABLE_INTER >>
            fs[subsets_def] >> pop_assum irule >> simp[COUNTABLE_IMAGE_NUM,COUNT_EMPTY] >>
            rw[SUBSET_DEF] >> last_x_assum (qspec_then `i` assume_tac) >>
            rfs[measurable_def,space_def,subsets_def] >> first_x_assum irule >> fs[FUNSET])
        >- (last_x_assum (qspec_then `n` assume_tac) >> rfs[measurable_def,space_def,subsets_def])
        >- (`mut_indep_rv n p fs (λi. Borel)` by (fs[mut_indep_rv_recur] >>
                (qspecl_then [`n`,`p`,`fs`,`(λi. Borel)`] assume_tac) mut_indep_rv_recur >> rfs[]) >>
            fs[mut_indep_rv_def,mut_indep_def] >> rw[] >>
            last_x_assum (qspec_then `(λi. if i = n then t else (ss i))` assume_tac) >>
            first_x_assum (qspec_then `ss` assume_tac) >>
            `(∀i. i < SUC n ⇒ (λi. if i = n then t else ss i) i ∈ subsets Borel)`
                by (rw[] >> fs[FUNSET]) >>
            `(∀i. i < n ⇒ ss i ∈ subsets Borel)` by (rw[] >> fs[FUNSET]) >>
            fs[] >> NTAC 2 (pop_assum kall_tac) >> fs[BIGINTER_IMAGE_COUNT_SUC_COMM,prod_def] >>
            `(IMAGE (λi. PREIMAGE (fs i) (if i = n then t else ss i) ∩ p_space p) (count n)) =
                (IMAGE (λi. PREIMAGE (fs i) (ss i) ∩ p_space p) (count n))` by (
                irule IMAGE_CONG >> rw[count_def]) >>
            fs[] >>
            `prod (0,n) (prob p ∘ (λi. PREIMAGE (fs i) (if i = n then t else ss i) ∩ p_space p)) =
                prod (0,n) (prob p ∘ (λi. PREIMAGE (fs i) (ss i) ∩ p_space p))` suffices_by rw[] >>
            irule PROD_EQ >> rw[])) >>
    `pi_sys (p_space p,sts)` by (simp[pi_sys_def,space_def,subsets_def] >>
        Q.UNABBREV_TAC `sts` >> rw[subset_class_def]
        >- (irule BIGINTER_SUBSET >> rw[EXTENSION] >> rw[SUBSET_DEF] >>
            qexists_tac `0` >> simp[])
        >- (simp[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `(λi. ∅)` >> simp[FUNSET] >>
            assume_tac SIGMA_ALGEBRA_BOREL >> fs[SIGMA_ALGEBRA_FN])
        >- (rename [`ts ∈ _`] >> qexists_tac `(λi. ss i ∩ ts i)` >> rw[]
            >- (rw[EXTENSION,IN_BIGINTER_IMAGE] >> eq_tac >> rw[] >>
                first_x_assum (dxrule_then assume_tac) >> fs[])
            >- (fs[FUNSET] >> rw[] >> irule SIGMA_ALGEBRA_INTER >> simp[SIGMA_ALGEBRA_BOREL]))) >>
    `lambda_sys (p_space p,{s | ∀t. t ∈ subsets Borel ⇒ indep p s (PREIMAGE (fs n) t ∩ p_space p)})` by (
        simp[lambda_sys_def,space_def,subsets_def] >> Q.UNABBREV_TAC `sts` >> rw[subset_class_def]
        >- (assume_tac SIGMA_ALGEBRA_BOREL >> fs[SIGMA_ALGEBRA_FN] >>
            NTAC 2 (pop_assum kall_tac) >> first_x_assum (dxrule_then assume_tac) >>
            fs[indep_def,subset_class_def,space_def,subsets_def])
        >- (simp[indep_def] >> fs[prob_space_def,measure_space_def,positive_def,prob_def] >>
            fs[SIGMA_ALGEBRA_FN,space_def,subsets_def] >>
            first_x_assum (qspec_then `n` assume_tac) >> rfs[measurable_def,space_def,subsets_def])
        >- (last_x_assum (dxrule_then assume_tac) >> fs[indep_def] >>
            simp[EVENTS_COMPL] >> Q.ABBREV_TAC `pt = PREIMAGE (fs n) t ∩ p_space p` >>
            `(p_space p DIFF s) ∩ pt = (pt DIFF s ∩ pt)` by (
                rw[EXTENSION] >> eq_tac >> rw[] >> fs[] >>
                (dxrule_all_then assume_tac) PROB_SPACE_IN_P_SPACE >> fs[]) >>
            simp[] >> pop_assum kall_tac >> `s ∩ pt ∈ events p` by simp[EVENTS_INTER] >>
            `s ∩ pt ⊆ pt` by rw[SUBSET_DEF] >> simp[PROB_COMPL,PROB_COMPL_SUBSET] >>
            simp[REAL_SUB_RDISTRIB])
        >- (fs[indep_def,FUNSET] >> last_x_assum (dxrule_then assume_tac) >>
            Q.ABBREV_TAC `pt = PREIMAGE (fs n) t ∩ p_space p` >> pop_assum kall_tac >>
            `BIGUNION (IMAGE f 𝕌(:num)) ∈ events p` by (irule EVENTS_COUNTABLE_UNION >>
                simp[countable_image_nats] >> rw[SUBSET_DEF] >> fs[]) >>
            simp[GSYM INTER_BIGUNION_IMAGE_COMM] >>
            (qspecl_then [`p`,`BIGUNION (IMAGE f 𝕌(:num))`,`f`] assume_tac) PROB_COUNTABLY_ADDITIVE >>
            rfs[FUNSET] >> (dxrule_then assume_tac) SER_CMUL >>
            pop_assum (qspec_then `prob p pt` assume_tac) >>
            `(λn. prob p pt * (prob p ∘ f) n) = (λx. prob p (f x) * prob p pt)` by (
                rw[FUN_EQ_THM] >> simp[REAL_MUL_COMM]) >>
            `prob p pt * prob p (BIGUNION (IMAGE f 𝕌(:num))) =
                prob p (BIGUNION (IMAGE f 𝕌(:num))) * prob p pt` by simp[REAL_MUL_COMM] >>
            fs[] >> NTAC 2 (pop_assum kall_tac) >>
            (qspecl_then [`p`,`BIGUNION (IMAGE (λx. f x ∩ pt) 𝕌(:num))`,`(λx. f x ∩ pt)`] assume_tac)
                PROB_COUNTABLY_ADDITIVE >>
            rfs[FUNSET] >>
            `(∀x. f x ∩ pt ∈ events p)` by (rw[] >> irule EVENTS_INTER >> simp[]) >>
            `(∀i j. i ≠ j ⇒ DISJOINT (f i ∩ pt) (f j ∩ pt))` by (rw[] >>
                first_x_assum (dxrule_all_then assume_tac) >> fs[DISJOINT_DEF,EXTENSION] >>
                rw[] >> pop_assum (qspec_then `x` assume_tac) >> fs[]) >>
            fs[] >> NTAC 2 (pop_assum kall_tac) >>
            `prob p ∘ (λx. f x ∩ pt) = (λx. prob p (f x) * prob p pt)` by rw[FUN_EQ_THM] >>
            fs[] >> pop_assum kall_tac >> NTAC 2 ((dxrule_then assume_tac) SUM_UNIQ) >> simp[])) >>
    (dxrule_all_then assume_tac) PI_LAMBDA_THM >> rw[indep_rv_def] >>
    fs[measurable_def,SPACE_SIGMA] >> first_x_assum (qspec_then `A` assume_tac) >> rfs[SUBSET_DEF]
);

val integral_pi = store_thm(
    "integral_pi",
    ``∀(n:num) p fs. (0 < n) ∧ prob_space p ∧ (∀i. i < n ⇒ integrable p (fs i)) ∧
        mut_indep_rv n p fs (λi. Borel) ⇒
        expectation p (λx. prod (0,n) (λi. fs i x)) = prod (0,n) (λi. expectation p (fs i))``,
    Induct_on `n` >> rw[] >> rename [`SUC m`] >> Cases_on `m`
    >- (simp[extreal_prod_def,mul_lone] >> simp[GSYM o_DEF,GSYM I_ALT]) >>
    `0 < SUC n` by fs[] >> rename [`0 < n`] >> simp[extreal_prod_def] >>
    `mut_indep_rv n p fs (λi. Borel)` by (
        (qspecl_then [`n`,`p`,`fs`,`(λi. Borel)`] assume_tac) mut_indep_rv_recur >>
        rfs[integrable_def,p_space_def,events_def]) >>
    last_x_assum (qspecl_then [`p`,`fs`] assume_tac) >> rfs[] >>
    `indep_rv p (λx. prod (0,n) (λi. fs i x)) (fs n) Borel Borel` by (
        irule mut_indep_rv_indep_prod >> simp[] >>
        fs[integrable_def,p_space_def,events_def]) >>
    fs[expectation_def] >>
    `integrable p (λx. prod (0,n) (λi. fs i x))` suffices_by (rw[] >>
        (qspecl_then [`p`,`(λx. prod (0,n) (λi. fs i x))`,`fs n`] assume_tac) integral_mul >>
        rfs[prob_space_def]) >>
    irule integral_finite_integrable >> fs[prob_space_def] >> rw[] >>
    `(λx. prod (0,n) (λi. fs i x)) ∈ measurable (m_space p,measurable_sets p) Borel`
        by (irule IN_MEASURABLE_BOREL_EXTPROD_ALT >> fs[measure_space_def,integrable_def]) >>
    simp[] >>
    `∃f. ∀i. i < n ⇒ integral p (fs i) = Normal (f i)` by (simp[GSYM SKOLEM_THM] >> rw[] >>
        Cases_on `i < n` >> simp[] >> irule integrable_integral_finite >> simp[]) >>
    `prod (0,n) (λi. integral p (fs i)) = prod (0,n) (Normal ∘ f)`
        by (irule extreal_prod_eq >> rw[]) >>
    simp[extreal_prod_normal]
);

val _ = export_theory();