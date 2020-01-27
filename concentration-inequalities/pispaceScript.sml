open HolKernel Parse boolLib bossLib;
open combinTheory;
open pairTheory;
open arithmeticTheory;
open pred_setTheory;
open realTheory;
open real_sigmaTheory;
open util_probTheory;
open c487306_extrealTheory;
open c487306_measureTheory;
open c487306_lebesgueTheory;
open trivialTheory;
open halmosTheory;

val _ = new_theory "pispace";

(* Definitions *)

val pi_pair_def = Define `pi_pair (n:num) f e = (λi. if (i = n) then e else f i)`;

val pi_cross_def = Define `pi_cross (n:num) fs s = {pi_pair n f e | f ∈ fs ∧ e ∈ s}`;

val pi_prod_sets_def = Define `pi_prod_sets n fsts sts = {pi_cross n fs s | fs ∈ fsts ∧ s ∈ sts}`;

val pi_m_space_def = Define `(pi_m_space 0 mss = {(λi. ARB)}) ∧
    (pi_m_space (SUC n) mss = pi_cross n (pi_m_space n mss) (m_space (mss n)))`;

val pi_measurable_sets_def = Define `(pi_measurable_sets 0 mss = POW {(λi. ARB)}) ∧
    (pi_measurable_sets (SUC n) mss = subsets (sigma (pi_m_space (SUC n) mss)
    (pi_prod_sets n (pi_measurable_sets n mss) (measurable_sets (mss n)))))`;

val pi_measure_def = Define `(pi_measure 0 mss = (λfs. if (fs = ∅) then 0 else 1)) ∧
    (pi_measure (SUC n) mss = (λfs. real (integral (mss n)
    (λe. Normal (pi_measure n mss ((PREIMAGE (λf. pi_pair n f e) fs) ∩ (pi_m_space n mss)))))))`;

val pi_measure_space_def = Define `pi_measure_space n mss =
    (pi_m_space n mss, pi_measurable_sets n mss, pi_measure n mss)`;

val pi_id_msp_def = Define `pi_id_msp = ({(λi:num. ARB:α)},POW {(λi:num. ARB:α)},
    (λfs:(num->α)->bool. if fs = ∅ then (0:real) else 1))`;

val measurability_preserving_def = Define `measurability_preserving a b = {f |
    sigma_algebra a ∧ sigma_algebra b ∧ BIJ f (space a) (space b) ∧
    (∀s. s ∈ subsets a ⇒ IMAGE f s ∈ subsets b) ∧
    ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a}`;

val measure_preserving_def = Define `measure_preserving m0 m1 = {f |
    f ∈ measurability_preserving (m_space m0,measurable_sets m0) (m_space m1,measurable_sets m1) ∧
    ∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))}`;

val isomorphic_def = Define `isomorphic m0 m1 ⇔ ∃f. f ∈ measure_preserving m0 m1`;

(* Alternate Representations/Definitions *)

val measure_preserving_alt = store_thm(
    "measure_preserving_alt",
    ``∀m0 m1. measure_preserving m0 m1 = {f |
        f ∈ measurability_preserving (m_space m0,measurable_sets m0) (m_space m1,measurable_sets m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))}``,
    rw[measure_preserving_def,EXTENSION] >> eq_tac >> rw[] >>
    Q.RENAME_TAC [`f ∈ measurability_preserving _ _`]
    >- (qpat_x_assum `∀s. _` (qspec_then `PREIMAGE f s ∩ m_space m0` assume_tac) >>
        rfs[measurability_preserving_def,space_def,subsets_def] >>
        `(IMAGE f (PREIMAGE f s ∩ m_space m0)) = s` suffices_by rw[] >>
        irule BIJ_IMAGE_PREIMAGE >> qexists_tac `m_space m1` >> rw[] >>
        fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def])
    >- (qpat_x_assum `∀s. _` (qspec_then `IMAGE f s` assume_tac) >>
        rfs[measurability_preserving_def,space_def,subsets_def] >>
        `(PREIMAGE f (IMAGE f s) ∩ m_space m0) = s` suffices_by rw[] >>
        irule BIJ_PREIMAGE_IMAGE >> rw[]
        >- (fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def])
        >- (qexists_tac `m_space m1` >> rw[]))
);

val measure_preserving_full = store_thm(
    "measure_preserving_full",
    ``∀m0 m1. measure_preserving m0 m1 = {f |
        f ∈ measurability_preserving (m_space m0,measurable_sets m0) (m_space m1,measurable_sets m1) ∧
        (∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))}``,
    rw[EXTENSION] >> eq_tac >> rw[]
    >- (fs[measure_preserving_def])
    >- (fs[measure_preserving_def])
    >- (fs[measure_preserving_alt])
    >- (rw[measure_preserving_alt])
);

(* Isomorphism as an Equivalence Relation *)

val isomorphic_refl = store_thm(
    "isomorphic_refl",
    ``∀m. measure_space m ⇒ isomorphic m m``,
    rw[isomorphic_def,measure_preserving_def,measurability_preserving_def,space_def,subsets_def] >>
    qexists_tac `I` >> rw[MEASURE_SPACE_SIGMA_ALGEBRA,IMAGE_I,PREIMAGE_I] >>
    rw[I_ALT,BIJ_ID] >> `s ∩ m_space m = s` suffices_by rw[] >>
    rw[EXTENSION] >> eq_tac >> rw[] >> dxrule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >>
    rfs[SUBSET_DEF]
);

val isomorphic_sym_imp = store_thm(
    "isomorphic_sym_imp",
    ``∀m0 m1. isomorphic m0 m1 ⇒ isomorphic m1 m0``,
    rw[isomorphic_def] >> rw[measure_preserving_def] >>
    fs[measure_preserving_alt,measurability_preserving_def,space_def,subsets_def] >>
    drule_then assume_tac BIJ_INV >> fs[] >> qexists_tac `g` >> rw[]
    >- (`IMAGE g s = PREIMAGE f s ∩ m_space m0` suffices_by rw[] >>
        rw[EXTENSION,PREIMAGE_def] >> eq_tac >> strip_tac
        >- (`s ⊆ m_space m1` by fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def] >>
            `x' ∈ m_space m1` by rfs[SUBSET_DEF] >> rw[] >> fs[BIJ_ALT,FUNSET])
        >- (qexists_tac `f x` >> rw[]))
    >- (`PREIMAGE g s ∩ m_space m1 = IMAGE f s` suffices_by rw[] >>
        rw[EXTENSION,PREIMAGE_def] >> eq_tac >> strip_tac
        >- (qexists_tac `g x` >> rw[])
        >- (`s ⊆ m_space m0` by fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def] >>
            `x' ∈ m_space m0` by rfs[SUBSET_DEF] >> rw[] >> fs[BIJ_ALT,FUNSET]))
    >- (`IMAGE g s = PREIMAGE f s ∩ m_space m0` suffices_by rw[] >>
        rw[EXTENSION,PREIMAGE_def] >> eq_tac >> strip_tac
        >- (`s ⊆ m_space m1` by fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def] >>
            `x' ∈ m_space m1` by rfs[SUBSET_DEF] >> rw[] >> fs[BIJ_ALT,FUNSET])
        >- (qexists_tac `f x` >> rw[]))
);

val isomorphic_sym = store_thm(
    "isomorphic_sym",
    ``∀m0 m1. isomorphic m0 m1 ⇔ isomorphic m1 m0``,
    rw[] >> eq_tac >> rw[isomorphic_sym_imp]
);

val isomorphic_trans = store_thm(
    "isomorphic_trans",
    ``∀m0 m1 m2. isomorphic m0 m1 ∧ isomorphic m1 m2 ⇒ isomorphic m0 m2``,
    rw[isomorphic_def,measure_preserving_def,measurability_preserving_def,space_def,subsets_def] >>
    Q.RENAME_TAC [`BIJ g _ _`] >> qexists_tac `g ∘ f` >> rw[]
    >- (irule BIJ_COMPOSE >> qexists_tac `m_space m1` >> rw[])
    >- (rw[IMAGE_COMPOSE])
    >- (rw[GSYM PREIMAGE_COMP] >>
        `PREIMAGE f (PREIMAGE g s) ∩ m_space m0 =
            PREIMAGE f (PREIMAGE g s ∩ m_space m1) ∩ m_space m0` suffices_by rw[] >>
        rw[EXTENSION] >> eq_tac >> rw[PREIMAGE_def] >> fs[BIJ_ALT,FUNSET])
    >- (rw[IMAGE_COMPOSE])
);

val isomorphic_equiv_on_measure_spaces = store_thm(
    "isomorphic_equiv_on_measure_spaces",
    ``isomorphic equiv_on measure_space``,
    rw[equiv_on_def]
    >- (fs[IN_DEF] >> rw[isomorphic_refl])
    >- (metis_tac[isomorphic_sym])
    >- (irule (INST_TYPE [beta |-> ``:α``,gamma |-> ``:α``] isomorphic_trans) >>
        qexists_tac `y` >> rw[])
);

(* Trivial Measure Space *)

val pi_measure_space_0_pi_id_msp = store_thm(
    "pi_measure_space_0_pi_id_msp",
    ``∀mss. pi_measure_space 0 mss = pi_id_msp``,
    rw[pi_measure_space_def,pi_m_space_def,pi_measurable_sets_def,pi_measure_def,pi_id_msp_def]
);

val pi_id_msp_iso_id_msp = store_thm(
    "pi_id_msp_iso_id_msp",
    ``isomorphic pi_id_msp id_msp``,
    rw[isomorphic_def,pi_id_msp_def,id_msp_def] >> qexists_tac `(λx. ARB)` >>
    rw[measure_preserving_def,measurability_preserving_def,
        m_space_def,measurable_sets_def,measure_def,space_def,subsets_def,POW_SIGMA_ALGEBRA]
    >- (rw[BIJ_DEF,INJ_DEF,SURJ_DEF])
    >- (fs[IN_POW_SING])
    >- (fs[IN_POW_SING,PREIMAGE_def])
);

val iso_measure_space_imp_measure_space = store_thm(
    "iso_measure_space_imp_measure_space",
    ``∀m0 m1. measure_space m0 ∧ isomorphic m0 m1 ⇒ measure_space m1``,
    rw[isomorphic_def,measure_preserving_def,measurability_preserving_def,measure_space_def,
        sigma_algebra_def,algebra_def,subset_class_def,positive_def,countably_additive_def,
        m_space_def,measurable_sets_def,measure_def,space_def,subsets_def] >> fs[]
    >- (RES_TAC >> fs[])
    >- (qpat_x_assum `∀s. s ∈ measurable_sets m1 ⇒ _ ⊆ _`
            (qspec_then `s` assume_tac) >> rfs[] >>
        qpat_x_assum `∀s. s ∈ measurable_sets m1 ⇒ _ ∈ measurable_sets m0`
            (qspec_then `s` assume_tac) >> rfs[] >>
        qpat_x_assum `∀s. s ∈ measurable_sets m0 ⇒ 0 ≤ _`
            (qspec_then `PREIMAGE f s ∩ m_space m0` assume_tac) >> rfs[] >>
        drule_all_then assume_tac BIJ_IMAGE_PREIMAGE >> fs[])
    >- (Q.RENAME_TAC [`measure m1 ∘ sf`] >>
        qpat_x_assum `∀f'. _ ∧ _ ∧ _ ⇒ _`
            (qspec_then `(λi. PREIMAGE f (sf i) ∩ m_space m0)` assume_tac) >>
        fs[IMAGE_BIGUNION,GSYM IMAGE_COMPOSE] >>
        `(IMAGE f ∘ (λi. PREIMAGE f (sf i) ∩ m_space m0)) = sf` by (
            `∀i. IMAGE f (PREIMAGE f (sf i) ∩ m_space m0) = sf i` suffices_by rw[FUN_EQ_THM] >>
            strip_tac >> irule BIJ_IMAGE_PREIMAGE >> qexists_tac `m_space m1` >> rw[] >>
            fs[FUNSET]) >>
        `measure m0 ∘ (λi. PREIMAGE f (sf i) ∩ m_space m0) = measure m1 ∘ sf` by (
            rw[FUN_EQ_THM] >> `sf x ∈ measurable_sets m1` by fs[FUNSET] >>
            qpat_x_assum `∀s. s ∈ measurable_sets m1 ⇒ _ ⊆ _`
                (qspec_then `sf x` assume_tac) >> rfs[] >>
            qpat_x_assum `∀s. s ∈ measurable_sets m1 ⇒ _ ∈ measurable_sets m0`
                (qspec_then `sf x` assume_tac) >> rfs[] >>
            qpat_x_assum `∀s. s ∈ measurable_sets m0 ⇒ (_ = _)`
                (qspec_then `PREIMAGE f (sf x) ∩ m_space m0` assume_tac) >> rfs[] >>
            drule_all_then assume_tac BIJ_IMAGE_PREIMAGE >> fs[]) >>
        fs[] >> NTAC 2 (pop_assum kall_tac) >> pop_assum irule >> rw[]
        >- (qpat_x_assum `∀m n. _` (dxrule_then assume_tac) >> fs[DISJOINT_DEF,EXTENSION] >>
            CCONTR_TAC >> fs[PREIMAGE_def] >>
            qpat_x_assum `∀x. _ ∨ _` (qspec_then `f x` assume_tac) >> rfs[])
        >- (qpat_x_assum `∀c. _ ∧ _ ⇒ BIGUNION c ∈ measurable_sets m0` irule >>
            rw[countable_image_nats] >>
            `∀i. PREIMAGE f (sf i) ∩ m_space m0 ∈ measurable_sets m0`
                suffices_by (rw[SUBSET_DEF] >> fs[]) >>
            strip_tac >> `sf i ∈ measurable_sets m1` by fs[FUNSET] >> fs[])
        >- (`∀i. PREIMAGE f (sf i) ∩ m_space m0 ∈ measurable_sets m0`
                suffices_by (rw[FUNSET] >> fs[]) >>
            strip_tac >> `sf i ∈ measurable_sets m1` by fs[FUNSET] >> fs[]))
);

val pi_id_msp_measure_space = store_thm(
    "pi_id_msp_measure_space",
    ``measure_space pi_id_msp``,
    assume_tac (INST_TYPE [alpha |-> ``:β``] id_msp_measure_space) >>
    assume_tac pi_id_msp_iso_id_msp >> dxrule_all_then assume_tac isomorphic_sym_imp >>
    irule (INST_TYPE [alpha |-> ``:β``,beta |-> ``:num -> α``] iso_measure_space_imp_measure_space) >>
    qexists_tac `id_msp` >> rw[]
);

(* Isomorphism Decomposition *)

val pi_measure_space_subset_class = store_thm(
    "pi_measure_space_subset_class",
    ``∀mss n. (∀i. i < n ⇒ subset_class (m_space (mss i)) (measurable_sets (mss i))) ⇒
        subset_class (pi_m_space n mss) (pi_measurable_sets n mss)``,
    NTAC 2 strip_tac >> Induct_on `n` >> rw[pi_m_space_def,pi_measurable_sets_def]
    >- (assume_tac pi_id_msp_measure_space >> fs[pi_id_msp_def] >>
        fs[measure_space_def,m_space_def,measurable_sets_def] >>
        fs[sigma_algebra_def,algebra_def,space_def,subsets_def])
    >- (`subset_class (pi_m_space n mss) (pi_measurable_sets n mss)` by rw[] >>
        `subset_class (m_space (mss n)) (measurable_sets (mss n))` by rw[] >>
        map_every Q.ABBREV_TAC [`pi_sp = pi_cross n (pi_m_space n mss) (m_space (mss n))`,
            `pi_sts = pi_prod_sets n (pi_measurable_sets n mss) (measurable_sets (mss n))`] >>
        `sigma_algebra (pi_sp,subsets (sigma pi_sp pi_sts))`
            suffices_by rw[sigma_algebra_def,algebra_def,space_def,subsets_def] >>
        rw[SIGMA_REDUCE] >> irule SIGMA_ALGEBRA_SIGMA >> NTAC 2 (last_x_assum kall_tac) >>
        map_every Q.UNABBREV_TAC [`pi_sp`,`pi_sts`] >> fs[subset_class_def] >> rw[] >>
        fs[pi_prod_sets_def] >> NTAC 2 (last_x_assum (dxrule_then assume_tac)) >>
        fs[SUBSET_DEF] >> rw[pi_cross_def] >> NTAC 2 (last_x_assum (dxrule_then assume_tac)) >>
        map_every qexists_tac [`f`,`e`] >> rw[])
);

val pi_m_space_elem_arb = store_thm(
    "pi_m_space_elem_arb",
    ``∀mss n f i. f ∈ pi_m_space n mss ∧ n ≤ i ⇒ (f i = ARB)``,
    NTAC 2 strip_tac >> Induct_on `n` >> rw[pi_m_space_def] >>
    Q.RENAME_TAC [`f_e i = _`] >> fs[pi_cross_def] >>
    last_x_assum (dxrule_then assume_tac) >> pop_assum (qspec_then `i` assume_tac) >>
    NTAC 2 (last_x_assum kall_tac) >> rfs[pi_pair_def]
);

val prod_measure_space_pi_measure_space_sigma_algebra = store_thm(
    "prod_measure_space_pi_measure_space_sigma_algebra",
    ``∀mss n. (∀i. i < SUC n ⇒ subset_class (m_space (mss i)) (measurable_sets (mss i))) ⇒
        sigma_algebra (sigma (pi_m_space n mss × m_space (mss n))
        (prod_sets (pi_measurable_sets n mss) (measurable_sets (mss n))))``,
    rw[] >> irule SIGMA_ALGEBRA_SIGMA >>
    `subset_class (pi_m_space n mss) (pi_measurable_sets n mss)`
        by rw[pi_measure_space_subset_class] >>
    `subset_class (m_space (mss n)) (measurable_sets (mss n))` by rw[] >>
    last_x_assum kall_tac >> fs[subset_class_def] >> rw[prod_sets_def,CROSS_DEF] >>
    NTAC 2 (last_x_assum (dxrule_then assume_tac)) >> fs[SUBSET_DEF]
);

val prod_measure_space_pi_measure_space_bij = store_thm(
    "prod_measure_space_pi_measure_space_bij",
    ``∀mss n. BIJ (λ(f,e). pi_pair n f e) (pi_m_space n mss × m_space (mss n))
        (pi_cross n (pi_m_space n mss) (m_space (mss n)))``,
    rw[BIJ_DEF,INJ_DEF,SURJ_DEF]
    >- (`∃f e. x = (f,e)` by rw[ABS_PAIR_THM] >> rw[pi_cross_def] >>
        map_every qexists_tac [`f`,`e`] >> fs[])
    >- (`(∃f e. x = (f,e)) ∧ (∃g a. y = (g,a))` by rw[ABS_PAIR_THM] >> fs[pi_pair_def] >>
        NTAC 2 (pop_assum kall_tac) >> fs[FUN_EQ_THM] >>
        first_assum (qspec_then `n` assume_tac) >> fs[] >> rw[] >>
        first_x_assum (qspec_then `x` assume_tac) >> Cases_on `x < n` >> fs[NOT_LESS] >>
        map_every
            (fn tm => (qspecl_then [`mss`,`n`,tm,`x`] assume_tac) pi_m_space_elem_arb) [`f`,`g`] >>
        rfs[])
    >- (`∃f e. x = (f,e)` by rw[ABS_PAIR_THM] >> rw[pi_cross_def] >>
        map_every qexists_tac [`f`,`e`] >> fs[])
    >- (fs[pi_cross_def] >> qexists_tac `(f,e)` >> rw[])
);

val prod_measure_space_pi_measure_space_bij_pow = store_thm(
    "prod_measure_space_pi_measure_space_bij_pow",
    ``∀mss n. BIJ (IMAGE (λ(f,e). pi_pair n f e))
        (POW (pi_m_space n mss × m_space (mss n)))
        (POW (pi_cross n (pi_m_space n mss) (m_space (mss n))))``,
    rw[] >> irule BIJ_POW >> simp[prod_measure_space_pi_measure_space_bij]
);

val pi_measure_space_iso_prod_measure_space = store_thm(
    "pi_measure_space_iso_prod_measure_space",
    ``∀mss n. (∀i. i < SUC n ⇒ subset_class (m_space (mss i)) (measurable_sets (mss i))) ⇒
        isomorphic (pi_measure_space (SUC n) mss)
        (prod_measure_space_hor (pi_measure_space n mss) (mss n))``,
    rw[] >> irule isomorphic_sym_imp >>
    rw[pi_measure_space_def,pi_m_space_def,pi_measurable_sets_def] >>
    rw[prod_measure_space_hor_def,m_space_def,measurable_sets_def,measure_def] >>
    rw[isomorphic_def] >> qexists_tac `(λ(f,e). pi_pair n f e)` >>
    rw[measure_preserving_def,m_space_def,measurable_sets_def,measure_def] >>
    rw[measurability_preserving_def,space_def,subsets_def]
    >- (rw[SIGMA_REDUCE,prod_measure_space_pi_measure_space_sigma_algebra])
    >- (rw[SIGMA_REDUCE] >> irule SIGMA_ALGEBRA_SIGMA >>
        dxrule_then assume_tac pi_measure_space_subset_class >>
        fs[pi_m_space_def,pi_measurable_sets_def,subset_class_def] >> rw[] >>
        last_x_assum irule >> rw[IN_SIGMA])
    >- (rw[prod_measure_space_pi_measure_space_bij])
    >- (fs[sigma_def,subsets_def] >> rw[] >>
        (qspecl_then [`mss`,`n`] assume_tac) pi_measure_space_subset_class >> rfs[] >>
        last_x_assum (qspec_then `n` assume_tac) >> rfs[] >>
        last_x_assum (qspec_then `PREIMAGE (λs. IMAGE (λ(f,e). pi_pair n f e) s) P ∩
            POW (pi_m_space n mss × m_space (mss n))` assume_tac) >>
        fs[IN_PREIMAGE] >>
        `IMAGE (λ(f,e). pi_pair n f e) s ∈ P ∧ s ∈ POW (pi_m_space n mss × m_space (mss n))`
            suffices_by rw[] >>
        pop_assum irule >> rw[]
        >- (fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def,POW_DEF] >> rw[]
            >- (qpat_x_assum `∀s. _ ⇒ _ DIFF _ ∈ _` (dxrule_then assume_tac) >>
                `pi_cross n (pi_m_space n mss) (m_space (mss n)) DIFF IMAGE (λ(f,e). pi_pair n f e) s =
                    IMAGE (λ(f,e). pi_pair n f e) (pi_m_space n mss × m_space (mss n) DIFF s)`
                    suffices_by (rw[] >> fs[]) >>
                pop_assum kall_tac >> fs[IN_POW,SUBSET_DEF] >> rw[EXTENSION,IN_IMAGE] >>
                eq_tac >> rw[]
                >- (fs[pi_cross_def] >> qexists_tac `(f,e)` >>
                    pop_assum (qspec_then `(f,e)` assume_tac) >> rfs[])
                >- (`∃f e. x' = (f,e)` by rw[ABS_PAIR_THM] >> rw[] >> fs[pi_cross_def] >>
                    map_every qexists_tac [`f`,`e`] >> rw[])
                >- (`(∃f e. x' = (f,e)) ∧ (∃g a. x'' = (g,a))` by rw[ABS_PAIR_THM] >> rw[] >> fs[] >>
                    CCONTR_TAC >> qpat_x_assum `∀x. _` (qspec_then `(g,a)` assume_tac) >> rfs[] >>
                    (qspecl_then [`mss`,`n`] assume_tac) prod_measure_space_pi_measure_space_bij >>
                    dxrule_then assume_tac BIJ_IMP_121C >>
                    pop_assum (qspecl_then [`(f,e)`,`(g,a)`] assume_tac) >> rfs[] >> fs[]))
            >- (fs[SUBSET_DEF,POW_DEF,IN_PREIMAGE] >> rw[IMAGE_BIGUNION] >>
                qpat_x_assum `∀c. _ ∧ _ ⇒ BIGUNION c ∈ P` irule >> rw[image_countable] >>
                qpat_x_assum `∀x. _ ⇒ IMAGE _ _ ∈ P` irule >> rw[])
            >- (fs[POW_DEF,BIGUNION_SUBSET] >> fs[SUBSET_DEF] >> fs[]))
        >- (rw[prod_sets_def,POW_DEF,SUBSET_DEF,CROSS_DEF] >> fs[subset_class_def] >>
            NTAC 2 (qpat_x_assum `∀x. _` (dxrule_then assume_tac)) >> fs[SUBSET_DEF])
        >- (fs[SUBSET_DEF] >> rw[PREIMAGE_def] >> fs[prod_sets_def,pi_prod_sets_def] >>
            last_x_assum (qspec_then `pi_cross n s t` assume_tac) >>
            `pi_cross n s t ∈ P` by (pop_assum irule >> map_every qexists_tac [`s`,`t`] >> rw[]) >>
            `IMAGE (λ(f,e). pi_pair n f e) (s × t) = pi_cross n s t` suffices_by rw[] >>
            rw[EXTENSION,IN_IMAGE,pi_cross_def] >> eq_tac >> rw[]
            >- (`∃f e. x' = (f,e)` by rw[ABS_PAIR_THM] >> rw[] >> fs[] >>
                map_every qexists_tac [`f`,`e`] >> rw[])
            >- (qexists_tac `(f,e)` >> rw[])))
    >- (fs[sigma_def,subsets_def] >> rw[] >> last_x_assum kall_tac >>
        last_x_assum (qspec_then `IMAGE (IMAGE (λ(f,e). pi_pair n f e)) P` assume_tac) >>
        `pi_prod_sets n (pi_measurable_sets n mss) (measurable_sets (mss n)) ⊆
            IMAGE (IMAGE (λ(f,e). pi_pair n f e)) P ∧
            sigma_algebra (pi_cross n (pi_m_space n mss) (m_space (mss n)),
            IMAGE (IMAGE (λ(f,e). pi_pair n f e)) P)` suffices_by (
            rw[] >> fs[] >> rw[] >>
            `PREIMAGE (λ(f,e). pi_pair n f e) (IMAGE (λ(f,e). pi_pair n f e) x) ∩
                (pi_m_space n mss × m_space (mss n)) = x` suffices_by rw[] >>
            irule BIJ_PREIMAGE_IMAGE >> rename [`s ⊆ _ ∧ _`] >>
            fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def] >>
            rpt (pop_assum kall_tac) >>
            (qspecl_then [`mss`,`n`] assume_tac) prod_measure_space_pi_measure_space_bij >>
            qexists_tac `pi_cross n (pi_m_space n mss) (m_space (mss n))` >> rw[]) >>
        pop_assum kall_tac >> rw[]
        >- (fs[SUBSET_DEF,pi_prod_sets_def,prod_sets_def] >> rw[] >>
            last_x_assum (qspec_then `fs × s` assume_tac) >>
            `fs × s ∈ P` by (pop_assum irule >> map_every qexists_tac [`fs`,`s`] >> simp[]) >>
            fs[] >> rw[pi_cross_def] >> qexists_tac `fs × s` >> simp[EXTENSION] >>
            rw[] >> eq_tac >> rw[]
            >- (qexists_tac `(f,e)` >> rw[])
            >- (`∃f e. x' = (f,e)` by rw[ABS_PAIR_THM] >> rw[] >> fs[] >>
                map_every qexists_tac [`f`,`e`] >> rw[]))
        >- (fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def] >> rw[]
            >- (rename [`s ∈ P`] >> qpat_x_assum `∀x. _ ⇒ _ ⊆ _` (dxrule_then assume_tac) >>
                fs[SUBSET_DEF] >> rw[] >> `∃f e. x' = (f,e)` by rw[ABS_PAIR_THM] >> rw[] >>
                qpat_x_assum `∀x. x ∈ s ⇒ _` (dxrule_then assume_tac) >> fs[pi_cross_def] >>
                map_every qexists_tac [`f`,`e`] >> rw[])
            >- (rename [`s ∈ P`] >> qexists_tac `pi_m_space n mss × m_space (mss n) DIFF s` >>
                rw[EXTENSION] >> rename [`fs ∈ _ ∧ _ ⇔ _`] >> eq_tac >> rw[]
                >- (fs[pi_cross_def] >> qexists_tac `(f,e)` >> simp[] >>
                    pop_assum (qspec_then `(f,e)` assume_tac) >> rfs[])
                >- (`∃f e. x' = (f,e)` by rw[ABS_PAIR_THM] >> rw[pi_cross_def] >> fs[] >>
                    map_every qexists_tac [`f`,`e`] >> simp[])
                >- (`(∃f e. x' = (f,e)) ∧ (∃g a. x'' = (g,a))` by rw[ABS_PAIR_THM] >> rw[] >>
                    fs[] >> CCONTR_TAC >> fs[] >>
                    qpat_x_assum `∀x. _ ⇒ _ ⊆ _` (dxrule_then assume_tac) >> fs[SUBSET_DEF] >>
                    pop_assum (drule_then assume_tac) >> fs[] >>
                    (qspecl_then [`mss`,`n`] assume_tac) prod_measure_space_pi_measure_space_bij >>
                    dxrule_then assume_tac BIJ_IMP_121C >>
                    pop_assum (qspecl_then [`(f,e)`,`(g,a)`] assume_tac) >> rfs[] >> fs[]))
            >- (rename [`_ _ fs ∪ _ _ gs`] >> qexists_tac `fs ∪ gs` >> rw[])
            >- (qexists_tac `BIGUNION (PREIMAGE (IMAGE (λ(f,e). pi_pair n f e)) c ∩
                    POW (pi_m_space n mss × m_space (mss n)))` >> rw[]
                >- (rw[IMAGE_BIGUNION] >>
                    `∀s0 s1:((num->α)->bool)->bool. (s0 = s1) ⇒ (BIGUNION s1 = BIGUNION s0)` by rw[] >>
                    pop_assum irule >> irule BIJ_IMAGE_PREIMAGE >>
                    qexists_tac `POW (pi_cross n (pi_m_space n mss) (m_space (mss n)))` >> rw[]
                    >- (fs[SUBSET_DEF] >> rw[] >> rename [`fs ∈ _`] >>
                        first_x_assum (dxrule_then assume_tac) >> fs[] >>
                        rename [`_ _ s ∈ _`] >> rw[POW_DEF,SUBSET_DEF] >>
                        `∃f e. x' = (f,e)` by rw[ABS_PAIR_THM] >> rw[pi_cross_def] >> fs[] >>
                        map_every qexists_tac [`f`,`e`] >> simp[] >> RES_TAC >> fs[])
                    >- (irule BIJ_POW >> rw[prod_measure_space_pi_measure_space_bij]))
                >- (first_x_assum irule >> rw[]
                    >- (irule preimage_bij_countable >> simp[] >>
                        qexists_tac `POW (pi_cross n (pi_m_space n mss) (m_space (mss n)))` >>
                        simp[prod_measure_space_pi_measure_space_bij_pow] >>
                        fs[SUBSET_DEF] >> rw[POW_DEF] >> rename [`fs ∈ _`] >>
                        first_x_assum (dxrule_then assume_tac) >> fs[] >> rename [`s ∈ P`] >>
                        fs[SUBSET_DEF,EXTENSION] >> rw[] >> `∃f e. x' = (f,e)` by rw[ABS_PAIR_THM] >>
                        rw[pi_cross_def] >> map_every qexists_tac [`f`,`e`] >> RES_TAC >> fs[])
                    >- (rw[SUBSET_DEF,IN_PREIMAGE] >> rename [`s ∈ P`] >>
                        `IMAGE (λ(f,e). pi_pair n f e) s ∈ IMAGE (IMAGE (λ(f,e). pi_pair n f e)) P`
                            by fs[SUBSET_DEF] >>
                        fs[] >> rename [`_ _ s = _ _ t`] >>
                        `t ∈ POW (pi_m_space n mss × m_space (mss n))` by fs[POW_DEF] >>
                        (qspecl_then [`mss`,`n`] assume_tac) prod_measure_space_pi_measure_space_bij >>
                        dxrule_then assume_tac BIJ_POW >> dxrule_then assume_tac BIJ_IMP_121C >>
                        pop_assum (qspecl_then [`s`,`t`] assume_tac) >> rfs[])))))
    >- (rw[prod_measure_hor_def,measure_def,pi_measure_def] >>
        `(λs1. Normal (pi_measure n mss (PREIMAGE (λs0. (s0,s1)) s))) =
            (λe. Normal (pi_measure n mss (PREIMAGE (λf. pi_pair n f e)
            (IMAGE (λ(f,e). pi_pair n f e) s) ∩ pi_m_space n mss)))` suffices_by rw[] >>
        rw[FUN_EQ_THM] >>
        `PREIMAGE (λf. pi_pair n f e) (IMAGE (λ(f,e). pi_pair n f e) s) ∩ pi_m_space n mss =
            PREIMAGE (λs0. (s0,e)) s` suffices_by rw[] >>
        rw[PREIMAGE_def] >> rw[EXTENSION] >> Q.RENAME_TAC [`_ ⇔ (f,e) ∈ _`] >>
        `s ⊆ pi_m_space n mss × m_space (mss n)` by (
            dxrule_then assume_tac prod_measure_space_pi_measure_space_sigma_algebra >>
            fs[sigma_algebra_def,algebra_def,subset_class_def,SPACE_SIGMA]) >>
        NTAC 2 (last_x_assum kall_tac) >> eq_tac >> rw[]
        >- (`∃g a. x = (g,a)` by rw[ABS_PAIR_THM] >> rw[] >> fs[] >>
            `e = a` by (fs[pi_pair_def,FUN_EQ_THM] >>
                qpat_x_assum `∀x. _ = _` (qspec_then `n` assume_tac) >> fs[]) >>
            rw[] >> fs[SUBSET_DEF,CROSS_DEF] >> last_x_assum (drule_then assume_tac) >> fs[] >>
            (qspecl_then [`mss`,`n`] assume_tac) prod_measure_space_pi_measure_space_bij >>
            dxrule_then assume_tac BIJ_IMP_121C >>
            pop_assum (qspecl_then [`(f,a)`,`(g,a)`] assume_tac) >> rfs[])
        >- (qexists_tac `(f,e)` >> rw[])
        >- (fs[SUBSET_DEF,CROSS_DEF] >> last_x_assum (drule_then assume_tac) >> fs[]))
);

(* Pi Measure Space Measure Space *)

val pi_measure_space_measure_space = store_thm(
    "pi_measure_space_measure_space",
    ``∀mss n. (∀i. i < n ⇒ measure_space (mss i)) ⇒ measure_space (pi_measure_space n mss)``,
    NTAC 2 strip_tac >> Induct_on `n` >> rw[]
    >- (rw[pi_measure_space_0_pi_id_msp,pi_id_msp_measure_space]) >> fs[] >>
    `(∀i. i < SUC n ⇒ subset_class (m_space (mss i)) (measurable_sets (mss i)))` by (rw[] >>
        last_x_assum kall_tac >> last_x_assum (dxrule_then assume_tac) >>
        fs[measure_space_def,sigma_algebra_def,algebra_def,space_def,subsets_def]) >>
    dxrule_then assume_tac pi_measure_space_iso_prod_measure_space >>
    qpat_x_assum `∀i. _` (qspec_then `n` assume_tac) >> rfs[] >>
    dxrule_then assume_tac isomorphic_sym_imp >>
    irule (INST_TYPE [alpha |-> ``:(num->α)#α``] iso_measure_space_imp_measure_space) >>
    qexists_tac `prod_measure_space_hor (pi_measure_space n mss) (mss n)` >> rw[] >>
    pop_assum kall_tac >> irule prod_measure_space_hor_measure_space >> simp[]
);

(* More isomorphism results *)

val measure_space_id_prod_measure_space_bij = store_thm(
    "measure_space_id_prod_measure_space_bij",
    ``∀m. BIJ (λx. (x,ARB)) (m_space m) (m_space m × m_space id_msp)``,
    rw[BIJ_DEF,INJ_DEF,SURJ_DEF]
    >- (rw[id_msp_def,m_space_def])
    >- (rw[id_msp_def,m_space_def])
    >- (fs[id_msp_def,m_space_def] >> qexists_tac `FST x` >> rw[] >>
        pop_assum (assume_tac o GSYM) >> rw[PAIR])
);

val prod_measure_space_id_iso_measure_space = store_thm(
    "prod_measure_space_id_iso_measure_space",
    ``∀m. measure_space m ⇒ isomorphic (prod_measure_space m id_msp) m``,
    rw[] >> irule isomorphic_sym_imp >>
    rw[prod_measure_space_def,m_space_def,measurable_sets_def] >>
    rw[isomorphic_def] >> qexists_tac `(λx. (x,ARB))` >>
    rw[measure_preserving_def,m_space_def,measurable_sets_def,measure_def] >>
    rw[measurability_preserving_def,space_def,subsets_def]
    >- (fs[measure_space_def])
    >- (rw[SIGMA_REDUCE] >> irule SIGMA_ALGEBRA_SIGMA >> rw[subset_class_def,prod_sets_def] >>
        `s ⊆ m_space m ∧ t ⊆ m_space id_msp` suffices_by rw[CROSS_SUBSET] >>
        rw[] >> irule MEASURABLE_SETS_SUBSET_SPACE >> rw[id_msp_measure_space])
    >- (rw[measure_space_id_prod_measure_space_bij])
    >- (fs[sigma_def,subsets_def] >> rw[] >> fs[prod_sets_def,SUBSET_DEF] >>
        qpat_x_assum `∀x. _` (qspec_then `IMAGE (λx. (x,ARB)) s` assume_tac) >>
        pop_assum irule >> map_every qexists_tac [`s`,`{ARB:β}`] >>
        rw[id_msp_def,measurable_sets_def,POW_DEF] >> rw[IMAGE_PAIR])
    >- (fs[GSYM measurable_sets_prod_measure_space] >>
        assume_tac (INST_TYPE [alpha |-> ``:β``] id_msp_measure_space) >>
        drule_all_then assume_tac product_measure_space_y_slice_measurable >>
        pop_assum (qspec_then `ARB` assume_tac) >>
        `PREIMAGE (λx. (x,ARB)) s ∩ m_space m = y_slice ARB s` suffices_by rw[] >>
        rw[y_slice_def] >> rw[EXTENSION] >> eq_tac >> rw[] >>
        `measure_space (prod_measure_space m id_msp)` by rw[prod_measure_space_measure_space] >>
        dxrule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >>
        fs[m_space_prod_measure_space,SUBSET_DEF] >> pop_assum (dxrule_then assume_tac) >> fs[])
    >- (rw[IMAGE_PAIR] >> (qspec_then `m` assume_tac) prod_measure_prod_set >>
        pop_assum (qspecl_then [`id_msp`,`s`,`{ARB}`] assume_tac) >>
        rfs[measure_prod_measure_space,id_msp_measure_space] >>
        rfs[id_msp_def,measurable_sets_def,measure_def,POW_DEF])
);

val prod_measure_space_iso_sym = store_thm(
    "prod_measure_space_iso_sym",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        isomorphic (prod_measure_space m0 m1) (prod_measure_space m1 m0)``,
    rw[isomorphic_def] >> qexists_tac `(λ(x,y). (y,x))` >>
    rw[measure_preserving_def,m_space_def,measurable_sets_def,measure_def] >>
    rw[measurability_preserving_def,space_def,subsets_def]
    >- (rw[prod_measure_space_sigma_algebra])
    >- (rw[prod_measure_space_sigma_algebra])
    >- (rw[m_space_prod_measure_space,BIJ_DEF,INJ_DEF,SURJ_DEF,GSYM PAIR,PAIR_FUN]
        >- (rw[PAIR_FST_SND_EQ])
        >- (qexists_tac `(SND x,FST x)` >> fs[]))
    >- (fs[measurable_sets_prod_measure_space,sigma_def,subsets_def] >> rw[] >>
        last_x_assum (qspec_then `PREIMAGE (IMAGE (λ(x,y). (y,x))) P ∩
            POW (m_space m0 × m_space m1)` assume_tac) >>
        fs[IN_PREIMAGE] >>
        `IMAGE (λ(x,y). (y,x)) s ∈ P ∧ s ∈ POW (m_space m0 × m_space m1)` suffices_by rw[] >>
        pop_assum irule >> rw[]
        >- (fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def,POW_DEF] >> rw[]
            >- (qpat_x_assum `∀s. _ ⇒ _ DIFF _ ∈ _` (dxrule_then assume_tac) >>
                `IMAGE (λ(x,y). (y,x)) (m_space m0 × m_space m1 DIFF s) =
                    m_space m1 × m_space m0 DIFF IMAGE (λ(x,y). (y,x)) s` suffices_by rw[] >>
                pop_assum kall_tac >> rw[EXTENSION] >> eq_tac >> rw[PAIR_FUN] >> fs[]
                >- (CCONTR_TAC >> fs[] >> rename [`SND z0 = SND z1`] >>
                    `z0 = z1` by rw[PAIR_FST_SND_EQ] >> fs[])
                >- (qexists_tac `(SND x,FST x)` >>
                    pop_assum (qspec_then `(SND x,FST x)` assume_tac) >> fs[]))
            >- (rw[IMAGE_BIGUNION] >> qpat_x_assum `∀c. _ ∧ _ ⇒ BIGUNION c ∈ P` irule >>
                rw[image_countable] >> fs[SUBSET_DEF,IN_IMAGE,IN_PREIMAGE] >> rw[] >> fs[])
            >- (fs[SUBSET_DEF,IN_BIGUNION,IN_PREIMAGE] >> NTAC 2 strip_tac >>
                qpat_x_assum `∀x. _ ⇒ IMAGE _ _ ∈ P` (dxrule_then assume_tac) >>
                qpat_x_assum `∀x. _ ⇒ ∀x'. _ ⇒ _` (dxrule_then assume_tac) >>
                fs[IN_IMAGE,PAIR_FUN] >> pop_assum (qspec_then `(SND x,FST x)` assume_tac) >>
                fs[] >> `SND x ∈ m_space m1 ∧ FST x ∈ m_space m0` suffices_by rw[] >>
                pop_assum irule >> qexists_tac `x` >> rw[]))
        >- (rw[SUBSET_DEF,prod_sets_def,CROSS_DEF,IN_POW] >> fs[] >>
            NTAC 2 (dxrule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE) >> fs[SUBSET_DEF])
        >- (fs[SUBSET_DEF,prod_sets_def,CROSS_DEF,IN_PREIMAGE] >> rw[] >>
            qpat_x_assum `∀x. _` irule >> map_every qexists_tac [`t`,`s`] >>
            rw[EXTENSION] >> eq_tac >> rw[PAIR_FUN] >> fs[] >>
            qexists_tac `(SND x,FST x)` >> fs[]))
    >- (fs[m_space_prod_measure_space,measurable_sets_prod_measure_space,sigma_def,subsets_def] >> rw[] >>
        last_x_assum (qspec_then `PREIMAGE (λs. PREIMAGE (λ(x,y). (y,x)) s ∩ (m_space m0 × m_space m1)) P ∩
            POW (m_space m1 × m_space m0)` assume_tac) >>
        fs[IN_PREIMAGE] >>
        `PREIMAGE (λ(x,y). (y,x)) s ∩ (m_space m0 × m_space m1) ∈ P ∧
            s ∈ POW (m_space m1 × m_space m0)` suffices_by rw[] >>
        pop_assum irule >> rw[]
        >- (fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def,POW_DEF] >> rw[]
            >- (qpat_x_assum `∀s. _ ⇒ _ DIFF _ ∈ _` (dxrule_then assume_tac) >>
                `PREIMAGE (λ(x,y). (y,x)) (m_space m1 × m_space m0 DIFF s) ∩ (m_space m0 × m_space m1) =
                    m_space m0 × m_space m1 DIFF PREIMAGE (λ(x,y). (y,x)) s ∩ (m_space m0 × m_space m1)`
                    suffices_by rw[] >>
                pop_assum kall_tac >> rw[EXTENSION] >> eq_tac >> rw[PAIR_FUN] >> fs[])
            >- (qpat_x_assum `∀s t. _` (dxrule_all_then assume_tac) >>
                `PREIMAGE (λ(x,y). (y,x)) (s ∪ t) ∩ (m_space m0 × m_space m1) =
                    PREIMAGE (λ(x,y). (y,x)) t ∩ (m_space m0 × m_space m1) ∪
                    PREIMAGE (λ(x,y). (y,x)) s ∩ (m_space m0 × m_space m1)` suffices_by rw[] >>
                pop_assum kall_tac >> rw[EXTENSION] >> eq_tac >> rw[PAIR_FUN] >> fs[])
            >- (rw[PREIMAGE_BIGUNION] >>
                `(m_space m0 × m_space m1) ∩ BIGUNION (IMAGE (PREIMAGE (λ(x,y). (y,x))) c) ∈ P`
                    suffices_by rw[INTER_COMM] >>
                rw[GSYM INTER_BIGUNION_IMAGE] >> qpat_x_assum `∀c. _ ∧ _ ⇒ BIGUNION c ∈ P` irule >>
                rw[image_countable] >>
                `IMAGE (λx. PREIMAGE (λ(x,y). (y,x)) x ∩ (m_space m0 × m_space m1)) c ⊆ P`
                    suffices_by rw[INTER_COMM] >>
                fs[SUBSET_DEF,IN_IMAGE,IN_PREIMAGE] >> rw[] >> fs[])
            >- (fs[SUBSET_DEF] >> NTAC 2 strip_tac >>
                qpat_x_assum `∀x. _ ⇒ ∀x'. _ ⇒ _` (dxrule_then assume_tac) >>
                pop_assum (dxrule_then assume_tac) >> rw[]))
        >- (rw[SUBSET_DEF,prod_sets_def,CROSS_DEF,IN_POW] >> fs[] >>
            NTAC 2 (dxrule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE) >> fs[SUBSET_DEF])
        >- (fs[SUBSET_DEF,prod_sets_def,CROSS_DEF,IN_PREIMAGE] >> rw[] >>
            qpat_x_assum `∀x. _` irule >> map_every qexists_tac [`t`,`s`] >>
            rw[EXTENSION] >> eq_tac >> rw[PAIR_FUN] >> fs[] >>
            NTAC 2 (dxrule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE) >> fs[SUBSET_DEF]))
    >- (rw[measure_prod_measure_space] >> fs[measurable_sets_prod_measure_space] >>
        rw[GSYM prod_measures_equiv_hor] >> rw[prod_measure_def,prod_measure_hor_def] >>
        NTAC 2 (irule IRULER) >> rw[FUN_EQ_THM] >> irule IRULER >>
        rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[PAIR_FUN]
        >- (qexists_tac `(x,s0)` >> fs[])
        >- (rw[PAIR]))
);

val prod_measure_space_iso_prod_measure_space_hor = store_thm(
    "prod_measure_space_iso_prod_measure_space_hor",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        isomorphic (prod_measure_space m0 m1) (prod_measure_space_hor m0 m1)``,
    rw[isomorphic_def] >> qexists_tac `I` >>
    rw[measure_preserving_def,m_space_def,measurable_sets_def,measure_def] >>
    rw[measurability_preserving_def,space_def,subsets_def]
    >- (rw[prod_measure_space_sigma_algebra])
    >- (rw[prod_measure_space_hor_sigma_algebra])
    >- (rw[m_space_prod_measure_space,m_space_prod_measure_space_hor,BIJ_I])
    >- (fs[measurable_sets_prod_measure_space,measurable_sets_prod_measure_space_hor])
    >- (rw[PREIMAGE_I] >>
        `s ∩ m_space (prod_measure_space m0 m1) = s` suffices_by
            fs[measurable_sets_prod_measure_space,measurable_sets_prod_measure_space_hor] >>
        rw[INTER_SUBSET_EQN] >> irule MEASURABLE_SETS_SUBSET_SPACE >>
        fs[measurable_sets_prod_measure_space,measurable_sets_prod_measure_space_hor] >>
        pop_assum kall_tac >> rw[prod_measure_space_measure_space])
    >- (fs[measurable_sets_prod_measure_space] >> dxrule_all_then assume_tac prod_measures_equiv_hor >>
        rw[measure_prod_measure_space,measure_prod_measure_space_hor])
);

val prod_measure_space_hor_iso_sym = store_thm(
    "prod_measure_space_hor_iso_sym",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        isomorphic (prod_measure_space_hor m0 m1) (prod_measure_space_hor m1 m0)``,
    rw[] >>
    `isomorphic (prod_measure_space m0 m1) (prod_measure_space m1 m0)`
        by rw[prod_measure_space_iso_sym] >>
    `isomorphic (prod_measure_space m0 m1) (prod_measure_space_hor m0 m1)`
        by rw[prod_measure_space_iso_prod_measure_space_hor] >>
    `isomorphic (prod_measure_space m1 m0) (prod_measure_space_hor m1 m0)`
        by rw[prod_measure_space_iso_prod_measure_space_hor] >>
    metis_tac[isomorphic_sym_imp,isomorphic_trans]
);

val prod_measure_space_iso_recur_right = store_thm(
    "prod_measure_space_iso_recur_right",
    ``∀m0 m1 m2. measure_space m0 ∧ measure_space m1 ∧ measure_space m2 ∧ isomorphic m1 m2 ⇒
        isomorphic (prod_measure_space m0 m1) (prod_measure_space m0 m2)``,
    rw[isomorphic_def] >> qexists_tac `I ## f` >> `I PERMUTES (m_space m0)` by rw[BIJ_I] >>
    fs[measure_preserving_def,m_space_def,measurable_sets_def,measure_def] >>
    fs[measurability_preserving_def,space_def,subsets_def] >> rw[prod_measure_space_sigma_algebra] >>
    NTAC 2 (qpat_x_assum `sigma_algebra _` kall_tac)
    >- (rw[m_space_prod_measure_space,BIJ_CROSS])
    >- (fs[measurable_sets_prod_measure_space,sigma_def,subsets_def] >> rw[] >>
        last_x_assum (qspec_then `PREIMAGE (IMAGE (I ## f)) P ∩
            POW (m_space m0 × m_space m1)` assume_tac) >>
        fs[IN_PREIMAGE] >>
        `IMAGE (I ## f) s ∈ P ∧ s ∈ POW (m_space m0 × m_space m1)` suffices_by rw[] >>
        pop_assum irule >> rw[]
        >- (fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def,POW_DEF] >> rw[]
            >- (qpat_x_assum `∀s. _ ⇒ _ DIFF _ ∈ _` (dxrule_then assume_tac) >>
                `IMAGE (I ## f) (m_space m0 × m_space m1 DIFF s) =
                    m_space m0 × m_space m2 DIFF IMAGE (I ## f) s` suffices_by rw[] >>
                pop_assum kall_tac >> rw[EXTENSION] >> eq_tac >> rw[PAIR_MAP,I_DEF] >> fs[]
                >- (fs[BIJ_ALT,FUNSET])
                >- (CCONTR_TAC >> fs[] >> rename [`z0 ∉ s`,`z1 ∈ s`] >>
                    `z0 = z1` suffices_by (strip_tac >> fs[]) >> simp[PAIR_FST_SND_EQ] >>
                    `z1 ∈ m_space m0 × m_space m1` by fs[SUBSET_DEF] >> fs[CROSS_DEF] >>
                    fs[BIJ_DEF,INJ_DEF])
                >- (fs[BIJ_DEF,SURJ_DEF] >>
                    qpat_x_assum `∀x. _ ⇒ ∃y. _` (dxrule_then assume_tac) >> fs[] >>
                    qexists_tac `(FST x,y)` >> fs[] >>
                    qpat_x_assum `∀x. _` (qspec_then `(FST x,y)` assume_tac) >> rfs[]))
            >- (rw[IMAGE_BIGUNION] >> qpat_x_assum `∀c. _ ∧ _ ⇒ BIGUNION c ∈ P` irule >>
                rw[image_countable] >> fs[SUBSET_DEF,IN_IMAGE,IN_PREIMAGE] >> rw[] >> fs[])
            >- (fs[SUBSET_DEF,IN_BIGUNION,IN_PREIMAGE] >> NTAC 2 strip_tac >>
                first_x_assum (dxrule_then assume_tac) >> first_x_assum (dxrule_then assume_tac) >> rw[]))
        >- (rw[SUBSET_DEF,prod_sets_def,CROSS_DEF,IN_POW] >> fs[] >>
            NTAC 2 (dxrule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE) >> fs[SUBSET_DEF])
        >- (fs[SUBSET_DEF,prod_sets_def,IN_PREIMAGE] >> rw[] >> rw[PAIR_MAP_IMAGE_CROSS] >>
            qpat_x_assum `∀x. _` irule >> map_every qexists_tac [`s`,`IMAGE f t`] >> rw[]))
    >- (fs[m_space_prod_measure_space,measurable_sets_prod_measure_space,sigma_def,subsets_def] >> rw[] >>
        last_x_assum (qspec_then `PREIMAGE (λs. PREIMAGE (I ## f) s ∩ (m_space m0 × m_space m1)) P ∩
            POW (m_space m0 × m_space m2)` assume_tac) >>
        fs[IN_PREIMAGE] >>
        `PREIMAGE (I ## f) s ∩ (m_space m0 × m_space m1) ∈ P ∧
            s ∈ POW (m_space m0 × m_space m2)` suffices_by rw[] >>
        pop_assum irule >> rw[]
        >- (fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def,POW_DEF] >> rw[]
            >- (qpat_x_assum `∀s. _ ⇒ _ DIFF _ ∈ _` (dxrule_then assume_tac) >>
                `PREIMAGE (I ## f) (m_space m0 × m_space m2 DIFF s) ∩ (m_space m0 × m_space m1) =
                    m_space m0 × m_space m1 DIFF PREIMAGE (I ## f) s ∩ (m_space m0 × m_space m1)`
                    suffices_by rw[] >>
                pop_assum kall_tac >> rw[EXTENSION] >> eq_tac >> rw[PAIR_MAP] >> fs[BIJ_ALT,FUNSET])
            >- (qpat_x_assum `∀s t. _` (dxrule_all_then assume_tac) >>
                `PREIMAGE (I ## f) (s ∪ t) ∩ (m_space m0 × m_space m1) =
                    PREIMAGE (I ## f) t ∩ (m_space m0 × m_space m1) ∪
                    PREIMAGE (I ## f) s ∩ (m_space m0 × m_space m1)` suffices_by rw[] >>
                pop_assum kall_tac >> rw[EXTENSION] >> eq_tac >> rw[PAIR_MAP] >> fs[])
            >- (rw[PREIMAGE_BIGUNION] >>
                `(m_space m0 × m_space m1) ∩ BIGUNION (IMAGE (PREIMAGE (I ## f)) c) ∈ P`
                    suffices_by rw[INTER_COMM] >>
                rw[GSYM INTER_BIGUNION_IMAGE] >> qpat_x_assum `∀c. _ ∧ _ ⇒ BIGUNION c ∈ P` irule >>
                rw[image_countable] >>
                `IMAGE (λx. PREIMAGE (I ## f) x ∩ (m_space m0 × m_space m1)) c ⊆ P`
                    suffices_by rw[INTER_COMM] >>
                fs[SUBSET_DEF,IN_IMAGE,IN_PREIMAGE] >> rw[] >> fs[])
            >- (fs[SUBSET_DEF] >> NTAC 2 strip_tac >>
                qpat_x_assum `∀x. _ ⇒ ∀x'. _ ⇒ _` (dxrule_then assume_tac) >>
                pop_assum (dxrule_then assume_tac) >> rw[]))
        >- (rw[SUBSET_DEF,prod_sets_def,CROSS_DEF,IN_POW] >> fs[] >>
            NTAC 2 (dxrule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE) >> fs[SUBSET_DEF])
        >- (fs[SUBSET_DEF,prod_sets_def,IN_PREIMAGE] >> rw[] >>
            qpat_x_assum `∀x. _` irule >> rw[PAIR_MAP_PREIMAGE_CROSS,CROSS_INTER,PREIMAGE_I] >>
            map_every qexists_tac [`s ∩ m_space m0`,`PREIMAGE f t ∩ m_space m1`] >> rw[] >>
            `s ∩ m_space m0 = s` suffices_by rw[] >> rw[EXTENSION] >> eq_tac >> rw[] >>
            `s ⊆ m_space m0` suffices_by (rw[] >> rfs[SUBSET_DEF]) >>
            irule MEASURABLE_SETS_SUBSET_SPACE >> rw[]))
    >- (rw[measure_prod_measure_space,prod_measure_def] >> NTAC 2 (irule IRULER) >>
        rw[FUN_EQ_THM] >> drule_all_then assume_tac product_measure_space_x_slice_measurable >>
        pop_assum (qspec_then `s0` assume_tac) >> fs[x_slice_def] >> irule IRULER >>
        rw[EXTENSION,PAIR_MAP] >> eq_tac >> rw[]
        >- (rename [`(s0,s1) ∈ s`] >> qexists_tac `(s0,s1)` >> fs[])
        >- (rename [`z ∈ s`] >> qexists_tac `SND z` >> rw[PAIR]))
);

val prod_measure_space_iso_recur_left = store_thm(
    "prod_measure_space_iso_recur_left",
    ``∀m0 m1 m2. measure_space m0 ∧ measure_space m1 ∧ measure_space m2 ∧ isomorphic m0 m1 ⇒
        isomorphic (prod_measure_space m0 m2) (prod_measure_space m1 m2)``,
    rw[] >>
    metis_tac[prod_measure_space_iso_recur_right,prod_measure_space_iso_sym,
        isomorphic_sym_imp,isomorphic_trans]
);

val prod_measure_space_iso_recur = store_thm(
    "prod_measure_space_iso_recur",
    ``∀m0 m1 m2 m3. measure_space m0 ∧ measure_space m1 ∧ measure_space m2 ∧ measure_space m3 ∧
        isomorphic m0 m2 ∧ isomorphic m1 m3 ⇒
        isomorphic (prod_measure_space m0 m1) (prod_measure_space m2 m3)``,
    rw[] >> metis_tac[prod_measure_space_iso_recur_right,prod_measure_space_iso_recur_left,
        prod_measure_space_iso_sym,isomorphic_sym_imp,isomorphic_trans]
);

val pi_measure_space_1_iso_measure_space = store_thm(
    "pi_measure_space_1_iso_measure_space",
    ``∀mss. measure_space (mss 0) ⇒ isomorphic (pi_measure_space 1 mss) (mss 0)``,
    rw[] >> (qspecl_then [`mss`,`0`] assume_tac) pi_measure_space_iso_prod_measure_space >>
    `(∀i. i < 1 ⇒ subset_class (m_space (mss i)) (measurable_sets (mss i)))`
        by (rw[] >> Cases_on `i` >> fs[MEASURE_SPACE_SUBSET_CLASS]) >>
    fs[] >> pop_assum kall_tac >>
    `isomorphic (prod_measure_space_hor (pi_measure_space 0 mss) (mss 0)) (mss 0)`
        suffices_by (rw[] >> dxrule_all_then assume_tac isomorphic_trans >> rw[]) >>
    pop_assum kall_tac >> rw[pi_measure_space_0_pi_id_msp] >> assume_tac pi_id_msp_measure_space >>
    (qspecl_then [`pi_id_msp`,`mss 0`] assume_tac) prod_measure_space_iso_prod_measure_space_hor >>
    rfs[] >> dxrule_then assume_tac isomorphic_sym_imp >>
    (qspecl_then [`pi_id_msp`,`mss 0`] assume_tac) prod_measure_space_iso_sym >> rfs[] >>
    dxrule_all_then assume_tac isomorphic_trans >> assume_tac id_msp_measure_space >>
    assume_tac (INST_TYPE [beta |-> ``:α``] pi_id_msp_iso_id_msp) >>
    (qspecl_then [`(mss 0)`,`pi_id_msp`,`id_msp`] assume_tac) prod_measure_space_iso_recur_right >>
    rfs[] >> dxrule_all_then assume_tac isomorphic_trans >>
    (qspec_then `(mss 0)` assume_tac)
        (INST_TYPE [beta |-> ``:α``] prod_measure_space_id_iso_measure_space) >>
    rfs[] >> dxrule_all_then assume_tac isomorphic_trans >> rw[]
);

(* integration of isomorphic spaces *)

val iso_pos_simple_fn_o = store_thm(
    "iso_pos_simple_fn_o",
    ``∀m0 m1 s e a f g. pos_simple_fn m1 f s e a ∧
        g ∈ measurability_preserving (m_space m0, measurable_sets m0) (m_space m1, measurable_sets m1) ⇒
        pos_simple_fn m0 (f ∘ g) s (λi. (PREIMAGE g (e i) ∩ m_space m0)) a``,
    rw[measurability_preserving_def,pos_simple_fn_def,space_def,subsets_def]
    >- (`g t ∈ m_space m1` by fs[BIJ_ALT,FUNSET] >> last_x_assum (dxrule_then assume_tac) >>
        rw[] >> `∀x y. x = y ⇒ SIGMA x s = SIGMA y s` by rw[] >> pop_assum irule >>
        rw[FUN_EQ_THM] >> irule IRULER >> rw[indicator_fn_def])
    >- (rename [`i ≠ j`] >> first_x_assum (drule_all_then assume_tac) >>
        fs[DISJOINT_DEF,EXTENSION,IN_PREIMAGE] >> CCONTR_TAC >> fs[] >>
        first_x_assum (qspec_then `g x` assume_tac) >> rfs[])
    >- (fs[EXTENSION,IN_BIGUNION_IMAGE] >> rw[] >> eq_tac >> rw[] >> fs[BIJ_ALT,FUNSET])
);

val iso_measurable_o = store_thm(
    "iso_measurable_o",
    ``∀m0 m1 a f g. f ∈ measurable (m_space m1, measurable_sets m1) a ∧
        g ∈ measurability_preserving (m_space m0, measurable_sets m0) (m_space m1, measurable_sets m1) ⇒
        f ∘ g ∈ measurable (m_space m0, measurable_sets m0) a``,
    rw[measurability_preserving_def,measurable_def,space_def,subsets_def] >- (fs[BIJ_ALT,FUNSET]) >>
    NTAC 2 (first_x_assum (dxrule_then assume_tac)) >>
    `PREIMAGE g (PREIMAGE f s ∩ m_space m1) ∩ m_space m0 = PREIMAGE (f ∘ g) s ∩ m_space m0`
        suffices_by (rw[] >> fs[]) >>
    rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[] >> fs[BIJ_ALT,FUNSET]
);

val iso_pos_simple_fn_integral_preimage_o = store_thm(
    "iso_pos_simple_fn_integral_preimage_o",
    ``∀m0 m1 s e a f g. pos_simple_fn m1 f s e a ∧ g ∈ measure_preserving m0 m1 ⇒
        pos_simple_fn_integral m1 s e a =
        pos_simple_fn_integral m0 s (λi. (PREIMAGE g (e i) ∩ m_space m0)) a``,
    rw[measure_preserving_alt,pos_simple_fn_integral_def,pos_simple_fn_def] >>
    irule REAL_SUM_IMAGE_EQ >> rw[]
);

val iso_pos_simple_fn_integral_image_o = store_thm(
    "iso_pos_simple_fn_integral_image_o",
    ``∀m0 m1 s e a f g. pos_simple_fn m0 f s e a ∧ g ∈ measure_preserving m0 m1 ⇒
        pos_simple_fn_integral m0 s e a =
        pos_simple_fn_integral m1 s (λi. IMAGE g (e i)) a``,
    rw[measure_preserving_def,pos_simple_fn_integral_def,pos_simple_fn_def] >>
    irule REAL_SUM_IMAGE_EQ >> rw[]
);

val iso_pos_fn_integral_o = store_thm(
    "iso_pos_fn_integral_o",
    ``∀m0 m1 f g. (∀x. 0 ≤ f x) ∧ g ∈ measure_preserving m0 m1 ⇒
        pos_fn_integral m1 f = pos_fn_integral m0 (f ∘ g)``,
    rw[pos_fn_integral_def] >> irule IRULER >> rw[EXTENSION] >>
    rename [`_ ⇔ ∃g. r ∈ psfis m0 g ∧ ∀x. g x ≤ f (h x)`] >> eq_tac >> rw[]
    >- (fs[psfis_def,psfs_def] >> rw[] >> rename [`pos_simple_fn m1 g s e a`] >>
        qexists_tac `g ∘ h` >> rw[] >> (drule_all_then assume_tac) iso_pos_simple_fn_integral_preimage_o >>
        qexists_tac `(s,(λi. PREIMAGE h (e i) ∩ m_space m0),a)` >> fs[measure_preserving_def] >>
        (drule_all_then assume_tac) iso_pos_simple_fn_o >> rw[])
    >- (fs[psfis_def,psfs_def] >> rw[] >> rename [`pos_simple_fn m0 g s e a`] >>
        `BIJ h (m_space m0) (m_space m1)` by
            fs[measure_preserving_def,measurability_preserving_def,space_def,subsets_def] >>
        `∃k. BIJ k (m_space m1) (m_space m0) ∧ (∀x. x ∈ (m_space m0) ⇒ (k ∘ h) x = x) ∧
            ∀x. x ∈ (m_space m1) ⇒ (h ∘ k) x = x` by (
            fs[measure_preserving_def,measurability_preserving_def,space_def] >>
            (dxrule_all_then assume_tac) BIJ_INV >> fs[] >> qexists_tac `g'` >> rw[]) >>
        qexists_tac `λx. (g ∘ k) x * indicator_fn (m_space m1) x` >> rw[]
        >- (qexists_tac `(s,(λi. IMAGE h (e i)),a)` >>
            (drule_all_then assume_tac) iso_pos_simple_fn_integral_image_o >> fs[] >>
            rw[pos_simple_fn_def]
            >- (rw[indicator_fn_def,mul_rzero,mul_rone,le_refl] >> fs[pos_simple_fn_def])
            >- (rename [`x ∈ _`] >> rw[indicator_fn_def,mul_rzero,mul_rone,le_refl] >>
                `k x ∈ m_space m0` by fs[BIJ_ALT,FUNSET] >> fs[pos_simple_fn_def] >>
                irule EXTREAL_SUM_IMAGE_EQ >> rw[indicator_fn_def,mul_rzero,mul_rone] >> fs[]
                >- (rename [`k x ∈ e n`] >> first_x_assum (qspec_then `k x` assume_tac) >> rfs[])
                >- (rename [`k (h x) ∉ e n`] >>
                    `x ∈ m_space m0` by (
                        `∃t. x ∈ t ∧ ∃y. t = e y ∧ y ∈ s`
                            suffices_by (rw[] >> fs[EXTENSION] >> metis_tac[]) >>
                        qexists_tac `e n` >> rw[] >> qexists_tac `n` >> rw[]) >>
                    first_x_assum (qspec_then `x` assume_tac) >> rfs[] >> fs[]))
            >- (`e i ∈ measurable_sets m0` by fs[pos_simple_fn_def] >>
                fs[measure_preserving_def,measurability_preserving_def,space_def,subsets_def])
            >- (fs[pos_simple_fn_def])
            >- (fs[pos_simple_fn_def])
            >- (rename [`i ≠ j`] >> `DISJOINT (e i) (e j)` by fs[pos_simple_fn_def] >>
                fs[DISJOINT_DEF,EXTENSION] >> CCONTR_TAC >> fs[] >> rw[] >>
                rename [`h x = h y`] >>
                `x ∈ m_space m0` by (fs[pos_simple_fn_def] >>
                    `∃t. x ∈ t ∧ ∃y. t = e y ∧ y ∈ s`
                        suffices_by (rw[] >> fs[EXTENSION] >> metis_tac[]) >>
                    qexists_tac `e j` >> rw[] >> qexists_tac `j` >> rw[]) >>
                `y ∈ m_space m0` by (fs[pos_simple_fn_def] >>
                    `∃t. y ∈ t ∧ ∃x. t = e x ∧ x ∈ s`
                        suffices_by (rw[] >> fs[EXTENSION] >> metis_tac[]) >>
                    qexists_tac `e i` >> rw[] >> qexists_tac `i` >> rw[]) >>
                `x = y` by fs[BIJ_DEF,INJ_DEF] >>
                rw[] >> first_x_assum (qspec_then `x` assume_tac) >> rfs[])
            >- (`∀x. (∃t. x ∈ t ∧ ∃i. t = IMAGE h (e i) ∧ i ∈ s) ⇔ x ∈ m_space m1`
                    suffices_by fs[EXTENSION] >>
                rw[] >> eq_tac >> rw[]
                >- (fs[IN_IMAGE] >> rename [`y = h x`] >>
                    `x ∈ m_space m0` by (fs[pos_simple_fn_def] >>
                        `∃t. x ∈ t ∧ ∃z. t = e z ∧ z ∈ s`
                            suffices_by (rw[] >> fs[EXTENSION] >> metis_tac[]) >>
                        qexists_tac `e i` >> rw[] >> qexists_tac `i` >> rw[]) >>
                    fs[BIJ_DEF,INJ_DEF])
                >- (fs[BIJ_DEF, SURJ_DEF] >> `∃y. y ∈ m_space m0 ∧ h y = x` by fs[] >>
                    `∃t. y ∈ t ∧ ∃n. t = e n ∧ n ∈ s` by fs[pos_simple_fn_def,EXTENSION] >>
                    rw[] >> qexists_tac `IMAGE h (e n)` >> simp[IN_IMAGE] >> rw[]
                    >- (qexists_tac `y` >> rw[])
                    >- (qexists_tac `n` >> rw[]))))
        >- (rw[indicator_fn_def,mul_rzero,mul_rone] >>
            last_x_assum (qspec_then `k x` assume_tac) >> rfs[]))
);

val iso_integral_o = store_thm(
    "iso_integral_o",
    ``∀m0 m1 s e a f g. g ∈ measure_preserving m0 m1 ⇒
        integral m1 f = integral m0 (f ∘ g)``,
    rw[integral_def,GSYM FN_PLUS_o,GSYM FN_MINUS_o] >>
    `(∀x. 0 ≤ fn_plus f x)` by rw[FN_PLUS_POS] >> `(∀x. 0 ≤ fn_minus f x)` by rw[FN_MINUS_POS] >>
    imp_res_tac iso_pos_fn_integral_o >> rw[]
);

val _ = export_theory();