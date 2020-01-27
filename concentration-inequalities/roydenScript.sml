open HolKernel Parse boolLib bossLib;
open combinTheory;
open pairTheory;
open pred_setTheory;
open arithmeticTheory;
open realTheory;
open seqTheory;
open util_probTheory;
open c487306_extrealTheory;
open c487306_measureTheory;
open c487306_lebesgueTheory;
open trivialTheory;
open finiteTheory;

val _ = new_theory "royden";

val semi_algebra_def = Define `semi_algebra a ⇔
    subset_class (space a) (subsets a) ∧ ∅ ∈ subsets a ∧
    (∀s. s ∈ subsets a ⇒ space a DIFF s ∈ finite_disjoint_unions (subsets a)) ∧
    ∀s t. s ∈ subsets a ∧ t ∈ subsets a ⇒ s ∩ t ∈ subsets a`;

val finitely_additive_def = Define `finitely_additive m = ∀n b.
    b ∈ (count n -> measurable_sets m) ∧
    BIGUNION (IMAGE b (count n)) ∈ measurable_sets m ∧
    (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
    (measure m (BIGUNION (IMAGE b (count n))) = sum (0,n) (measure m ∘ b))`;

val semi_alg_ext_rel_def = Define `semi_alg_ext_rel m =
    (λx y. ∀n b. b ∈ (count n -> measurable_sets m) ∧
    (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ∧
    (BIGUNION (IMAGE b (count n)) = x) ⇒
    (sum (0,n) (measure m ∘ b) = y))`;

val semi_alg_ext_meas_def = Define `semi_alg_ext_meas m = @nu. ∀x. semi_alg_ext_rel m x (nu x)`;

val prod_rect_rel_def = Define `prod_rect_rel m0 m1 =
    (λx y. ∀s0 s1. s0 ∈ measurable_sets m0 ∧ s1 ∈ measurable_sets m1 ∧ (s0 × s1 = x) ⇒
    (measure m0 s0 * measure m1 s1 = y))`;

val prod_rect_meas_def = Define `prod_rect_meas m0 m1 = @mnu. ∀s. prod_rect_rel m0 m1 s (mnu s)`;

val prod_measure_rect_def = Define `prod_measure_rect m0 m1 =
    inf_measure (m_space m0 × m_space m1,
    prod_sets (measurable_sets m0) (measurable_sets m1),prod_rect_meas m0 m1)`;

val prod_measure_space_rect_def = Define `prod_measure_space_rect m0 m1 =
    (m_space m0 × m_space m1,
    subsets (sigma (m_space m0 × m_space m1) (prod_sets (measurable_sets m0) (measurable_sets m1))),
    prod_measure_rect m0 m1)`;

(*****************)
(* Semi-Algebras *)
(*****************)

val semi_alg_diff = store_thm(
    "semi_alg_diff",
    ``∀a s. semi_algebra a ∧ s ∈ (subsets a) ⇒
        (space a) DIFF s ∈ finite_disjoint_unions (subsets a)``,
    rpt strip_tac >> Q.ABBREV_TAC `sp = space a` >> Q.ABBREV_TAC `sts = subsets a` >>
    `a = (sp,sts)` by (Q.UNABBREV_TAC `sp` >> Q.UNABBREV_TAC `sts` >> fs[SPACE]) >>
    fs[semi_algebra_def]
);

val semi_alg_finite_inters = store_thm(
    "semi_alg_finite_inters",
    ``∀a. semi_algebra a ⇒ (finite_inters (subsets a) = subsets a)``,
    rpt strip_tac >> Q.ABBREV_TAC `sp = space a` >> Q.ABBREV_TAC `sts = subsets a` >>
    `a = (sp,sts)` by (Q.UNABBREV_TAC `sp` >> Q.UNABBREV_TAC `sts` >> fs[SPACE]) >>
    fs[] >> NTAC 3 (pop_assum kall_tac) >>
    fs[EXTENSION] >> strip_tac >> eq_tac
    >- (fs[semi_algebra_def,finite_inters_alt,space_def,subsets_def] >>
        `∀n b x. 0 < n ∧ b ∈ (count n -> sts) ∧
            (BIGINTER (IMAGE b (count n)) = x) ⇒ x ∈ sts` suffices_by
            (rpt strip_tac >> RES_TAC) >>
        strip_tac >> Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >>
        qpat_x_assum `∀b'. _` (qspec_then `b` assume_tac) >> rfs[FUNSET] >>
        Cases_on `SUC n = 1` >> fs[BIGINTER_IMAGE_COUNT_ONE] >>
        fs[BIGINTER_IMAGE_COUNT_SUC])
    >- ((qspec_then `sts` assume_tac) sets_subset_finite_inters >> fs[SUBSET_DEF])
);

val semi_alg_finite_disj_unions_diff = store_thm(
    "semi_alg_finite_disj_unions_diff",
    ``∀a s. semi_algebra a ∧ s ∈ finite_disjoint_unions (subsets a) ⇒
        (space a) DIFF s ∈ finite_disjoint_unions (subsets a)``,
    rpt strip_tac >> Q.ABBREV_TAC `sp = space a` >> Q.ABBREV_TAC `sts = subsets a` >>
    `a = (sp,sts)` by (Q.UNABBREV_TAC `sp` >> Q.UNABBREV_TAC `sts` >> fs[SPACE]) >>
    fs[] >> NTAC 3 (pop_assum kall_tac) >>
    `sp DIFF s ∈ finite_inters (finite_disjoint_unions sts)` suffices_by (strip_tac >>
        `sp DIFF s ∈ finite_disjoint_unions (finite_inters sts)` by (
            (qspec_then `sts` assume_tac) finite_inter_finite_disj_union_conjugation >>
            fs[SUBSET_DEF]) >>
        imp_res_tac semi_alg_finite_inters >> fs[subsets_def]) >>
    `∀n b x. 0 < n ∧ b ∈ (count n -> sts) ∧ (BIGUNION (IMAGE b (count n)) = x) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
        sp DIFF x ∈ finite_inters (finite_disjoint_unions sts)` suffices_by (strip_tac >>
        fs[finite_disjoint_unions_alt] >> pop_assum (qspecl_then [`n`,`b`] assume_tac) >> rfs[]) >>
    pop_assum kall_tac >> strip_tac >> Induct_on `n` >> fs[] >> rpt strip_tac >>
    fs[BIGUNION_IMAGE_COUNT_SUC] >> fs[SET_DEMORGANS] >>
    `(sp DIFF b n) ∈ finite_disjoint_unions sts ∧
        (sp DIFF BIGUNION (IMAGE b (count n))) ∈ finite_inters (finite_disjoint_unions sts)`
        suffices_by fs[finite_disj_union_inter_finite_inter_of_finite_disj_union] >> rw[]
    >- (`b n ∈ sts` by fs[count_def,FUNSET] >>
        fs[semi_algebra_def,space_def,subsets_def])
    >- (qpat_x_assum `∀b. _` (qspec_then `b` assume_tac) >> Cases_on `n`
        >- (fs[BIGUNION_IMAGE_COUNT_ONE] >> rw[] >> pop_assum kall_tac >>
            fs[semi_algebra_def,space_def,subsets_def] >> RES_TAC >> fs[] >> rw[] >>
            (qspec_then `finite_disjoint_unions sts` assume_tac) sets_subset_finite_inters >>
            fs[SUBSET_DEF])
        >- (fs[] >> Q.RENAME_TAC[`sp DIFF BIGUNION (IMAGE b (count n))`] >>
            fs[count_def,FUNSET]))
);

val semi_alg_union_in_finite_disj_unions = store_thm(
    "semi_alg_union_in_finite_disj_unions",
    ``∀a s0 s1. semi_algebra a ∧ s0 ∈ subsets a ∧ s1 ∈ subsets a ⇒
        s0 ∪ s1 ∈ finite_disjoint_unions (subsets a)``,
    rpt strip_tac >> Q.ABBREV_TAC `sp = space a` >> Q.ABBREV_TAC `sts = subsets a` >>
    `a = (sp,sts)` by (Q.UNABBREV_TAC `sp` >> Q.UNABBREV_TAC `sts` >> fs[SPACE]) >>
    fs[] >> NTAC 3 (pop_assum kall_tac) >>
    imp_res_tac semi_alg_diff >> fs[space_def,subsets_def] >>
    `sp DIFF s0 ∈ finite_disjoint_unions sts` by RES_TAC >>
    `sp DIFF s1 ∈ finite_disjoint_unions sts` by RES_TAC >>
    `s0 ∩ s1 ∈ finite_inters sts` by fs[inter_in_finite_inters] >>
    `s0 ∩ (sp DIFF s1) ∈ finite_disjoint_unions (finite_inters sts)`
        by fs[set_inter_finite_disj_union] >>
    `s1 ∩ (sp DIFF s0) ∈ finite_disjoint_unions (finite_inters sts)`
        by fs[set_inter_finite_disj_union] >>
    imp_res_tac semi_alg_finite_inters >> fs[subsets_def] >>
    (qspecl_then [`sts`,`s0 ∩ s1`,`s0 ∩ (sp DIFF s1)`] assume_tac)
        set_union_finite_disj_union >> rfs[] >> rw[] >>
    `DISJOINT (s0 ∩ s1) (s0 ∩ (sp DIFF s1))` by (
        fs[DISJOINT_DEF,INTER_DEF,UNION_DEF,DIFF_DEF,EXTENSION] >> rw[] >>
        CCONTR_TAC >> fs[] >> metis_tac[]) >> fs[] >>
    (qspecl_then [`sts`,`s0 ∩ s1 ∪ s0 ∩ (sp DIFF s1)`,`s1 ∩ (sp DIFF s0)`] assume_tac)
        finite_disj_union_union_finite_disj_union >> rfs[] >>
    `DISJOINT (s0 ∩ s1) (s1 ∩ (sp DIFF s0))` by (
        fs[DISJOINT_DEF,INTER_DEF,UNION_DEF,DIFF_DEF,EXTENSION] >> rw[] >>
        CCONTR_TAC >> fs[] >> metis_tac[]) >> fs[] >>
    `DISJOINT (s0 ∩ (sp DIFF s1)) (s1 ∩ (sp DIFF s0))` by (
        fs[DISJOINT_DEF,INTER_DEF,UNION_DEF,DIFF_DEF,EXTENSION] >> rw[] >>
        CCONTR_TAC >> fs[] >> metis_tac[]) >> fs[] >>
    `s0 ∩ s1 ∪ s0 ∩ (sp DIFF s1) ∪ s1 ∩ (sp DIFF s0) = s0 ∪ s1` by (
        fs[DISJOINT_DEF,INTER_DEF,UNION_DEF,DIFF_DEF,EXTENSION] >> rw[] >>
        NTAC 10 (pop_assum kall_tac) >>
        fs[semi_algebra_def,subset_class_def,SUBSET_DEF,space_def,subsets_def] >>
        eq_tac >> rw[] >> fs[] >> CCONTR_TAC >> fs[] >> RES_TAC) >>
    fs[]
);

val semi_alg_finite_unions_disj = store_thm(
    "semi_alg_finite_unions_disj",
    ``∀a. semi_algebra a ⇒ (finite_unions (subsets a) = finite_disjoint_unions (subsets a))``,
    rpt strip_tac >> fs[SET_EQ_SUBSET] >> strip_tac
    >- (fs[finite_unions_alt,SUBSET_DEF] >> strip_tac >>
        `∀n b. 0 < n ∧ b ∈ (count n -> subsets a) ⇒
            BIGUNION (IMAGE b (count n)) ∈ finite_disjoint_unions (subsets a)` suffices_by (
            rpt strip_tac >> metis_tac[]) >>
        strip_tac >> Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >> Cases_on `n`
        >- (assume_tac sets_subset_finite_disj_unions >>
            fs[BIGUNION_IMAGE_COUNT_ONE,FUNSET,SUBSET_DEF])
        >- (fs[] >> Q.ABBREV_TAC `n = SUC n'` >> pop_assum kall_tac >>
            fs[BIGUNION_IMAGE_COUNT_SUC] >>
            qpat_x_assum `∀b. _` (qspecl_then [`b`] assume_tac) >>
            `b ∈ (count n -> subsets a)` by fs[count_def,FUNSET] >> fs[] >>
            pop_assum kall_tac >> `b n ∈ subsets a` by fs[FUNSET] >>
            qpat_x_assum `b ∈ _` kall_tac >>
            map_every Q.ABBREV_TAC [`A = b n`,`B = BIGUNION (IMAGE b (count n))`,
                `sp = space a`,`sts = subsets a`] >>
            `a = (space a,subsets a)` by fs[SPACE] >> rfs[] >> fs[] >>
            NTAC 5 (pop_assum kall_tac) >>
            `A ∩ (sp DIFF B) ∈ finite_disjoint_unions sts` by (
                imp_res_tac semi_alg_finite_disj_unions_diff >>
                fs[space_def,subsets_def] >> pop_assum imp_res_tac >>
                imp_res_tac set_inter_finite_disj_union >>
                imp_res_tac semi_alg_finite_inters >>
                fs[space_def,subsets_def]) >>
            `A ∩ B ∈ finite_disjoint_unions sts` by (
                imp_res_tac set_inter_finite_disj_union >>
                imp_res_tac semi_alg_finite_inters >>
                fs[space_def,subsets_def]) >>
            `(sp DIFF A) ∩ B ∈ finite_disjoint_unions sts` by (
                `sp DIFF A ∈ finite_disjoint_unions sts` by
                    fs[semi_algebra_def,space_def,subsets_def] >>
                `(sp DIFF A) ∩ B ∈ finite_disjoint_unions (finite_inters sts)` by
                    imp_res_tac finite_disj_union_inter_finite_disj_union >>
                imp_res_tac semi_alg_finite_inters >>
                fs[space_def,subsets_def]) >>
            `DISJOINT (A ∩ (sp DIFF B)) ((sp DIFF A) ∩ B)` by (rpt (pop_assum kall_tac) >>
                fs[DISJOINT_DEF,INTER_DEF,INTER_DEF,EXTENSION] >> rw[] >> metis_tac[]) >>
            (qspecl_then [`sts`,`A ∩ (sp DIFF B)`,`(sp DIFF A) ∩ B`] assume_tac)
                finite_disj_union_union_finite_disj_union >> rfs[] >>
            `DISJOINT (A ∩ B) (A ∩ (sp DIFF B) ∪ (sp DIFF A) ∩ B)` by (rpt (pop_assum kall_tac) >>
                fs[DISJOINT_DEF,INTER_DEF,INTER_DEF,EXTENSION] >> rw[] >> metis_tac[]) >>
            (qspecl_then [`sts`,`A ∩ B`,`A ∩ (sp DIFF B) ∪ (sp DIFF A) ∩ B`] assume_tac)
                finite_disj_union_union_finite_disj_union >> rfs[] >>
            `A ∩ B ∪ (A ∩ (sp DIFF B) ∪ (sp DIFF A) ∩ B) = A ∪ B` by (NTAC 8 (pop_assum kall_tac) >>
                fs[DISJOINT_DEF,INTER_DEF,INTER_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[] >>
                fs[] >> CCONTR_TAC >> fs[]
                >- (fs[semi_algebra_def,space_def,subsets_def,subset_class_def,SUBSET_DEF] >>
                    metis_tac[])
                >- (metis_tac[])
                >- (fs[finite_disjoint_unions_def] >> `x ∈ BIGUNION t` by fs[EXTENSION] >>
                    fs[IN_BIGUNION] >> `s ∈ sts` by fs[SUBSET_DEF] >>
                    fs[semi_algebra_def,space_def,subsets_def,subset_class_def,SUBSET_DEF] >>
                    metis_tac[])
                >- (metis_tac[])) >>
            fs[]))
    >- (assume_tac finite_disj_unions_subset_finite_unions >> fs[])
);

val semi_algebra_finite_disj_unions_semi_algebra = store_thm(
    "semi_algebra_finite_disj_unions_semi_algebra",
    ``∀a. semi_algebra a ⇒ semi_algebra (space a, finite_disjoint_unions (subsets a))``,
    strip_tac >> Q.ABBREV_TAC `sp = space a` >> Q.ABBREV_TAC `sts = subsets a` >> strip_tac >>
    `semi_algebra (sp,sts)` by (Q.UNABBREV_TAC `sp` >> Q.UNABBREV_TAC `sts` >> fs[SPACE]) >>
    NTAC 3 (last_x_assum kall_tac) >>
    pop_assum (fn th => fs[semi_algebra_def,space_def,subsets_def] >> assume_tac th) >> rw[]
    >- (fs[semi_algebra_def,space_def,subsets_def] >>
        NTAC 3 (first_x_assum kall_tac) >> fs[subset_class_def,finite_disjoint_unions_alt] >>
        rpt strip_tac >> fs[count_def,IMAGE_DEF,BIGUNION] >> fs[SUBSET_DEF,EXTENSION,FUNSET] >>
        rpt strip_tac >> qpat_x_assum `∀x'. _ ⇔ _` (qspec_then `x'` assume_tac) >> rfs[] >>
        qpat_x_assum `∀x. _ ⇔ _` (qspec_then `x'` assume_tac) >> rfs[] >>
        qpat_x_assum `∀x. _ ⇒ _` (qspec_then `x''` assume_tac) >> rfs[] >>
        qpat_x_assum `∀x. _ ⇒ _` (qspec_then `b x''` assume_tac) >> rfs[])
    >- (fs[semi_algebra_def,space_def,subsets_def] >>
        (qspec_then `sts` assume_tac) sets_subset_finite_disj_unions >> fs[SUBSET_DEF])
    >- ((qspecl_then [`(sp,sts)`,`s`] assume_tac) semi_alg_finite_disj_unions_diff >>
        rfs[composition_finite_disj_unions,space_def,subsets_def])
    >- (imp_res_tac finite_disj_union_inter_finite_disj_union >>
        imp_res_tac semi_alg_finite_inters >> fs[subsets_def])
);

val semi_alg_ext = store_thm(
    "semi_alg_ext",
    ``∀a. semi_algebra a ⇒ algebra (space a, finite_disjoint_unions (subsets a))``,
    strip_tac >> Q.ABBREV_TAC `sp = space a` >> Q.ABBREV_TAC `sts = subsets a` >> strip_tac >>
    `semi_algebra (sp,sts)` by (Q.UNABBREV_TAC `sp` >> Q.UNABBREV_TAC `sts` >> fs[SPACE]) >>
    NTAC 3 (last_x_assum kall_tac) >> imp_res_tac semi_algebra_finite_disj_unions_semi_algebra >>
    fs[algebra_def,space_def,subsets_def] >> rw[]
    >- (fs[semi_algebra_def,space_def,subsets_def])
    >- (fs[semi_algebra_def,space_def,subsets_def])
    >- (fs[semi_algebra_def,space_def,subsets_def,composition_finite_disj_unions])
    >- (imp_res_tac (GSYM semi_alg_finite_unions_disj) >>
        fs[space_def,subsets_def,finite_union_union_finite_union])
);

val semi_alg_ext_rel_mbl_set = store_thm(
    "semi_alg_ext_rel_mbl_set",
    ``∀m x y. semi_alg_ext_rel m x y ∧ x ∈ measurable_sets m ⇒ (measure m x = y)``,
    rw[] >> `∃sp sts mu. m = (sp,sts,mu)` by metis_tac[MEASURE_SPACE_REDUCE] >>
    fs[semi_alg_ext_rel_def,m_space_def,measurable_sets_def,measure_def] >> pop_assum kall_tac >>
    last_x_assum (qspecl_then [`1`,`(λi. x)`] assume_tac) >>
    rfs[FUNSET,BIGUNION_IMAGE_COUNT_ONE] >> assume_tac sum >> fs[] >>
    pop_assum (qspecl_then [`0`,`0`] assume_tac) >> fs[]
);

val semi_alg_ext_positive = store_thm(
    "semi_alg_ext_positive",
    ``∀m nu. positive m ∧ (∀x. (semi_alg_ext_rel m) x (nu x)) ⇒
        positive (m_space m,finite_disjoint_unions (measurable_sets m),nu)``,
    rpt strip_tac >> `∃sp sts mu. m = (sp,sts,mu)` by metis_tac[MEASURE_SPACE_REDUCE] >>
    fs[positive_def,m_space_def,measurable_sets_def,measure_def] >> pop_assum kall_tac >> rw[]
    >- (qpat_x_assum `∀x. _` (qspec_then `∅ : α -> bool` assume_tac) >>
        fs[semi_alg_ext_rel_def,measurable_sets_def,measure_def] >>
        pop_assum (qspecl_then [`0`,`λx. sp`] assume_tac) >> fs[count_def,FUNSET,sum])
    >- (qpat_x_assum `∀x. _` (qspec_then `s` assume_tac) >>
        fs[semi_alg_ext_rel_def,measurable_sets_def,measure_def] >>
        fs[finite_disjoint_unions_alt_dir] >>
        pop_assum (qspecl_then [`n`,`b`] assume_tac) >> rfs[] >>
        pop_assum (assume_tac o GSYM) >> fs[] >>
        `∀i. i < n ⇒ 0 ≤ (mu ∘ b) i` suffices_by fs[SUM_GE0] >> rw[] >>
        fs[count_def,FUNSET])
);

val semi_alg_ext_additive = store_thm(
    "semi_alg_ext_additive",
    ``∀m nu. (∀x. semi_alg_ext_rel m x (nu x)) ⇒
        additive (m_space m,finite_disjoint_unions (measurable_sets m),nu)``,
    rpt strip_tac >> `∃sp sts mu. m = (sp,sts,mu)` by metis_tac[MEASURE_SPACE_REDUCE] >>
    fs[additive_def,m_space_def,measurable_sets_def,measure_def] >> pop_assum kall_tac >> rw[] >>
    fs[finite_disjoint_unions_alt_dir] >>
    Q.RENAME_TAC [`nu (BIGUNION (IMAGE bs (count ns)) ∪ BIGUNION (IMAGE bt (count nt))) = _`] >>
    map_every Q.ABBREV_TAC [`bst = (λn. if n < ns then bs n else bt (n - ns))`,`nst = ns + nt`] >>
    `bst ∈ (count nst -> sts)` by (map_every Q.UNABBREV_TAC [`bst`,`nst`] >>
        fs[FUNSET] >> rw[]) >>
    `(∀i j. i < nst ∧ j < nst ∧ i ≠ j ⇒ DISJOINT (bst i) (bst j))` by (rw[] >>
        map_every Q.UNABBREV_TAC [`bst`,`nst`] >>
        Cases_on `i < ns` >> Cases_on `j < ns` >> fs[] >> rw[]
        >- (qpat_x_assum `∀s. _` (qspec_then `bs i` assume_tac) >> pop_assum imp_res_tac >> rfs[])
        >- (`DISJOINT (bs j) (bt (i − ns))` suffices_by fs[DISJOINT_SYM] >>
            qpat_x_assum `∀s. _` (qspec_then `bs j` assume_tac) >> pop_assum imp_res_tac >> rfs[])) >>
    `s ∪ t = BIGUNION (IMAGE bst (count nst))` by (map_every Q.UNABBREV_TAC [`bst`,`nst`] >>
        fs[EXTENSION] >> rw[] >> eq_tac >> rw[]
        >- (EXISTS_TAC ``s':α->bool`` >> fs[] >> EXISTS_TAC ``x':num`` >> fs[])
        >- (EXISTS_TAC ``s':α->bool`` >> fs[] >> EXISTS_TAC ``x'+ns:num`` >> fs[])
        >- (Cases_on `n < ns` >> fs[] >> rw[]
            >- (`∃s'. x ∈ s' ∧ ∃x. (∀x'. x' ∈ s' ⇔ x' ∈ bs x) ∧ x < ns` suffices_by fs[] >>
                EXISTS_TAC ``s':α->bool`` >> fs[] >> EXISTS_TAC ``n:num`` >> fs[])
            >- (`∃s'. x ∈ s' ∧ ∃x. (∀x'. x' ∈ s' ⇔ x' ∈ bt x) ∧ x < nt` suffices_by fs[] >>
                EXISTS_TAC ``s':α->bool`` >> fs[] >> EXISTS_TAC ``n-ns:num`` >> fs[]))) >>
    qpat_assum `∀x. _` (qspec_then `s` assume_tac) >>
    qpat_assum `∀x. _` (qspec_then `t` assume_tac) >>
    qpat_x_assum `∀x. _` (qspec_then `s ∪ t` assume_tac) >>
    fs[semi_alg_ext_rel_def,measurable_sets_def,measure_def] >>
    qpat_x_assum `∀n b. _` (qspecl_then [`nst`,`bst`] assume_tac) >>
    qpat_x_assum `∀n b. _` (qspecl_then [`nt`,`bt`] assume_tac) >>
    qpat_x_assum `∀n b. _` (qspecl_then [`ns`,`bs`] assume_tac) >> rfs[] >>
    `sum (0,nst) (mu ∘ bst) = sum (0,ns) (mu ∘ bs) + sum (0,nt) (mu ∘ bt)` suffices_by fs[] >>
    NTAC 3 (pop_assum kall_tac) >> Q.UNABBREV_TAC `nst` >> fs[GSYM SUM_TWO] >> 
    (qspecl_then [`(mu ∘ bst)`,`0`,`ns`,`nt`] assume_tac) SUM_REINDEX >> fs[] >>
    pop_assum kall_tac >>
    `∀r. r < ns ⇒ ((mu ∘ bst) r = (mu ∘ bs) r)` by (Q.UNABBREV_TAC `bst` >> rw[]) >>
    `∀r. r < nt ⇒ ((λr. mu (bst (ns + r))) r = (mu ∘ bt) r)` by (Q.UNABBREV_TAC `bst` >> rw[]) >>
    (qspecl_then [`(mu ∘ bst)`,`(mu ∘ bs)`,`0`,`ns`] assume_tac) SUM_EQ >>
    (qspecl_then [`(λr. mu (bst (ns + r)))`,`(mu ∘ bt)`,`0`,`nt`] assume_tac) SUM_EQ >> fs[]
);

val semi_alg_ext_meas_exists_lemma = store_thm(
    "semi_alg_ext_meas_exists_lemma",
    ``∀m n1 n2 b1 b2. semi_algebra (m_space m,measurable_sets m) ∧ finitely_additive m ∧
        b1 ∈ (count n1 -> measurable_sets m) ∧ b2 ∈ (count n2 -> measurable_sets m) ∧
        (∀i j. i < n2 ∧ j < n2 ∧ i ≠ j ⇒ DISJOINT (b2 i) (b2 j)) ∧
        BIGUNION (IMAGE b1 (count n1)) ⊆ BIGUNION (IMAGE b2 (count n2)) ⇒
        (sum (0,n1) (measure m ∘ b1) =
        sum (0,n1 * n2) (measure m ∘ (λn. b1 (n DIV n2) ∩ b2 (n MOD n2))))``,
    rw[GSYM SUM_GROUP] >> Q.ABBREV_TAC `f = (measure m ∘ (λn. b1 (n DIV n2) ∩ b2 (n MOD n2)))` >>
    `∀r. 0 ≤ r ∧ r < 0 + n1 ⇒ ((measure m ∘ b1) r = (λm. sum (m * n2,n2) f) r)`
        suffices_by fs[SUM_EQ] >>
    rw[] >> (qspecl_then [`f`,`0`,`n2 * r`,`n2`] assume_tac) SUM_REINDEX >> fs[] >>
    pop_assum kall_tac >> fs[finitely_additive_def] >>
    qpat_x_assum `∀n b. _` (qspecl_then [`n2`,`(λn. b1 r ∩ b2 n)`] assume_tac) >> fs[] >>
    `(λn. b1 r ∩ b2 n) ∈ (count n2 -> measurable_sets m)` by (fs[FUNSET] >> rw[] >>
        RES_TAC >> fs[semi_algebra_def,subsets_def]) >>
    `BIGUNION (IMAGE (λn. b1 r ∩ b2 n) (count n2)) = b1 r` by (fs[INTER_BIGUNION_IMAGE] >>
        fs[EXTENSION] >> rw[] >> eq_tac >> fs[] >> rw[] >> fs[GSYM EXTENSION,SUBSET_DEF] >>
        metis_tac[]) >>
    `b1 r ∈ measurable_sets m` by fs[FUNSET] >>
    `(∀i j. i < n2 ∧ j < n2 ∧ i ≠ j ⇒ DISJOINT (b1 r ∩ b2 i) (b1 r ∩ b2 j))` by (rw[] >>
        `DISJOINT (b2 i) (b2 j)` by RES_TAC >> fs[DISJOINT_DEF,INTER_DEF,EXTENSION] >>
        rw[] >> pop_assum (qspec_then `x` assume_tac) >> fs[]) >>
    fs[] >> NTAC 5 (pop_assum kall_tac) >>
    `∀q. 0 ≤ q ∧ q < 0 + n2 ⇒ ((measure m ∘ (λn. b1 r ∩ b2 n)) q = (λr'. f (r' + n2 * r)) q)`
        suffices_by fs[SUM_EQ] >>
    rw[] >> Q.UNABBREV_TAC `f` >> fs[] >> `((q + n2 * r) DIV n2) = r` suffices_by fs[] >>
    (qspecl_then [`n2`,`q`] assume_tac) DIV_MULT >> rfs[]
);

val semi_alg_ext_meas_exists = store_thm(
    "semi_alg_ext_meas_exists",
    ``∀m. semi_algebra (m_space m,measurable_sets m) ∧ finitely_additive m ⇒
        ∃nu. ∀x. semi_alg_ext_rel m x (nu x)``,
    rw[] >> fs[GSYM SKOLEM_THM] >> rw[semi_alg_ext_rel_def] >>
    Cases_on `∃n b. b ∈ (count n -> measurable_sets m) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ∧
        (BIGUNION (IMAGE b (count n)) = x)` >> rw[]
    >- (EXISTS_TAC ``sum (0,n) (measure m ∘ b)`` >> rw[] >>
        Q.RENAME_TAC [`sum (0,n2) (measure m ∘ b2) = sum (0,n1) (measure m ∘ b1)`] >>
        (qspecl_then [`m`,`n1`,`n2`,`b1`,`b2`] assume_tac) semi_alg_ext_meas_exists_lemma >>
        (qspecl_then [`m`,`n2`,`n1`,`b2`,`b1`] assume_tac) semi_alg_ext_meas_exists_lemma >>
        rfs[EQ_SUBSET_SUBSET] >> rpt (pop_assum kall_tac) >>
        Cases_on `n1` >> Cases_on `n2` >> fs[sum] >> `0 < SUC n ∧ 0 < SUC n'` by fs[] >>
        Q.RENAME_TAC [`sum (0,n1 * n2) _ = _`] >>
        (qspecl_then [`n1 * n2`,`(λn. (n MOD n1) * n2 + (n DIV n1))`] assume_tac) SUM_PERMUTE_0 >>
        `(∀y. y < n1 * n2 ⇒ ∃!x. x < n1 * n2 ∧ ((λn. n MOD n1 * n2 + n DIV n1) x = y))` by (
            pop_assum kall_tac >> rw[] >> fs[EXISTS_UNIQUE_THM] >> rw[]
            >- (EXISTS_TAC ``(y MOD n2) * n1 + (y DIV n2)`` >> rw[]
                >- (`y MOD n2 < n2` by fs[MOD_LESS] >> `y DIV n2 < n1` by fs[DIV_LT_X] >>
                    `y MOD n2 ≤ n2 - 1` by fs[] >> `y DIV n2 ≤ n1 - 1` by fs[] >>
                    `n1 * y MOD n2 ≤ n1 * (n2 - 1)` by fs[] >>
                    `n1 * y MOD n2 + y DIV n2 ≤ n1 * (n2 − 1) + (n1 - 1)`
                        by fs[LESS_EQ_LESS_EQ_MONO] >>
                    `n1 * y MOD n2 + y DIV n2 < n1 * (n2 − 1) + (n1 - 1) + 1` by fs[] >>
                    `n1 * (n2 − 1) + (n1 − 1) + 1 = n1 * n2` suffices_by fs[] >>
                    NTAC 8 (pop_assum kall_tac) >> fs[LEFT_SUB_DISTRIB,ADD_ASSOC] >>
                    `n2 * n1 − n1 + ((n1 − 1) + 1) = n1 * n2` suffices_by fs[] >> fs[] >>
                    `n1 ≤ n1 * n2` by fs[] >> fs[SUB_ADD])
                >- ((qspecl_then [`y`,`n2`] assume_tac) DA >> rfs[] >>
                    (qspecl_then [`n2`,`r`] assume_tac) DIV_MULT >> rfs[] >>
                    (qspecl_then [`n1`,`q`] assume_tac) DIV_MULT >>
                    `q < n1` by (CCONTR_TAC >> fs[] >> rw[] >>
                        `n1 ≤ q` by fs[] >> `n1 * n2 ≤ q * n2` by fs[] >> rw[]) >>
                    fs[]))
            >- (Q.RENAME_TAC [`x = y`] >> (qspecl_then [`x`,`n1`] assume_tac) DA >>
                (qspecl_then [`y`,`n1`] assume_tac) DA >> rfs[] >> fs[] >>
                (qspecl_then [`n1`,`r`] assume_tac) DIV_MULT >>
                (qspecl_then [`n1`,`r'`] assume_tac) DIV_MULT >> rfs[] >> fs[] >> rw[] >>
                NTAC 2 (pop_assum kall_tac) >> Q.RENAME_TAC [`ra + n1 * qa = rb + n1 * qb`] >>
                `qa < n2` by (CCONTR_TAC >> `n2 ≤ qa` by fs[] >> `n1 * n2 ≤ n1 * qa` by fs[] >>
                    `ra + n1 * n2 ≤ ra + n1 * qa` by fs[] >> rw[]) >>
                `qb < n2` by (CCONTR_TAC >> `n2 ≤ qb` by fs[] >> `n1 * n2 ≤ n1 * qb` by fs[] >>
                    `rb + n1 * n2 ≤ rb + n1 * qb` by fs[] >> rw[]) >>
                fs[] >> rw[] >> map_every Q.ABBREV_TAC [`x = qa + n2 * ra`,`y = qb + n2 * rb`] >>
                `(x MOD n2) * n1 + (x DIV n2) = (y MOD n2) * n1 + (y DIV n2)` by fs[] >>
                map_every Q.UNABBREV_TAC [`x`,`y`] >> qpat_x_assum `qa + _ = _` kall_tac >>
                rfs[] >> (qspecl_then [`n2`,`qa`] assume_tac) DIV_MULT >>
                (qspecl_then [`n2`,`qb`] assume_tac) DIV_MULT >> rfs[] >> fs[])) >>
        fs[] >> pop_assum kall_tac >>
        Q.ABBREV_TAC `g = (measure m ∘ (λn. b1 (n DIV n2) ∩ b2 (n MOD n2)))` >>
        qpat_x_assum `∀f. _` (qspec_then `g` assume_tac) >>
        `∀x. 0 ≤ x ∧ x < n1 * n2 ⇒ ((measure m ∘ (λn. b2 (n DIV n1) ∩ b1 (n MOD n1))) x =
            (λn. g (n2 * n MOD n1 + n DIV n1)) x)` suffices_by (rw[] >>
            (qspecl_then [`(measure m ∘ (λn. b2 (n DIV n1) ∩ b1 (n MOD n1)))`,
                `(λn. g (n2 * n MOD n1 + n DIV n1))`,`0`,`n1 * n2`] assume_tac) SUM_EQ >>
            rfs[]) >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `g` >> rw[] >>
        (qspecl_then [`x`,`n1`] assume_tac) DA >> rfs[] >> fs[] >> rw[] >>
        `q < n2` by (CCONTR_TAC >> `n2 ≤ q` by fs[] >> `n1 * n2 ≤ n1 * q` by fs[] >>
            `r + n1 * n2 ≤ r + n1 * q` by fs[] >> rw[]) >>
        fs[] >> rw[] >> (qspecl_then [`n1`,`r`] assume_tac) DIV_MULT >> rfs[] >> fs[] >>
        (qspecl_then [`n2`,`q`] assume_tac) DIV_MULT >> rfs[] >> fs[INTER_COMM])
    >- (EXISTS_TAC ``0:real`` >> rw[] >> CCONTR_TAC >> fs[] >>
        qpat_x_assum `∀n b. _` (qspecl_then [`n`,`b`] assume_tac) >> metis_tac[])
);

val semi_alg_ext_meas_replace = store_thm(
    "semi_alg_ext_meas_replace",
    ``∀m. semi_algebra (m_space m,measurable_sets m) ∧ finitely_additive m ⇒
        ∃nu. (semi_alg_ext_meas m = nu) ∧ ∀x. semi_alg_ext_rel m x (nu x)``,
    rw[] >> `∃sp sts mu. m = (sp,sts,mu)` by metis_tac[MEASURE_SPACE_REDUCE] >>
    fs[measurable_sets_def,measure_def] >> pop_assum kall_tac >>
    Q.ABBREV_TAC `nu = semi_alg_ext_meas (sp,sts,mu)` >>
    Q.ABBREV_TAC `nu_rel = semi_alg_ext_rel (sp,sts,mu)` >>
    `(∀x. nu_rel x (nu x))` by (Q.UNABBREV_TAC `nu` >>
        fs[semi_alg_ext_meas_def] >> Q.ABBREV_TAC `P = (λf. ∀x. nu_rel x (f x))` >>
        assume_tac (ISPEC ``P : ((α -> bool) -> real) -> bool`` SELECT_THM) >>
        map_every Q.UNABBREV_TAC [`P`,`nu_rel`] >> fs[] >> pop_assum kall_tac >>
        (qspecl_then [`(sp,sts,mu)`] assume_tac) semi_alg_ext_meas_exists >>
        rfs[m_space_def,measurable_sets_def] >>
        EXISTS_TAC ``nu : (α -> bool) -> real`` >> fs[]) >>
    fs[]
);

val semi_alg_ext_meas_mbl_set = store_thm(
    "semi_alg_ext_meas_mbl_set",
    ``∀m x y. semi_algebra (m_space m,measurable_sets m) ∧ finitely_additive m ∧
        x ∈ measurable_sets m ⇒ (semi_alg_ext_meas m x = measure m x)``,
    rw[] >> (qspec_then `m` assume_tac) semi_alg_ext_meas_replace >> rfs[] >>
    Q.RENAME_TAC [`nu x = _`] >>
    (qspecl_then [`m`,`x`,`nu x`] assume_tac) semi_alg_ext_rel_mbl_set >> rfs[]
);

val inf_meas_semi_alg_ext_meas = store_thm(
    "inf_meas_semi_alg_ext_meas",
    ``∀m. semi_algebra (m_space m,measurable_sets m) ∧ finitely_additive m ∧ positive m ⇒
        (inf_measure (m_space m,finite_disjoint_unions (measurable_sets m),semi_alg_ext_meas m) =
        inf_measure m)``,
    rw[] >> fs[FUN_EQ_THM,inf_measure_def] >> rw[measurable_sets_def,measure_def] >>
    `{r | (∃f. f ∈ (𝕌(:num) -> finite_disjoint_unions (measurable_sets m)) ∧
        (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
        x ⊆ BIGUNION (IMAGE f 𝕌(:num)) ∧ semi_alg_ext_meas m ∘ f sums r)} =
        {r | (∃f. f ∈ (𝕌(:num) -> measurable_sets m) ∧
        (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
        x ⊆ BIGUNION (IMAGE f 𝕌(:num)) ∧ measure m ∘ f sums r)}` suffices_by fs[] >>
    fs[EXTENSION] >> rw[] >> eq_tac >> rw[]
    >- (`∃ns bs. ∀k. 0 < (ns k) ∧ (∀i. (ns k) ≤ i ⇒ (bs k i = ∅)) ∧
            (bs k) ∈ (count (ns k) -> measurable_sets m) ∧
            (BIGUNION (IMAGE (bs k) (count (ns k))) = f k) ∧
            ∀i j. i < (ns k) ∧ j < (ns k) ∧ i ≠ j ⇒ DISJOINT (bs k i) (bs k j)` by (
            fs[GSYM SKOLEM_THM] >> rw[] >>
            `f k ∈ finite_disjoint_unions (measurable_sets m)` by fs[FUNSET] >>
            fs[finite_disjoint_unions_alt] >>
            map_every EXISTS_TAC [``n : num``,
                ``(λij : num. if ij < n then (b ij) else ∅ : α -> bool)``] >>
            fs[FUNSET] >>
            `∀y. y ∈ BIGUNION (IMAGE b (count n)) ⇔ y ∈ f k` by fs[EXTENSION] >>
            `∀y. y ∈ BIGUNION (IMAGE (λij. if ij < n then b ij else ∅) (count n)) ⇔ y ∈ f k`
                suffices_by fs[EXTENSION] >>
            fs[IN_BIGUNION_IMAGE] >> rw[] >> eq_tac >> rw[]
            >- (rfs[] >> qpat_x_assum `∀y. _` (qspec_then `y` (assume_tac o GSYM)) >>
                fs[] >> EXISTS_TAC ``ij:num`` >> fs[])
            >- (qpat_x_assum `∀y. _` (qspec_then `y` (assume_tac o GSYM)) >> fs[] >>
                EXISTS_TAC ``x'':num`` >> fs[])) >>
        (qspecl_then [`(λi j. measure m (bs i j))`,`semi_alg_ext_meas m ∘ f`,`num_to_pair`]
            assume_tac) SUMINF_2D >>
        Q.ABBREV_TAC `tmp = (λ(i,j). bs i j) ∘ num_to_pair` >>
        EXISTS_TAC ``tmp : num -> α -> bool`` >> Q.UNABBREV_TAC `tmp` >>
        (qspec_then `m` assume_tac) semi_alg_ext_meas_replace >> rfs[] >>
        Q.ABBREV_TAC `nu = semi_alg_ext_meas m` >> pop_assum kall_tac >>
        `∃sp sts mu. m = (sp,sts,mu)` by metis_tac[MEASURE_SPACE_REDUCE] >>
        fs[m_space_def,measurable_sets_def,measure_def,semi_alg_ext_rel_def] >>
        map_every Q.ABBREV_TAC [`s = x`,`r = x'`] >> NTAC 3 (pop_assum kall_tac) >>
        rfs[SUMS_EQ] >> fs[GSYM SUMS_EQ,NUM_TO_PAIR_BIJ] >>
        `∀m' n. 0 ≤ mu (bs m' n)` by(rw[] >> Q.RENAME_TAC [`0 ≤ mu (bs m n)`] >>
            qpat_x_assum `∀k. 0 < ns k ∧ _` (qspec_then `m` assume_tac) >>
            fs[FUNSET,positive_def,measure_def,measurable_sets_def] >>
            Cases_on `n < ns m` >> fs[]) >>
        `∀n. (λj. mu (bs n j)) sums nu (f n)` by (rw[] >>
            qpat_x_assum `∀k. 0 < ns k ∧ _` (qspec_then `n` assume_tac) >> fs[] >>
            qpat_x_assum `∀n b. _` (qspecl_then [`ns n`,`bs n`] assume_tac) >> rfs[] >>
            pop_assum (assume_tac o GSYM) >> fs[] >> pop_assum kall_tac >>
            (qspecl_then [`(mu ∘ bs n)`,`ns n`] assume_tac) SER_0 >>
            `∀m. ns n ≤ m ⇒ ((mu ∘ bs n) m = 0)` suffices_by metis_tac[o_DEF] >>
            rw[] >> fs[positive_def,measure_def]) >>
        fs[] >> rw[]
        >- (fs[o_DEF,FUNSET,num_to_pair_def] >> rw[] >>
            qpat_x_assum `∀k. 0 < ns k ∧ _` (qspec_then `(nfst x)` assume_tac) >>
            fs[semi_algebra_def,space_def,subsets_def] >>
            Cases_on `nsnd x < ns (nfst x)` >> fs[])
        >- (`DISJOINT (f m) (f n)` by RES_TAC >> fs[DISJOINT_DEF,num_to_pair_def] >>
            qpat_assum `∀k. 0 < ns k ∧ _` (qspec_then `(nfst m)` assume_tac) >>
            qpat_x_assum `∀k. 0 < ns k ∧ _` (qspec_then `(nfst n)` assume_tac) >> fs[] >>
            Cases_on `(nsnd m) < ns (nfst m)` >> Cases_on `(nsnd n) < ns (nfst n)` >>
            fs[] >> rw[] >>
            `bs (nfst m) (nsnd m) ⊆ BIGUNION (IMAGE (bs (nfst m)) (count (ns (nfst m))))` by (
                NTAC 2 (qpat_x_assum `BIGUNION _ = _` kall_tac) >>
                fs[SUBSET_DEF,count_def] >> metis_tac[]) >>
            `bs (nfst n) (nsnd n) ⊆ BIGUNION (IMAGE (bs (nfst n)) (count (ns (nfst n))))` by (
                NTAC 2 (qpat_x_assum `BIGUNION _ = _` kall_tac) >>
                fs[SUBSET_DEF,count_def] >> metis_tac[]) >>
            rfs[] >> rw[] >> Cases_on `nfst m = nfst n`
            >- (fs[] >> rw[] >> Cases_on `nsnd m = nsnd n`
                >- (fs[] >> rw[] >>
                    `pair_to_num (num_to_pair m) = m` by fs[pair_to_num_inv] >>
                    `pair_to_num (num_to_pair n) = n` by fs[pair_to_num_inv] >>
                    fs[num_to_pair_def] >> rfs[])
                >- (qpat_x_assum `∀i j. _` (qspecl_then [`nsnd m`,`nsnd n`] assume_tac) >> rfs[]))
            >- (`f (nfst m) ∩ f (nfst n) = ∅` by RES_TAC >>
                fs[INTER_DEF,EXTENSION,SUBSET_DEF] >> metis_tac[]))
        >- (`∀x. x ∈ s ⇒ x ∈ BIGUNION (IMAGE ((λ(i,j). bs i j) ∘ num_to_pair) 𝕌(:num))`
                suffices_by fs[SUBSET_DEF] >>
            `∀x. x ∈ s ⇒ x ∈ BIGUNION (IMAGE f 𝕌(:num))` by fs[SUBSET_DEF] >>
            fs[IN_BIGUNION] >> rw[] >> RES_TAC >>
            qpat_x_assum `∀k. 0 < ns k ∧ _` (qspec_then `x'` assume_tac) >> fs[] >>
            qpat_x_assum `BIGUNION _ = _` (assume_tac o GSYM) >> fs[IN_BIGUNION] >>
            EXISTS_TAC ``s'' : α -> bool`` >> fs[] >>
            EXISTS_TAC ``pair_to_num (x',x'')`` >> fs[pair_to_num_inv])
        >- (fs[o_DEF,num_to_pair_def]))
    >- (EXISTS_TAC ``f:num -> α -> bool`` >> fs[] >> rw[]
        >- (fs[FUNSET] >> rw[] >>
            (qspec_then `measurable_sets m` assume_tac) sets_subset_finite_disj_unions >>
            fs[SUBSET_DEF])
        >- (`semi_alg_ext_meas m ∘ f = measure m ∘ f` suffices_by fs[] >>
            fs[FUN_EQ_THM,FUNSET] >> rw[] >> fs[semi_alg_ext_meas_mbl_set]))
);

val ALGEBRA_FROM_SEMI_ALGEBRA = store_thm(
    "ALGEBRA_FROM_SEMI_ALGEBRA",
    ``∀m. semi_algebra (m_space m,measurable_sets m) ∧ finitely_additive m ∧
        positive m ⇒ algebra (m_space m,finite_disjoint_unions (measurable_sets m)) ∧
        positive (m_space m,finite_disjoint_unions (measurable_sets m),semi_alg_ext_meas m) ∧
        additive (m_space m,finite_disjoint_unions (measurable_sets m),semi_alg_ext_meas m)``,
    NTAC 2 strip_tac >>
    (qspecl_then [`m`,`semi_alg_ext_meas m`] assume_tac) semi_alg_ext_positive >>
    (qspecl_then [`m`,`semi_alg_ext_meas m`] assume_tac) semi_alg_ext_additive >>
    (qspec_then `m` assume_tac) semi_alg_ext_meas_replace >> rfs[] >> fs[] >>
    imp_res_tac semi_alg_ext >> fs[space_def,subsets_def]
);

val MEASURE_SPACE_FROM_SEMI_ALGEBRA = store_thm(
    "MEASURE_SPACE_FROM_SEMI_ALGEBRA",
    ``∀m. semi_algebra (m_space m,measurable_sets m) ∧ finitely_additive m ∧
        positive m ⇒ measure_space
        (m_space m,subsets (sigma (m_space m) (measurable_sets m)),inf_measure m)``,
    rw[] >> imp_res_tac ALGEBRA_FROM_SEMI_ALGEBRA >>
    imp_res_tac MEASURE_SPACE_FROM_ALGEBRA >> pop_assum kall_tac >>
    rfs[m_space_def,measurable_sets_def] >> fs[sigma_finite_disj_unions] >>
    rfs[inf_meas_semi_alg_ext_meas]
);

(*************************)
(* Product Measure Space *)
(*************************)

val RECT_MEASURE_EMPTY = store_thm(
    "RECT_MEASURE_EMPTY",
    ``∀m0 m1 mnu. measure_space m0 ∧ measure_space m1 ∧ (∀s. prod_rect_rel m0 m1 s (mnu s)) ⇒
        (mnu ∅ = 0)``,
    rw[] >> fs[prod_rect_rel_def] >>
    pop_assum (qspecl_then [`∅ : α -> bool`,`∅ : β -> bool`] (assume_tac o GSYM)) >>
    rfs[MEASURE_SPACE_EMPTY_MEASURABLE] >> fs[MEASURE_EMPTY]
);

val prod_rect_meas_union_left = store_thm(
    "prod_rect_meas_union_left",
    ``∀m0 m1 mnu r s t. measure_space m0 ∧ measure_space m1 ∧ (∀s. prod_rect_rel m0 m1 s (mnu s)) ∧
        DISJOINT s t ∧ r ∈ measurable_sets m1 ∧ s ∈ measurable_sets m0 ∧ t ∈ measurable_sets m0 ⇒
        (mnu ((s ∪ t) × r) = mnu (s × r) + mnu (t × r))``,
    rw[] >> `s ∪ t ∈ measurable_sets m0` by fs[MEASURE_SPACE_UNION] >> fs[prod_rect_rel_def] >>
    `∀u. (u = s ∪ t) ⇒ (measure m0 u = measure m0 s + measure m0 t)` by imp_res_tac MEASURE_ADDITIVE >>
    pop_assum (qspec_then `s ∪ t` assume_tac) >> fs[] >>
    qpat_x_assum `∀s0 s1. _` (fn th => map_every (fn sp => (qspecl_then sp (assume_tac o GSYM)) th)
        [[`s`,`r`],[`t`,`r`],[`s ∪ t`,`r`]]) >>
    rfs[REAL_ADD_RDISTRIB]
);

val prod_rect_meas_union_right = store_thm(
    "prod_rect_meas_union_right",
    ``∀m0 m1 mnu r s t. measure_space m0 ∧ measure_space m1 ∧ (∀s. prod_rect_rel m0 m1 s (mnu s)) ∧
        DISJOINT s t ∧ r ∈ measurable_sets m0 ∧ s ∈ measurable_sets m1 ∧ t ∈ measurable_sets m1 ⇒
        (mnu (r × (s ∪ t)) = mnu (r × s) + mnu (r × t))``,
    rw[] >> `s ∪ t ∈ measurable_sets m1` by fs[MEASURE_SPACE_UNION] >> fs[prod_rect_rel_def] >>
    `∀u. (u = s ∪ t) ⇒ (measure m1 u = measure m1 s + measure m1 t)` by imp_res_tac MEASURE_ADDITIVE >>
    pop_assum (qspec_then `s ∪ t : β -> bool` assume_tac) >> fs[] >>
    qpat_x_assum `∀s0 s1. _` (fn th => map_every (fn sp => (qspecl_then sp (assume_tac o GSYM)) th)
        [[`r`,`s`],[`r`,`t`],[`r`,`s ∪ t`]]) >>
    rfs[REAL_ADD_LDISTRIB]
);

val prod_sets_semi_alg = store_thm(
    "prod_sets_semi_alg",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        semi_algebra (m_space m0 × m_space m1,prod_sets (measurable_sets m0) (measurable_sets m1))``,
    rw[] >> `∃sp0 sts0 mu0. m0 = (sp0,sts0,mu0)` by metis_tac[MEASURE_SPACE_REDUCE] >>
    `∃sp1 sts1 mu1. m1 = (sp1,sts1,mu1)` by metis_tac[MEASURE_SPACE_REDUCE] >>
    fs[semi_algebra_def,space_def,subsets_def,m_space_def,measurable_sets_def,measure_def] >>
    NTAC 2 (pop_assum kall_tac) >> rw[]
    >- (fs[measure_space_def,sigma_algebra_def,algebra_def,subset_class_def,prod_sets_def] >>
        fs[m_space_def,measurable_sets_def,space_def,subsets_def] >> rw[] >>
        `s ⊆ sp0` by RES_TAC >> `t ⊆ sp1` by RES_TAC >> NTAC 16 (last_x_assum kall_tac) >>
        fs[CROSS_DEF,SUBSET_DEF])
    >- (fs[measure_space_def,sigma_algebra_def,algebra_def,subset_class_def,prod_sets_def] >>
        fs[m_space_def,measurable_sets_def,space_def,subsets_def] >> rw[] >>
        map_every EXISTS_TAC [``∅ : α -> bool``,``∅ : β -> bool``] >> fs[])
    >- (fs[prod_sets_def] >> Q.RENAME_TAC [`_ = s × t`] >> qpat_x_assum `_ = _` kall_tac >>
        fs[GSYM prod_sets_def] >>
        (qspecl_then [`s`,`(sp0,sts0,mu0)`] assume_tac) MEASURE_SPACE_SUBSET_MSPACE >>
        (assume_tac o ISPECL [``t : β -> bool``,
            ``(sp1,sts1,mu1) : (β -> bool) # ((β -> bool) -> bool) # ((β -> bool) -> real)``])
            MEASURE_SPACE_SUBSET_MSPACE >>
        rfs[measurable_sets_def,m_space_def,CROSS_DIFF] >>
        `(sp0 DIFF s) × (sp1 DIFF t) ∈ prod_sets sts0 sts1 ∧
            (sp0 DIFF s) × t ∈ prod_sets sts0 sts1 ∧
            s × (sp1 DIFF t) ∈ prod_sets sts0 sts1` by (fs[prod_sets_def] >>
            fs[measure_space_def,sigma_algebra_def,algebra_def,subset_class_def,prod_sets_def] >>
            fs[m_space_def,measurable_sets_def,space_def,subsets_def] >>
            `sp0 DIFF s ∈ sts0` by RES_TAC >> `sp1 DIFF t ∈ sts1` by RES_TAC >>
            NTAC 14 (last_x_assum kall_tac) >> rw[] >> metis_tac[]) >>
        `DISJOINT ((sp0 DIFF s) × (sp1 DIFF t)) ((sp0 DIFF s) × t)` by (
            fs[DISJOINT_DEF,DIFF_DEF,CROSS_DEF,EXTENSION] >> rw[] >>
            Cases_on `SND x ∈ t` >> fs[]) >>
        `DISJOINT ((sp0 DIFF s) × (sp1 DIFF t) ∪ (sp0 DIFF s) × t) (s × (sp1 DIFF t))` by (
            fs[DISJOINT_DEF,DIFF_DEF,CROSS_DEF,EXTENSION] >> rw[] >>
            Cases_on `FST x ∈ s` >> Cases_on `SND x ∈ t` >> fs[]) >>
        map_every Q.ABBREV_TAC [`A = (sp0 DIFF s) × (sp1 DIFF t)`,
            `B = (sp0 DIFF s) × t`,`C = s × (sp1 DIFF t)`,`P = prod_sets sts0 sts1`] >>
        NTAC 4 (pop_assum kall_tac) >> NTAC 6 (last_x_assum kall_tac) >>
        `A ∪ B ∈ finite_disjoint_unions P` by imp_res_tac union_in_finite_disj_unions >>
        (assume_tac o ISPECL [``P : (α # β -> bool) -> bool``,``C : α # β -> bool``,
            ``A ∪ B : α # β -> bool``]) set_union_finite_disj_union >>
        rfs[DISJOINT_SYM,UNION_COMM])
    >- (fs[prod_sets_def] >> Q.RENAME_TAC [`t = c × d`] >> qpat_x_assum `_ = _` kall_tac >>
        Q.RENAME_TAC [`s = a × b`] >> qpat_x_assum `_ = _` kall_tac >>
        map_every EXISTS_TAC [``a ∩ c : α -> bool``,``b ∩ d : β -> bool``] >> rw[]
        >- (fs[EXTENSION] >> metis_tac[])
        >- (imp_res_tac MEASURE_SPACE_INTER >> fs[measurable_sets_def])
        >- (imp_res_tac MEASURE_SPACE_INTER >> fs[measurable_sets_def]))
);

val prod_sets_finite_union_algebra = store_thm(
    "prod_sets_finite_union_algebra",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        algebra (m_space m0 × m_space m1,
        finite_disjoint_unions (prod_sets (measurable_sets m0) (measurable_sets m1)))``,
    rw[] >> imp_res_tac prod_sets_semi_alg >> imp_res_tac semi_alg_ext >>
    fs[space_def,subsets_def]
);

val prod_rect_positive = store_thm(
    "prod_rect_positive",
    ``∀m0 m1 mnu. measure_space m0 ∧ measure_space m1 ∧ (∀s. prod_rect_rel m0 m1 s (mnu s)) ⇒
        positive (m_space m0 × m_space m1,prod_sets (measurable_sets m0) (measurable_sets m1),mnu)``,
    rw[] >> `∃sp0 sts0 mu0. m0 = (sp0,sts0,mu0)` by metis_tac[MEASURE_SPACE_REDUCE] >>
    `∃sp1 sts1 mu1. m1 = (sp1,sts1,mu1)` by metis_tac[MEASURE_SPACE_REDUCE] >>
    fs[positive_def,prod_rect_rel_def,m_space_def,measurable_sets_def,measure_def] >>
    NTAC 2 (pop_assum kall_tac) >> rw[]
    >- (map_every imp_res_tac [MEASURE_EMPTY,MEASURE_SPACE_EMPTY_MEASURABLE] >>
        fs[measurable_sets_def,measure_def] >> qpat_x_assum `∀s0 s1. _` imp_res_tac >> rfs[])
    >- (fs[prod_sets_def] >> Q.RENAME_TAC [`_ = s × t`] >> qpat_x_assum `_ = _` kall_tac >>
        qpat_x_assum `∀s0 s1. _` (imp_res_tac o GSYM) >> fs[] >> pop_assum kall_tac >>
        imp_res_tac MEASURE_POSITIVE >> fs[measurable_sets_def,measure_def] >> RES_TAC >>
        fs[REAL_LE_MUL])
);

val prod_rect_meas_exists = store_thm(
    "prod_rect_meas_exists",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒ ∃mnu. ∀s. prod_rect_rel m0 m1 s (mnu s)``,
    rw[] >> fs[GSYM SKOLEM_THM] >> rw[prod_rect_rel_def] >>
    Cases_on `∃t0 t1. t0 ∈ measurable_sets m0 ∧ t1 ∈ measurable_sets m1 ∧ (t0 × t1 = s)` >> fs[]
    >- (EXISTS_TAC ``measure m0 t0 * measure m1 t1`` >> rw[] >> imp_res_tac MEASURE_EMPTY >>
        Cases_on `t0 × t1 = ∅` >- (fs[] >> fs[CROSS_EMPTY_EQN]) >>
        imp_res_tac CROSS_EQ >> fs[])
    >- (EXISTS_TAC ``0:real`` >> rw[] >>
        qpat_x_assum `∀t0 t1. _` (assume_tac o ISPECL [``s0 : α -> bool``,``s1 : β -> bool``]) >>
        rfs[])
);

val prod_rect_meas_replace = store_thm(
    "prod_rect_meas_replace",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        ∃mnu. (prod_rect_meas m0 m1 = mnu) ∧ ∀s. prod_rect_rel m0 m1 s (mnu s)``,
    rw[prod_rect_meas_def] >>
    (assume_tac o ISPEC ``λmnu. ∀s. prod_rect_rel m0 m1 s (mnu s)``) (GSYM SELECT_THM) >>
    fs[EQ_IMP_THM] >> rfs[prod_rect_meas_exists]
);

val prod_rect_finitely_additive_left = store_thm(
    "prod_rect_finitely_additive_left",
    ``∀m0 m1 mnu n s t. measure_space m0 ∧ measure_space m1 ∧ (∀s. prod_rect_rel m0 m1 s (mnu s)) ∧
        s ∈ (count n -> measurable_sets m0) ∧ t ∈ measurable_sets m1 ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (s i) (s j)) ⇒
        (mnu (BIGUNION (IMAGE s (count n)) × t) = sum (0,n) (mnu ∘ (λr. s r × t)))``,
    rw[] >> `mnu ∅ = 0` by imp_res_tac RECT_MEASURE_EMPTY >>
    Induct_on `n` >> rw[] >> fs[sum,BIGUNION_IMAGE_COUNT_SUC,FUNSET] >>
    `BIGUNION (IMAGE s (count n)) ∈ measurable_sets m0` by (
        (qspecl_then [`m0`,`n`,`s`] assume_tac) MEASURE_SPACE_FINITE_UNION >> rfs[FUNSET]) >>
    `s n ∈ measurable_sets m0` by fs[] >>
    `DISJOINT (BIGUNION (IMAGE s (count n))) (s n)` by (fs[DISJOINT_DEF] >> rw[] >>
        qpat_x_assum `∀i j. _` (qspecl_then [`x`,`n`] assume_tac) >> fs[]) >>
    `s n ∪ BIGUNION (IMAGE s (count n)) = BIGUNION (IMAGE s (count n)) ∪ s n` by fs[UNION_COMM] >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`m0`,`m1`,`mnu`,`t`,`BIGUNION (IMAGE s (count n))`,`s n`] assume_tac)
        prod_rect_meas_union_left >> rfs[]
);

val prod_rect_finitely_additive_right = store_thm(
    "prod_rect_finitely_additive_right",
    ``∀m0 m1 mnu n s t. measure_space m0 ∧ measure_space m1 ∧ (∀s. prod_rect_rel m0 m1 s (mnu s)) ∧
        s ∈ measurable_sets m0 ∧ t ∈ (count n -> measurable_sets m1) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (t i) (t j)) ⇒
        (mnu (s × BIGUNION (IMAGE t (count n))) = sum (0,n) (mnu ∘ (λr. s × t r)))``,
    rw[] >> `mnu ∅ = 0` by imp_res_tac RECT_MEASURE_EMPTY >>
    Induct_on `n` >> rw[] >> fs[sum,BIGUNION_IMAGE_COUNT_SUC,FUNSET] >>
    `BIGUNION (IMAGE t (count n)) ∈ measurable_sets m1` by (
        (assume_tac o ISPECL [``m1 : (β -> bool) # ((β -> bool) -> bool) # ((β -> bool) -> real)``,
            ``n : num``,``t : num -> β -> bool``]) MEASURE_SPACE_FINITE_UNION >>
        rfs[FUNSET]) >>
    `t n ∈ measurable_sets m1` by fs[] >>
    `DISJOINT (BIGUNION (IMAGE t (count n))) (t n)` by (fs[DISJOINT_DEF] >> rw[] >>
        qpat_x_assum `∀i j. _` (qspecl_then [`x`,`n`] assume_tac) >> fs[]) >>
    `t n ∪ BIGUNION (IMAGE t (count n)) = BIGUNION (IMAGE t (count n)) ∪ t n` by fs[UNION_COMM] >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`m0`,`m1`,`mnu`,`s`,`BIGUNION (IMAGE t (count n))`,`t n`] assume_tac)
        prod_rect_meas_union_right >> rfs[]
);

val prod_rect_finitely_additive_square = store_thm(
    "prod_rect_finitely_additive_square",
    ``∀m0 m1 mnu m n a b. measure_space m0 ∧ measure_space m1 ∧ (∀s. prod_rect_rel m0 m1 s (mnu s)) ∧
        a ∈ (count m -> measurable_sets m0) ∧ b ∈ (count n -> measurable_sets m1) ∧
        (∀i j. i < m ∧ j < m ∧ i ≠ j ⇒ DISJOINT (a i) (a j)) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
        (mnu (BIGUNION (IMAGE a (count m)) × BIGUNION (IMAGE b (count n))) =
        sum (0,m * n) (mnu ∘ (λij. a (ij MOD m) × b (ij DIV m))))``,
    rw[] >> `mnu ∅ = 0` by imp_res_tac RECT_MEASURE_EMPTY >>
    Induct_on `n` >> rw[] >> fs[sum,FUNSET,BIGUNION_IMAGE_COUNT_SUC] >>
    map_every Q.ABBREV_TAC [`A = BIGUNION (IMAGE a (count m))`,
        `B = BIGUNION (IMAGE b (count n))`,`AxB = (λij. a (ij MOD m) × b (ij DIV m))`] >>
    `mnu (A × (B ∪ b n)) = sum (0,m * n + m) (mnu ∘ AxB)` suffices_by
        fs[UNION_COMM,MULT_CLAUSES] >>
    `A ∈ measurable_sets m0` by (
        (qspecl_then [`m0`,`m`,`a`] assume_tac) MEASURE_SPACE_FINITE_UNION >>
        Q.UNABBREV_TAC `A` >> rfs[FUNSET]) >>
    `B ∈ measurable_sets m1` by (
        (assume_tac o ISPECL [``m1 : (β -> bool) # ((β -> bool) -> bool) # ((β -> bool) -> real)``,
            ``n : num``,``b : num -> β -> bool``]) MEASURE_SPACE_FINITE_UNION >>
        Q.UNABBREV_TAC `B` >> rfs[FUNSET]) >>
    `b n ∈ measurable_sets m1` by fs[] >>
    `DISJOINT B (b n)` by (Q.UNABBREV_TAC `B` >> fs[DISJOINT_DEF] >> rw[] >>
        qpat_x_assum `∀i j. _` (qspecl_then [`x`,`n`] assume_tac) >> fs[]) >>
    (qspecl_then [`m0`,`m1`,`mnu`,`A`,`B`,`b n`] assume_tac) prod_rect_meas_union_right >>
    fs[GSYM SUM_TWO] >> pop_assum kall_tac >>
    (qspecl_then [`mnu ∘ AxB`,`0`,`m * n`,`m`] assume_tac) SUM_REINDEX >> fs[] >>
    map_every Q.UNABBREV_TAC [`A`,`B`,`AxB`] >> pop_assum kall_tac >> fs[] >>
    (qspecl_then [`(λr. mnu (a ((r + m * n) MOD m) × b ((r + m * n) DIV m)))`,
        `(λr. mnu (a r × b n))`,`0`,`m`] assume_tac) SUM_EQ >>
    `(∀r. 0 ≤ r ∧ r < m + 0 ⇒
        ((λr. mnu (a ((r + m * n) MOD m) × b ((r + m * n) DIV m))) r =
        (λr. mnu (a r × b n)) r))` by (rw[] >>
        `(r + m * n) DIV m = n` suffices_by (rw[] >> fs[]) >>
        `0 < m` by (CCONTR_TAC >> fs[]) >> imp_res_tac ADD_DIV_ADD_DIV >> fs[] >>
        pop_assum kall_tac >> fs[LESS_DIV_EQ_ZERO]) >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >>
    (qspecl_then [`m0`,`m1`,`mnu`,`m`,`a`,`b n`] assume_tac) prod_rect_finitely_additive_left >>
    rfs[FUNSET,o_DEF]
);

val prod_rect_finitely_additive_lemma_1 = store_thm(
    "prod_rect_finitely_additive_lemma_1",
    ``∀n b sts0 sts1. b ∈ (count n -> prod_sets sts0 sts1 DIFF {∅}) ∧
        BIGUNION (IMAGE b (count n)) ∈ prod_sets sts0 sts1 ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
        ∃b0 b1. b0 ∈ (count n -> sts0 DIFF {∅}) ∧ b1 ∈ (count n -> sts1 DIFF {∅}) ∧
        (∀i. i < n ⇒ (b i = b0 i × b1 i)) ∧ (BIGUNION (IMAGE b (count n)) =
        BIGUNION (IMAGE b0 (count n)) × BIGUNION (IMAGE b1 (count n)))``,
    rw[] >>
    `∃b0 b1. ∀i. i < n ⇒ b0 i ∈ sts0 ∧ b1 i ∈ sts1 ∧ ((b i) = (b0 i) × (b1 i))` by (fs[GSYM SKOLEM_THM] >>
        rw[] >> Cases_on `i < n` >> fs[] >> fs[FUNSET,prod_sets_def] >>
        qpat_x_assum `∀x. x < n ⇒ _` (qspec_then `i` assume_tac) >> rfs[] >>
        map_every EXISTS_TAC [``s' : α -> bool``,``t' : β -> bool``] >> fs[]) >>
    map_every qexists_tac [`b0`,`b1`] >> rw[]
    >- (fs[FUNSET,prod_sets_def] >> rw[] >>
        last_x_assum (qspec_then `x` assume_tac) >> rfs[] >>
        CCONTR_TAC >> fs[])
    >- (fs[FUNSET,prod_sets_def] >> rw[] >>
        last_x_assum (qspec_then `x` assume_tac) >> rfs[] >>
        CCONTR_TAC >> fs[])
    >- (rw[EXTENSION,IN_BIGUNION_IMAGE] >> eq_tac >> rw[]
        >- (Q.RENAME_TAC [`k < n`] >> qexists_tac `k` >> fs[FUNSET,prod_sets_def] >>
            qpat_x_assum `∀i. _'` (qspec_then `k` assume_tac) >> rfs[] >>
            `x ∈ b0 k × b1 k` by fs[EXTENSION] >> fs[CROSS_DEF])
        >- (Q.RENAME_TAC [`k < n`] >> qexists_tac `k` >> fs[FUNSET,prod_sets_def] >>
            qpat_x_assum `∀i. _'` (qspec_then `k` assume_tac) >> rfs[] >>
            `x ∈ b0 k × b1 k` by fs[EXTENSION] >> fs[CROSS_DEF])
        >- (map_every Q.ABBREV_TAC [`kl = x'`,`kr = x''`] >> NTAC 2 (pop_assum kall_tac) >>
            qpat_x_assum `∀i. _'`
                (fn th => map_every (fn tm => (qspec_then tm assume_tac) th) [`kl`,`kr`]) >>
            rfs[] >> fs[FUNSET,prod_sets_def] >>
            map_every (fn asm => asm by (rw[MEMBER_NOT_EMPTY] >> CCONTR_TAC >> fs[] >> RES_TAC))
                [`∃yl. yl ∈ b1 kl`,`∃yr. yr ∈ b0 kr`] >>
            map_every (fn asm => asm by rw[]) [`(FST x,yl) ∈ b kl`,`(yr,SND x) ∈ b kr`] >>
            `FST x ∈ s` by (fs[EXTENSION,IN_BIGUNION_IMAGE] >>
                qpat_x_assum `∀x'. (∃x. _ ) ⇔ _` (qspec_then `(FST x,yl)` assume_tac) >>
                fs[] >> metis_tac[]) >>
            `SND x ∈ t` by (fs[EXTENSION,IN_BIGUNION_IMAGE] >>
                qpat_x_assum `∀x'. (∃x. _ ) ⇔ _` (qspec_then `(yr,SND x)` assume_tac) >>
                fs[] >> metis_tac[]) >>
            `x ∈ s × t` by rw[CROSS_DEF] >> fs[EXTENSION,IN_BIGUNION_IMAGE]))
);

val prod_rect_finitely_additive_lemma_2 = store_thm(
    "prod_rect_finitely_additive_lemma_2",
    ``∀n b m. measure_space m ∧ b ∈ (count n -> measurable_sets m DIFF {∅}) ⇒
        ∃l c. c ∈ (count l -> measurable_sets m DIFF {∅}) ∧
        (∀i j. i < l ∧ j < l ∧ i ≠ j ⇒ DISJOINT (c i) (c j)) ∧
        b ∈ (count n -> finite_disjoint_unions (IMAGE c (count l))) ∧
        (BIGUNION (IMAGE b (count n)) = BIGUNION (IMAGE c (count l)))``,
    rw[] >>
    (qspecl_then [`n`,`b`,`(m_space m,measurable_sets m)`] assume_tac)
        alg_sets_to_disj_unions_alt >>
    rfs[MEASURE_SPACE_ALGEBRA,subsets_def] >>
    `b ∈ (count n -> measurable_sets m)` by fs[FUNSET] >>
    fs[] >> pop_assum kall_tac >>
    (qspecl_then [`m'`,`c`,`(λx. 0)`] assume_tac) disjoint_set_sum_remove_empty >> rfs[] >>
    map_every qexists_tac [`m''`,`a`] >> rw[]
    >- (rw[FUNSET] >> `∃j. j < m' ∧ (c j = a x)` by (RES_TAC >> fs[]) >>
        pop_assum (assume_tac o GSYM) >> rw[] >> fs[FUNSET])
    >- (fs[FUNSET,finite_disjoint_unions_dir] >> rw[] >>
        qpat_x_assum `∀x. x < n ⇒ _` (qspec_then `x` assume_tac) >> rfs[] >>
        qexists_tac `t DIFF {∅}` >> rw[]
        >- (rw[EXTENSION,IN_BIGUNION] >> eq_tac >> rw[] >>
            qexists_tac `s` >> fs[] >> qexists_tac `x'` >> fs[])
        >- (CCONTR_TAC >> fs[DIFF_SING_EMPTY] >> fs[] >> rw[] >> RES_TAC >> fs[])
        >- (fs[SUBSET_DEF,IN_IMAGE] >> rw[] >>
            qpat_x_assum `∀x. _` (qspec_then `x'` assume_tac) >> rfs[] >> rw[] >>
            `∃z. z ∈ c x''` by fs[MEMBER_NOT_EMPTY] >>
            `∃k. k < m'' ∧ z ∈ a k` by (fs[EXTENSION,IN_BIGUNION_IMAGE] >>
                qpat_x_assum `∀x. (∃x'. _) ⇔ (∃x'. _)` (qspec_then `z` (assume_tac o GSYM)) >>
                rw[] >> qexists_tac `x''` >> fs[]) >>
            qexists_tac `k` >> rw[] >>
            qpat_x_assum `∀i. _ < _ ⇒ _` (qspec_then `k` assume_tac) >> rfs[] >>
            `x'' = j` suffices_by (rw[] >> fs[]) >> CCONTR_TAC >>
            qpat_x_assum `∀i j. _ ⇒ DISJOINT (c i) (c j)` (qspecl_then [`x''`,`j`] assume_tac) >>
            rfs[] >> fs[DISJOINT_DEF,EXTENSION] >>
            pop_assum (qspec_then `z` assume_tac) >> rfs[]))
);

val prod_rect_finitely_additive_lemma_3 = store_thm(
    "prod_rect_finitely_additive_lemma_3",
    ``∀nb nc b c. b ∈ (count nb -> finite_disjoint_unions (IMAGE c (count nc))) ∧
        (∀i j. i < nc ∧ j < nc ∧ i ≠ j ⇒ DISJOINT (c i) (c j)) ⇒
        ∃d nd. ∀k. k < nb ⇒ d k ∈ (count (nd k) -> IMAGE c (count nc)) ∧
        (∀i j. i < nd k ∧ j < nd k ∧ i ≠ j ⇒ DISJOINT (d k i) (d k j)) ∧
        (b k = BIGUNION (IMAGE (d k) (count (nd k))))``,
    rw[GSYM SKOLEM_THM] >> Q.ABBREV_TAC `s = IMAGE c (count nc)` >>
    Cases_on `k < nb` >> fs[FUNSET,finite_disjoint_unions_dir] >>
    last_x_assum (drule_then assume_tac) >> fs[FINITE_BIJ_COUNT_EQ] >>
    Q.RENAME_TAC [`BIJ d (count n) t`] >> map_every qexists_tac [`d`,`n`] >> rw[]
    >- (`d x ∈ t` by fs[BIJ_ALT,FUNSET] >> fs[SUBSET_DEF])
    >- (`d i ∈ t ∧ d j ∈ t` by fs[BIJ_ALT,FUNSET] >>
        qpat_x_assum `∀i j. _` irule >> rw[] >> fs[BIJ_DEF,INJ_DEF] >>
        qpat_x_assum `∀x y. _` (qspecl_then [`i`,`j`] assume_tac) >> rfs[])
    >- (drule_then assume_tac BIJ_IMAGE >> rw[])
);

val prod_rect_finitely_additive_lemma_4 = store_thm(
    "prod_rect_finitely_additive_lemma_4",
    ``∀m0 m1 mnu n b0 b1 nd0 nd1 d0 d1. measure_space m0 ∧ measure_space m1 ∧
        (∀s. prod_rect_rel m0 m1 s (mnu s)) ∧
        (∀k. k < n ⇒ d0 k ∈ (count (nd0 k) -> measurable_sets m0)) ∧
        (∀k. k < n ⇒ d1 k ∈ (count (nd1 k) -> measurable_sets m1)) ∧
        (∀k. k < n ⇒ (b0 k = BIGUNION (IMAGE (d0 k) (count (nd0 k))))) ∧
        (∀k. k < n ⇒ (b1 k = BIGUNION (IMAGE (d1 k) (count (nd1 k))))) ∧
        (∀i j k. k < n ∧ i < nd0 k ∧ j < nd0 k ∧ i ≠ j ⇒ DISJOINT (d0 k i) (d0 k j)) ∧
        (∀i j k. k < n ∧ i < nd1 k ∧ j < nd1 k ∧ i ≠ j ⇒ DISJOINT (d1 k i) (d1 k j)) ⇒
        (sum (0,n) (mnu ∘ (λk. b0 k × b1 k)) =
        sum (0,n) (λk. sum (0,nd0 k * nd1 k)
        (mnu ∘ (λij. (d0 k) (ij MOD (nd0 k)) × (d1 k) (ij DIV (nd0 k))))))``,
    rw[] >> irule SUM_EQ >> rw[] >> irule prod_rect_finitely_additive_square >> rw[] >>
    map_every qexists_tac [`m0`,`m1`] >> rw[]
);

val prod_rect_finitely_additive = store_thm(
    "prod_rect_finitely_additive",
    ``∀m0 m1 mnu. measure_space m0 ∧ measure_space m1 ∧ (∀s. prod_rect_rel m0 m1 s (mnu s)) ⇒
        finitely_additive (m_space m0 × m_space m1,
        prod_sets (measurable_sets m0) (measurable_sets m1),mnu)``,
    rw[finitely_additive_def,measurable_sets_def,measure_def] >>
    `∀n b. b ∈ (count n -> (prod_sets (measurable_sets m0) (measurable_sets m1)) DIFF {∅}) ∧
        BIGUNION (IMAGE b (count n)) ∈ prod_sets (measurable_sets m0) (measurable_sets m1) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
        (mnu (BIGUNION (IMAGE b (count n))) = sum (0,n) (mnu ∘ b))` suffices_by (rw[] >>
        `mnu ∅ = 0` by (drule_all_then assume_tac RECT_MEASURE_EMPTY >> fs[]) >>
        drule_all_then assume_tac disjoint_set_sum_remove_empty >> fs[] >>
        qpat_x_assum `∀n (b : num -> α # β -> bool). _` irule >> rw[] >> fs[] >>
        fs[FUNSET] >> rw[prod_sets_def] >> `∃j. j < n ∧ (b j = a x)` by fs[] >>
        pop_assum (assume_tac o GSYM) >>
        `b j ∈ prod_sets (measurable_sets m0) (measurable_sets m1)` suffices_by fs[prod_sets_def] >>
        RES_TAC) >>
    NTAC 3 (pop_assum kall_tac) >> rw[] >>
    drule_all_then assume_tac prod_rect_finitely_additive_lemma_1 >> fs[] >>
    (qspecl_then [`n`,`b0`,`m0`] assume_tac) prod_rect_finitely_additive_lemma_2 >>
    (qspecl_then [`n`,`b1`,`m1`] assume_tac)
        (INST_TYPE [alpha |-> ``:β``] prod_rect_finitely_additive_lemma_2) >> rfs[] >>
    map_every Q.ABBREV_TAC [`c0 = c'`,`n0 = l'`,`c1 = c`,`n1 = l`] >> NTAC 4 (pop_assum kall_tac) >>
    (qspecl_then [`m0`,`m1`,`mnu`,`n0`,`n1`,`c0`,`c1`] assume_tac)
        prod_rect_finitely_additive_square >> rfs[] >>
    `c0 ∈ (count n0 -> measurable_sets m0)` by fs[FUNSET] >>
    `c1 ∈ (count n1 -> measurable_sets m1)` by fs[FUNSET] >> fs[] >> NTAC 3 (pop_assum kall_tac) >>
    (qspecl_then [`n`,`n0`,`b0`,`c0`] assume_tac) prod_rect_finitely_additive_lemma_3 >>
    rfs[] >> pop_assum (assume_tac o GSYM) >>
    (qspecl_then [`n`,`n1`,`b1`,`c1`] assume_tac)
        (INST_TYPE [alpha |-> ``:β``] prod_rect_finitely_additive_lemma_3) >>
    rfs[] >> pop_assum (assume_tac o GSYM) >>
    map_every Q.ABBREV_TAC [`d0 = d`,`nd0 = nd`,`d1 = d'`,`nd1 = nd'`] >> NTAC 4 (pop_assum kall_tac) >>
    `sum (0,n) (mnu ∘ b) = sum (0,n) (mnu ∘ (λk. b0 k × b1 k))` by (irule SUM_EQ >> rw[]) >>
    `sum (0,n) (mnu ∘ (λk. b0 k × b1 k)) = sum (0,n) (λk. sum (0,nd0 k * nd1 k)
        (mnu ∘ (λij. (d0 k) (ij MOD (nd0 k)) × (d1 k) (ij DIV (nd0 k)))))` by (
        irule prod_rect_finitely_additive_lemma_4 >> rw[] >>
        map_every qexists_tac [`m0`,`m1`] >> rw[FUNSET]
        >- (`d0 k x ∈ IMAGE c0 (count n0)` by fs[FUNSET] >> fs[IN_IMAGE,FUNSET])
        >- (`d1 k x ∈ IMAGE c1 (count n1)` by fs[FUNSET] >> fs[IN_IMAGE,FUNSET])) >>
    rw[] >> NTAC 2 (pop_assum kall_tac) >>
    map_every Q.ABBREV_TAC [`tmpni = (λk. nd0 k * nd1 k)`,
        `tmpg = mnu ∘ (λij. c0 (ij MOD n0) × c1 (ij DIV n0))`,
        `tmpf = (λk ij. (mnu ∘ (λij. d0 k (ij MOD nd0 k) × d1 k (ij DIV nd0 k))) ij)`] >>
    rw[] >> fs[o_DEF] >>
    `sum (0,n) (λk. sum (0,tmpni k) (λij. tmpf k ij)) = sum (0,n0 * n1) tmpg`
        suffices_by (rw[] >> fs[]) >>
    irule SUM_2D_BIJ >> map_every Q.UNABBREV_TAC [`tmpni`,`tmpg`,`tmpf`] >> rw[] >>
    `∃h. BIJ h (count (n0 * n1)) {(i,j) | i < n ∧ j < nd0 i * nd1 i} ∧
        ∀k. k < n0 * n1 ⇒ ((λ(k,ij). d0 k (ij MOD nd0 k) × d1 k (ij DIV nd0 k)) (h k) =
        c0 (k MOD n0) × c1 (k DIV n0))` suffices_by (rw[] >> qexists_tac `h` >> rw[] >>
        qpat_x_assum `∀k. _` (qspec_then `k` assume_tac) >> rfs[] >>
        `∃i j. h k = (i,j)` by (map_every qexists_tac [`FST (h k)`,`SND (h k)`] >> fs[]) >>
        fs[]) >>
    `∃h. ∀k. k < n0 * n1 ⇒ FST (h k) < n ∧ SND (h k) < nd0 (FST (h k)) * nd1 (FST (h k)) ∧
        ((λ(k,ij). d0 k (ij MOD nd0 k) × d1 k (ij DIV nd0 k)) (h k) =
        c0 (k MOD n0) × c1 (k DIV n0))` by (rw[GSYM SKOLEM_THM] >>
        Cases_on `k < n0 * n1` >> rw[] >> drule_then assume_tac LT_PROD_MOD_DIV >> rw[] >>
        `∃nk. nk < n ∧ c0 (k MOD n0) × c1 (k DIV n0) ⊆ b nk` by (
            `∀x y. x ∈ c0 (k MOD n0) ∧ y ∈ c1 (k DIV n0) ⇒ ∃nk. nk < n ∧ (x,y) ∈ b nk` by (rw[] >>
                `(x,y) ∈ BIGUNION (IMAGE b (count n))`
                    suffices_by (rw[] >> qexists_tac `x'` >> fs[]) >>
                fs[EXTENSION] >> rw[GSYM EXTENSION]
                >- (map_every (fn tm => qexists_tac tm >> rw[]) [`c0 (k MOD n0)`,`(k MOD n0)`])
                >- (map_every (fn tm => qexists_tac tm >> rw[]) [`c1 (k DIV n0)`,`(k DIV n0)`])) >>
            `∃x. x ∈ c0 (k MOD n0)` by (fs[FUNSET] >> rw[MEMBER_NOT_EMPTY]) >>
            `∃y. y ∈ c1 (k DIV n0)` by (fs[FUNSET] >> rw[MEMBER_NOT_EMPTY]) >>
            qpat_assum `∀x y. _` (drule_all_then assume_tac) >> fs[] >>
            qexists_tac `nk` >> rw[SUBSET_DEF]
            >- (`b0 nk ∈ finite_disjoint_unions (IMAGE c0 (count n0))` by (rw[] >> fs[FUNSET]) >>
                (qspecl_then [`c0 (k MOD n0)`,`IMAGE c0 (count n0)`,`b0 nk`] assume_tac)
                    subset_or_disjoint_finite_disj_union >> rfs[] >>
                `¬(DISJOINT (c0 (k MOD n0)) (b0 nk))` by (rw[DISJOINT_DEF,GSYM MEMBER_NOT_EMPTY] >>
                    qexists_tac `x` >> rw[]) >> fs[] >> pop_assum kall_tac >>
                `(∀i j. (∃x. (i = c0 x) ∧ x < n0) ∧ (∃x. (j = c0 x) ∧ x < n0) ∧ i ≠ j ⇒
                    DISJOINT i j)` by (rw[] >> qpat_x_assum `∀i j. _` irule >> rw[] >>
                    CCONTR_TAC >> fs[]) >>
                `c0 (k MOD n0) ⊆ b0 nk` by RES_TAC >> fs[SUBSET_DEF])
            >- (`b1 nk ∈ finite_disjoint_unions (IMAGE c1 (count n1))` by (rw[] >> fs[FUNSET]) >>
                (qspecl_then [`c1 (k DIV n0)`,`IMAGE c1 (count n1)`,`b1 nk`] assume_tac)
                    (INST_TYPE [alpha |-> ``:β``] subset_or_disjoint_finite_disj_union) >> rfs[] >>
                `¬(DISJOINT (c1 (k DIV n0)) (b1 nk))` by (rw[DISJOINT_DEF,GSYM MEMBER_NOT_EMPTY] >>
                    qexists_tac `y` >> rw[]) >> fs[] >> pop_assum kall_tac >>
                `(∀i j. (∃x. (i = c1 x) ∧ x < n1) ∧ (∃x. (j = c1 x) ∧ x < n1) ∧ i ≠ j ⇒
                    DISJOINT i j)` by (rw[] >> qpat_x_assum `∀i j. _` irule >> rw[] >>
                    CCONTR_TAC >> fs[]) >>
                `c1 (k DIV n0) ⊆ b1 nk` by RES_TAC >> fs[SUBSET_DEF])) >>
        rfs[] >> `b0 nk = BIGUNION (IMAGE (d0 nk) (count (nd0 nk)))` by fs[] >>
        `b1 nk = BIGUNION (IMAGE (d1 nk) (count (nd1 nk)))` by fs[] >> fs[] >>
        NTAC 2 (pop_assum kall_tac) >>
        `∃x. x ∈ c0 (k MOD n0)` by (fs[FUNSET] >> rw[MEMBER_NOT_EMPTY]) >>
        `∃y. y ∈ c1 (k DIV n0)` by (fs[FUNSET] >> rw[MEMBER_NOT_EMPTY]) >>
        fs[CROSS_SUBSET] >- (rfs[EXTENSION]) >- (rfs[EXTENSION]) >>
        fs[SUBSET_DEF,IN_BIGUNION_IMAGE] >>
        NTAC 2 (qpat_x_assum `∀x. _` (drule_then assume_tac)) >> fs[] >>
        map_every Q.ABBREV_TAC [`i = x''`,`j = x'`] >> NTAC 2 (pop_assum kall_tac) >>
        `d0 nk i = c0 (k MOD n0)` by (`d0 nk i ∈ IMAGE c0 (count n0)` by fs[FUNSET] >>
            fs[] >> `x' = k MOD n0` suffices_by (rw[] >> fs[]) >> CCONTR_TAC >>
            `DISJOINT (c0 x') (c0 (k MOD n0))` by fs[] >> fs[DISJOINT_DEF,EXTENSION] >>
            pop_assum (qspec_then `x` assume_tac) >> fs[] >> fs[]) >>
        `d1 nk j = c1 (k DIV n0)` by (`d1 nk j ∈ IMAGE c1 (count n1)` by fs[FUNSET] >>
            fs[] >> `x' = k DIV n0` suffices_by (rw[] >> fs[]) >> CCONTR_TAC >>
            `DISJOINT (c1 x') (c1 (k DIV n0))` by fs[] >> fs[DISJOINT_DEF,EXTENSION] >>
            pop_assum (qspec_then `y` assume_tac) >> fs[] >> fs[]) >>
        qexists_tac `(nk,j * (nd0 nk) + i)` >> rw[DIV_MULT] >>
        NTAC 26 (last_x_assum kall_tac) >> NTAC 3 (pop_assum kall_tac) >>
        qpat_x_assum `_ ∈ _` kall_tac >>
        `(1 + j) * nd0 nk ≤ nd0 nk * nd1 nk` by fs[] >> simp[RIGHT_ADD_DISTRIB]) >>
    qexists_tac `h` >> rw[BIJ_ALT,EXISTS_UNIQUE_DEF]
    >- (rw[FUNSET] >> RES_TAC >> map_every qexists_tac [`FST (h x)`,`SND (h x)`] >> rw[])
    >- (map_every Q.ABBREV_TAC [`k = i`,`ij = j`] >> NTAC 2 (pop_assum kall_tac) >>
        `0 < nd0 k` by (CCONTR_TAC >> fs[]) >>
        drule_then assume_tac LT_PROD_MOD_DIV >> fs[] >> rw[] >>
        `d0 k (ij MOD nd0 k) ∈ IMAGE c0 (count n0)` by fs[FUNSET] >>
        `d1 k (ij DIV nd0 k) ∈ IMAGE c1 (count n1)` by fs[FUNSET] >>
        fs[] >> Q.RENAME_TAC [`y < n1`] >> `y * n0 + x < n0 * n1` by fs[MOD_DIV_LT_PROD] >>
        qpat_x_assum `∀k. _` (drule_then assume_tac) >> rfs[DIV_MULT] >>
        `∃h0 h1. h (x + n0 * y) = (h0,h1)` by fs[ABS_PAIR_THM] >> fs[] >>
        `c0 x × c1 y ≠ ∅` by fs[CROSS_EMPTY_EQN,FUNSET] >>
        drule_all_then assume_tac CROSS_EQ >> fs[CROSS_EMPTY_EQN] >>
        qexists_tac `x + n0 * y` >> Cases_on `k = h0` >> rw[]
        >- (drule_then assume_tac LT_PROD_MOD_DIV >> fs[] >> rw[] >>
            NTAC 2 (qpat_x_assum `∀k. _` (drule_then assume_tac)) >> fs[] >> rw[] >>
            qpat_x_assum `∀i j. _` (qspecl_then [`ij MOD nd0 h0`,`h1 MOD nd0 h0`] assume_tac) >>
            qpat_x_assum `∀i j. _` (qspecl_then [`ij DIV nd0 h0`,`h1 DIV nd0 h0`] assume_tac) >>
            rfs[] >> `0 < nd0 h0` by (CCONTR_TAC >> fs[]) >>
            drule_then assume_tac (GSYM DIV_MOD_EQ) >>
            pop_assum (qspecl_then [`ij`,`h1`] assume_tac) >> rfs[])
        >- (drule_then assume_tac LT_PROD_MOD_DIV >> fs[] >> rw[] >>
            `d0 k (ij MOD nd0 k) ⊆ b0 k` by (
                NTAC 5 (qpat_x_assum `_ = _` kall_tac) >> rw[SUBSET_DEF] >>
                `BIGUNION (IMAGE (d0 k) (count (nd0 k))) = b0 k` by fs[] >>
                fs[EXTENSION] >> pop_assum (qspec_then `x'` assume_tac) >> fs[GSYM EXTENSION] >>
                `(∃s. x' ∈ s ∧ ∃x. (s = d0 k x) ∧ x < nd0 k)` suffices_by (rw[] >> fs[]) >>
                map_every (fn tm => qexists_tac tm >> rw[])
                    [`d0 k (ij MOD nd0 k)`,`ij MOD nd0 k`]) >>
            `d0 h0 (h1 MOD nd0 h0) ⊆ b0 h0` by (
                NTAC 5 (qpat_x_assum `_ = _` kall_tac) >> rw[SUBSET_DEF] >>
                `BIGUNION (IMAGE (d0 h0) (count (nd0 h0))) = b0 h0` by fs[] >>
                fs[EXTENSION] >> pop_assum (qspec_then `x'` assume_tac) >> fs[GSYM EXTENSION] >>
                `(∃s. x' ∈ s ∧ ∃x. (s = d0 h0 x) ∧ x < nd0 h0)` suffices_by (rw[] >> fs[]) >>
                map_every (fn tm => qexists_tac tm >> rw[])
                    [`d0 h0 (h1 MOD nd0 h0)`,`h1 MOD nd0 h0`]) >>
            `d1 k (ij DIV nd0 k) ⊆ b1 k` by (
                NTAC 5 (qpat_x_assum `_ = _` kall_tac) >> rw[SUBSET_DEF] >>
                `BIGUNION (IMAGE (d1 k) (count (nd1 k))) = b1 k` by fs[] >>
                fs[EXTENSION] >> pop_assum (qspec_then `x'` assume_tac) >> fs[GSYM EXTENSION] >>
                `(∃s. x' ∈ s ∧ ∃x. (s = d1 k x) ∧ x < nd1 k)` suffices_by (rw[] >> fs[]) >>
                map_every (fn tm => qexists_tac tm >> rw[])
                    [`d1 k (ij DIV nd0 k)`,`ij DIV nd0 k`]) >>
            `d1 h0 (h1 DIV nd0 h0) ⊆ b1 h0` by (
                NTAC 5 (qpat_x_assum `_ = _` kall_tac) >> rw[SUBSET_DEF] >>
                `BIGUNION (IMAGE (d1 h0) (count (nd1 h0))) = b1 h0` by fs[] >>
                fs[EXTENSION] >> pop_assum (qspec_then `x'` assume_tac) >> fs[GSYM EXTENSION] >>
                `(∃s. x' ∈ s ∧ ∃x. (s = d1 h0 x) ∧ x < nd1 h0)` suffices_by (rw[] >> fs[]) >>
                map_every (fn tm => qexists_tac tm >> rw[])
                    [`d1 h0 (h1 DIV nd0 h0)`,`h1 DIV nd0 h0`]) >>
            rfs[] >> `DISJOINT (b0 k × b1 k) (b0 h0 × b1 h0)` by fs[] >>
            NTAC 20 (last_x_assum kall_tac) >> fs[DISJOINT_DEF] >>
            `b0 k × b1 k ∩ (b0 h0 × b1 h0) ≠ ∅` suffices_by (rw[] >> fs[]) >>
            fs[GSYM MEMBER_NOT_EMPTY,SUBSET_DEF] >> qexists_tac `(x',x'')` >> RES_TAC >> rw[]))
    >- (map_every Q.ABBREV_TAC [`k = i`,`ij = j`] >> NTAC 2 (pop_assum kall_tac) >>
        map_every Q.ABBREV_TAC [`i = x`,`j = y'`] >> NTAC 2 (pop_assum kall_tac) >>
        qpat_x_assum `_ = _` (assume_tac o GSYM) >> rfs[] >>
        qpat_x_assum `∀k. _` (fn th => map_every (fn tm => (qspec_then tm assume_tac) th) [`i`,`j`]) >>
        rfs[] >> imp_res_tac LT_PROD_MOD_DIV >>
        `c0 (j MOD n0) × c1 (j DIV n0) ≠ ∅` by fs[CROSS_EMPTY_EQN,FUNSET] >>
        drule_all_then assume_tac CROSS_EQ >> fs[CROSS_EMPTY_EQN] >> rw[] >>
        qpat_x_assum `∀i j. _` (qspecl_then [`i DIV n0`,`j DIV n0`] assume_tac) >>
        qpat_x_assum `∀i j. _` (qspecl_then [`i MOD n0`,`j MOD n0`] assume_tac) >>
        rfs[] >> `0 < n0` by (CCONTR_TAC >> fs[]) >> imp_res_tac DIV_MOD_EQ)
);

val prod_measure_space_rect_measure_space = store_thm(
    "prod_measure_space_rect_measure_space",
    ``∀m0 m1 mnu. measure_space m0 ∧ measure_space m1 ⇒
        measure_space (prod_measure_space_rect m0 m1)``,
    rw[prod_measure_rect_def,prod_measure_space_rect_def] >>
    last_assum assume_tac >> dxrule_then assume_tac prod_rect_meas_replace >>
    pop_assum (drule_then assume_tac) >> fs[] >> Q.ABBREV_TAC `mnu = prod_rect_meas m0 m1` >>
    pop_assum kall_tac >>
    Q.ABBREV_TAC
        `m = (m_space m0 × m_space m1,prod_sets (measurable_sets m0) (measurable_sets m1),mnu)` >>
    (assume_tac o ISPEC ``m :
        (α # β -> bool) # ((α # β -> bool) -> bool) # ((α # β -> bool) -> real)``)
        MEASURE_SPACE_FROM_SEMI_ALGEBRA >>
    Q.UNABBREV_TAC `m` >> fs[m_space_def,measurable_sets_def] >>
    pop_assum irule >> rw[]
    >- (fs[prod_rect_finitely_additive])
    >- (fs[prod_rect_positive])
    >- (fs[prod_sets_semi_alg])
);

val _ = export_theory();