open HolKernel Parse boolLib bossLib;
open pred_setTheory;
open c487306_measureTheory;
open trivialTheory;

val _ = new_theory "finite";

val finite_unions_def = Define `finite_unions a =
    {s | ∃t. (t ≠ ∅) ∧ t ⊆ a ∧ FINITE t ∧ (BIGUNION t = s)}`;

val finite_inters_def = Define `finite_inters a =
    {s | ∃t. (t ≠ ∅) ∧ t ⊆ a ∧ FINITE t ∧ (BIGINTER t = s)}`;

val finite_disjoint_unions_def = Define `finite_disjoint_unions a =
    {s | ∃t. (t ≠ ∅) ∧ t ⊆ a ∧ FINITE t ∧ (BIGUNION t = s) ∧
    ∀i j. i ∈ t ∧ j ∈ t ∧ i ≠ j ⇒ DISJOINT i j}`;

val finite_unions_alt = store_thm(
    "finite_unions_alt",
    ``∀a. finite_unions a =
        {s | ∃b n. 0 < n ∧ b ∈ ((count n) -> a) ∧ (BIGUNION (IMAGE b (count n)) = s)}``,
    fs[finite_unions_def] >> rpt strip_tac >>
    `∀s. (∃t. t ≠ ∅ ∧ t ⊆ a ∧ FINITE t ∧ (BIGUNION t = s)) ⇔
        (∃b n. 0 < n ∧ b ∈ (count n -> a) ∧ (BIGUNION (IMAGE b (count n)) = s))`
        suffices_by (rpt strip_tac >> fs[EXTENSION]) >>
    strip_tac >> eq_tac >> rpt strip_tac
    >- (fs[FINITE_BIJ_COUNT_EQ] >>
        map_every EXISTS_TAC [``c : num -> α -> bool``,``n : num``] >>
        rpt strip_tac >> fs[]
        >- (CCONTR_TAC >> fs[])
        >- (fs[FUNSET,SUBSET_DEF,BIJ_ALT])
        >- (`∀x. x ∈ BIGUNION (IMAGE c (count n)) ⇔ x ∈ s` suffices_by fs[EXTENSION] >>
            fs[IN_BIGUNION_IMAGE] >> strip_tac >> eq_tac >> rpt strip_tac >>
            fs[BIJ_ALT,BIGUNION,FUNSET,SUBSET_DEF,EXTENSION] >> metis_tac[]))
    >- (EXISTS_TAC ``IMAGE (b:num->α->bool) (count n)`` >> fs[] >> rw[]
        >- (CCONTR_TAC >> fs[count_def,EXTENSION])
        >- (fs[SUBSET_DEF,FUNSET,IMAGE_DEF] >> rw[] >> fs[]))
);

val finite_disjoint_unions_dir = store_thm(
    "finite_disjoint_unions_dir",
    ``∀a. finite_disjoint_unions a =
        {BIGUNION t | (t ≠ ∅) ∧ t ⊆ a ∧ FINITE t ∧
        ∀i j. i ∈ t ∧ j ∈ t ∧ i ≠ j ⇒ DISJOINT i j}``,
    rw[finite_disjoint_unions_def,EXTENSION] >> eq_tac >> rw[] >>
    EXISTS_TAC ``t : (α -> bool) -> bool`` >> rw[] >>
    EXISTS_TAC ``x' : α -> bool`` >> rw[]
);

val finite_disjoint_unions_alt = store_thm(
    "finite_disjoint_unions_alt",
    ``∀a. finite_disjoint_unions a =
        {s | ∃b n. 0 < n ∧ b ∈ ((count n) -> a) ∧ (BIGUNION (IMAGE b (count n)) = s) ∧
        ∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)}``,
    fs[finite_disjoint_unions_def] >> rpt strip_tac >>
    `∀s. (∃t. t ≠ ∅ ∧ t ⊆ a ∧ FINITE t ∧ (BIGUNION t = s) ∧
        ∀i j. i ∈ t ∧ j ∈ t ∧ i ≠ j ⇒ DISJOINT i j) ⇔
        ∃b n. 0 < n ∧ b ∈ (count n -> a) ∧ (BIGUNION (IMAGE b (count n)) = s) ∧
        ∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)`
        suffices_by (rpt strip_tac >> fs[EXTENSION]) >>
    strip_tac >> eq_tac >> rpt strip_tac
    >- (fs[FINITE_BIJ_COUNT_EQ] >>
        map_every EXISTS_TAC [``c : num -> α -> bool``,``n : num``] >>
        rpt strip_tac >> fs[]
        >- (CCONTR_TAC >> fs[])
        >- (fs[FUNSET,SUBSET_DEF,BIJ_ALT])
        >- (`∀x. x ∈ BIGUNION (IMAGE c (count n)) ⇔ x ∈ s` suffices_by fs[EXTENSION] >>
            fs[IN_BIGUNION_IMAGE] >> strip_tac >> eq_tac >> rpt strip_tac >>
            fs[BIJ_ALT,BIGUNION,FUNSET,SUBSET_DEF,EXTENSION] >> metis_tac[])
        >- (fs[BIJ_DEF,INJ_DEF] >> RES_TAC >> metis_tac[]))
    >- (EXISTS_TAC ``IMAGE (b:num->α->bool) (count n)`` >> fs[] >> rw[]
        >- (CCONTR_TAC >> fs[count_def,EXTENSION])
        >- (fs[SUBSET_DEF,FUNSET,IMAGE_DEF] >> rw[] >> fs[])
        >- (Cases_on `x = x'` >> fs[]))
);

val finite_disjoint_unions_alt_dir = store_thm(
    "finite_disjoint_unions_alt_dir",
    ``∀a. finite_disjoint_unions a = {BIGUNION (IMAGE b (count n)) |
        0 < n ∧ b ∈ (count n -> a) ∧
        ∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)}``,
    rpt strip_tac >> fs[finite_disjoint_unions_alt] >> rw[EXTENSION] >> eq_tac >> rw[] >>
    map_every EXISTS_TAC [``b:num->α->bool``,``n:num``] >> fs[]
);

val finite_inters_alt = store_thm(
    "finite_inters_alt",
    ``∀a. finite_inters a =
        {s | ∃b n. 0 < n ∧ b ∈ ((count n) -> a) ∧ (BIGINTER (IMAGE b (count n)) = s)}``,
    fs[finite_inters_def] >> rpt strip_tac >>
    `∀s. (∃t. t ≠ ∅ ∧ t ⊆ a ∧ FINITE t ∧ (BIGINTER t = s)) ⇔
        (∃b n. 0 < n ∧ b ∈ (count n -> a) ∧ (BIGINTER (IMAGE b (count n)) = s))`
        suffices_by (rpt strip_tac >> fs[EXTENSION]) >>
    strip_tac >> eq_tac >> rpt strip_tac
    >- (fs[FINITE_BIJ_COUNT_EQ] >>
        map_every EXISTS_TAC [``c : num -> α -> bool``,``n : num``] >>
        rpt strip_tac >> fs[]
        >- (CCONTR_TAC >> fs[])
        >- (fs[FUNSET,SUBSET_DEF,BIJ_ALT])
        >- (`∀x. x ∈ BIGINTER (IMAGE c (count n)) ⇔ x ∈ s` suffices_by fs[EXTENSION] >>
            fs[IN_BIGINTER_IMAGE] >> strip_tac >> eq_tac >> rpt strip_tac >>
            fs[BIJ_ALT,BIGINTER,FUNSET,SUBSET_DEF,EXTENSION] >> metis_tac[]))
    >- (EXISTS_TAC ``IMAGE (b:num->α->bool) (count n)`` >> fs[] >> rw[]
        >- (CCONTR_TAC >> fs[count_def,EXTENSION])
        >- (fs[SUBSET_DEF,FUNSET,IMAGE_DEF] >> rw[] >> fs[]))
);

val subset_or_disjoint_finite_disj_union = store_thm(
    "subset_or_disjoint_finite_disj_union",
    ``∀r s t. r ∈ s ∧ t ∈ finite_disjoint_unions s ∧
        (∀i j. i ∈ s ∧ j ∈ s ∧ i ≠ j ⇒ DISJOINT i j) ⇒ r ⊆ t ∨ DISJOINT r t``,
    rw[] >> CCONTR_TAC >> fs[SUBSET_DEF,DISJOINT_DEF,INTER_DEF,GSYM MEMBER_NOT_EMPTY] >>
    Q.RENAME_TAC [`y ∈ t`] >> fs[finite_disjoint_unions_dir] >>
    Q.RENAME_TAC [`ss ⊆ s`] >> Cases_on `r ∈ ss`
    >- (`x ∈ BIGUNION ss` by (fs[BIGUNION] >> qexists_tac `r` >> fs[]) >>
        fs[EXTENSION] >> metis_tac[])
    >- (`y ∈ BIGUNION ss` by rw[] >> fs[BIGUNION] >> Q.RENAME_TAC [`ys ∈ ss`] >>
        `ys ∈ s` by fs[SUBSET_DEF] >>
        qpat_x_assum `∀i j. _` (qspecl_then [`r`,`ys`] assume_tac) >> rfs[] >>
        `{x | x ∈ r ∧ x ∈ ys} ≠ ∅` by (rw[GSYM MEMBER_NOT_EMPTY] >>
            qexists_tac `y` >> rw[]) >> fs[])
);

val sets_subset_finite_unions = store_thm(
    "sets_subset_finite_unions",
    ``∀s. s ⊆ finite_unions s``,
    fs[SUBSET_DEF,finite_unions_alt] >> rpt strip_tac >>
    map_every EXISTS_TAC [``λi:num. x:α->bool``,``1 : num``] >>
    fs[BIGUNION_IMAGE_COUNT_ONE] >> fs[FUNSET]
);

val sets_subset_finite_inters = store_thm(
    "sets_subset_finite_inters",
    ``∀s. s ⊆ finite_inters s``,
    fs[SUBSET_DEF,finite_inters_alt] >> rpt strip_tac >>
    map_every EXISTS_TAC [``λi:num. x:α->bool``,``1 : num``] >>
    fs[BIGINTER_IMAGE_COUNT_ONE] >> fs[FUNSET]
);

val subset_imp_finite_unions_subset = store_thm(
    "subset_imp_finite_unions_subset",
    ``∀s t. s ⊆ t ⇒ finite_unions s ⊆ finite_unions t``,
    rpt strip_tac >> fs[SUBSET_DEF,finite_unions_def] >> rpt strip_tac >>
    metis_tac[]
);

val subset_imp_finite_inters_subset = store_thm(
    "subset_imp_finite_inters_subset",
    ``∀s t. s ⊆ t ⇒ finite_inters s ⊆ finite_inters t``,
    rpt strip_tac >> fs[SUBSET_DEF,finite_inters_def] >> rpt strip_tac >>
    metis_tac[]
);

val union_in_finite_unions = store_thm(
    "union_in_finite_unions",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ s ⇒ s0 ∪ s1 ∈ finite_unions s``,
    rpt strip_tac >> fs[finite_unions_alt] >>
    map_every EXISTS_TAC [``λx:num. if (x=0) then s0:α->bool else s1``,``2:num``] >>
    fs[] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x` >> fs[])
    >- (`∀x. x ∈ BIGUNION (IMAGE (λx. if x = 0 then s0 else s1) (count 2)) ⇔ x ∈ s0 ∪ s1`
            suffices_by fs[EXTENSION] >>
        fs[IN_BIGINTER_IMAGE] >> strip_tac >> eq_tac >> rw[]
        >- (Cases_on `x' = 0` >> fs[])
        >- (EXISTS_TAC ``s0: α -> bool`` >> fs[] >>
            EXISTS_TAC ``0: num`` >> fs[])
        >- (EXISTS_TAC ``s1: α -> bool`` >> fs[] >>
            EXISTS_TAC ``1: num`` >> fs[]))
);

val inter_in_finite_inters = store_thm(
    "inter_in_finite_inters",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ s ⇒ s0 ∩ s1 ∈ finite_inters s``,
    rpt strip_tac >> fs[finite_inters_alt] >>
    map_every EXISTS_TAC [``λx:num. if (x=0) then s0:α->bool else s1``,``2:num``] >>
    fs[] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x` >> fs[])
    >- (`∀x. x ∈ BIGINTER (IMAGE (λx. if x = 0 then s0 else s1) (count 2)) ⇔ x ∈ s0 ∩ s1`
            suffices_by fs[EXTENSION] >>
        fs[IN_BIGINTER_IMAGE] >> strip_tac >> eq_tac >> rw[]
        >- (pop_assum (qspec_then `0` assume_tac) >> fs[])
        >- (pop_assum (qspec_then `1` assume_tac) >> fs[])
        >- (Cases_on `x' = 0` >> fs[]))
);

val finite_inter_inter_finite_inter = store_thm(
    "finite_inter_inter_finite_inter",
    ``∀s s0 s1. s0 ∈ finite_inters s ∧ s1 ∈ finite_inters s ⇒
        s0 ∩ s1 ∈ finite_inters s``,
    rpt strip_tac >> fs[finite_inters_alt] >>
    map_every EXISTS_TAC
        [``(λx. if x < n then b x else b' (x - n)) : num -> α -> bool``,
        ``n + n': num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGINTER_IMAGE_COUNT_INTER])
);

val finite_union_union_finite_union = store_thm(
    "finite_union_union_finite_union",
    ``∀s s0 s1. s0 ∈ finite_unions s ∧ s1 ∈ finite_unions s ⇒
        s0 ∪ s1 ∈ finite_unions s``,
    rpt strip_tac >> fs[finite_unions_alt] >>
    map_every EXISTS_TAC
        [``(λx. if x < n then b x else b' (x - n)) : num -> α -> bool``,
        ``n + n': num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGUNION_IMAGE_COUNT_UNION])
);

val set_union_finite_inter = store_thm(
    "set_union_finite_inter",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_inters s ⇒
        s0 ∪ s1 ∈ finite_inters (finite_unions s)``,
    rpt strip_tac >> fs[finite_inters_alt] >>
    map_every EXISTS_TAC [``λx:num. s0 ∪ b x``,``n:num``] >> rw[]
    >- (fs[FUNSET,union_in_finite_unions])
    >- (fs[UNION_BIGINTER_IMAGE])
);

val set_inter_finite_inter = store_thm(
    "set_inter_finite_inter",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_inters s ⇒
        s0 ∩ s1 ∈ finite_inters s``,
    rpt strip_tac >> fs[finite_inters_alt] >>
    map_every EXISTS_TAC
        [``(λx:num. if x < n then b x else s0):num -> α -> bool``,``SUC n:num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGINTER_IMAGE_COUNT_SUC] >>
        `IMAGE (λx. if x < n then b x else s0) (count n) = IMAGE b (count n)`
            suffices_by fs[] >>
        fs[IMAGE_DEF,EXTENSION] >> strip_tac >> eq_tac >> rw[] >> fs[] >>
        EXISTS_TAC ``x':num`` >> fs[])
);

val set_union_finite_union = store_thm(
    "set_union_finite_union",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_unions s ⇒
        s0 ∪ s1 ∈ finite_unions s``,
    rpt strip_tac >> fs[finite_unions_alt] >>
    map_every EXISTS_TAC
        [``(λx:num. if x < n then b x else s0):num -> α -> bool``,``SUC n:num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGUNION_IMAGE_COUNT_SUC] >>
        `IMAGE (λx. if x < n then b x else s0) (count n) = IMAGE b (count n)`
            suffices_by fs[] >>
        fs[IMAGE_DEF,EXTENSION] >> strip_tac >> eq_tac >> rw[] >> fs[] >>
        EXISTS_TAC ``x':num`` >> fs[])
);

val set_inter_finite_union = store_thm(
    "set_inter_finite_union",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_unions s ⇒
        s0 ∩ s1 ∈ finite_unions (finite_inters s)``,
    rpt strip_tac >> fs[finite_unions_alt] >>
    map_every EXISTS_TAC [``λx:num. s0 ∩ b x``,``n:num``] >> rw[]
    >- (fs[FUNSET,inter_in_finite_inters])
    >- (fs[INTER_BIGUNION_IMAGE])
);

val finite_union_union_finite_inter_of_finite_union = store_thm(
    "finite_union_union_finite_inter_of_finite_union",
    ``∀s s0 s1. s0 ∈ (finite_unions s) ∧ s1 ∈ finite_inters (finite_unions s) ⇒
        s0 ∪ s1 ∈ finite_inters (finite_unions s)``,
    rpt strip_tac >> fs[finite_inters_alt] >>
    map_every EXISTS_TAC [``λx:num. s0 ∪ b x``,``n:num``] >> rw[]
    >- (fs[FUNSET,finite_union_union_finite_union])
    >- (fs[UNION_BIGINTER_IMAGE])
);

val finite_union_inter_finite_inter_of_finite_union = store_thm(
    "finite_union_inter_finite_inter_of_finite_union",
    ``∀s s0 s1. s0 ∈ (finite_unions s) ∧ s1 ∈ finite_inters (finite_unions s) ⇒
        s0 ∩ s1 ∈ finite_inters (finite_unions s)``,
    rpt strip_tac >> fs[finite_inters_alt] >>
    map_every EXISTS_TAC
        [``(λx:num. if x < n then b x else s0):num -> α -> bool``,``SUC n:num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGINTER_IMAGE_COUNT_SUC] >>
        `IMAGE (λx. if x < n then b x else s0) (count n) = IMAGE b (count n)`
            suffices_by fs[] >>
        fs[IMAGE_DEF,EXTENSION] >> strip_tac >> eq_tac >> rw[] >> fs[] >>
        EXISTS_TAC ``x':num`` >> fs[])
);

val finite_inter_union_finite_union_of_finite_inter = store_thm(
    "finite_inter_union_finite_union_of_finite_inter",
    ``∀s s0 s1. s0 ∈ (finite_inters s) ∧ s1 ∈ finite_unions (finite_inters s) ⇒
        s0 ∪ s1 ∈ finite_unions (finite_inters s)``,
    rpt strip_tac >> fs[finite_unions_alt] >>
    map_every EXISTS_TAC
        [``(λx:num. if x < n then b x else s0):num -> α -> bool``,``SUC n:num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGUNION_IMAGE_COUNT_SUC] >>
        `IMAGE (λx. if x < n then b x else s0) (count n) = IMAGE b (count n)`
            suffices_by fs[] >>
        fs[IMAGE_DEF,EXTENSION] >> strip_tac >> eq_tac >> rw[] >> fs[] >>
        EXISTS_TAC ``x':num`` >> fs[])
);

val finite_inter_inter_finite_union_of_finite_inter = store_thm(
    "finite_inter_inter_finite_union_of_finite_inter",
    ``∀s s0 s1. s0 ∈ (finite_inters s) ∧ s1 ∈ finite_unions (finite_inters s) ⇒
        s0 ∩ s1 ∈ finite_unions (finite_inters s)``,
    rpt strip_tac >> fs[finite_unions_alt] >>
    map_every EXISTS_TAC [``λx:num. s0 ∩ b x``,``n:num``] >> rw[]
    >- (fs[FUNSET,finite_inter_inter_finite_inter])
    >- (fs[INTER_BIGUNION_IMAGE])
);

val set_union_finite_inter_of_finite_union = store_thm(
    "set_union_finite_inter_of_finite_union",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_inters (finite_unions s) ⇒
        s0 ∪ s1 ∈ finite_inters (finite_unions s)``,
    rpt strip_tac >> `s0 ∈ finite_unions s` by metis_tac[sets_subset_finite_unions,SUBSET_DEF] >>
    fs[finite_union_union_finite_inter_of_finite_union]
);

val set_inter_finite_inter_of_finite_union = store_thm(
    "set_inter_finite_inter_of_finite_union",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_inters (finite_unions s) ⇒
        s0 ∩ s1 ∈ finite_inters (finite_unions s)``,
    rpt strip_tac >> `s0 ∈ finite_unions s` by metis_tac[sets_subset_finite_unions,SUBSET_DEF] >>
    fs[finite_union_inter_finite_inter_of_finite_union]
);

val set_union_finite_union_of_finite_inter = store_thm(
    "set_union_finite_union_of_finite_inter",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_unions (finite_inters s) ⇒
        s0 ∪ s1 ∈ finite_unions (finite_inters s)``,
    rpt strip_tac >> `s0 ∈ finite_inters s` by metis_tac[sets_subset_finite_inters,SUBSET_DEF] >>
    fs[finite_inter_union_finite_union_of_finite_inter]
);

val set_inter_finite_union_of_finite_inter = store_thm(
    "set_inter_finite_union_of_finite_inter",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_unions (finite_inters s) ⇒
        s0 ∩ s1 ∈ finite_unions (finite_inters s)``,
    rpt strip_tac >> `s0 ∈ finite_inters s` by metis_tac[sets_subset_finite_inters,SUBSET_DEF] >>
    fs[finite_inter_inter_finite_union_of_finite_inter]
);

val composition_finite_unions = store_thm(
    "composition_finite_unions",
    ``∀s. finite_unions (finite_unions s) = finite_unions s``,
    strip_tac >> fs[EXTENSION] >> strip_tac >> eq_tac >> rw[]
    >- (`∃b n. 0 < n ∧ b ∈ (count n -> finite_unions s) ∧ (BIGUNION (IMAGE b (count n)) = x)`
            by (fs[finite_unions_alt] >> metis_tac[]) >>
        `∀n b. 0 < n ∧ b ∈ (count n -> finite_unions s) ⇒
            BIGUNION (IMAGE b (count n)) ∈ finite_unions s`
            suffices_by (strip_tac >> pop_assum imp_res_tac >> rfs[]) >>
        rpt (pop_assum kall_tac) >> strip_tac >> Induct_on `n` >> rw[] >>
        last_x_assum (qspec_then `b` assume_tac) >> Cases_on `n` >> fs[]
        >- (fs[BIGUNION_IMAGE_COUNT_ONE] >> fs[count_def,FUNSET])
        >- (Q.RENAME_TAC [`BIGUNION (IMAGE b (count (SUC n)))`] >>
            fs[BIGUNION_IMAGE_COUNT_SUC] >>
            `BIGUNION (IMAGE b (count n)) ∈ finite_unions s` by rfs[count_def,FUNSET] >>
            `b n ∈ finite_unions s` by fs[count_def,FUNSET] >>
            fs[finite_union_union_finite_union]))
    >- ((qspec_then `finite_unions s` assume_tac) sets_subset_finite_unions >>
        fs[SUBSET_DEF])
);

val composition_finite_inters = store_thm(
    "composition_finite_inters",
    ``∀s. finite_inters (finite_inters s) = finite_inters s``,
    strip_tac >> fs[EXTENSION] >> strip_tac >> eq_tac >> rw[]
    >- (`∃b n. 0 < n ∧ b ∈ (count n -> finite_inters s) ∧ (BIGINTER (IMAGE b (count n)) = x)`
            by (fs[finite_inters_alt] >> metis_tac[]) >>
        `∀n b. 0 < n ∧ b ∈ (count n -> finite_inters s) ⇒
            BIGINTER (IMAGE b (count n)) ∈ finite_inters s`
            suffices_by (strip_tac >> pop_assum imp_res_tac >> rfs[]) >>
        rpt (pop_assum kall_tac) >> strip_tac >> Induct_on `n` >> rw[] >>
        last_x_assum (qspec_then `b` assume_tac) >> Cases_on `n` >> fs[]
        >- (fs[BIGINTER_IMAGE_COUNT_ONE] >> fs[count_def,FUNSET])
        >- (Q.RENAME_TAC [`BIGINTER (IMAGE b (count (SUC n)))`] >>
            fs[BIGINTER_IMAGE_COUNT_SUC] >>
            `BIGINTER (IMAGE b (count n)) ∈ finite_inters s` by rfs[count_def,FUNSET] >>
            `b n ∈ finite_inters s` by fs[count_def,FUNSET] >>
            fs[finite_inter_inter_finite_inter]))
    >- ((qspec_then `finite_inters s` assume_tac) sets_subset_finite_inters >>
        fs[SUBSET_DEF])
);

val finite_union_inter_finite_union = store_thm(
    "finite_union_inter_finite_union",
    ``∀s s0 s1. s0 ∈ finite_unions s ∧ s1 ∈ finite_unions s ⇒
        s0 ∩ s1 ∈ finite_unions (finite_inters s)``,
    rpt strip_tac >>
    `∀n b. 0 < n ∧ b ∈ (count n -> s) ⇒
        BIGUNION (IMAGE b (count n)) ∩ s1 ∈ finite_unions (finite_inters s)`
        suffices_by (rpt strip_tac >> rfs[finite_unions_alt] >>
        RES_TAC >> rfs[] >> metis_tac[]) >>
    last_x_assum kall_tac >> strip_tac >>
    Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >> Cases_on `n`
    >- (fs[BIGUNION_IMAGE_COUNT_ONE] >> rw[] >>
        `b 0 ∈ s` by fs[count_def,FUNSET] >>
        (qspec_then `s` assume_tac) sets_subset_finite_inters >>
        `b 0 ∈ finite_inters s` by fs[SUBSET_DEF] >>
        imp_res_tac subset_imp_finite_unions_subset >>
        fs[SUBSET_DEF,finite_inter_inter_finite_union_of_finite_inter])
    >- (fs[] >> Q.ABBREV_TAC `n = SUC n'` >> pop_assum kall_tac >>
        fs[BIGUNION_IMAGE_COUNT_SUC] >> fs[INTER_COMM,UNION_OVER_INTER] >>
        qpat_x_assum `∀b. _` (qspec_then `b` assume_tac) >> rfs[count_def,FUNSET] >>
        `s1 ∩ b n ∈ finite_unions (finite_inters s)` suffices_by (strip_tac >>
            fs[finite_union_union_finite_union]) >>
        pop_assum kall_tac >> pop_assum (qspec_then `n` assume_tac) >> fs[] >>
        imp_res_tac set_inter_finite_union >> fs[INTER_COMM])
);

val finite_inter_union_finite_inter = store_thm(
    "finite_inter_union_finite_inter",
    ``∀s s0 s1. s0 ∈ finite_inters s ∧ s1 ∈ finite_inters s ⇒
        s0 ∪ s1 ∈ finite_inters (finite_unions s)``,
    rpt strip_tac >>
    `∀n b. 0 < n ∧ b ∈ (count n -> s) ⇒
        BIGINTER (IMAGE b (count n)) ∪ s1 ∈ finite_inters (finite_unions s)`
        suffices_by (rpt strip_tac >> rfs[finite_inters_alt] >>
        RES_TAC >> rfs[] >> metis_tac[]) >>
    last_x_assum kall_tac >> strip_tac >>
    Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >> Cases_on `n`
    >- (fs[BIGINTER_IMAGE_COUNT_ONE] >> rw[] >>
        `b 0 ∈ s` by fs[count_def,FUNSET] >>
        (qspec_then `s` assume_tac) sets_subset_finite_unions >>
        `b 0 ∈ finite_unions s` by fs[SUBSET_DEF] >>
        imp_res_tac subset_imp_finite_inters_subset >>
        fs[SUBSET_DEF,finite_union_union_finite_inter_of_finite_union])
    >- (fs[] >> Q.ABBREV_TAC `n = SUC n'` >> pop_assum kall_tac >>
        fs[BIGINTER_IMAGE_COUNT_SUC] >> fs[UNION_COMM,INTER_OVER_UNION] >>
        qpat_x_assum `∀b. _` (qspec_then `b` assume_tac) >> rfs[count_def,FUNSET] >>
        `s1 ∪ b n ∈ finite_inters (finite_unions s)` suffices_by (strip_tac >>
            fs[finite_inter_inter_finite_inter]) >>
        pop_assum kall_tac >> pop_assum (qspec_then `n` assume_tac) >> fs[] >>
        imp_res_tac set_union_finite_inter >> fs[UNION_COMM])
);

val finite_union_finite_inter_conjugation = store_thm(
    "finite_union_finite_inter_conjugation",
    ``∀s. finite_unions (finite_inters s) = finite_inters (finite_unions s)``,
    strip_tac >> fs[EXTENSION] >> strip_tac >> eq_tac >> strip_tac
    >- (`∀n b. 0 < n ∧ b ∈ (count n -> finite_inters s) ⇒
            BIGUNION (IMAGE b (count n)) ∈ finite_inters (finite_unions s)`
            suffices_by (rpt strip_tac >> fs[finite_unions_alt] >>
            pop_assum imp_res_tac >> rfs[]) >>
        last_x_assum kall_tac >> strip_tac >>
        Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >> Cases_on `n`
        >- (fs[BIGUNION_IMAGE_COUNT_ONE] >> rw[] >>
            `b 0 ∈ finite_inters s` by fs[count_def,FUNSET] >>
            (qspec_then `s` assume_tac) sets_subset_finite_unions >>
            imp_res_tac subset_imp_finite_inters_subset >> fs[SUBSET_DEF])
        >- (fs[] >> Q.ABBREV_TAC `n = SUC n'` >> pop_assum kall_tac >>
            fs[BIGUNION_IMAGE_COUNT_SUC] >>
            last_x_assum (qspec_then `b` assume_tac) >> rfs[count_def,FUNSET] >>
            last_x_assum (qspec_then `n` assume_tac) >> fs[] >>
            `b n ∈ finite_inters (finite_unions s)` by (
                (qspec_then `s` assume_tac) sets_subset_finite_unions >>
                imp_res_tac subset_imp_finite_inters_subset >> fs[SUBSET_DEF]) >>
            imp_res_tac finite_inter_union_finite_inter >>
            rfs[composition_finite_unions]))
    >- (`∀n b. 0 < n ∧ b ∈ (count n -> finite_unions s) ⇒
            BIGINTER (IMAGE b (count n)) ∈ finite_unions (finite_inters s)`
            suffices_by (rpt strip_tac >> fs[finite_inters_alt] >>
            pop_assum imp_res_tac >> rfs[]) >>
        last_x_assum kall_tac >> strip_tac >>
        Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >> Cases_on `n`
        >- (fs[BIGINTER_IMAGE_COUNT_ONE] >> rw[] >>
            `b 0 ∈ finite_unions s` by fs[count_def,FUNSET] >>
            (qspec_then `s` assume_tac) sets_subset_finite_inters >>
            imp_res_tac subset_imp_finite_unions_subset >> fs[SUBSET_DEF])
        >- (fs[] >> Q.ABBREV_TAC `n = SUC n'` >> pop_assum kall_tac >>
            fs[BIGINTER_IMAGE_COUNT_SUC] >>
            last_x_assum (qspec_then `b` assume_tac) >> rfs[count_def,FUNSET] >>
            last_x_assum (qspec_then `n` assume_tac) >> fs[] >>
            `b n ∈ finite_unions (finite_inters s)` by (
                (qspec_then `s` assume_tac) sets_subset_finite_inters >>
                imp_res_tac subset_imp_finite_unions_subset >> fs[SUBSET_DEF]) >>
            imp_res_tac finite_union_inter_finite_union >>
            rfs[composition_finite_inters]))
);

val finite_disj_unions_subset_finite_unions = store_thm(
    "finite_disj_unions_subset_finite_unions",
    ``∀a. finite_disjoint_unions a ⊆ finite_unions a``,
    fs[SUBSET_DEF,finite_disjoint_unions_def,finite_unions_def] >> metis_tac[]
);

val sets_subset_finite_disj_unions = store_thm(
    "sets_subset_finite_disj_unions",
    ``∀s. s ⊆ finite_disjoint_unions s``,
    fs[SUBSET_DEF,finite_disjoint_unions_alt] >> rpt strip_tac >>
    map_every EXISTS_TAC [``λi:num. x:α->bool``,``1 : num``] >>
    fs[BIGUNION_IMAGE_COUNT_ONE] >> fs[FUNSET]
);

val subset_imp_finite_disj_unions_subset = store_thm(
    "subset_imp_finite_disj_unions_subset",
    ``∀s t. s ⊆ t ⇒ finite_disjoint_unions s ⊆ finite_disjoint_unions t``,
    rpt strip_tac >> fs[SUBSET_DEF,finite_disjoint_unions_def] >> rpt strip_tac >>
    metis_tac[]
);

val union_in_finite_disj_unions = store_thm(
    "union_in_finite_disj_unions",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ s ∧ DISJOINT s0 s1 ⇒ s0 ∪ s1 ∈ finite_disjoint_unions s``,
    rpt strip_tac >> fs[finite_disjoint_unions_alt] >>
    map_every EXISTS_TAC [``λx:num. if (x=0) then s0:α->bool else s1``,``2:num``] >>
    fs[] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x` >> fs[])
    >- (`∀x. x ∈ BIGUNION (IMAGE (λx. if x = 0 then s0 else s1) (count 2)) ⇔ x ∈ s0 ∪ s1`
            suffices_by fs[EXTENSION] >>
        fs[IN_BIGINTER_IMAGE] >> strip_tac >> eq_tac >> rw[]
        >- (Cases_on `x' = 0` >> fs[])
        >- (EXISTS_TAC ``s0: α -> bool`` >> fs[] >>
            EXISTS_TAC ``0: num`` >> fs[])
        >- (EXISTS_TAC ``s1: α -> bool`` >> fs[] >>
            EXISTS_TAC ``1: num`` >> fs[]))
    >- (fs[DISJOINT_SYM])
);

val finite_disj_union_union_finite_disj_union = store_thm(
    "finite_disj_union_union_finite_disj_union",
    ``∀s s0 s1. s0 ∈ finite_disjoint_unions s ∧ s1 ∈ finite_disjoint_unions s ∧
        DISJOINT s0 s1 ⇒ s0 ∪ s1 ∈ finite_disjoint_unions s``,
    rpt strip_tac >> fs[finite_disjoint_unions_alt] >>
    map_every EXISTS_TAC
        [``(λx. if x < n then b x else b' (x - n)) : num -> α -> bool``,
        ``n + n': num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGUNION_IMAGE_COUNT_UNION])
    >- (fs[DISJOINT_BIGUNION,FUNSET] >> rw[] >>
        qpat_x_assum `∀s. _` (qspec_then `b i` assume_tac) >> pop_assum imp_res_tac >>
        pop_assum kall_tac >> fs[])
    >- (fs[DISJOINT_BIGUNION,FUNSET] >> rw[] >>
        qpat_x_assum `∀s. _` (qspec_then `b j` assume_tac) >> pop_assum imp_res_tac >>
        pop_assum kall_tac >> fs[DISJOINT_SYM])
);

val set_union_finite_disj_union = store_thm(
    "set_union_finite_disj_union",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_disjoint_unions s ∧ DISJOINT s0 s1 ⇒
        s0 ∪ s1 ∈ finite_disjoint_unions s``,
    rpt strip_tac >> assume_tac sets_subset_finite_disj_unions >>
    fs[SUBSET_DEF] >> pop_assum (qspec_then `s` imp_res_tac) >>
    fs[finite_disj_union_union_finite_disj_union]
);

val set_inter_finite_disj_union = store_thm(
    "set_inter_finite_disj_union",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_disjoint_unions s ⇒
        s0 ∩ s1 ∈ finite_disjoint_unions (finite_inters s)``,
    rpt strip_tac >> fs[finite_disjoint_unions_alt] >>
    map_every EXISTS_TAC [``λx:num. s0 ∩ b x``,``n:num``] >> rw[]
    >- (fs[FUNSET,inter_in_finite_inters])
    >- (fs[INTER_BIGUNION_IMAGE])
    >- (qpat_x_assum `∀i j. _` (qspecl_then [`i`,`j`] assume_tac) >> rfs[] >>
        fs[DISJOINT_DEF,INTER_DEF,EXTENSION] >> strip_tac >>
        qpat_x_assum `∀x. _` (qspecl_then [`x`] assume_tac) >> fs[])
);

val composition_finite_disj_unions = store_thm(
    "composition_finite_disj_unions",
    ``∀s. finite_disjoint_unions (finite_disjoint_unions s) = finite_disjoint_unions s``,
    strip_tac >> fs[EXTENSION] >> strip_tac >> eq_tac >> rw[]
    >- (`∃b n. 0 < n ∧ b ∈ (count n -> finite_disjoint_unions s) ∧
            (BIGUNION (IMAGE b (count n)) = x) ∧
            ∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)`
            by (fs[finite_disjoint_unions_alt] >> metis_tac[]) >>
        `∀n b. 0 < n ∧ b ∈ (count n -> finite_disjoint_unions s) ∧
            (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
            BIGUNION (IMAGE b (count n)) ∈ finite_disjoint_unions s`
            suffices_by (strip_tac >> pop_assum imp_res_tac >> rfs[]) >>
        rpt (pop_assum kall_tac) >> strip_tac >> Induct_on `n` >> rw[] >>
        last_x_assum (qspec_then `b` assume_tac) >> Cases_on `n` >> fs[]
        >- (fs[BIGUNION_IMAGE_COUNT_ONE] >> fs[count_def,FUNSET])
        >- (Q.RENAME_TAC [`BIGUNION (IMAGE b (count (SUC n)))`] >>
            fs[BIGUNION_IMAGE_COUNT_SUC] >>
            `BIGUNION (IMAGE b (count n)) ∈ finite_disjoint_unions s` by rfs[count_def,FUNSET] >>
            `b n ∈ finite_disjoint_unions s` by fs[count_def,FUNSET] >>
            `DISJOINT (b n) (BIGUNION (IMAGE b (count n)))` by (fs[DISJOINT_DEF] >>
                rpt strip_tac >> fs[INTER_DEF,EXTENSION]) >>
            fs[finite_disj_union_union_finite_disj_union]))
    >- ((qspec_then `finite_disjoint_unions s` assume_tac) sets_subset_finite_disj_unions >>
        fs[SUBSET_DEF])
);

val finite_disj_union_inter_finite_inter_of_finite_disj_union = store_thm(
    "finite_disj_union_inter_finite_inter_of_finite_disj_union",
    ``∀s s0 s1. s0 ∈ (finite_disjoint_unions s) ∧ s1 ∈ finite_inters (finite_disjoint_unions s) ⇒
        s0 ∩ s1 ∈ finite_inters (finite_disjoint_unions s)``,
    rpt strip_tac >> fs[finite_inters_alt] >>
    map_every EXISTS_TAC
        [``(λx:num. if x < n then b x else s0):num -> α -> bool``,``SUC n:num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGINTER_IMAGE_COUNT_SUC] >>
        `IMAGE (λx. if x < n then b x else s0) (count n) = IMAGE b (count n)`
            suffices_by fs[] >>
        fs[IMAGE_DEF,EXTENSION] >> strip_tac >> eq_tac >> rw[] >> fs[] >>
        EXISTS_TAC ``x':num`` >> fs[])
);

val finite_inter_union_finite_disj_union_of_finite_inter = store_thm(
    "finite_inter_union_finite_disj_union_of_finite_inter",
    ``∀s s0 s1. s0 ∈ (finite_inters s) ∧ s1 ∈ finite_disjoint_unions (finite_inters s) ∧
        DISJOINT s0 s1 ⇒ s0 ∪ s1 ∈ finite_disjoint_unions (finite_inters s)``,
    rpt strip_tac >> fs[finite_disjoint_unions_alt] >>
    map_every EXISTS_TAC
        [``(λx:num. if x < n then b x else s0):num -> α -> bool``,``SUC n:num``] >> rw[]
    >- (fs[FUNSET] >> rpt strip_tac >> Cases_on `x < n` >> fs[])
    >- (fs[BIGUNION_IMAGE_COUNT_SUC] >>
        `IMAGE (λx. if x < n then b x else s0) (count n) = IMAGE b (count n)`
            suffices_by fs[] >>
        fs[IMAGE_DEF,EXTENSION] >> strip_tac >> eq_tac >> rw[] >> fs[] >>
        EXISTS_TAC ``x':num`` >> fs[])
    >- (fs[DISJOINT_DEF,INTER_DEF,EXTENSION] >> metis_tac[])
    >- (fs[DISJOINT_DEF,INTER_DEF,EXTENSION] >> metis_tac[])
);

val finite_inter_inter_finite_disj_union_of_finite_inter = store_thm(
    "finite_inter_inter_finite_disj_union_of_finite_inter",
    ``∀s s0 s1. s0 ∈ (finite_inters s) ∧ s1 ∈ finite_disjoint_unions (finite_inters s) ⇒
        s0 ∩ s1 ∈ finite_disjoint_unions (finite_inters s)``,
    rpt strip_tac >> fs[finite_disjoint_unions_alt] >>
    map_every EXISTS_TAC [``λx:num. s0 ∩ b x``,``n:num``] >> rw[]
    >- (fs[FUNSET,finite_inter_inter_finite_inter])
    >- (fs[INTER_BIGUNION_IMAGE])
    >- (`DISJOINT (b i) (b j)` by RES_TAC >> fs[DISJOINT_DEF,EXTENSION] >> metis_tac[])
);

val set_inter_finite_inter_of_finite_disj_union = store_thm(
    "set_inter_finite_inter_of_finite_disj_union",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_inters (finite_disjoint_unions s) ⇒
        s0 ∩ s1 ∈ finite_inters (finite_disjoint_unions s)``,
    rpt strip_tac >>
    `s0 ∈ finite_disjoint_unions s` by metis_tac[sets_subset_finite_disj_unions,SUBSET_DEF] >>
    fs[finite_disj_union_inter_finite_inter_of_finite_disj_union]
);

val set_union_finite_disj_union_of_finite_inter = store_thm(
    "set_union_finite_disj_union_of_finite_inter",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_disjoint_unions (finite_inters s) ∧
        DISJOINT s0 s1 ⇒ s0 ∪ s1 ∈ finite_disjoint_unions (finite_inters s)``,
    rpt strip_tac >> `s0 ∈ finite_inters s` by metis_tac[sets_subset_finite_inters,SUBSET_DEF] >>
    fs[finite_inter_union_finite_disj_union_of_finite_inter]
);

val set_inter_finite_disj_union_of_finite_inter = store_thm(
    "set_inter_finite_disj_union_of_finite_inter",
    ``∀s s0 s1. s0 ∈ s ∧ s1 ∈ finite_disjoint_unions (finite_inters s) ⇒
        s0 ∩ s1 ∈ finite_disjoint_unions (finite_inters s)``,
    rpt strip_tac >> `s0 ∈ finite_inters s` by metis_tac[sets_subset_finite_inters,SUBSET_DEF] >>
    fs[finite_inter_inter_finite_disj_union_of_finite_inter]
);

val finite_union_inter_finite_union = store_thm(
    "finite_union_inter_finite_union",
    ``∀s s0 s1. s0 ∈ finite_disjoint_unions s ∧ s1 ∈ finite_disjoint_unions s ⇒
        s0 ∩ s1 ∈ finite_disjoint_unions (finite_inters s)``,
    rpt strip_tac >>
    `∀n b. 0 < n ∧ b ∈ (count n -> s) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
        BIGUNION (IMAGE b (count n)) ∩ s1 ∈ finite_disjoint_unions (finite_inters s)`
        suffices_by (rpt strip_tac >> fs[finite_disjoint_unions_alt] >>
        pop_assum (qspecl_then [`n`,`b`] assume_tac) >> rfs[] >> metis_tac[]) >>
    last_x_assum kall_tac >> strip_tac >>
    Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >> Cases_on `n`
    >- (fs[BIGUNION_IMAGE_COUNT_ONE] >> rw[] >>
        `b 0 ∈ s` by fs[count_def,FUNSET] >>
        fs[set_inter_finite_disj_union])
    >- (fs[] >> Q.ABBREV_TAC `n = SUC n'` >> pop_assum kall_tac >>
        fs[BIGUNION_IMAGE_COUNT_SUC] >> fs[INTER_COMM,UNION_OVER_INTER] >>
        qpat_x_assum `∀b. _` (qspec_then `b` assume_tac) >> rfs[count_def,FUNSET] >>
        `DISJOINT (s1 ∩ b n) (s1 ∩ BIGUNION (IMAGE b {m | m < n}))` by (
            fs[DISJOINT_DEF,EXTENSION,INTER_DEF] >> rw[] >> CCONTR_TAC >> fs[] >>
            `x ∈ b x'` by fs[] >>
            qpat_x_assum `∀ i j. _` (qspecl_then [`n`,`x'`] assume_tac) >> rfs[] >>
            pop_assum (qspec_then `x` assume_tac) >> metis_tac[]) >>
        `s1 ∩ b n ∈ finite_disjoint_unions (finite_inters s)` suffices_by (strip_tac >>
            fs[finite_disj_union_union_finite_disj_union]) >>
        NTAC 3 (pop_assum kall_tac) >> pop_assum (qspec_then `n` assume_tac) >> fs[] >>
        imp_res_tac set_inter_finite_disj_union >> fs[INTER_COMM])
);

val finite_disj_union_inter_finite_disj_union = store_thm(
    "finite_disj_union_inter_finite_disj_union",
    ``∀s s0 s1. s0 ∈ finite_disjoint_unions s ∧ s1 ∈ finite_disjoint_unions s ⇒
        s0 ∩ s1 ∈ finite_disjoint_unions (finite_inters s)``,
    rpt strip_tac >>
    `∀n b. 0 < n ∧ b ∈ (count n -> s) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
        BIGUNION (IMAGE b (count n)) ∩ s1 ∈ finite_disjoint_unions (finite_inters s)`
        suffices_by (rpt strip_tac >> qpat_x_assum `s1 ∈ _` kall_tac >>
        rfs[finite_disjoint_unions_alt] >>
        pop_assum (qspecl_then [`n`,`b`] assume_tac) >> rfs[] >>
        NTAC 4 (last_x_assum kall_tac) >> metis_tac[]) >>
    last_x_assum kall_tac >> strip_tac >>
    Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >> Cases_on `n`
    >- (fs[BIGUNION_IMAGE_COUNT_ONE] >> rw[] >>
        `b 0 ∈ s` by fs[count_def,FUNSET] >>
        (qspec_then `s` assume_tac) sets_subset_finite_inters >>
        `b 0 ∈ finite_inters s` by fs[SUBSET_DEF] >>
        imp_res_tac subset_imp_finite_disj_unions_subset >>
        fs[SUBSET_DEF,finite_inter_inter_finite_disj_union_of_finite_inter])
    >- (fs[] >> Q.ABBREV_TAC `n = SUC n'` >> pop_assum kall_tac >>
        fs[BIGUNION_IMAGE_COUNT_SUC] >> fs[INTER_COMM,UNION_OVER_INTER] >>
        qpat_x_assum `∀b. _` (qspec_then `b` assume_tac) >> rfs[count_def,FUNSET] >>
        `DISJOINT (s1 ∩ b n) (s1 ∩ BIGUNION (IMAGE b {m | m < n}))` by (
            fs[DISJOINT_DEF,INTER_DEF,EXTENSION] >> CCONTR_TAC >> fs[] >>
            qpat_x_assum `∀x. _` (qspec_then `x` assume_tac) >> fs[] >> rw[] >>
            qpat_x_assum `∀i j. _` (qspecl_then [`n`,`x'`] assume_tac) >> rfs[] >>
            pop_assum (qspec_then `x` assume_tac) >> metis_tac[]) >>
        `s1 ∩ b n ∈ finite_disjoint_unions (finite_inters s)` suffices_by (strip_tac >>
            fs[finite_disj_union_union_finite_disj_union]) >>
        NTAC 3 (pop_assum kall_tac) >> pop_assum (qspec_then `n` assume_tac) >> fs[] >>
        imp_res_tac set_inter_finite_disj_union >> fs[INTER_COMM])
);

val finite_inter_finite_disj_union_conjugation = store_thm(
    "finite_inter_finite_disj_union_conjugation",
    ``∀s. finite_inters (finite_disjoint_unions s) ⊆ finite_disjoint_unions (finite_inters s)``,
    strip_tac >> fs[SUBSET_DEF] >> rpt strip_tac >>
    `∀n b. 0 < n ∧ b ∈ (count n -> finite_disjoint_unions s) ⇒
        BIGINTER (IMAGE b (count n)) ∈ finite_disjoint_unions (finite_inters s)`
        suffices_by (rpt strip_tac >> fs[finite_inters_alt] >>
        pop_assum imp_res_tac >> rfs[]) >>
    last_x_assum kall_tac >> strip_tac >>
    Induct_on `n` >> rpt strip_tac >> fs[] >> rw[] >> Cases_on `n`
    >- (fs[BIGINTER_IMAGE_COUNT_ONE] >> rw[] >>
        `b 0 ∈ finite_disjoint_unions s` by fs[count_def,FUNSET] >>
        (qspec_then `s` assume_tac) sets_subset_finite_inters >>
        imp_res_tac subset_imp_finite_disj_unions_subset >> fs[SUBSET_DEF])
    >- (fs[] >> Q.ABBREV_TAC `n = SUC n'` >> pop_assum kall_tac >>
        fs[BIGINTER_IMAGE_COUNT_SUC] >>
        last_x_assum (qspec_then `b` assume_tac) >> rfs[count_def,FUNSET] >>
        last_x_assum (qspec_then `n` assume_tac) >> fs[] >>
        `b n ∈ finite_disjoint_unions (finite_inters s)` by (
            (qspec_then `s` assume_tac) sets_subset_finite_inters >>
            imp_res_tac subset_imp_finite_disj_unions_subset >> fs[SUBSET_DEF]) >>
        imp_res_tac finite_disj_union_inter_finite_disj_union >>
        rfs[composition_finite_inters])
);

val alg_sets_to_disj_unions = store_thm(
    "alg_sets_to_disj_unions",
    ``∀a s. algebra a ∧ s ⊆ subsets a ∧ FINITE s ⇒
        ∃t. t ⊆ subsets a ∧ (∀x y. x ∈ t ∧ y ∈ t ∧ (x ≠ y) ⇒ DISJOINT x y) ∧
        s ⊆ finite_disjoint_unions t ∧ FINITE t ∧ (BIGUNION s = BIGUNION t)``,
    strip_tac >>
    `∀s. FINITE s ⇒ algebra a ∧ s ⊆ subsets a ⇒
        ∃t. t ⊆ subsets a ∧ (∀x y. x ∈ t ∧ y ∈ t ∧ x ≠ y ⇒ DISJOINT x y) ∧
        s ⊆ finite_disjoint_unions t ∧ FINITE t ∧ (BIGUNION s = BIGUNION t)` suffices_by rw[] >>
    Induct_on `s` >> rw[] >> fs[]
    >- (EXISTS_TAC ``∅ : (α -> bool) -> bool`` >> fs[]) >>
    map_every Q.ABBREV_TAC [`et = IMAGE (λx. e ∩ x) t`,`ect = IMAGE (λx. (space a DIFF e) ∩ x) t`,
        `tce = (space a DIFF BIGUNION t) ∩ e`] >>
    EXISTS_TAC ``et ∪ ect ∪ {tce} : (α -> bool) -> bool`` >> rw[] >> fs[]
    >- (Q.UNABBREV_TAC `et` >> fs[SUBSET_DEF,IN_IMAGE] >> rw[] >> fs[ALGEBRA_INTER])
    >- (Q.UNABBREV_TAC `ect` >> fs[SUBSET_DEF,IN_IMAGE] >> rw[] >> fs[ALGEBRA_COMPL,ALGEBRA_INTER])
    >- (Q.UNABBREV_TAC `tce` >> imp_res_tac ALGEBRA_FINITE_UNION >> fs[ALGEBRA_COMPL,ALGEBRA_INTER])
    >- (Q.UNABBREV_TAC `et` >> fs[DISJOINT_DEF,IN_IMAGE] >>
        qpat_x_assum `∀x y. _` (qspecl_then [`x'`,`x''`] assume_tac) >> rfs[] >>
        `x' ≠ x''` by (CCONTR_TAC >> fs[]) >> fs[EXTENSION] >> metis_tac[])
    >- (map_every Q.UNABBREV_TAC [`et`,`ect`] >> fs[DISJOINT_DEF,IN_IMAGE] >>
        rpt (pop_assum kall_tac) >> fs[EXTENSION] >> metis_tac[])
    >- (map_every Q.UNABBREV_TAC [`et`,`tce`] >> fs[DISJOINT_DEF,IN_IMAGE] >>
        fs[EXTENSION] >> rw[] >> Q.RENAME_TAC [`_ ∨ _ ∨ y ∉ e`] >>
        Cases_on `y ∈ x'` >> fs[] >> `∃s. y ∈ s ∧ s ∈ t` suffices_by fs[] >>
        EXISTS_TAC ``x' : α -> bool`` >> fs[])
    >- (map_every Q.UNABBREV_TAC [`et`,`ect`] >> fs[DISJOINT_DEF,IN_IMAGE] >>
        rpt (pop_assum kall_tac) >> fs[EXTENSION] >> metis_tac[])
    >- (Q.UNABBREV_TAC `ect` >> fs[DISJOINT_DEF,IN_IMAGE] >> rw[] >>
        qpat_x_assum `∀x y. _` (qspecl_then [`x'`,`x''`] assume_tac) >> rfs[] >>
        `x' ≠ x''` by (CCONTR_TAC >> fs[]) >> fs[EXTENSION] >> metis_tac[])
    >- (map_every Q.UNABBREV_TAC [`ect`,`tce`] >> fs[DISJOINT_DEF,IN_IMAGE] >>
        rpt (pop_assum kall_tac) >> fs[EXTENSION] >> metis_tac[])
    >- (map_every Q.UNABBREV_TAC [`et`,`tce`] >> fs[DISJOINT_DEF,IN_IMAGE] >>
        fs[EXTENSION] >> rw[] >> Q.RENAME_TAC [`_ ∨ _ ∨ y ∉ x`] >>
        Cases_on `y ∈ x` >> fs[] >> `∃s. y ∈ s ∧ s ∈ t` suffices_by fs[] >>
        EXISTS_TAC ``x : α -> bool`` >> fs[])
    >- (map_every Q.UNABBREV_TAC [`ect`,`tce`] >> fs[DISJOINT_DEF,IN_IMAGE] >>
        rpt (pop_assum kall_tac) >> fs[EXTENSION] >> metis_tac[])
    >- (fs[finite_disjoint_unions_def] >>
        EXISTS_TAC ``et ∪ {tce} : (α -> bool) -> bool`` >> rw[] >> fs[]
        >- (fs[SUBSET_DEF])
        >- (Q.UNABBREV_TAC `et` >> fs[])
        >- (`∀z. z ∈ BIGUNION et ∨ z ∈ tce ⇔ z ∈ e` suffices_by fs[EXTENSION] >>
            map_every Q.UNABBREV_TAC [`et`,`tce`] >> fs[IN_BIGUNION] >> rw[] >>
            eq_tac >> rw[] >> fs[] >> Cases_on `z ∈ BIGUNION t` >> fs[]
            >- (`(∃s. z ∈ s ∧ ∃x. (s = e ∩ x) ∧ x ∈ t)` suffices_by fs[] >>
                EXISTS_TAC ``e ∩ s' : α -> bool`` >> fs[] >> EXISTS_TAC ``s' : α -> bool`` >> fs[])
            >- (`z ∈ space a` suffices_by fs[] >> fs[algebra_def,subset_class_def] >>
                `e ⊆ space a` by fs[] >> fs[SUBSET_DEF]))
        >- (Q.UNABBREV_TAC `et` >> fs[DISJOINT_DEF,IN_IMAGE] >>
            qpat_x_assum `∀x y. _` (qspecl_then [`x`,`x'`] assume_tac) >> rfs[] >>
            `x ≠ x'` by (CCONTR_TAC >> fs[]) >> fs[EXTENSION] >> metis_tac[])
        >- (map_every Q.UNABBREV_TAC [`et`,`j`] >> fs[DISJOINT_DEF,IN_IMAGE] >>
            fs[EXTENSION] >> rw[] >> Q.RENAME_TAC [`_ ∨ _ ∨ y ∉ e`] >>
            Cases_on `y ∈ x` >> fs[] >> `∃s. y ∈ s ∧ s ∈ t` suffices_by fs[] >>
            EXISTS_TAC ``x : α -> bool`` >> fs[])
        >- (map_every Q.UNABBREV_TAC [`et`,`i`] >> fs[DISJOINT_DEF,IN_IMAGE] >>
            fs[EXTENSION] >> rw[] >> Q.RENAME_TAC [`_ ∨ _ ∨ y ∉ x`] >>
            Cases_on `y ∈ x` >> fs[] >> `∃s. y ∈ s ∧ s ∈ t` suffices_by fs[] >>
            EXISTS_TAC ``x : α -> bool`` >> fs[]))
    >- (`t ⊆ finite_disjoint_unions (et ∪ ect)` suffices_by (rw[] >>
            `et ∪ ect ⊆ et ∪ ect ∪ {tce}` by fs[SUBSET_DEF] >>
            `finite_disjoint_unions (et ∪ ect) ⊆ finite_disjoint_unions (et ∪ ect ∪ {tce})`
                by fs[subset_imp_finite_disj_unions_subset] >>
            `t ⊆ finite_disjoint_unions (et ∪ ect ∪ {tce})` by imp_res_tac SUBSET_TRANS >>
            `finite_disjoint_unions t ⊆
                finite_disjoint_unions (finite_disjoint_unions (et ∪ ect ∪ {tce}))`
                by fs[subset_imp_finite_disj_unions_subset] >>
            fs[composition_finite_disj_unions] >> imp_res_tac SUBSET_TRANS) >>
        Q.UNABBREV_TAC `tce` >> fs[SUBSET_DEF,finite_disjoint_unions_def] >> rw[] >>
        Q.RENAME_TAC [`r ∈ t`] >> EXISTS_TAC ``{e ∩ r;(space a DIFF e) ∩ r}`` >> rw[] >> fs[]
        >- (`e ∩ r ∈ et` suffices_by fs[] >> Q.UNABBREV_TAC `et` >> fs[IN_IMAGE] >>
            EXISTS_TAC ``r : α -> bool`` >> fs[])
        >- (`(space a DIFF e) ∩ r ∈ ect` suffices_by fs[] >> Q.UNABBREV_TAC `ect` >>
            fs[IN_IMAGE] >> EXISTS_TAC ``r : α -> bool`` >> fs[])
        >- (fs[EXTENSION] >> rw[] >> eq_tac >> rw[] >> Cases_on `x ∈ e` >> fs[] >>
            `r ∈ subsets a` by fs[] >> fs[algebra_def,subset_class_def] >>
            `r ⊆ space a` by fs[] >> fs[SUBSET_DEF])
        >- (rpt (pop_assum kall_tac) >> fs[DISJOINT_DEF,EXTENSION] >> metis_tac[])
        >- (rpt (pop_assum kall_tac) >> fs[DISJOINT_DEF,EXTENSION] >> metis_tac[]))
    >- (Q.UNABBREV_TAC `et` >> fs[])
    >- (Q.UNABBREV_TAC `ect` >> fs[])
    >- (`∀z. z ∈ e ∨ z ∈ BIGUNION t ⇔ z ∈ BIGUNION et ∨ z ∈ BIGUNION ect ∨ z ∈ tce`
            suffices_by fs[EXTENSION,DISJ_ASSOC] >>
        strip_tac >> map_every Q.UNABBREV_TAC [`et`,`ect`,`tce`] >>
        Cases_on `z ∈ e` >> Cases_on `z ∈ BIGUNION t` >> fs[IN_BIGUNION_IMAGE]
        >- (`(∃x. x ∈ t ∧ z ∈ x)` suffices_by fs[] >> EXISTS_TAC ``s' : α -> bool`` >> fs[])
        >- (`z ∈ space a` suffices_by fs[] >>
            drule_all_then assume_tac ALGEBRA_SUBSETS_SUBSET_SPACE >> fs[SUBSET_DEF])
        >- (`∃x. x ∈ t ∧ z ∈ space a ∧ z ∈ x` suffices_by metis_tac[] >>
            EXISTS_TAC ``s' : α -> bool`` >> fs[] >>
            `s' ∈ subsets a` by fs[SUBSET_DEF] >>
            drule_all_then assume_tac ALGEBRA_SUBSETS_SUBSET_SPACE >> fs[SUBSET_DEF])
        >- (`¬∃x. x ∈ t ∧ z ∈ space a ∧ z ∈ x` suffices_by metis_tac[] >> fs[] >> rw[] >>
            pop_assum (qspec_then `x` assume_tac) >> fs[]))
);

val alg_sets_to_disj_unions_alt = store_thm(
    "alg_sets_to_disj_unions_alt",
    ``∀n b a. algebra a ∧ b ∈ (count n -> subsets a) ⇒
        ∃m c. c ∈ (count m -> subsets a) ∧
        (∀i j. i < m ∧ j < m ∧ i ≠ j ⇒ DISJOINT (c i) (c j)) ∧
        b ∈ (count n -> finite_disjoint_unions (IMAGE c (count m))) ∧
        (BIGUNION (IMAGE b (count n)) = BIGUNION (IMAGE c (count m)))``,
    rw[] >>
    (qspecl_then [`a`,`IMAGE b (count n)`] assume_tac) alg_sets_to_disj_unions >>
    rfs[IMAGE_FINITE] >>
    `IMAGE b (count n) ⊆ subsets a` by (rw[SUBSET_DEF] >> fs[FUNSET]) >>
    fs[] >> pop_assum kall_tac >> fs[FINITE_BIJ_COUNT_EQ] >>
    Q.RENAME_TAC [`BIJ c (count m) t`] >> map_every qexists_tac [`m`,`c`] >> rw[]
    >- (fs[SUBSET_DEF,FUNSET,BIJ_ALT])
    >- (fs[BIJ_DEF,INJ_DEF] >>
        qpat_x_assum `∀x y. _` (qspecl_then [`i`,`j`] assume_tac) >> rfs[])
    >- (pop_assum kall_tac >> drule_all_then assume_tac (GSYM BIJ_IMAGE) >>
        fs[SUBSET_DEF,IN_IMAGE,FUNSET] >> pop_assum kall_tac >> rw[] >>
        qpat_x_assum `∀x. _` irule >> qexists_tac `x` >> fs[])
    >- (drule_all_then assume_tac (GSYM BIJ_IMAGE) >> fs[])
);

val finite_unions_subset_sigma = store_thm(
    "finite_unions_subset_sigma",
    ``∀sp sts. finite_unions sts ⊆ subsets (sigma sp sts)``,
    rpt strip_tac >> fs[subsets_def,sigma_def] >>
    `∀x. x ∈ finite_unions sts ⇒ x ∈ BIGINTER {s | sts ⊆ s ∧ sigma_algebra (sp,s)}`
        suffices_by fs[SUBSET_DEF] >>
    rpt strip_tac >> fs[IN_BIGINTER] >> rpt strip_tac >>
    fs[SIGMA_ALGEBRA,finite_unions_def,space_def,subsets_def] >>
    imp_res_tac finite_countable >> RES_TAC >>
    NTAC 2 (qpat_x_assum `∀x. _` kall_tac) >> metis_tac[SUBSET_TRANS]
);

val sigma_finite_unions = store_thm(
    "sigma_finite_unions",
    ``∀sp sts. sigma sp (finite_unions sts) = sigma sp sts``,
    rpt strip_tac >>
    `sts ⊆ finite_unions sts` by fs[sets_subset_finite_unions] >>
    imp_res_tac SUBSET_IMP_SIGMA_SUBSET >> pop_assum (qspec_then `sp` assume_tac) >>
    `finite_unions sts ⊆ subsets (sigma sp sts)` suffices_by (strip_tac >>
        (qspecl_then [`sp`,`finite_unions sts`,`subsets (sigma sp sts)`] assume_tac)
            SUBSET_IMP_SIGMA_SUBSET >> rfs[] >>
        fs[SIGMA_SIGMA] >> fs[sigma_def,subsets_def,SET_EQ_SUBSET]) >>
    fs[finite_unions_subset_sigma]
);

val finite_disj_unions_subset_sigma = store_thm(
    "finite_disj_unions_subset_sigma",
    ``∀sp sts. finite_disjoint_unions sts ⊆ subsets (sigma sp sts)``,
    rpt strip_tac >> fs[subsets_def,sigma_def] >>
    `∀x. x ∈ finite_disjoint_unions sts ⇒ x ∈ BIGINTER {s | sts ⊆ s ∧ sigma_algebra (sp,s)}`
        suffices_by fs[SUBSET_DEF] >>
    rpt strip_tac >> fs[IN_BIGINTER] >> rpt strip_tac >>
    fs[SIGMA_ALGEBRA,finite_disjoint_unions_def,space_def,subsets_def] >>
    imp_res_tac finite_countable >> RES_TAC >>
    NTAC 2 (qpat_x_assum `∀x. _` kall_tac) >> metis_tac[SUBSET_TRANS]
);

val sigma_finite_disj_unions = store_thm(
    "sigma_finite_disj_unions",
    ``∀sp sts. sigma sp (finite_disjoint_unions sts) = sigma sp sts``,
    rw[] >> `sts ⊆ finite_disjoint_unions sts` by fs[sets_subset_finite_disj_unions] >>
    imp_res_tac SUBSET_IMP_SIGMA_SUBSET >> pop_assum (qspec_then `sp` assume_tac) >>
    `finite_disjoint_unions sts ⊆ subsets (sigma sp sts)` suffices_by (strip_tac >>
        (qspecl_then [`sp`,`finite_disjoint_unions sts`,`subsets (sigma sp sts)`] assume_tac)
            SUBSET_IMP_SIGMA_SUBSET >> rfs[] >>
        fs[SIGMA_SIGMA] >> fs[sigma_def,subsets_def,SET_EQ_SUBSET]) >>
    fs[finite_disj_unions_subset_sigma]
);

val _ = export_theory();