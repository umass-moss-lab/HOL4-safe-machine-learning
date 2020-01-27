open HolKernel Parse boolLib bossLib;
open combinTheory;
open pairTheory;
open arithmeticTheory;
open pred_setTheory;
open listTheory;
open realTheory;
open realLib;
open seqTheory;
open limTheory;
open transcTheory;
open real_sigmaTheory;
open util_probTheory;
open c487306_extrealTheory;
open c487306_measureTheory;
open c487306_lebesgueTheory;
open c487306_probabilityTheory;

val _ = new_theory "trivial";

(*---------------------------------------------------------------------------*)
(* Offensively Trivial stuff (Combinとか, Pairとか) *)
(*---------------------------------------------------------------------------*)

val DUP_DEF = new_definition("DUP_DEF",``DUP x = (x,x)``);

val I_ALT = store_thm(
    "I_ALT",
    ``I = (λx. x)``,
    rw[FUN_EQ_THM]
);

val F_SIMP = store_thm(
    "F_SIMP",
    ``∀f. (λx. f x) = f``,
    rw[FUN_EQ_THM]
);

val FUN_EQ = store_thm(
    "FUN_EQ",
    ``∀f x y. (x = y) ⇒ (f x = f y)``,
    rw[]
);

val IRULER = store_thm(
    "IRULER",
    ``∀P x y. x = y ⇒ P x = P y``,
    rw[]
);

val PAIR_FUN = store_thm(
    "PAIR_FUN",
    ``∀P z. (λ(x,y). P x y) z = P (FST z) (SND z)``,
    rw[] >> (qspec_then `z` assume_tac) ABS_PAIR_THM >> fs[]
);

val PAIR_EQ_ALT = store_thm(
    "PAIR_EQ_ALT",
    ``∀x y. x = y ⇔ FST x = FST y ∧ SND x = SND y``,
    rw[] >> map_every (fn tm => (qspec_then tm assume_tac) ABS_PAIR_THM) [`x`,`y`] >> fs[]
);

val PAIR_MAP_IMAGE_CROSS = store_thm(
    "PAIR_MAP_IMAGE_CROSS",
    ``∀f g s t. IMAGE (f ## g) (s × t) = (IMAGE f s) × (IMAGE g t)``,
    rw[EXTENSION,PAIR_MAP] >> eq_tac >> rw[] >> fs[]
    >- (rename [`FST z ∈ s`] >> qexists_tac `FST z` >> rw[])
    >- (rename [`FST z ∈ s`] >> qexists_tac `SND z` >> rw[])
    >- (rename [`FST z = f x`,`SND z = g y`] >> qexists_tac `(x,y)` >> fs[] >> metis_tac[PAIR])
);

val PAIR_MAP_PREIMAGE_CROSS = store_thm(
    "PAIR_MAP_PREIMAGE_CROSS",
    ``∀f g s t. PREIMAGE (f ## g) (s × t) = (PREIMAGE f s) × (PREIMAGE g t)``,
    rw[EXTENSION,PAIR_MAP] >> eq_tac >> rw[] >> fs[]
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Arithmetic *)
(*---------------------------------------------------------------------------*)

val DIV_MOD_EQ = store_thm(
    "DIV_MOD_EQ",
    ``∀x y z. 0 < z ⇒ ((x = y) ⇔ (x DIV z = y DIV z) ∧ (x MOD z = y MOD z))``,
    rw[] >> eq_tac >> fs[] >> rw[] >> imp_res_tac DA >>
    pop_assum (fn th => map_every (fn sp => (qspec_then sp assume_tac) th) [`x`,`y`]) >>
    fs[] >> rw[] >> Q.RENAME_TAC [`r + q * z = s + p * z`] >>
    (fn th => map_every (fn sp => (qspecl_then sp assume_tac) th) [[`z`,`r`],[`z`,`s`]]) DIV_MULT >>
    rfs[] >> fs[]
);

val LT_PROD_MOD_DIV = store_thm(
    "LT_PROD_MOD_DIV",
    ``∀m n k. k < m * n ⇒ k MOD m < m ∧ k DIV m < n``,
    rw[] >> `0 < m` by (CCONTR_TAC >> fs[])
    >- (rw[DIVISION])
    >- (drule_then assume_tac DA >> pop_assum (qspec_then `k` assume_tac) >>
        fs[] >> rw[] >> drule_then assume_tac DIV_MULT >> fs[] >>
        NTAC 2 (pop_assum kall_tac) >> CCONTR_TAC >> `n ≤ q` by fs[] >>
        `m * n ≤ m * q` by fs[] >>
        (qspecl_then [`0`,`m * n`,`r`,`m * q`] assume_tac) LESS_EQ_LESS_EQ_MONO >> rfs[])
);

val MOD_DIV_LT_PROD = store_thm(
    "MOD_DIV_LT_PROD",
    ``∀x:num y m n. x < m ∧ y < n ⇒ y * m + x < m * n``,
    rw[] >> `1 + y ≤ n` by fs[] >> `m * (1 + y) ≤ n * m` by fs[] >> fs[LEFT_ADD_DISTRIB]
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Pred Set *)
(*---------------------------------------------------------------------------*)

val UNIV_FUN = store_thm(
    "UNIV_FUN",
    ``(𝕌(:α) -> 𝕌(:β)) = 𝕌(:α -> β)``,
    rw[EXTENSION,FUNSET]
);

val BIJ_I = store_thm(
    "BIJ_I",
    ``∀s. I PERMUTES s``,
    rw[I_ALT,BIJ_ID]
);

val BIJ_CROSS = store_thm(
    "BIJ_CROSS",
    ``∀a b c d f g. BIJ f a b ∧ BIJ g c d ⇒ BIJ (f ## g) (a × c) (b × d)``,
    rw[BIJ_DEF,INJ_DEF,SURJ_DEF,PAIR_FUN,PAIR_MAP]
    >- (NTAC 2 (qpat_x_assum `∀x y. _` (dxrule_all_then assume_tac)) >> rw[PAIR_EQ_ALT])
    >- (NTAC 2 (qpat_x_assum `∀x. _ ⇒ ∃y. _` (dxrule_then assume_tac)) >> fs[] >>
        rename [`f y0 = FST x`,`g y1 = SND x`] >> qexists_tac `(y0,y1)` >> fs[])
);

val CROSS_INTER = store_thm(
    "CROSS_INTER",
    ``∀a b c d. (a × b) ∩ (c × d) = (a ∩ c) × (b ∩ d)``,
    rw[EXTENSION] >> eq_tac >> rw[]
);

val SET_DEMORGANS = store_thm(
    "SET_DEMORGANS",
    ``∀x y z. (x DIFF (y ∪ z) = (x DIFF y) ∩ (x DIFF z)) ∧
        (x DIFF (y ∩ z) = (x DIFF y) ∪ (x DIFF z))``,
    rpt strip_tac >> fs[EXTENSION] >> strip_tac >> eq_tac >> rw[] >> fs[]
);

val DIFF_DIFF2 = store_thm(
    "DIFF_DIFF2",
    ``∀s t. s DIFF (s DIFF t) = s ∩ t``,
    rw[EXTENSION] >> eq_tac >> rw[]
);

val UNION_INTER_DIFF = store_thm(
    "UNION_INTER_DIFF",
    ``∀s t. (s ∩ t) ∪ (s DIFF t) = s``,
    rw[EXTENSION] >> eq_tac >> rw[]
);

val BIJ_IMP_121C = store_thm(
    "BIJ_IMP_121C",
    ``∀f s t x y. BIJ f s t ∧ x ∈ s ∧ y ∈ s ⇒ ((f x = f y) ⇔ (x = y))``,
    rw[BIJ_ALT,EXISTS_UNIQUE_DEF] >> eq_tac >> rw[] >> fs[FUNSET]
);

val BIJ_IMAGE_PREIMAGE = store_thm(
    "BIJ_IMAGE_PREIMAGE",
    ``∀f s a b. BIJ f a b ∧ s ⊆ b ⇒ (IMAGE f (PREIMAGE f s ∩ a) = s)``,
    rw[] >> irule SUBSET_ANTISYM >> rw[IMAGE_PREIMAGE] >> rw[SUBSET_DEF] >>
    fs[PREIMAGE_def] >> `x ∈ b` by fs[SUBSET_DEF] >> fs[BIJ_ALT] >> RES_TAC >>
    fs[EXISTS_UNIQUE_THM] >> qexists_tac `x'` >> rw[]
);

val BIJ_PREIMAGE_IMAGE = store_thm(
    "BIJ_PREIMAGE_IMAGE",
    ``∀f s a b. BIJ f a b ∧ s ⊆ a ⇒ (PREIMAGE f (IMAGE f s) ∩ a = s)``,
    rw[] >> irule SUBSET_ANTISYM >> rw[PREIMAGE_IMAGE] >> rw[SUBSET_DEF] >>
    fs[PREIMAGE_def] >> `x' ∈ a` by fs[SUBSET_DEF] >>
    fs[BIJ_DEF,INJ_DEF] >> qpat_x_assum `∀x y. _` (qspecl_then [`x`,`x'`] assume_tac) >> rfs[]
);

val BIJ_POW = store_thm(
    "BIJ_POW",
    ``∀f s t. BIJ f s t ⇒ BIJ (IMAGE f) (POW s) (POW t)``,
    rw[] >> rw[BIJ_ALT,EXISTS_UNIQUE_THM]
    >- (fs[BIJ_ALT,EXISTS_UNIQUE_THM,FUNSET,POW_DEF,SUBSET_DEF] >> rw[] >> RES_TAC >> RES_TAC)
    >- (qexists_tac `PREIMAGE f y ∩ s` >> simp[IN_PREIMAGE,POW_DEF] >>
        irule (GSYM BIJ_IMAGE_PREIMAGE) >> qexists_tac `t` >> fs[POW_DEF])
    >- (rename [`a = b`] >> `PREIMAGE f (IMAGE f b) ∩ s = PREIMAGE f (IMAGE f a) ∩ s` by rw[] >>
        `PREIMAGE f (IMAGE f b) ∩ s = b` by (irule BIJ_PREIMAGE_IMAGE >> fs[POW_DEF] >>
            qexists_tac `t` >> rw[]) >>
        `PREIMAGE f (IMAGE f a) ∩ s = a` by (irule BIJ_PREIMAGE_IMAGE >> fs[POW_DEF] >>
            qexists_tac `t` >> rw[]) >>
        fs[])
);

val DISJOINT_CROSS = store_thm(
    "DISJOINT_CROSS",
    ``∀s0 s1 t0 t1. DISJOINT (s0 × s1) (t0 × t1) ⇔ DISJOINT s0 t0 ∨ DISJOINT s1 t1``,
    rw[DISJOINT_DEF,EXTENSION] >> eq_tac >> rw[]
    >- (CCONTR_TAC >> fs[] >> qpat_x_assum `∀x. _` (qspec_then `(x,x')` assume_tac) >> rw[])
    >- (qpat_x_assum `∀x. _` (qspec_then `FST x` assume_tac) >> fs[])
    >- (qpat_x_assum `∀x. _` (qspec_then `SND x` assume_tac) >> fs[])
);

val CROSS_DIFF = store_thm(
    "CROSS_DIFF",
    ``∀A B X Y. A ⊆ X ∧ B ⊆ Y ⇒ (X × Y DIFF A × B =
        ((X DIFF A) × (Y DIFF B)) ∪ ((X DIFF A) × B) ∪ (A × (Y DIFF B)))``,
    rw[] >> fs[CROSS_DEF,DIFF_DEF,UNION_DEF,EXTENSION,SUBSET_DEF] >> rw[] >>
    Cases_on `FST x ∈ X` >> Cases_on `SND x ∈ Y` >> Cases_on `FST x ∈ A` >> Cases_on `SND x ∈ B` >>
    fs[] >> RES_TAC
);

val CROSS_EQ = store_thm(
    "CROSS_EQ",
    ``∀A B X Y. (A × B = X × Y) ∧ (X × Y ≠ ∅) ⇒ (A = X) ∧ (B = Y)``,
    rw[] >> fs[CROSS_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[]
    >- (`SND x ∈ B` by metis_tac[] >>
        qpat_x_assum `∀x. _` (assume_tac o ISPEC ``(x' : α,SND (x : α # β))``) >> rfs[])
    >- (qpat_x_assum `∀x. _` (assume_tac o ISPEC ``(x' : α,SND (x : α # β))``) >> rfs[])
    >- (`FST x ∈ A` by metis_tac[] >>
        qpat_x_assum `∀x. _` (assume_tac o ISPEC ``(FST (x : α # β),x' : β)``) >> rfs[])
    >- (qpat_x_assum `∀x. _` (assume_tac o ISPEC ``(FST (x : α # β),x' : β)``) >> rfs[])
);

val CROSS_UNION_LEFT = store_thm(
    "CROSS_UNION_LEFT",
    ``∀r s t. (s ∪ t) × r = s × r ∪ t × r``,
    rw[] >> fs[CROSS_DEF,UNION_DEF,EXTENSION] >> metis_tac[]
);

val CROSS_UNION_RIGHT = store_thm(
    "CROSS_UNION_RIGHT",
    ``∀r s t. r × (s ∪ t) = r × s ∪ r × t``,
    rw[] >> fs[CROSS_DEF,UNION_DEF,EXTENSION] >> metis_tac[]
);

val POW_SING = store_thm(
    "POW_SING",
    ``∀x. POW {x} = {{x}} ∪ {∅}``,
    rw[POW_DEF,EXTENSION,SUBSET_DEF] >> eq_tac >> rw[]
    >- (Cases_on `∀x. x ∉ x'` >> rw[] >> fs[] >> eq_tac >> rw[] >> RES_TAC >> fs[])
    >- (rfs[])
    >- (last_x_assum (qspec_then `x''` assume_tac) >> fs[])
);

val IN_POW_SING = store_thm(
    "IN_POW_SING",
    ``∀x y. x ∈ POW {y} ⇔ (x = {y}) ∨ (x = ∅)``,
    rw[POW_SING]
);

val MEMBER_EMPTY = store_thm(
    "MEMBER_EMPTY",
    ``∀s. (∀x. x ∉ s) ⇔ (s = ∅)``,
    rw[EMPTY_DEF,EXTENSION]
);

val SUBSET_POW_SING = store_thm(
    "SUBSET_POW_SING",
    ``∀s x. s ⊆ POW {x} ⇔ (s = POW {x}) ∨ (s = {{x}}) ∨ (s = {∅}) ∨ (s = ∅)``,
    rw[POW_SING] >> Q.RENAME_TAC [`s ⊆ {{y}} ∪ {∅}`] >>
    rw[SUBSET_DEF,UNION_DEF] >> eq_tac >> rw[] >> fs[] >>
    Cases_on `{y} ∈ s` >> Cases_on `∅ ∈ s` >> fs[]
    >- (`s = {x | (x = {y}) ∨ (x = ∅)}` suffices_by rw[] >> rw[EXTENSION] >> eq_tac >> rw[]
        >- (last_x_assum (dxrule_then assume_tac) >> fs[EXTENSION])
        >- (`x = {y}` by rw[EXTENSION] >> rw[])
        >- (fs[MEMBER_EMPTY]))
    >- (`s = {{y}}` suffices_by rw[] >> rw[EXTENSION] >> eq_tac >> rw[]
        >- (last_x_assum (drule_then assume_tac) >> fs[EXTENSION] >> fs[MEMBER_EMPTY])
        >- (`x = {y}` by rw[EXTENSION] >> rw[]))
    >- (`s = {∅}` suffices_by rw[] >> rw[EXTENSION] >> eq_tac >> rw[]
        >- (last_x_assum (drule_then assume_tac) >> fs[EXTENSION] >>
            `x = {y}` by rw[EXTENSION] >> fs[])
        >- (fs[MEMBER_EMPTY]))
    >- (`s = ∅` suffices_by rw[] >> rw[EXTENSION] >> CCONTR_TAC >> fs[] >>
        last_x_assum (drule_then assume_tac) >> fs[] >> fs[])
);

val COUNT_EMPTY = store_thm(
    "COUNT_EMPTY",
    ``∀n. (count n = ∅) ⇔ (n = 0)``,
    rw[count_def,EXTENSION] >> eq_tac >> rw[] >>
    Cases_on `n` >> simp[] >> rename [`SUC n`] >>
    pop_assum (qspec_then `n` assume_tac) >> fs[]
);

val COUNT_ONE = store_thm(
    "COUNT_ONE",
    ``count 1 = {0}``,
    fs[count_def,EXTENSION]
);

val IMAGE_COUNT_ONE = store_thm(
    "IMAGE_COUNT_ONE",
    ``∀f. IMAGE f (count 1) = {f 0}``,
    fs[COUNT_ONE]
);

val IMAGE_PAIR = store_thm(
    "IMAGE_PAIR",
    ``∀s y. IMAGE (λx. (x,y)) s = s × {y}``,
    rw[EXTENSION,CROSS_DEF] >> eq_tac >> rw[] >> fs[] >>
    qexists_tac `FST x` >> rw[PAIR]
);

val BIGUNION_POW = store_thm(
    "BIGUNION_POW",
    ``∀s. BIGUNION (POW s) = s``,
    rw[EXTENSION,POW_DEF] >> eq_tac >> rw[]
    >- (rfs[SUBSET_DEF])
    >- (qexists_tac `s` >> fs[])
);

val BIGUNION_IMAGE_COUNT_ONE = store_thm(
    "BIGUNION_IMAGE_COUNT_ONE",
    ``∀f. BIGUNION (IMAGE f (count 1)) = f 0``,
    fs[IMAGE_COUNT_ONE]
);

val BIGINTER_IMAGE_COUNT_ONE = store_thm(
    "BIGINTER_IMAGE_COUNT_ONE",
    ``∀f. BIGINTER (IMAGE f (count 1)) = f 0``,
    fs[IMAGE_COUNT_ONE]
);

val BIGUNION_IMAGE_COUNT_SUC = store_thm(
    "BIGUNION_IMAGE_COUNT_SUC",
    ``∀f n. BIGUNION (IMAGE f (count (SUC n))) = f n ∪ BIGUNION (IMAGE f (count n))``,
    rpt strip_tac >>
    `∀x. x ∈ BIGUNION (IMAGE f (count (SUC n))) ⇔ x ∈ f n ∨ x ∈ BIGUNION (IMAGE f (count n))`
        suffices_by (strip_tac >> fs[EXTENSION]) >> strip_tac >> eq_tac >> rw[]
    >- (Cases_on `x ∈ f n` >> fs[] >>
        EXISTS_TAC ``(f : num->α->bool) x'`` >> fs[] >>
        EXISTS_TAC ``x' : num`` >> fs[] >> Cases_on `x' = n` >> fs[])
    >- (EXISTS_TAC ``(f : num->α->bool) n`` >> fs[] >>
        EXISTS_TAC ``n : num`` >> fs[])
    >- (EXISTS_TAC ``(f : num->α->bool) x'`` >> fs[] >>
        EXISTS_TAC ``x' : num`` >> fs[])
);

val BIGINTER_IMAGE_COUNT_SUC = store_thm(
    "BIGINTER_IMAGE_COUNT_SUC",
    ``∀f n. BIGINTER (IMAGE f (count (SUC n))) = f n ∩ BIGINTER (IMAGE f (count n))``,
    rpt strip_tac >>
    `∀x. x ∈ BIGINTER (IMAGE f (count (SUC n))) ⇔ x ∈ f n ∧ x ∈ BIGINTER (IMAGE f (count n))`
        suffices_by (strip_tac >> fs[EXTENSION]) >> strip_tac >> eq_tac >> rw[]
    >- (qpat_x_assum `∀P. _` (qspec_then `f n` assume_tac) >>
        `(f n = f n) ∧ n < SUC n` by fs[] >> RES_TAC)
    >- (qpat_x_assum `∀P. _` (qspec_then `f x'` assume_tac) >>
        `(f x' = f x') ∧ x' < SUC n` by fs[] >> RES_TAC)
    >- (Cases_on `x' = n` >> fs[] >>
        qpat_x_assum `∀P. _` (qspec_then `f x'` assume_tac) >>
        `(f x' = f x') ∧ x' < SUC n` by fs[] >> RES_TAC >> fs[])
);

val BIGINTER_IMAGE_COUNT_SUC_COMM = store_thm(
    "BIGINTER_IMAGE_COUNT_SUC_COMM",
    ``∀f n. BIGINTER (IMAGE f (count (SUC n))) = BIGINTER (IMAGE f (count n)) ∩ f n``,
    rw[BIGINTER_IMAGE_COUNT_SUC,INTER_COMM]
);

val BIGUNION_IMAGE_COUNT_SUC_COMM = store_thm(
    "BIGUNION_IMAGE_COUNT_SUC_COMM",
    ``∀f n. BIGUNION (IMAGE f (count (SUC n))) = BIGUNION (IMAGE f (count n)) ∪ f n``,
    rw[BIGUNION_IMAGE_COUNT_SUC,UNION_COMM]
);

val DIFF_BIGUNION1 = store_thm(
    "DIFF_BIGUNION1",
    ``∀sp s. (s ≠ ∅) ⇒ (sp DIFF BIGUNION s = BIGINTER (IMAGE (λu. sp DIFF u) s))``,
    rpt strip_tac >> fs[GSYM MEMBER_NOT_EMPTY] >>
    `∀x. x ∈ sp ∧ x ∉ BIGUNION s ⇔ x ∈ BIGINTER (IMAGE (λu. sp DIFF u) s)`
        suffices_by (strip_tac >> fs[EXTENSION]) >>
    fs[IN_BIGINTER_IMAGE] >> strip_tac >> eq_tac >> rpt strip_tac >> fs[]
    >- (qpat_x_assum `∀s'. _` (qspec_then `u` assume_tac) >> rfs[])
    >- (RES_TAC)
    >- (CCONTR_TAC >> fs[] >> RES_TAC)
);

val DIFF_BIGINTER_IMAGE = store_thm(
    "DIFF_BIGINTER_IMAGE",
    ``∀sp s f. s ≠ ∅ ∧ f ∈ (s -> POW sp) ⇒
        (sp DIFF BIGINTER (IMAGE f s) = BIGUNION (IMAGE (λu. sp DIFF f u) s))``,
    rw[] >> rw[EXTENSION,IN_BIGUNION_IMAGE,IN_BIGINTER_IMAGE] >>
    eq_tac >> rw[] >> fs[] >> EXISTS_TAC ``u : β`` >> fs[]
);

val DIFF_BIGUNION_IMAGE = store_thm(
    "DIFF_BIGUNION_IMAGE",
    ``∀sp s f. s ≠ ∅ ∧ f ∈ (s -> POW sp) ⇒
        (sp DIFF BIGUNION (IMAGE f s) = BIGINTER (IMAGE (λu. sp DIFF f u) s))``,
    rw[] >> rw[EXTENSION,IN_BIGUNION_IMAGE,IN_BIGINTER_IMAGE] >>
    eq_tac >> rw[] >> fs[FUNSET,POW_DEF]
    >- (qpat_x_assum `∀x. _` (qspec_then `u` assume_tac) >> rfs[])
    >- (fs[EXTENSION] >> RES_TAC)
    >- (CCONTR_TAC >> fs[] >> RES_TAC)
);

val BIGINTER_IMAGE_COUNT_INTER = store_thm(
    "BIGINTER_IMAGE_COUNT_INTER",
    ``∀n m f g. BIGINTER (IMAGE f (count n)) ∩ BIGINTER (IMAGE g (count m)) =
        BIGINTER (IMAGE (λx. if x < n then f x else g (x − n)) (count (n + m)))``,
    rpt strip_tac >>
    `∀x. x ∈ BIGINTER (IMAGE (λx. if x < n then f x else g (x − n)) (count (n + m))) ⇔
        x ∈ BIGINTER (IMAGE f (count n)) ∧ x ∈ BIGINTER (IMAGE g (count m))`
        suffices_by (rpt strip_tac >> fs[EXTENSION]) >>
    fs[IN_BIGINTER_IMAGE] >> strip_tac >> eq_tac >> rpt strip_tac
    >- (last_x_assum (qspec_then `y` assume_tac) >> rfs[])
    >- (last_x_assum (qspec_then `y + n` assume_tac) >> rfs[])
    >- (last_x_assum (qspec_then `x'` assume_tac) >>
        last_x_assum (qspec_then `x' - n` assume_tac) >>
        Cases_on `x' < n` >> rfs[])
);

val BIGUNION_IMAGE_COUNT_UNION = store_thm(
    "BIGUNION_IMAGE_COUNT_UNION",
    ``∀n m f g. BIGUNION (IMAGE f (count n)) ∪ BIGUNION (IMAGE g (count m)) =
        BIGUNION (IMAGE (λx. if x < n then f x else g (x − n)) (count (n + m)))``,
    rpt strip_tac >>
    `∀x. x ∈ BIGUNION (IMAGE (λx. if x < n then f x else g (x − n)) (count (n + m))) ⇔
        x ∈ BIGUNION (IMAGE f (count n)) ∨ x ∈ BIGUNION (IMAGE g (count m))`
        suffices_by (rpt strip_tac >> fs[EXTENSION]) >>
    fs[IN_BIGUNION_IMAGE] >> strip_tac >> eq_tac >> rpt strip_tac
    >- (Cases_on `x' < n` >> fs[] >> rw[]
        >- (`∃x'. x' < n ∧ x ∈ f x'` suffices_by fs[] >> EXISTS_TAC ``x': num`` >> fs[])
        >- (`∃x'. x' < m ∧ x ∈ g x'` suffices_by fs[] >> EXISTS_TAC ``x' - n: num`` >> fs[]))
    >- (EXISTS_TAC ``x': num`` >> fs[])
    >- (EXISTS_TAC ``x' + n: num`` >> fs[])    
);

val UNION_BIGINTER_IMAGE = store_thm(
    "UNION_BIGINTER_IMAGE",
    ``∀s t f. BIGINTER (IMAGE (λx. s ∪ f x) t) = s ∪ BIGINTER (IMAGE f t)``,
    rpt strip_tac >>
    `∀x. x ∈ BIGINTER (IMAGE (λx. s ∪ f x) t) ⇔ x ∈ s ∨ x ∈ BIGINTER (IMAGE f t)`
        suffices_by (strip_tac >> fs[EXTENSION]) >>
    fs[IN_BIGINTER_IMAGE] >> rpt strip_tac >> rpt strip_tac >> eq_tac >> rw[]
    >- (CCONTR_TAC >> fs[] >> RES_TAC)
    >- (fs[])
    >- (RES_TAC >> fs[])
);

val INTER_BIGUNION_IMAGE = store_thm(
    "INTER_BIGUNION_IMAGE",
    ``∀s t f. BIGUNION (IMAGE (λx. s ∩ f x) t) = s ∩ BIGUNION (IMAGE f t)``,
    rpt strip_tac >>
    `∀x. x ∈ BIGUNION (IMAGE (λx. s ∩ f x) t) ⇔ x ∈ s ∧ x ∈ BIGUNION (IMAGE f t)`
        suffices_by (strip_tac >> fs[EXTENSION]) >>
    fs[IN_BIGUNION_IMAGE] >> rpt strip_tac >> rpt strip_tac >> eq_tac >> rw[]
    >- (fs[])
    >- (EXISTS_TAC ``x':β`` >> fs[])
);

val UNION_BIGUNION_IMAGE = store_thm(
    "UNION_BIGUNION_IMAGE",
    ``∀s t f. t ≠ ∅ ⇒ BIGUNION (IMAGE (λx. s ∪ f x) t) = s ∪ BIGUNION (IMAGE f t)``,
    rw[] >> rw[EXTENSION,IN_BIGUNION_IMAGE] >> eq_tac >> rw[] >> fs[]
    >- (`∃x'. x' ∈ t ∧ x ∈ f x'` suffices_by rw[] >>
        EXISTS_TAC ``x' : β`` >> fs[])
    >- (fs[MEMBER_NOT_EMPTY])
    >- (EXISTS_TAC ``x' : β`` >> rw[])
);

val INTER_BIGINTER_IMAGE = store_thm(
    "INTER_BIGINTER_IMAGE",
    ``∀s t f. t ≠ ∅ ⇒ BIGINTER (IMAGE (λx. s ∩ f x) t) = s ∩ BIGINTER (IMAGE f t)``,
    rw[] >> rw[EXTENSION,IN_BIGINTER_IMAGE] >> eq_tac >> rw[] >> fs[MEMBER_NOT_EMPTY]
);

val UNION_BIGINTER_IMAGE_COMM = store_thm(
    "UNION_BIGINTER_IMAGE_COMM",
    ``∀s t f. BIGINTER (IMAGE (λx. f x ∪ s) t) = BIGINTER (IMAGE f t) ∪ s``,
    fs[UNION_BIGINTER_IMAGE,UNION_COMM]
);

val INTER_BIGUNION_IMAGE_COMM = store_thm(
    "INTER_BIGUNION_IMAGE_COMM",
    ``∀s t f. BIGUNION (IMAGE (λx. f x ∩ s) t) = BIGUNION (IMAGE f t) ∩ s``,
    fs[INTER_BIGUNION_IMAGE,INTER_COMM]
);

val UNION_BIGUNION_IMAGE_COMM = store_thm(
    "UNION_BIGUNION_IMAGE_COMM",
    ``∀s t f. t ≠ ∅ ⇒ BIGUNION (IMAGE (λx. f x ∪ s) t) = BIGUNION (IMAGE f t) ∪ s``,
    fs[UNION_BIGUNION_IMAGE,UNION_COMM]
);

val INTER_BIGINTER_IMAGE_COMM = store_thm(
    "INTER_BIGINTER_IMAGE_COMM",
    ``∀s t f. t ≠ ∅ ⇒ BIGINTER (IMAGE (λx. f x ∩ s) t) = BIGINTER (IMAGE f t) ∩ s``,
    fs[INTER_BIGINTER_IMAGE,INTER_COMM]
);

val BIGUNION_IMAGE_EQUAL = store_thm(
    "BIGUNION_IMAGE_EQUAL",
    ``∀f g s. (∀x. x ∈ s ⇒ (f x = g x)) ⇒
        (BIGUNION (IMAGE f s) = BIGUNION (IMAGE g s))``,
    rw[] >> `∀x. x ∈ BIGUNION (IMAGE f s) ⇔ x ∈ BIGUNION (IMAGE g s)`
        suffices_by (rw[] >> fs[EXTENSION]) >>
    fs[IN_BIGUNION_IMAGE] >> metis_tac[]
);

val PREIMAGE_o_INTER = store_thm(
    "PREIMAGE_o_INTER",
    ``∀X Y f g s. IMAGE f X ⊆ Y ⇒ PREIMAGE (g ∘ f) s ∩ X = PREIMAGE f (PREIMAGE g s ∩ Y) ∩ X``,
    rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[] >> fs[SUBSET_DEF,IN_IMAGE] >>
    last_x_assum irule >> qexists_tac `x` >> simp[]
);

val NUM_TO_PAIR_BIJ = store_thm(
    "NUM_TO_PAIR_BIJ",
    ``BIJ num_to_pair 𝕌(:num) (𝕌(:num) × 𝕌(:num))``,
    fs[BIJ_IFF_INV] >> EXISTS_TAC ``pair_to_num`` >>
    fs[pair_to_num_inv] >> rw[] >>
    assume_tac (ISPEC ``x:num#num`` ABS_PAIR_THM) >> fs[pair_to_num_inv]
);

val PAIR_TO_NUM_BIJ = store_thm(
    "PAIR_TO_NUM_BIJ",
    ``BIJ pair_to_num (𝕌(:num) × 𝕌(:num)) 𝕌(:num)``,
    fs[BIJ_IFF_INV] >> EXISTS_TAC ``num_to_pair`` >>
    fs[pair_to_num_inv] >> rw[] >>
    assume_tac (ISPEC ``x:num#num`` ABS_PAIR_THM) >> fs[pair_to_num_inv]
);

val FINITE_SURJ_COUNT_EQ = store_thm(
    "FINITE_SURJ_COUNT_EQ",
    ``∀s. FINITE s ⇔ ∃c n. SURJ c (count n) s``,
    rw[] >> eq_tac >> rw[]
    >- (Induct_on `s` >> rw[]
        >- (map_every EXISTS_TAC [``_ : num -> α``,``0 : num``] >> fs[count_def,SURJ_DEF])
        >- (map_every EXISTS_TAC [``λi : num. if i < n then (c i) else e : α``,``SUC n``] >>
            fs[count_def,SURJ_DEF] >> rw[]
            >- (EXISTS_TAC ``n:num`` >> fs[])
            >- (RES_TAC >> EXISTS_TAC ``y:num`` >> fs[])))
    >- (imp_res_tac FINITE_SURJ >> rfs[])
);

val FINITE_INJ_COUNT_EQ = store_thm(
    "FINITE_INJ_COUNT_EQ",
    ``∀s. FINITE s ⇔ ∃c n. INJ c s (count n)``,
    rw[] >> eq_tac >> rw[]
    >- (fs[FINITE_SURJ_COUNT_EQ] >> metis_tac[SURJ_IMP_INJ])
    >- (imp_res_tac inj_surj >> fs[] >> metis_tac[GSYM FINITE_SURJ_COUNT_EQ])
);

val ITSET_SING = store_thm(
    "ITSET_SING",
    ``∀f x a. ITSET f {x} a = f x a``,
    rw[] >> fs[ITSET_THM]
);

val SUBSET_IMP_DIFFS_SUBSET = store_thm(
    "SUBSET_IMP_DIFFS_SUBSET",
    ``∀a b s. a ⊆ b ⇒ s DIFF b ⊆ s DIFF a``,
    rw[SUBSET_DEF,DIFF_DEF] >> CCONTR_TAC >> fs[] >> RES_TAC
);

val DIFF_SING_EMPTY = store_thm(
    "DIFF_SING_EMPTY",
    ``∀s x. (s DIFF {x} = ∅) ⇔ (s = ∅) ∨ (s = {x})``,
    rw[] >> eq_tac >> rw[]
    >- (Cases_on `s = ∅` >> rw[] >> fs[EXTENSION] >> rw[] >>
        last_x_assum (fn th => map_every (fn tm => (qspec_then tm assume_tac) th) [`x'`,`x''`]) >>
        rfs[] >> fs[] >> CCONTR_TAC >> fs[])
    >- (rw[EMPTY_DIFF])
    >- (rw[DIFF_EQ_EMPTY])
);

val surj_countable = store_thm(
    "surj_countable",
    ``∀f s t. countable s ∧ SURJ f s t ⇒ countable t``,
    rw[] >> dxrule_then assume_tac image_countable >>
    pop_assum (qspec_then `f` assume_tac) >> irule subset_countable >>
    qexists_tac `IMAGE f s` >> rw[] >> fs[IMAGE_SURJ]
);

val preimage_bij_countable = store_thm(
    "preimage_bij_countable",
    ``∀f s a b. BIJ f a b ∧ s ⊆ b ∧ countable s ⇒ countable (PREIMAGE f s ∩ a)``,
    rw[] >> irule (INST_TYPE [alpha |-> ``:β``,beta |-> ``:α``] surj_countable) >>
    drule_then assume_tac BIJ_INV >> fs[] >> map_every qexists_tac [`g`,`s`] >>
    simp[SURJ_DEF,IN_PREIMAGE] >> fs[BIJ_ALT,EXISTS_UNIQUE_THM,FUNSET] >> rw[]
    >- (`x ∈ b` by fs[SUBSET_DEF] >> fs[])
    >- (`x ∈ b` by fs[SUBSET_DEF] >> fs[])
    >- (qexists_tac `f x` >> fs[])
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Reals *)
(*---------------------------------------------------------------------------*)

val sum_def = store_thm(
    "sum_def",
    ``(∀n f. sum (n,0) f = 0) ∧ ∀n m f. sum (n,SUC m) f = sum (n,m) f + f (n + m)``,
    rw[sum]
);

val prod_def = Define `(prod (n,0) f = 1) ∧
    (prod (n,SUC m) f = prod (n,m) f * f (n + m): real)`;

val PROD_EQ = store_thm(
    "PROD_EQ",
    ``∀f g m n. (∀r. m ≤ r ∧ r < n + m ⇒ f r = g r) ⇒ prod (m,n) f = (prod (m,n) g : real)``,
    NTAC 4 strip_tac >> Induct_on `n` >> rw[prod_def]
);

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

val REAL_SUB_GT = store_thm(
    "REAL_SUB_GT",
    ``∀x y. y − x < (0:real) ⇔ y < x``,
    rpt strip_tac >>
    `y − x < 0 ⇔ 0 < x - y` suffices_by fs[REAL_SUB_LT] >>
    `y − x = -(x − y)` by fs[REAL_NEG_SUB] >> fs[]
);

val ABS_REFL_IMP = store_thm(
    "ABS_REFL_IMP",
    ``∀x:real. (0 < x ⇒ (abs x = x)) ∧ (x < 0 ⇒ (abs x = -x)) ∧
        (¬(0 < x) ⇒ (abs x = -x)) ∧ (¬(x < 0) ⇒ (abs x = x))``,
    rw[abs] >> fs[REAL_NOT_LT]
    >- rw[REAL_LE_LT]
    >- (dxrule_all_then assume_tac REAL_LTE_TRANS >> fs[REAL_LT_REFL])
    >- (`x = 0` suffices_by rw[REAL_NEG_0] >> rw[GSYM REAL_LE_ANTISYM])
);

val SUM_GE0 = store_thm(
    "SUM_GE0",
    ``∀f n. (∀i. (i < n) ⇒ 0 ≤ f i) ⇒ 0 ≤ sum (0,n) f``,
    Induct_on `n` >> rpt strip_tac >> fs[sum] >>
    `0 ≤ sum (0,n) f` by fs[] >> `0 ≤ f n` by fs[] >>
    fs[REAL_LE_ADD]
);

val REAL_INV_CANCEL = store_thm(
    "REAL_INV_CANCEL",
    ``∀x:real. x ≠ 0 ⇒ (x * x⁻¹ = 1) ∧ (x⁻¹ * x = 1)``,
    strip_tac >> `x⁻¹ * x = x * x⁻¹` by rw[REAL_MUL_COMM] >>
    rw[GSYM real_div,REAL_DIV_REFL]
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

val disjoint_set_sum_remove_empty = store_thm(
    "disjoint_set_sum_remove_empty",
    ``∀n b f. (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ∧ (f ∅ = 0) ⇒
        ∃m a. (BIGUNION (IMAGE b (count n)) = BIGUNION (IMAGE a (count m))) ∧
        (sum (0,n) (f ∘ b) = sum (0,m) (f ∘ a)) ∧
        (∀i j. i < m ∧ j < m ∧ i ≠ j ⇒ DISJOINT (a i) (a j)) ∧
        ∀i. i < m ⇒ a i ≠ ∅ ∧ ∃j. j < n ∧ (b j = a i)``,
    rw[] >> Induct_on `n` >> fs[] >> rw[]
    >- (EXISTS_TAC ``0 : num`` >> fs[count_def,sum]) >>
    fs[BIGUNION_IMAGE_COUNT_SUC,sum] >>
    Cases_on `b n = ∅` >> fs[] >> rw[]
    >- (map_every EXISTS_TAC [``m : num``,``a : num -> α -> bool``] >> fs[count_def,sum] >>
        rw[] >> RES_TAC >> EXISTS_TAC ``j : num`` >> fs[]) >>
    map_every EXISTS_TAC [``SUC m : num``,
        ``(λi. if i < m then a i else b (n : num)) : num -> α -> bool``] >>
    fs[BIGUNION_IMAGE_COUNT_SUC,sum] >> rw[]
    >- (fs[Cong BIGUNION_IMAGE_EQUAL])
    >- (fs[Cong SUM_EQ])
    >- (NTAC 2 (pop_assum kall_tac) >> `∃j. j < n ∧ (b j = a i)` by fs[] >>
        pop_assum (assume_tac o GSYM) >> fs[DISJOINT_DEF,EXTENSION])
    >- (`∃k. k < n ∧ (b k = a j)` by fs[] >>
        pop_assum (assume_tac o GSYM) >> fs[DISJOINT_DEF,EXTENSION])
    >- (RES_TAC >> EXISTS_TAC ``j : num`` >> fs[])
    >- (EXISTS_TAC ``n : num`` >> fs[])
);

val SUM_EXTRACT = store_thm(
    "SUM_EXTRACT",
    ``∀n m c f. m < n ⇒ (sum (0,n) (λi. if i = m then f i + c else f i) = sum (0,n) f + c)``,
    strip_tac >> Induct_on `n` >> fs[sum] >> rw[]
    >- (fs[REAL_ADD_ASSOC] >> irule SUM_EQ >> rw[])
    >- (metis_tac[REAL_ADD_ASSOC,REAL_ADD_COMM])
);

val SUM_2D_FLATTEN = store_thm(
    "SUM_2D_FLATTEN",
    ``∀n ni f. ∃m g h. (sum (0,n) (λi. sum (0,ni i) (λj. f i j)) = sum (0,m) g) ∧
        BIJ h (count m) {(i,j) | i < n ∧ j < ni i} ∧
        ∀k. k < m ⇒ (UNCURRY f (h k) = g k)``,
    Induct_on `n` >> rw[sum] >- (qexists_tac `0` >> rw[sum]) >>
    Induct_on `ni n` >> rw[sum]
    >- (last_x_assum (assume_tac o GSYM) >> fs[sum] >>
        last_x_assum (qspecl_then [`ni`,`f`] assume_tac) >> fs[] >>
        map_every qexists_tac [`m`,`g`,`h`] >> rw[] >>
        `{(i,j) | i < SUC n ∧ j < ni i} = {(i,j) | i < n ∧ j < ni i}` suffices_by rw[] >>
        NTAC 3 (pop_assum kall_tac) >> rw[EXTENSION] >> eq_tac >> rw[] >>
        CCONTR_TAC >> `i = n` by fs[] >> fs[]) >>
    qpat_x_assum `_ = _` (assume_tac o GSYM) >> fs[sum] >>
    `∃ni'. ∀i. ((i = n) ⇒ (ni' i = v)) ∧ ((i ≠ n) ⇒ (ni' i = ni i))`
        by (rw[GSYM SKOLEM_THM] >> Cases_on `i = n` >> rw[]) >>
    last_x_assum (qspecl_then [`ni'`,`n`] assume_tac) >> rfs[] >>
    `∃g'. ∀k. ((k = m) ⇒ (g' k = f n v)) ∧ ((k < m) ⇒ (g' k = g k))` by (
        rw[GSYM SKOLEM_THM] >> Cases_on `k = m` >> rw[] >>
        Cases_on `k < m` >> rw[]) >>
    `∃h'. ∀k. ((k = m) ⇒ (h' k = (n,v))) ∧ ((k < m) ⇒ (h' k = h k))` by (
        rw[GSYM SKOLEM_THM] >> Cases_on `k = m` >> rw[] >>
        Cases_on `k < m` >> rw[]) >>
    map_every qexists_tac [`SUC m`,`g'`,`h'`] >> rw[sum,REAL_ADD_ASSOC]
    >- (`sum (0,m) g' = sum (0,m) g` by (irule SUM_EQ >> rw[]) >>
        qpat_x_assum `_ + _ = _` (assume_tac o GSYM) >> rw[] >>
        irule SUM_EQ >> rw[])
    >- (last_x_assum kall_tac >> fs[BIJ_ALT,FUNSET,EXISTS_UNIQUE_THM] >> rw[]
        >- (Cases_on `x < m` >> rw[]
            >- (`∃i j. (h x = (i,j)) ∧ i < SUC n ∧ j < ni' i` by fs[] >>
                map_every qexists_tac [`i`,`j`] >> rw[] >>
                qpat_x_assum `∀i. _ ∧ (_ ≠ _ ⇒ _)` (qspec_then `i` assume_tac) >>
                Cases_on `i = n` >> rw[])
            >- (NTAC 2 (qpat_x_assum `∀k. _` (qspec_then `x` assume_tac)) >>
                `x = m` by fs[] >> fs[]))
        >- (qpat_x_assum `∀y. _` (qspec_then `(i,j)` assume_tac) >>
            Cases_on `i = n` >> rw[]
            >- (qpat_x_assum `∀i. _ ∧ (_ ≠ _ ⇒ _)` (qspec_then `i` assume_tac) >>
                rfs[] >> fs[] >> rw[] >> Cases_on `j = ni' i` >> rw[]
                >- (qexists_tac `m` >> rw[])
                >- (`j < ni' i` by fs[] >> fs[] >> rw[] >> qexists_tac `x` >> rw[]))
            >- (qpat_x_assum `∀i. _ ∧ (_ ≠ _ ⇒ _)` (qspec_then `i` assume_tac) >>
                rfs[] >> fs[] >> rw[] >> rfs[] >> qexists_tac `x` >> rw[]))
        >- (qpat_x_assum `∀y. _` (qspec_then `(i,j)` assume_tac) >> rfs[] >>
            Q.RENAME_TAC [`y < SUC m`] >> Cases_on `i = n` >> rw[]
            >- (qpat_x_assum `∀i. _ ∧ (_ ≠ _ ⇒ _)` (qspec_then `i` assume_tac) >>
                rfs[] >> fs[] >> rw[] >> Cases_on `j = ni' i` >> rw[]
                >- (rfs[] >> rw[] >> Cases_on `x < m` >> Cases_on `y < m`
                    >- (NTAC 3 (qpat_x_assum `∀x. _` (qspec_then `x` assume_tac)) >>
                        rfs[] >> fs[] >> rw[])
                    >- (NTAC 3 (qpat_x_assum `∀x. _` (qspec_then `x` assume_tac)) >>
                        rfs[] >> fs[] >> rw[])
                    >- (NTAC 3 (qpat_x_assum `∀x. _` (qspec_then `y` assume_tac)) >>
                        rfs[] >> fs[] >> rw[])
                    >- (`x = m` by rw[] >> `y = m` by rw[] >> rw[]))
                >- (`j < ni' i` by rw[] >> fs[] >> rw[] >>
                    qpat_x_assum `∀x y. _` (qspecl_then [`x`,`y`] assume_tac) >>
                    Cases_on `x < m` >> Cases_on `y < m`
                    >- (qpat_x_assum `∀k. _` (fn th => map_every
                            (fn tm => (qspec_then tm assume_tac) th) [`x`,`y`]) >> rfs[])
                    >- (`y = m` by fs[] >> fs[] >> rw[] >>
                        qpat_x_assum `∀k. _` (fn th => map_every
                            (fn tm => (qspec_then tm assume_tac) th) [`x`,`m`]) >>
                        rfs[] >> fs[])
                    >- (`x = m` by fs[] >> fs[] >> rw[] >>
                        qpat_x_assum `∀k. _` (fn th => map_every
                            (fn tm => (qspec_then tm assume_tac) th) [`m`,`y`]) >>
                        rfs[] >> fs[] >> pop_assum (assume_tac o GSYM) >> fs[])
                    >- (`x = m` by rw[] >> `y = m` by rw[] >> rw[])))
            >- (qpat_x_assum `∀i. _ ∧ (_ ≠ _ ⇒ _)` (qspec_then `i` assume_tac) >>
                rfs[] >> fs[] >> rfs[] >>
                qpat_x_assum `∀x y. _` (qspecl_then [`x`,`y`] assume_tac) >>
                Cases_on `x < m` >> Cases_on `y < m`
                >- (qpat_x_assum `∀k. _` (fn th => map_every
                        (fn tm => (qspec_then tm assume_tac) th) [`x`,`y`]) >> rfs[])
                >- (`y = m` by fs[] >> fs[] >> rw[] >>
                    qpat_x_assum `∀k. _` (fn th => map_every
                        (fn tm => (qspec_then tm assume_tac) th) [`x`,`m`]) >>
                    rfs[] >> fs[])
                >- (`x = m` by fs[] >> fs[] >> rw[] >>
                    qpat_x_assum `∀k. _` (fn th => map_every
                        (fn tm => (qspec_then tm assume_tac) th) [`m`,`y`]) >>
                    rfs[] >> fs[] >> pop_assum (assume_tac o GSYM) >> fs[])
                >- (`x = m` by rw[] >> `y = m` by rw[] >> rw[]))))
    >- (NTAC 3 (qpat_x_assum `∀x. _` (qspec_then `k` assume_tac)) >> Cases_on `k = m` >> fs[])
);

val SUM_PERMUTE_BIJ = store_thm(
    "SUM_PERMUTE_BIJ",
    ``∀n f g. (∃p. p PERMUTES (count n) ∧ ∀i. i < n ⇒ (f (p i) = g i)) ⇒
        (sum (0,n) f = sum (0,n) g)``,
    rw[] >> `sum (0,n) g = sum (0,n) (λi. f (p i))` by (irule SUM_EQ >> rw[]) >>
    `sum (0,n) (λi. f (p i)) = sum (0,n) f` suffices_by rw[] >> pop_assum kall_tac >>
    irule SUM_PERMUTE_0 >> pop_assum kall_tac >> fs[BIJ_ALT] >> last_x_assum kall_tac >>
    metis_tac[]
);

val SUM_2D_BIJ = store_thm(
    "SUM_2D_BIJ",
    ``∀n ni m f g. (∃h. BIJ h (count m) {(i,j) | i < n ∧ j < ni i} ∧
        ∀k. k < m ⇒ (UNCURRY f (h k) = g k)) ⇒
        (sum (0,n) (λi. sum (0,ni i) (λj. f i j)) = sum (0,m) g)``,
    rw[] >> (qspecl_then [`n`,`ni`,`f`] assume_tac) SUM_2D_FLATTEN >> fs[] >>
    `m' = m` by (imp_res_tac FINITE_BIJ_CARD >> rfs[]) >>
    fs[] >> pop_assum kall_tac >> irule SUM_PERMUTE_BIJ >>
    drule_then assume_tac BIJ_INV >> fs[] >> Q.RENAME_TAC [`BIJ hpinv _ _`] >>
    `hpinv ∘ h PERMUTES count m` by (irule BIJ_COMPOSE >>
        qexists_tac `{(i,j) | i < n ∧ j < ni i}` >> rw[]) >>
    qexists_tac `hpinv ∘ h` >> rw[] >>
    `UNCURRY f (h i) = g i` by fs[] >> `hpinv (h i) < m` by fs[BIJ_ALT,FUNSET] >>
    `UNCURRY f (h' (hpinv (h i))) = g' (hpinv (h i))` by fs[] >>
    `h' (hpinv (h i)) = h i` suffices_by (rw[] >> fs[]) >> NTAC 3 (pop_assum kall_tac) >>
    qpat_x_assum `∀x. _` (qspec_then `h i` assume_tac) >> pop_assum irule >>
    fs[BIJ_ALT,FUNSET]
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Limits/Derivatives *)
(*---------------------------------------------------------------------------*)

val SUMS_SEQ_EQ = store_thm(
    "SUMS_SEQ_EQ",
    ``∀f g l. (f = g) ⇒ (f sums l ⇔ g sums l)``,
    rw[]
);

val TENDS_EQ = store_thm(
    "TENDS_EQ",
    ``∀f g l. (f = g) ⇒ (f --> l ⇔ g --> l)``,
    rw[]
);

val SEQ_OFFSET = store_thm(
    "SEQ_OFFSET",
    ``∀f l m. f --> l ⇔ (λn. f (n + m)) --> l``,
    rw[] >> Induct_on `m` >> rw[F_SIMP] >> pop_assum kall_tac >>
    (qspecl_then [`(λn. f (m + n))`,`l`] assume_tac) SEQ_SUC >> rw[] >> pop_assum kall_tac >>
    irule TENDS_EQ >> rw[FUN_EQ_THM] >> irule FUN_EQ >> rw[]
);

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

val closed_interval_def = Define `closed_interval a b = {x | a ≤ x ∧ x ≤ b}`;

val extreal_ln_def = Define
    `(extreal_ln (Normal x) = (if (x ≤ 0) then NegInf else Normal (ln x))) ∧
    (extreal_ln PosInf = PosInf) ∧ (extreal_ln NegInf = NegInf)`;

val _ = overload_on ("ln", Term `extreal_ln`);

val extreal_sum_def = Define `(extreal_sum (n,0) f = 0) ∧
    (extreal_sum (n,SUC m) f = extreal_sum (n,m) f + f (n + m): extreal)`;

val _ = overload_on ("sum", Term `extreal_sum`);

val extreal_prod_def = Define `(extreal_prod (n,0) f = 1) ∧
    (extreal_prod (n,SUC m) f = extreal_prod (n,m) f * f (n + m): extreal)`;

val _ = overload_on ("prod", Term `extreal_prod`);

val closed_interval_point = store_thm(
    "closed_interval_point",
    ``∀y. closed_interval y y = {y}``,
    strip_tac >> fs[closed_interval_def,EXTENSION,le_antisym]
);

val interval_3_right_closed_total = store_thm(
    "interval_3_right_closed_total",
    ``∀(x:extreal) a b. x ≤ a ∨ (a < x ∧ x ≤ b) ∨ b < x``,
    rw[] >> Cases_on `x ≤ a` >> Cases_on `x ≤ b` >> fs[GSYM extreal_lt_def]
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

val NM1_EQ_M1 = store_thm(
    "NM1_EQ_M1",
    ``Normal (-1) = -1``,
    `Normal (-1) = -(Normal 1)` suffices_by fs[N1_EQ_1] >> fs[extreal_ainv_def]
);

val zero_not_infty = store_thm(
    "zero_not_infty",
    ``PosInf ≠ 0 ∧ 0 ≠ PosInf ∧ NegInf ≠ 0 ∧ 0 ≠ NegInf``,
    rw[GSYM N0_EQ_0]
);

val extreal_abs_alt = store_thm(
    "extreal_abs_alt",
    ``∀(x : extreal). abs x = if 0 ≤ x then x else -x``,
    rw[] >> Cases_on `x` >> fs[GSYM N0_EQ_0,extreal_le_def] >> rw[extreal_abs_def] >>
    rw[ABS_REFL,extreal_ainv_def] >> rw[abs]
);

val extreal_mul_alt = store_thm(
    "extreal_mul_alt",
    ``∀x. (PosInf * x = if x = 0 then 0 else if 0 < x then PosInf else NegInf) ∧
        (x * PosInf = if x = 0 then 0 else if 0 < x then PosInf else NegInf) ∧
        (NegInf * x = if x = 0 then 0 else if 0 < x then NegInf else PosInf) ∧
        (x * NegInf = if x = 0 then 0 else if 0 < x then NegInf else PosInf)``,
    strip_tac >> Cases_on `x` >> rw[GSYM N0_EQ_0,extreal_mul_def,extreal_lt_alt]
);

val mul_infty = store_thm(
    "mul_infty",
    ``∀x. (x < 0 ⇒ (NegInf * x = PosInf)) ∧ (x < 0 ⇒ (x * NegInf = PosInf)) ∧
        (x < 0 ⇒ (PosInf * x = NegInf)) ∧ (x < 0 ⇒ (x * PosInf = NegInf)) ∧
        ((x = 0) ⇒ (NegInf * x = 0)) ∧ ((x = 0) ⇒ (x * NegInf = 0)) ∧
        ((x = 0) ⇒ (PosInf * x = 0)) ∧ ((x = 0) ⇒ (x * PosInf = 0)) ∧
        (0 < x ⇒ (NegInf * x = NegInf)) ∧ (0 < x ⇒ (x * NegInf = NegInf)) ∧
        (0 < x ⇒ (PosInf * x = PosInf)) ∧ (0 < x ⇒ (x * PosInf = PosInf))``,
    rw[extreal_mul_alt,lt_refl] >> CCONTR_TAC >> fs[] >>
    dxrule_all_then assume_tac lt_trans >> fs[lt_refl]
);

val neq_neg = store_thm(
    "neq_neg",
    ``∀x y. (-x ≠ -y) ⇔ (x ≠ y)``,
    rpt strip_tac >> eq_tac >> strip_tac >> fs[eq_neg]
);

val mul_neq_zero = store_thm(
    "mul_neq_zero",
    ``∀x y. x * y ≠ 0 ⇒ x ≠ 0 ∧ y ≠ 0``,
    rw[] >> CCONTR_TAC >> fs[mul_lzero,mul_rzero]
);

val abs_mul = store_thm(
    "abs_mul",
    ``∀x y. abs (x * y) = abs x * abs y``,
    rw[] >> Cases_on `x` >> Cases_on `y` >> rw[extreal_mul_def,extreal_abs_def] >>
    fs[ABS_0] >> rfs[ABS_REFL_IMP,REAL_NEG_EQ0] >> rw[ABS_MUL] >>
    (qspecl_then [`r`,`0`] assume_tac) REAL_LT_TOTAL >> fs[] >> fs[]
);

val abs_0 = store_thm(
    "abs_0",
    ``abs 0 = 0``,
    rw[GSYM N0_EQ_0,extreal_abs_def,ABS_0]
);

val abs_nz = store_thm(
    "abs_nz",
    ``∀x. x ≠ 0 ⇔ 0 < abs x``,
    rw[] >> Cases_on `x` >> rw[GSYM N0_EQ_0,extreal_abs_def,extreal_lt_alt,ABS_NZ]
);

val abs_zero = store_thm(
    "abs_zero",
    ``∀x. (abs x = 0) ⇔ (x = 0)``,
    rw[] >> Cases_on `x` >> rw[extreal_abs_def,GSYM N0_EQ_0,ABS_ZERO]
);

val abs_abs = store_thm(
    "abs_abs",
    ``∀x. abs (abs x) = abs x``,
    rw[] >> Cases_on `x` >> rw[extreal_abs_def,ABS_ABS]
);

val abs_pos_fun = store_thm(
    "abs_pos_fun",
    ``∀f. (∀x. 0 ≤ f x) ⇒ (abs ∘ f = f)``,
    rw[o_DEF,FUN_EQ_THM,abs_refl]
);

val extreal_prod_eq = store_thm(
    "extreal_prod_eq",
    ``∀(f:num -> extreal) g m n. (∀r. m ≤ r ∧ r < n + m ⇒ f r = g r) ⇒ prod (m,n) f = prod (m,n) g``,
    Induct_on `n` >> rw[extreal_prod_def] >> `prod (m,n) f = prod (m,n) g` by fs[] >> rw[]
);

val extreal_prod_normal = store_thm(
    "extreal_prod_normal",
    ``∀n m f. prod (n,m) (Normal ∘ f) = Normal (prod (n,m) f)``,
    Induct_on `m` >> rw[extreal_prod_def,prod_def,N1_EQ_1,extreal_mul_def]
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

val EXTREAL_SUM_IMAGE_COUNT_0 = store_thm(
    "EXTREAL_SUM_IMAGE_COUNT_0",
    ``∀f. SIGMA f (count 0) = 0``,
    rw[] >> fs[EXTREAL_SUM_IMAGE_DEF,ITSET_EMPTY]
);

val EXTREAL_SUM_IMAGE_COUNT_1 = store_thm(
    "EXTREAL_SUM_IMAGE_COUNT_1",
    ``∀f. SIGMA f (count 1) = f 0``,
    rw[] >> `count 1 = {0}` by fs[count_def,EXTENSION] >>
    fs[EXTREAL_SUM_IMAGE_DEF,ITSET_SING,add_rzero]
);

val EXTREAL_SUM_IMAGE_COUNT_SUC = store_thm(
    "EXTREAL_SUM_IMAGE_COUNT_SUC",
    ``∀f n. SIGMA f (count (SUC n)) = (SIGMA f (count n)) + f n``,
    rw[] >> `count (SUC n) = (count n) ∪ {n}` by fs[count_def,EXTENSION] >>
    fs[EXTREAL_SUM_IMAGE_DISJOINT_UNION,EXTREAL_SUM_IMAGE_SING]
);

val ext_suminf_pos = store_thm(
    "ext_suminf_pos",
    ``∀f. (∀i. 0 ≤ f i) ⇒ 0 ≤ suminf f``,
    rw[] >> fs[ext_suminf_def] >>
    `f 0 ∈ IMAGE (λn. SIGMA f (count n)) 𝕌(:num)` by(
        fs[IMAGE_DEF] >> EXISTS_TAC ``1 : num`` >> fs[EXTREAL_SUM_IMAGE_COUNT_1]) >>
    Q.ABBREV_TAC `sigs = IMAGE (λn. SIGMA f (count n)) 𝕌(:num)` >>
    fs[IN_APP] >> pop_assum kall_tac >> dxrule_then assume_tac le_sup_imp >>
    `0 ≤ f 0` by fs[] >> drule_all_then assume_tac le_trans >> fs[]
);

val le_sup_imp_alt = store_thm(
    "le_sup_imp_alt",
    ``∀p x. x ∈ p ⇒ x ≤ sup p``,
    rw[] >> fs[IN_APP,le_sup_imp]
);

val sums_to_ext_suminf = store_thm(
    "sums_to_ext_suminf",
    ``∀f s. (∀i. 0 ≤ f i) ⇒ ((suminf (λi. Normal (f i)) = Normal s) ⇔ f sums s)``,
    rw[] >> eq_tac >> rw[]
    >- (drule_then assume_tac ext_suminf_suminf >> rfs[] >>
        irule SUMMABLE_SUM >> irule POS_SUMMABLE >> pop_assum kall_tac >> rw[] >>
        EXISTS_TAC ``s : real`` >> rw[] >>
        fs[GSYM REAL_SUM_IMAGE_COUNT] >> fs[GSYM extreal_le_def,GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
        pop_assum (assume_tac o GSYM) >> fs[] >> pop_assum kall_tac >>
        fs[ext_suminf_def] >> irule le_sup_imp_alt >> fs[IN_IMAGE] >>
        EXISTS_TAC ``n : num`` >> fs[])
    >- (`suminf (λi. Normal (f i)) ≠ PosInf` suffices_by (rw[] >>
            map_every (drule_all_then assume_tac) [ext_suminf_suminf,SUM_UNIQ] >> fs[]) >>
        `suminf (λi. Normal (f i)) ≤ Normal s` suffices_by
            (CCONTR_TAC >> fs[] >> fs[extreal_le_def]) >>
        rw[ext_suminf_def,sup_le] >> rw[EXTREAL_SUM_IMAGE_NORMAL,extreal_le_def,REAL_SUM_IMAGE_COUNT] >>
        fs[SUMS_EQ] >> pop_assum (assume_tac o GSYM) >> rw[] >>
        irule SER_POS_LE >> rw[])
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
    >- (`Normal 0 < Normal z` by fs[extreal_lt_alt] >>
        fs[N0_EQ_0,le_lt,le_lmul_imp])
    >- (`Normal 0 < Normal z` by fs[extreal_lt_alt] >> fs[N0_EQ_0] >>
        `Normal z ≠ PosInf` by fs[] >>
        imp_res_tac inv_pos >> `0 < inv (Normal z)` by fs[inv_1over] >>
        `0 ≤ inv (Normal z)` by fs[lt_le] >>
        `inv (Normal z) * (Normal z * x) ≤ inv (Normal z) * (Normal z * y)`
            by imp_res_tac le_lmul_imp >>
        `z ≠ 0` by fs[REAL_POS_NZ] >>
        fs[extreal_inv_def,mul_assoc,extreal_mul_def,REAL_MUL_LINV,N1_EQ_1,mul_lone])
);

val sup_mul_mono = store_thm(
    "sup_mul_mono",
    ``∀f g. (∀n. 0 ≤ f n) ∧ (∀n. 0 ≤ g n) ∧ mono_increasing f ∧ mono_increasing g ⇒
        (sup (IMAGE (λn. f n * g n) 𝕌(:num)) = sup (IMAGE f 𝕌(:num)) * sup (IMAGE g 𝕌(:num)))``,
    rw[] >> Cases_on `(sup (IMAGE f 𝕌(:num)) = 0) ∨ (sup (IMAGE g 𝕌(:num)) = 0)`
    >- (fs[mul_lzero,mul_rzero]
        >- (`∀n. f n = 0` by (rw[] >>
                (qspecl_then [`(IMAGE f 𝕌(:num))`,`f n`] assume_tac) le_sup_imp >>
                rfs[IMAGE_DEF] >> rw[GSYM le_antisym] >> pop_assum irule >>
                qexists_tac `n` >> rw[]) >>
            `(λn. f n * g n) = (λn. 0)` by rw[FUN_EQ_THM,mul_lzero] >>
            rw[] >> irule sup_const_over_set >> rw[])
        >- (`∀n. g n = 0` by (rw[] >>
                (qspecl_then [`(IMAGE g 𝕌(:num))`,`g n`] assume_tac) le_sup_imp >>
                rfs[IMAGE_DEF] >> rw[GSYM le_antisym] >> pop_assum irule >>
                qexists_tac `n` >> rw[]) >>
            `(λn. f n * g n) = (λn. 0)` by rw[FUN_EQ_THM,mul_rzero] >>
            rw[] >> irule sup_const_over_set >> rw[])) >>
    fs[] >>
    `∃k. 0 < f k ∧ 0 < g k` by (
        `∃i. 0 < f i` by (CCONTR_TAC >> fs[extreal_lt_def] >>
            `∀n. f n = 0` by rw[GSYM le_antisym] >>
            `(IMAGE f 𝕌(:num)) = (λy. y = 0)` by rw[IMAGE_DEF,FUN_EQ_THM] >>
            fs[sup_const]) >>
        `∃j. 0 < g j` by (CCONTR_TAC >> fs[extreal_lt_def] >>
            `∀n. g n = 0` by rw[GSYM le_antisym] >>
            `(IMAGE g 𝕌(:num)) = (λy. y = 0)` by rw[IMAGE_DEF,FUN_EQ_THM] >>
            fs[sup_const]) >>
        qexists_tac `MAX i j` >> fs[ext_mono_increasing_def] >>
        qpat_x_assum `∀m n. _` (qspecl_then [`j`, `MAX i j`] assume_tac) >>
        qpat_x_assum `∀m n. _` (qspecl_then [`i`, `MAX i j`] assume_tac) >> rfs[] >>
        metis_tac[lte_trans]) >>
    `0 < sup (IMAGE f 𝕌(:num)) ∧ 0 < sup (IMAGE g 𝕌(:num))` by (
        (qspecl_then [`(IMAGE f 𝕌(:num))`,`f k`] assume_tac) le_sup_imp >>
        (qspecl_then [`(IMAGE g 𝕌(:num))`,`g k`] assume_tac) le_sup_imp >>
        rfs[IMAGE_DEF] >> metis_tac[lte_trans]) >>
    Cases_on `(sup (IMAGE f 𝕌(:num)) = PosInf) ∨ (sup (IMAGE g 𝕌(:num)) = PosInf)`
    >- (fs[extreal_mul_alt]
        >- (`(λn. f n * g n) = (λn. g n * f n)` by rw[FUN_EQ_THM,mul_comm] >>
            `∀f:num->extreal g. (f = g) ⇒ (IMAGE f 𝕌(:num) = IMAGE g 𝕌(:num))` by rw[] >>
            pop_assum (dxrule_then assume_tac) >>
            `∀s t. (s = t) ⇒ (sup s = sup t)` by rw[] >>
            pop_assum (dxrule_then assume_tac) >>
            `sup (IMAGE (λn. g n * f n) 𝕌(:num)) = PosInf` suffices_by (rw[] >> fs[]) >>
            pop_assum kall_tac >>
            `sup (IMAGE (λn. g k * f n) 𝕌(:num)) ≤ sup (IMAGE (λn. g n * f n) 𝕌(:num))` by (
                irule sup_le_sup_imp >> rw[IMAGE_DEF] >>
                qexists_tac `g (MAX k n) * f (MAX k n)` >> rw[]
                >- (qexists_tac `MAX k n` >> rw[])
                >- (irule le_mul2 >> fs[ext_mono_increasing_def])) >>
            `sup (IMAGE (λn. g k * f n) 𝕌(:num)) = PosInf` suffices_by (CCONTR_TAC >> fs[] >>
                Cases_on `sup (IMAGE (λn. g n * f n) 𝕌(:num))` >> fs[extreal_le_def]) >>
            pop_assum kall_tac >> Cases_on `g k` >> fs[extreal_lt_alt] >> rw[]
            >- (`(IMAGE (λn. PosInf * f n) 𝕌(:num)) PosInf` by (rw[IMAGE_DEF] >>
                    qexists_tac `k` >> rw[extreal_mul_alt] >> fs[lt_refl]) >>
                dxrule_then assume_tac le_sup_imp >>
                Cases_on `sup (IMAGE (λn. PosInf * f n) 𝕌(:num))` >> fs[extreal_le_def])
            >- (fs[GSYM N0_EQ_0,extreal_lt_alt] >> fs[N0_EQ_0] >> rw[] >>
                (qspecl_then [`f`,`r`] assume_tac) (INST_TYPE [alpha |-> ``:num``] sup_cmul) >>
                rfs[REAL_LT_LE,extreal_mul_def]))
        >- (`sup (IMAGE (λn. f k * g n) 𝕌(:num)) ≤ sup (IMAGE (λn. f n * g n) 𝕌(:num))` by (
                irule sup_le_sup_imp >> rw[IMAGE_DEF] >>
                qexists_tac `f (MAX k n) * g (MAX k n)` >> rw[]
                >- (qexists_tac `MAX k n` >> rw[])
                >- (irule le_mul2 >> fs[ext_mono_increasing_def])) >>
            `sup (IMAGE (λn. f k * g n) 𝕌(:num)) = PosInf` suffices_by (CCONTR_TAC >> fs[] >>
                Cases_on `sup (IMAGE (λn. f n * g n) 𝕌(:num))` >> fs[extreal_le_def]) >>
            pop_assum kall_tac >> Cases_on `f k` >> fs[extreal_lt_alt] >> rw[]
            >- (`(IMAGE (λn. PosInf * g n) 𝕌(:num)) PosInf` by (rw[IMAGE_DEF] >>
                    qexists_tac `k` >> rw[extreal_mul_alt] >> fs[lt_refl]) >>
                dxrule_then assume_tac le_sup_imp >>
                Cases_on `sup (IMAGE (λn. PosInf * g n) 𝕌(:num))` >> fs[extreal_le_def])
            >- (fs[GSYM N0_EQ_0,extreal_lt_alt] >> fs[N0_EQ_0] >> rw[] >>
                (qspecl_then [`g`,`r`] assume_tac) (INST_TYPE [alpha |-> ``:num``] sup_cmul) >>
                rfs[REAL_LT_LE,extreal_mul_def]))) >>
    fs[] >> Cases_on `sup (IMAGE f 𝕌(:num))` >> Cases_on `sup (IMAGE g 𝕌(:num))` >>
    fs[GSYM N0_EQ_0,extreal_lt_alt] >> fs[N0_EQ_0] >> rw[extreal_mul_def] >>
    Q.RENAME_TAC [`_ = Normal (x * y)`] >> NTAC 2 (qpat_x_assum `_ ≠ 0` kall_tac) >>
    `∃rf. (λn. (Normal (rf n))) = f` by (rw[FUN_EQ_THM,GSYM SKOLEM_THM] >>
        `0 ≤ f n` by rw[] >> Cases_on `f n` >> fs[GSYM N0_EQ_0,extreal_le_def] >>
        rw[] >> fs[N0_EQ_0] >>
        `(IMAGE f 𝕌(:num)) PosInf` by (rw[IMAGE_DEF] >> qexists_tac `n` >> rw[]) >>
        dxrule_then assume_tac le_sup_imp >> rfs[extreal_le_def]) >>
    `∃rg. (λn. (Normal (rg n))) = g` by (rw[FUN_EQ_THM,GSYM SKOLEM_THM] >>
        `0 ≤ g n` by rw[] >> Cases_on `g n` >> fs[GSYM N0_EQ_0,extreal_le_def] >>
        rw[] >> fs[N0_EQ_0] >>
        `(IMAGE g 𝕌(:num)) PosInf` by (rw[IMAGE_DEF] >> qexists_tac `n` >> rw[]) >>
        dxrule_then assume_tac le_sup_imp >> rfs[extreal_le_def]) >>
    `mono_increasing rf ∧ mono_increasing rg ∧ mono_increasing (λn. rf n * rg n)` by (
        NTAC 2 (qpat_x_assum `(λn. Normal _ ) = _` (assume_tac o GSYM)) >>
        fs[mono_increasing_suc,ext_mono_increasing_suc,extreal_le_def,GSYM N0_EQ_0] >>
        rw[] >> irule REAL_LE_MUL2 >> rw[]) >>
    map_every (fn tms => (qspecl_then tms assume_tac) (GSYM sup_seq)) [[`rf`,`x`],[`rg`,`y`]] >>
    (qspecl_then [`λn. rf n * rg n`,`x * y`] assume_tac) sup_seq >>
    rfs[GSYM extreal_mul_def,SEQ_MUL] >> rw[]
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

val EXP_LE_1 = store_thm(
    "EXP_LE_1",
    ``∀x. (0:real) ≤ x ⇒ 1 ≤ exp x``,
    rpt strip_tac >> Cases_on `x = 0` >> fs[EXP_0] >>
    `0 < x` by fs[REAL_LT_LE] >>
    `1 < exp x` by fs[EXP_LT_1] >>
    fs[REAL_LT_LE]
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

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Measurable Sets and Functions *)
(*---------------------------------------------------------------------------*)

val a_e_def = Define `a_e m P ⇔ null_set m (m_space m DIFF P)`;

val id_msp_def = Define `id_msp = ({ARB:α},POW {ARB:α},(λfs:α->bool. if fs = ∅ then (0:real) else 1))`;

val Borel_2D_def = Define `Borel_2D = sigma (𝕌(:extreal) × 𝕌(:extreal))
    (prod_sets (subsets Borel) (subsets Borel))`;

val pos_simple_fn_alt = store_thm(
    "pos_simple_fn_alt",
    ``∀m f s e a. pos_simple_fn m f s e a ⇔ (∀t. 0 ≤ f t) ∧
        (∀i t. i ∈ s ∧ t ∈ e i ⇒ (f t = Normal (a i))) ∧
        (∀i. i ∈ s ⇒ e i ∈ measurable_sets m) ∧ FINITE s ∧
        (∀i. i ∈ s ⇒ 0 ≤ a i) ∧
        (∀i j. i ∈ s ∧ j ∈ s ∧ i ≠ j ⇒ DISJOINT (e i) (e j)) ∧
        (BIGUNION (IMAGE e s) = m_space m)``,
    rw[pos_simple_fn_def] >> eq_tac >> rw[]
    >- (`t ∈ m_space m` by (fs[EXTENSION,IN_BIGUNION_IMAGE] >> metis_tac[]) >>
        RES_TAC >> rw[] >> NTAC 4 (pop_assum kall_tac) >>
        dxrule_then assume_tac EXTREAL_SUM_IMAGE_ZERO_DIFF >>
        pop_assum (qspecl_then [`(λi. Normal (a i) * indicator_fn (e i) t)`,
            `s DIFF {i}`] assume_tac) >>
        `(∀x. x ∈ s DIFF {i} ⇒ ((λi. Normal (a i) * indicator_fn (e i) t) x = 0))` by (
            pop_assum kall_tac >> rw[indicator_fn_def,mul_rzero,mul_rone] >>
            qpat_x_assum `∀j. _` (dxrule_all_then assume_tac) >>
            rfs[DISJOINT_DEF,EXTENSION] >> pop_assum (qspec_then `t` assume_tac) >> rfs[]) >>
        fs[DIFF_DIFF2] >> NTAC 2 (pop_assum kall_tac) >>
        `s ∩ {i} = {i}` by (rw[EXTENSION] >> eq_tac >> rw[]) >>
        rw[EXTREAL_SUM_IMAGE_SING] >> pop_assum kall_tac >>
        rw[indicator_fn_def,mul_rone])
    >- (`∃i. i ∈ s ∧ t ∈ e i` by (fs[EXTENSION,IN_BIGUNION_IMAGE] >> metis_tac[]) >>
        dxrule_then assume_tac EXTREAL_SUM_IMAGE_ZERO_DIFF >>
        pop_assum (qspecl_then [`(λi. Normal (a i) * indicator_fn (e i) t)`,
            `s DIFF {i}`] assume_tac) >>
        `(∀x. x ∈ s DIFF {i} ⇒ ((λi. Normal (a i) * indicator_fn (e i) t) x = 0))` by (
            pop_assum kall_tac >> rw[indicator_fn_def,mul_rzero,mul_rone] >>
            qpat_x_assum `∀i j. _` (dxrule_all_then assume_tac) >>
            rfs[DISJOINT_DEF,EXTENSION] >> pop_assum (qspec_then `t` assume_tac) >> rfs[]) >>
        fs[DIFF_DIFF2] >> NTAC 2 (pop_assum kall_tac) >>
        `s ∩ {i} = {i}` by (rw[EXTENSION] >> eq_tac >> rw[]) >>
        rw[EXTREAL_SUM_IMAGE_SING] >> pop_assum kall_tac >>
        rw[indicator_fn_def,mul_rone])
);

val SPACE_BOREL_2D = store_thm(
    "SPACE_BOREL_2D",
    ``space Borel_2D = 𝕌(:extreal) × 𝕌(:extreal)``,
    simp[Borel_2D_def,SPACE_SIGMA]
);

val SIGMA_ALGEBRA_BOREL_2D = store_thm(
    "SIGMA_ALGEBRA_BOREL_2D",
    ``sigma_algebra Borel_2D``,
    rw[Borel_2D_def] >> irule SIGMA_ALGEBRA_SIGMA >>
    rw[subset_class_def,space_def,subsets_def,SUBSET_DEF]
);

val id_msp_measure_space = store_thm(
    "id_msp_measure_space",
    ``measure_space id_msp``,
    rw[measure_space_def,id_msp_def]
    >- (rw[m_space_def,measurable_sets_def] >>
        rw[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def] >>
        fs[IN_POW_SING,SUBSET_POW_SING,BIGUNION_POW])
    >- (rw[positive_def,measurable_sets_def,measure_def] >> fs[IN_POW_SING])
    >- (rw[countably_additive_def,measurable_sets_def,measure_def] >> fs[FUNSET,IN_POW_SING]
        >- (Cases_on `IMAGE f 𝕌(:num) = {∅}` >> fs[] >>
            `∃i. f i = {ARB}` by (CCONTR_TAC >> fs[] >> rfs[IMAGE_DEF,EXTENSION]) >>
            `(λfs. if fs = ∅ then 0 else 1) ∘ f sums 1 ⇔ (λj. if j = i then 1 else 0) sums 1` by (
                irule SUMS_SEQ_EQ >> rw[FUN_EQ_THM] >> Cases_on `j = i` >> fs[] >>
                last_x_assum (qspec_then `j` assume_tac) >> last_x_assum (dxrule_then assume_tac) >>
                rfs[DISJOINT_DEF] >> rfs[]) >>
            rw[] >> pop_assum kall_tac >> rw[sums] >>
            `(λn. sum (0,n) (λj. if j = i then 1 else 0)) --> 1 ⇔ (λn. if i < n then 1 else 0) --> 1` by (
                irule TENDS_EQ >> rw[FUN_EQ_THM] >> Induct_on `n` >> rw[sum]) >>
            rw[] >> pop_assum kall_tac >>
            (qspecl_then [`(λn. if i < n then 1 else 0)`,`1`,`SUC i`] assume_tac) SEQ_OFFSET >>
            fs[] >> pop_assum kall_tac >> rw[SEQ_CONST])
        >- (`∀i. f i = ∅` by (CCONTR_TAC >> fs[] >>
                last_x_assum (qspec_then `i` assume_tac) >> rfs[] >>
                `{ARB} ∈ IMAGE f 𝕌(:num)` by (rw[IMAGE_DEF] >> qexists_tac `i` >> rw[]) >>
                Q.RENAME_TAC [`{ARB} ∈ img`] >> rfs[]) >>
            `(λfs. if fs = ∅ then 0 else 1) ∘ f sums 0 ⇔ (λj. 0) sums 0` by (
                irule SUMS_SEQ_EQ >> rw[FUN_EQ_THM]) >>
            rw[sums,SUM_0,SEQ_CONST]))
);

val SIGMA_ALGEBRA_SPACE = store_thm(
    "SIGMA_ALGEBRA_SPACE",
    ``∀a. sigma_algebra a ⇒ space a ∈ subsets a``,
    rw[] >> irule ALGEBRA_SPACE >> fs[sigma_algebra_def]
);

val POW_SUBSET_CLASS = store_thm(
    "POW_SUBSET_CLASS",
    ``∀sp. subset_class sp (POW sp)``,
    rw[subset_class_def,POW_DEF]
);

val ALGEBRA_SUBSETS_SUBSET_SPACE = store_thm(
    "ALGEBRA_SUBSETS_SUBSET_SPACE",
    ``∀a s. algebra a ∧ s ∈ subsets a ⇒ s ⊆ space a``,
    rw[] >> fs[algebra_def,subset_class_def]
);

val ALGEBRA_FINITE_INTER = store_thm(
    "ALGEBRA_FINITE_INTER",
    ``∀a s t. algebra a ∧ s ⊆ subsets a ∧ s ≠ ∅ ∧ FINITE s ⇒ BIGINTER s ∈ subsets a``,
    strip_tac >>
    `∀s. FINITE s ⇒ algebra a ∧ s ⊆ subsets a ∧ s ≠ ∅ ⇒ BIGINTER s ∈ subsets a` suffices_by rw[] >>
    Induct_on `s` >> rw[] >> fs[] >> Cases_on `s = ∅` >> rw[] >> fs[ALGEBRA_INTER]
);

val ALGEBRA_FINITE_UNION = store_thm(
    "ALGEBRA_FINITE_UNION",
    ``∀a s t. algebra a ∧ s ⊆ subsets a ∧ FINITE s ⇒ BIGUNION s ∈ subsets a``,
    strip_tac >>
    `∀s. FINITE s ⇒ algebra a ∧ s ⊆ subsets a ⇒ BIGUNION s ∈ subsets a` suffices_by rw[] >>
    Induct_on `s` >> rw[] >> fs[ALGEBRA_EMPTY,ALGEBRA_UNION]
);

val SIGMA_ALGEBRA_INTER = store_thm(
    "SIGMA_ALGEBRA_INTER",
    ``∀a s t. sigma_algebra a ∧ s ∈ subsets a ∧ t ∈ subsets a ⇒ s ∩ t ∈ subsets a``,
    rw[] >> irule ALGEBRA_INTER >> fs[sigma_algebra_def] >> simp[]
);

val SIGMA_ALGEBRA_COUNTABLE_INTER = store_thm(
    "SIGMA_ALGEBRA_COUNTABLE_INTER",
    ``∀a c. sigma_algebra a ∧ c ≠ ∅ ∧ countable c ∧ c ⊆ subsets a ⇒ BIGINTER c ∈ subsets a``,
    rw[] >> (dxrule_then assume_tac) SIGMA_ALGEBRA_FN_BIGINTER >>
    rfs[COUNTABLE_ENUM] >> last_x_assum irule >> simp[FUNSET] >> rw[] >>
    fs[SUBSET_DEF] >> rw[] >> last_x_assum irule >> qexists_tac `x` >> simp[]
);

val SIGMA_SMALLEST = store_thm(
    "SIGMA_SMALLEST",
    ``∀sp stsa stsb. stsa ⊆ stsb ∧ sigma_algebra (sp,stsb) ⇒
        subsets (sigma sp stsa) ⊆ stsb``,
    rw[sigma_def,subsets_def,SUBSET_DEF]
);

val MEASURE_SPACE_IN_M_SPACE = store_thm(
    "MEASURE_SPACE_IN_M_SPACE",
    ``∀m s x. measure_space m ∧ s ∈ measurable_sets m ∧ x ∈ s ⇒ x ∈ m_space m``,
    rw[] >> (dxrule_all_then assume_tac) MEASURE_SPACE_IN_MSPACE >> simp[]
);

val MEASURE_SPACE_COMPL = store_thm(
    "MEASURE_SPACE_COMPL",
    ``∀m s. measure_space m ∧ s ∈ measurable_sets m ⇒ (m_space m DIFF s) ∈ measurable_sets m``,
    rw[] >> irule MEASURE_SPACE_DIFF >> rw[MEASURE_SPACE_MSPACE_MEASURABLE]
);

val MEASURE_SPACE_SIGMA_ALGEBRA = store_thm(
    "MEASURE_SPACE_SIGMA_ALGEBRA",
    ``∀m. measure_space m ⇒ sigma_algebra (m_space m,measurable_sets m)``,
    rw[measure_space_def]
);

val MEASURE_SPACE_ALGEBRA = store_thm(
    "MEASURE_SPACE_ALGEBRA",
    ``∀m. measure_space m ⇒ algebra (m_space m,measurable_sets m)``,
    fs[measure_space_def,sigma_algebra_def]
);

val MEASURE_SPACE_SUBSET_CLASS = store_thm(
    "MEASURE_SPACE_SUBSET_CLASS",
    ``∀m. measure_space m ⇒ subset_class (m_space m) (measurable_sets m)``,
    fs[measure_space_def,sigma_algebra_def,algebra_def,space_def,subsets_def]
);

val MEASURE_POSITIVE = store_thm(
    "MEASURE_POSITIVE",
    ``∀m s. measure_space m ∧ s ∈ measurable_sets m ⇒ 0 ≤ measure m s``,
    rpt strip_tac >> imp_res_tac MEASURE_SPACE_POSITIVE >> fs[positive_def]
);

val MEASURE_INCREASING = store_thm(
    "MEASURE_INCREASING",
    ``∀m s t. measure_space m ∧ s ⊆ t ∧
        s ∈ measurable_sets m ∧ t ∈ measurable_sets m ⇒
        measure m s ≤ measure m t``,
    rw[] >> drule_then assume_tac MEASURE_SPACE_INCREASING >> fs[increasing_def]
);

val MEASURE_SPACE_COUNTABLY_SUBADDITIVE = store_thm(
    "MEASURE_SPACE_COUNTABLY_SUBADDITIVE",
    ``∀m. measure_space m ⇒ countably_subadditive m``,
    rw[countably_subadditive_def] >>
    `∀s. s ∈ measurable_sets m ⇒ (inf_measure m s = measure m s)` by (rw[] >>
        irule INF_MEASURE_AGREES >> fs[measure_space_def,sigma_algebra_def]) >>
    map_every (drule_then assume_tac)
        [MEASURE_SPACE_ALGEBRA,MEASURE_SPACE_INCREASING,MEASURE_SPACE_POSITIVE] >>
    dxrule_all_then assume_tac INF_MEASURE_COUNTABLY_SUBADDITIVE >>
    fs[countably_subadditive_def,measurable_sets_def,measure_def] >>
    pop_assum (qspec_then `f` assume_tac) >> rfs[] >>
    `inf_measure m ∘ f = measure m ∘ f` by (rw[FUN_EQ_THM] >> fs[FUNSET]) >>
    fs[] >> pop_assum kall_tac >> rfs[] >> pop_assum irule >>
    drule_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >> fs[FUNSET,POW_DEF]
);

val MEASURE_SPACE_SUBADDITIVE = store_thm(
    "MEASURE_SPACE_SUBADDITIVE",
    ``∀m. measure_space m ⇒ subadditive m``,
    rw[] >> irule COUNTABLY_SUBADDITIVE_SUBADDITIVE >>
    rw[MEASURE_SPACE_ALGEBRA,MEASURE_SPACE_POSITIVE,MEASURE_SPACE_COUNTABLY_SUBADDITIVE]
);

val MEASURE_SPACE_UNION_NULL = store_thm(
    "MEASURE_SPACE_UNION_NULL",
    ``∀m s t. measure_space m ∧ null_set m s ∧ null_set m t ⇒ null_set m (s ∪ t)``,
    rw[] >> fs[null_set_def] >> rw[MEASURE_SPACE_UNION,GSYM REAL_LE_ANTISYM]
    >- (imp_res_tac MEASURE_SPACE_SUBADDITIVE >> fs[subadditive_def] >>
        pop_assum imp_res_tac >> rfs[])
    >- (imp_res_tac MEASURE_SPACE_POSITIVE >> fs[positive_def] >>
        pop_assum irule >> rw[MEASURE_SPACE_UNION])
);

val MEASURE_SPACE_OUTER_MEASURE_SPACE = store_thm(
    "MEASURE_SPACE_OUTER_MEASURE_SPACE",
    ``∀m. measure_space m ⇒ outer_measure_space m``,
    rw[] >> fs[outer_measure_space_def] >>
    rw[MEASURE_SPACE_INCREASING,MEASURE_SPACE_POSITIVE,MEASURE_SPACE_COUNTABLY_SUBADDITIVE]
);

val MEASURE_NONZERO_POSITIVE = store_thm(
    "MEASURE_NONZERO_POSITIVE",
    ``∀m s. measure_space m ∧ s ∈ measurable_sets m ∧ measure m s ≠ 0 ⇒ 0 < measure m s``,
    rw[measure_space_def,positive_def] >> RES_TAC >> rw[REAL_LT_LE]
);

val MEASURE_MAXIMUM = store_thm(
    "MEASURE_MAXIMUM",
    ``∀m s. measure_space m ∧ s ∈ measurable_sets m ⇒ measure m s ≤ measure m (m_space m)``,
    rpt strip_tac >> imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >>
    imp_res_tac MEASURABLE_SETS_SUBSET_SPACE >> imp_res_tac MEASURE_SPACE_INCREASING >>
    imp_res_tac INCREASING
);

val MEASURE_COUNTABLE_INCREASING_ALT = store_thm(
    "MEASURE_COUNTABLE_INCREASING_ALT",
    ``∀m f. measure_space m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧ (∀n. f n ⊆ f (SUC n)) ⇒
        measure m ∘ f --> measure m (BIGUNION (IMAGE f 𝕌(:num)))``,
    rw[] >>
    `∃g. (g 0 = ∅) ∧ ∀n. g (SUC n) = f n` by (
        Q.ABBREV_TAC `g = (λn. if (n = 0) then ∅ else f (n - 1))` >>
        qexists_tac `g` >> Q.UNABBREV_TAC `g` >> rw[]) >>
    `measure m ∘ g --> measure m (BIGUNION (IMAGE g 𝕌(:num)))` by (
        irule MEASURE_COUNTABLE_INCREASING >> rw[]
        >- (Cases_on `n` >> rw[])
        >- (fs[FUNSET] >> Cases_on `x` >> rw[MEASURE_SPACE_EMPTY_MEASURABLE])) >>
    `BIGUNION (IMAGE g 𝕌(:num)) = BIGUNION (IMAGE f 𝕌(:num))` by (
        rw[FUN_EQ_THM,IN_BIGUNION_IMAGE] >> eq_tac >> rw[IN_APP]
        >- (qexists_tac `s` >> rw[] >> qexists_tac `x' - 1` >> rw[] >>
            Cases_on `x'` >> rfs[] >> pop_assum (qspec_then `x` assume_tac) >> rfs[])
        >- (qexists_tac `s` >> rw[] >> qexists_tac `SUC x'` >> rw[])) >> fs[] >>
    (qspecl_then [`measure m ∘ g`,`measure m (BIGUNION (IMAGE f 𝕌(:num)))`] assume_tac) SEQ_SUC >>
    rfs[o_DEF]
);

val MEASURE_SPACE_TRIVIAL_A_E = store_thm(
    "MEASURE_SPACE_TRIVIAL_A_E",
    ``∀m s. measure_space m ∧ (measure m (m_space m) = 0) ∧
        m_space m DIFF s ∈ measurable_sets m ⇒ a_e m s``,
    rw[a_e_def,null_set_def] >> imp_res_tac MEASURE_SPACE_INCREASING >>
    fs[increasing_def] >> pop_assum (qspecl_then [`m_space m DIFF s`,`m_space m`] assume_tac) >>
    rfs[MEASURE_SPACE_MSPACE_MEASURABLE,SUBSET_DEF] >> rw[GSYM REAL_LE_ANTISYM] >>
    imp_res_tac MEASURE_SPACE_POSITIVE >> fs[positive_def]
);

val MEASURE_SPACE_EMPTY_NULL = store_thm(
    "MEASURE_SPACE_EMPTY_NULL",
    ``∀m. measure_space m ⇒ null_set m ∅``,
    rw[null_set_def,MEASURE_SPACE_EMPTY_MEASURABLE] >> fs[measure_space_def,positive_def]
);

val IN_MEASURABLE_BOREL_FINITE = store_thm(
    "IN_MEASURABLE_BOREL_FINITE",
    ``∀f a. f ∈ measurable a Borel ⇒ {x | f x ≠ PosInf ∧ f x ≠ NegInf} ∩ space a ∈ subsets a``,
    rw[] >>
    `{x | f x ≠ PosInf ∧ f x ≠ NegInf} = {x | NegInf < f x ∧ f x < PosInf}` by (rw[EXTENSION] >>
        Cases_on `f x` >> simp[extreal_lt_alt]) >>
    simp[] >> pop_assum kall_tac >> simp[IN_MEASURABLE_BOREL_ALL]
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

val IN_MEASURABLE_BOREL_ABS_ALT = store_thm(
    "IN_MEASURABLE_BOREL_ABS_ALT",
    ``∀a f. sigma_algebra a ∧ f ∈ measurable a Borel ⇒ (abs ∘ f) ∈ measurable a Borel``,
    rw[] >> irule IN_MEASURABLE_BOREL_ABS >> rw[] >> qexists_tac `f` >> rw[]
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

val IN_MEASURABLE_BOREL_EXTCMUL_ALT = store_thm(
    "IN_MEASURABLE_BOREL_EXTCMUL_ALT",
    ``∀a f c. sigma_algebra a ∧ f ∈ measurable a Borel ⇒ (λx. c * f x) ∈ measurable a Borel``,
    rw[] >> Cases_on `c` >> fs[IN_MEASURABLE_BOREL_CMUL_ALT] >>
    `{x | f x < 0} ∩ space a ∈ subsets a` by rw[IN_MEASURABLE_BOREL_ALL] >>
    `{x | 0 < f x} ∩ space a ∈ subsets a` by rw[IN_MEASURABLE_BOREL_ALL]
    >- (`(λx. NegInf * f x) =
            (λx. PosInf * indicator_fn {x | f x < 0} x + NegInf * indicator_fn {x | 0 < f x} x)` by (
            rw[FUN_EQ_THM] >> (qspecl_then [`f x`,`0`] assume_tac) lt_antisym >>
            (qspecl_then [`f x`,`0`] assume_tac) lt_total >> fs[] >>
            fs[indicator_fn_def,mul_rzero,mul_rone,add_lzero,add_rzero,lt_refl] >>
            fs[extreal_mul_alt] >> fs[lt_le]) >>
        rw[] >> pop_assum kall_tac >> irule IN_MEASURABLE_BOREL_ADD >> rw[] >>
        map_every qexists_tac [`(λx. PosInf * indicator_fn ({x | f x < 0} ∩ space a) x)`,
            `(λx. NegInf * indicator_fn ({x | 0 < f x} ∩ space a) x)`] >>
        fs[] >> rw[]
        >- (rw[indicator_fn_def])
        >- ((qspecl_then [`a`,`(λx. PosInf)`,`{x | f x < 0} ∩ space a`] assume_tac)
                IN_MEASURABLE_BOREL_MUL_INDICATOR >>
            rfs[] >> pop_assum irule >> irule IN_MEASURABLE_BOREL_CONST_ALT >> rw[])
        >- ((qspecl_then [`a`,`(λx. NegInf)`,`{x | 0 < f x} ∩ space a`] assume_tac)
                IN_MEASURABLE_BOREL_MUL_INDICATOR >>
            rfs[] >> pop_assum irule >> irule IN_MEASURABLE_BOREL_CONST_ALT >> rw[]))
    >- (`(λx. PosInf * f x) =
            (λx. PosInf * indicator_fn {x | 0 < f x} x + NegInf * indicator_fn {x | f x < 0} x)` by (
            rw[FUN_EQ_THM] >> (qspecl_then [`f x`,`0`] assume_tac) lt_antisym >>
            (qspecl_then [`f x`,`0`] assume_tac) lt_total >> fs[] >>
            fs[indicator_fn_def,mul_rzero,mul_rone,add_lzero,add_rzero,lt_refl] >>
            fs[extreal_mul_alt] >> fs[lt_le]) >>
        rw[] >> pop_assum kall_tac >> irule IN_MEASURABLE_BOREL_ADD >> rw[] >>
        map_every qexists_tac [`(λx. PosInf * indicator_fn ({x | 0 < f x} ∩ space a) x)`,
            `(λx. NegInf * indicator_fn ({x | f x < 0} ∩ space a) x)`] >>
        fs[] >> rw[]
        >- (rw[indicator_fn_def])
        >- ((qspecl_then [`a`,`(λx. PosInf)`,`{x | 0 < f x} ∩ space a`] assume_tac)
                IN_MEASURABLE_BOREL_MUL_INDICATOR >>
            rfs[] >> pop_assum irule >> irule IN_MEASURABLE_BOREL_CONST_ALT >> rw[])
        >- ((qspecl_then [`a`,`(λx. NegInf)`,`{x | f x < 0} ∩ space a`] assume_tac)
                IN_MEASURABLE_BOREL_MUL_INDICATOR >>
            rfs[] >> pop_assum irule >> irule IN_MEASURABLE_BOREL_CONST_ALT >> rw[]))
);

val IN_MEASURABLE_BOREL_EXTCMUL = store_thm(
    "IN_MEASURABLE_BOREL_EXTCMUL",
    ``∀a f g c. sigma_algebra a ∧ f ∈ measurable a Borel ∧ (∀x. x ∈ space a ⇒ g x = c * f x) ⇒
        g ∈ measurable a Borel``,
    rw[] >> irule IN_MEASURABLE_BOREL_CMUL >> simp[] >>
    map_every qexists_tac [`(λx. c * f x)`,`1`] >> simp[N1_EQ_1,mul_lone] >>
    irule IN_MEASURABLE_BOREL_EXTCMUL_ALT >> simp[]
);

val IN_MEASURABLE_BOREL_EXTMUL = store_thm(
    "IN_MEASURABLE_BOREL_EXTMUL",
    ``∀a f g h. sigma_algebra a ∧ f ∈ measurable a Borel ∧ g ∈ measurable a Borel ∧
        (∀x. x ∈ space a ⇒ h x = f x * g x) ⇒ h ∈ measurable a Borel``,
    rw[] >>
    `∀x. x ∈ space a ⇒ h x =
        PosInf * g x * indicator_fn {x | f x = PosInf ∧ x ∈ space a} x +
        NegInf * g x * indicator_fn {x | f x = NegInf ∧ x ∈ space a} x +
        PosInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = PosInf ∧ x ∈ space a} x +
        NegInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = NegInf ∧ x ∈ space a} x +
        f x * g x * indicator_fn
        {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x ≠ PosInf ∧ g x ≠ NegInf ∧ x ∈ space a} x` by (
        rw[] >> Cases_on `f x` >> Cases_on `g x` >>
        simp[indicator_fn_def,mul_lzero,mul_rzero,mul_lone,mul_rone,add_lzero,add_rzero,
            extreal_add_def,extreal_mul_def]) >>
    irule IN_MEASURABLE_BOREL_ADD >> simp[] >> pop_assum kall_tac >>
    map_every qexists_tac [`(λx. PosInf * g x * indicator_fn {x | f x = PosInf ∧ x ∈ space a} x)`,
        `(λx. NegInf * g x * indicator_fn {x | f x = NegInf ∧ x ∈ space a} x +
        PosInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = PosInf ∧ x ∈ space a} x +
        NegInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = NegInf ∧ x ∈ space a} x +
        f x * g x * indicator_fn
        {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x ≠ PosInf ∧ g x ≠ NegInf ∧ x ∈ space a} x)`] >>
    rw[add_assoc]
    >- (irule IN_MEASURABLE_BOREL_EXTCMUL >> simp[] >>
        map_every qexists_tac [`PosInf`,
            `(λx. g x * indicator_fn {x | f x = PosInf ∧ x ∈ space a} x)`] >>
        simp[mul_assoc] >> irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[] >>
        `{x | f x = PosInf ∧ x ∈ space a} = {x | f x = PosInf} ∩ space a` by rw[INTER_DEF] >>
        simp[] >> pop_assum kall_tac >> simp[IN_MEASURABLE_BOREL_ALL]) >>
    irule IN_MEASURABLE_BOREL_ADD >> simp[] >> pop_assum kall_tac >>
    map_every qexists_tac [`(λx. NegInf * g x * indicator_fn {x | f x = NegInf ∧ x ∈ space a} x)`,
        `(λx. PosInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = PosInf ∧ x ∈ space a} x +
        NegInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = NegInf ∧ x ∈ space a} x +
        f x * g x * indicator_fn
        {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x ≠ PosInf ∧ g x ≠ NegInf ∧ x ∈ space a} x)`] >>
    rw[add_assoc]
    >- (irule IN_MEASURABLE_BOREL_EXTCMUL >> simp[] >>
        map_every qexists_tac [`NegInf`,
            `(λx. g x * indicator_fn {x | f x = NegInf ∧ x ∈ space a} x)`] >>
        simp[mul_assoc] >> irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[] >>
        `{x | f x = NegInf ∧ x ∈ space a} = {x | f x = NegInf} ∩ space a` by rw[INTER_DEF] >>
        simp[] >> pop_assum kall_tac >> simp[IN_MEASURABLE_BOREL_ALL]) >>
    irule IN_MEASURABLE_BOREL_ADD >> simp[] >>
    map_every qexists_tac [
        `(λx. PosInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = PosInf ∧ x ∈ space a} x)`,
        `(λx. NegInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = NegInf ∧ x ∈ space a} x +
        f x * g x * indicator_fn
        {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x ≠ PosInf ∧ g x ≠ NegInf ∧ x ∈ space a} x)`] >>
    rw[add_assoc]
    >- (irule IN_MEASURABLE_BOREL_EXTCMUL >> simp[] >>
        map_every qexists_tac [`PosInf`,
            `(λx. f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = PosInf ∧ x ∈ space a} x)`] >>
        simp[mul_assoc] >> irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[] >>
        `{x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = PosInf ∧ x ∈ space a} =
            ({x | f x ≠ PosInf ∧ f x ≠ NegInf} ∩ space a) ∩
            ({x | g x = PosInf} ∩ space a)` by (rw[EXTENSION] >> eq_tac >> rw[]) >>
        simp[] >> pop_assum kall_tac >> irule SIGMA_ALGEBRA_INTER >>
        simp[IN_MEASURABLE_BOREL_FINITE,IN_MEASURABLE_BOREL_ALL]) >>
    irule IN_MEASURABLE_BOREL_ADD >> simp[] >>
    map_every qexists_tac [
        `(λx. NegInf * f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = NegInf ∧ x ∈ space a} x)`,
        `(λx. f x * g x * indicator_fn
        {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x ≠ PosInf ∧ g x ≠ NegInf ∧ x ∈ space a} x)`] >>
    rw[add_assoc]
    >- (irule IN_MEASURABLE_BOREL_EXTCMUL >> simp[] >>
        map_every qexists_tac [`NegInf`,
            `(λx. f x * indicator_fn {x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = NegInf ∧ x ∈ space a} x)`] >>
        simp[mul_assoc] >> irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[] >>
        `{x | f x ≠ PosInf ∧ f x ≠ NegInf ∧ g x = NegInf ∧ x ∈ space a} =
            ({x | f x ≠ PosInf ∧ f x ≠ NegInf} ∩ space a) ∩
            ({x | g x = NegInf} ∩ space a)` by (rw[EXTENSION] >> eq_tac >> rw[]) >>
        simp[] >> pop_assum kall_tac >> irule SIGMA_ALGEBRA_INTER >>
        simp[IN_MEASURABLE_BOREL_FINITE,IN_MEASURABLE_BOREL_ALL]) >>
    irule IN_MEASURABLE_BOREL_MUL >> simp[] >>
    map_every qexists_tac [`(λx. f x * indicator_fn ({x | f x ≠ PosInf ∧ f x ≠ NegInf} ∩ space a) x)`,
        `(λx. g x * indicator_fn ({x | g x ≠ PosInf ∧ g x ≠ NegInf} ∩ space a) x)`] >>
    rw[]
    >- (Cases_on `f x` >>
        simp[indicator_fn_def,mul_lzero,mul_rzero,mul_lone,mul_rone,add_lzero,add_rzero,
            extreal_add_def,extreal_mul_def] >>
        simp[GSYM N0_EQ_0])
    >- (Cases_on `f x` >>
        simp[indicator_fn_def,mul_lzero,mul_rzero,mul_lone,mul_rone,add_lzero,add_rzero,
            extreal_add_def,extreal_mul_def] >>
        simp[GSYM N0_EQ_0])
    >- (Cases_on `g x` >>
        simp[indicator_fn_def,mul_lzero,mul_rzero,mul_lone,mul_rone,add_lzero,add_rzero,
            extreal_add_def,extreal_mul_def] >>
        simp[GSYM N0_EQ_0])
    >- (Cases_on `g x` >>
        simp[indicator_fn_def,mul_lzero,mul_rzero,mul_lone,mul_rone,add_lzero,add_rzero,
            extreal_add_def,extreal_mul_def] >>
        simp[GSYM N0_EQ_0])
    >- (Cases_on `f x` >> Cases_on `g x` >>
        simp[indicator_fn_def,mul_lzero,mul_rzero,mul_lone,mul_rone,add_lzero,add_rzero,
            extreal_add_def,extreal_mul_def])
    >- (irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[IN_MEASURABLE_BOREL_FINITE])
    >- (irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[IN_MEASURABLE_BOREL_FINITE])
);

val IN_MEASURABLE_BOREL_EXTMUL_ALT = store_thm(
    "IN_MEASURABLE_BOREL_EXTMUL_ALT",
    ``∀a f g. sigma_algebra a ∧ f ∈ measurable a Borel ∧ g ∈ measurable a Borel ⇒
        (λx. f x * g x) ∈ measurable a Borel``,
    rw[] >> irule IN_MEASURABLE_BOREL_EXTMUL >> simp[] >>
    map_every qexists_tac [`f`,`g`] >> simp[]
);

val IN_MEASURABLE_BOREL_EXTPROD = store_thm(
    "IN_MEASURABLE_BOREL_EXTPROD",
    ``∀n a fs h. sigma_algebra a ∧ (∀i. i < n ⇒ (fs i) ∈ measurable a Borel) ∧
        (∀x. x ∈ space a ⇒ h x = prod (0,n) (λi. fs i x)) ⇒ h ∈ measurable a Borel``,
    Induct_on `n` >> rw[extreal_prod_def]
    >- (irule IN_MEASURABLE_BOREL_CONST >> simp[] >> qexists_tac `1` >> simp[]) >>
    irule IN_MEASURABLE_BOREL_EXTMUL >> simp[] >>
    map_every qexists_tac [`(λx. prod (0,n) (λi. fs i x))`,`fs n`] >> simp[] >>
    last_x_assum irule >> simp[] >> qexists_tac `fs` >> simp[]
);

val IN_MEASURABLE_BOREL_EXTPROD_ALT = store_thm(
    "IN_MEASURABLE_BOREL_EXTPROD_ALT",
    ``∀n a fs. sigma_algebra a ∧ (∀i. i < n ⇒ (fs i) ∈ measurable a Borel) ⇒
        (λx. prod (0,n) (λi. fs i x)) ∈ measurable a Borel``,
    rw[] >> irule IN_MEASURABLE_BOREL_EXTPROD >> simp[] >>
    map_every qexists_tac [`fs`,`n`] >> simp[]
);

val IN_MEASURABLE_BOREL_SUM_ALT = store_thm(
    "IN_MEASURABLE_BOREL_SUM_ALT",
    ``∀a f s. FINITE s ∧ sigma_algebra a ∧
        (∀i. i ∈ s ⇒ f i ∈ measurable a Borel) ⇒
        (λx. SIGMA (λi. f i x) s) ∈ measurable a Borel``,
    rw[] >> drule_then assume_tac IN_MEASURABLE_BOREL_SUM >>
    NTAC 2 (pop_assum (drule_then assume_tac)) >>
    pop_assum irule >> rw[]
);

val IN_MEASURABLE_BOREL_MONO_SUP_ALT = store_thm(
    "IN_MEASURABLE_BOREL_MONO_SUP_ALT",
    ``∀fn a. sigma_algebra a ∧ (∀n. fn n ∈ measurable a Borel) ∧
        (∀n x. x ∈ space a ⇒ fn n x ≤ fn (SUC n) x) ⇒
        (λx. sup (IMAGE (λn. fn n x) 𝕌(:num))) ∈ measurable a Borel``,
    rw[] >> drule_then assume_tac IN_MEASURABLE_BOREL_MONO_SUP >>
    NTAC 2 (pop_assum (drule_then assume_tac)) >>
    pop_assum irule >> rw[]
);

val IN_MEASURABLE_BOREL_POS_SUMINF_ALT = store_thm(
    "IN_MEASURABLE_BOREL_POS_SUMINF_ALT",
    ``∀fn f a. sigma_algebra a ∧ (∀n. fn n ∈ measurable a Borel) ∧
        (∀n x. x ∈ space a ⇒ 0 ≤ fn n x) ⇒ (λx. suminf (λi. fn i x)) ∈ measurable a Borel``,
    rw[] >> (qspecl_then [`λn x. SIGMA (λi. fn i x) (count n)`,
        `λx. suminf (λi. fn i x)`,`a`] assume_tac) IN_MEASURABLE_BOREL_MONO_SUP >>
    pop_assum irule >> rw[] >> fs[]
    >- (fs[ext_suminf_def])
    >- (irule EXTREAL_SUM_IMAGE_MONO_SET >> rw[] >> fs[count_def,SUBSET_DEF])
    >- (irule IN_MEASURABLE_BOREL_SUM_ALT >> rw[])
);

val IN_MEASURABLE_BOREL_INTEGRABLE = store_thm(
    "IN_MEASURABLE_BOREL_INTEGRABLE",
    ``∀m f. integrable m f ⇒ f ∈ measurable (m_space m,measurable_sets m) Borel``,
    rw[integrable_def]
);

val IN_MEASURABLE_BOREL_2D_ALT = store_thm(
    "IN_MEASURABLE_BOREL_2D_ALT",
    ``∀f a. f ∈ measurable a Borel_2D ⇔ sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal) × 𝕌(:extreal)) ∧
        ∀s t. s ∈ subsets Borel ∧ t ∈ subsets Borel ⇒ PREIMAGE f (s × t) ∩ space a ∈ subsets a``,
    rw[measurable_def,SPACE_BOREL_2D] >> eq_tac >> rw[SIGMA_ALGEBRA_BOREL_2D]
    >- (first_x_assum irule >> simp[Borel_2D_def] >>
        assume_tac (INST_TYPE [alpha |-> ``:extreal # extreal``] SIGMA_SUBSET_SUBSETS) >>
        fs[SUBSET_DEF] >> pop_assum irule >> simp[prod_sets_def] >>
        map_every qexists_tac [`s`,`t`] >> simp[]) >>
    `sigma_algebra (𝕌(:extreal) × 𝕌(:extreal),{s | PREIMAGE f s ∩ space a ∈ subsets a})` suffices_by (
        rw[] >> fs[Borel_2D_def,sigma_def,subsets_def] >>
        first_x_assum (qspec_then `{s | PREIMAGE f s ∩ space a ∈ subsets a}` assume_tac) >> rfs[] >>
        pop_assum irule >> pop_assum kall_tac >> rw[SUBSET_DEF,prod_sets_def] >>
        first_x_assum irule >> simp[]) >>
    pop_assum kall_tac >> fs[sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def] >> rw[]
    >- (simp[SUBSET_DEF])
    >- (qpat_x_assum `∀s. _ ⇒ _ DIFF _ ∈ _` (dxrule_then assume_tac) >>
        `PREIMAGE f (𝕌(:extreal) × 𝕌(:extreal) DIFF s) ∩ space a =
            space a DIFF PREIMAGE f s ∩ space a` suffices_by rw[] >>
        pop_assum kall_tac >> rw[EXTENSION] >> eq_tac >> rw[])
    >- (qpat_x_assum `∀s t. _` (dxrule_all_then assume_tac) >>
        `PREIMAGE f (s ∪ t) ∩ space a =
            PREIMAGE f t ∩ space a ∪ PREIMAGE f s ∩ space a` suffices_by rw[] >>
        pop_assum kall_tac >> rw[EXTENSION] >> eq_tac >> rw[] >> rw[])
    >- (simp[PREIMAGE_BIGUNION,GSYM INTER_BIGUNION_IMAGE_COMM] >>
        qpat_x_assum `∀c. countable c ∧ _ ⇒ _` irule >>
        simp[image_countable] >> fs[SUBSET_DEF] >> rw[] >> rename [`PREIMAGE f x ∩ _ ∈ _`] >>
        first_x_assum irule >> simp[])
);

val IN_MEASURABLE_BOREL_2D_PAIR_MAP_DUP = store_thm(
    "IN_MEASURABLE_BOREL_2D_PAIR_MAP_DUP",
    ``∀a f g h. sigma_algebra a ∧ f ∈ measurable a Borel ∧ g ∈ measurable a Borel ∧
        (∀x. x ∈ space a ⇒ (h x = ((f ## g) ∘ DUP) x)) ⇒ h ∈ measurable a Borel_2D``,
    rw[] >> rw[IN_MEASURABLE_BOREL_2D_ALT,FUNSET] >> fs[measurable_def,DUP_DEF] >> rw[] >>
    NTAC 2 (first_x_assum (dxrule_then assume_tac)) >>
    `PREIMAGE h (s × t) ∩ space a = PREIMAGE ((f ## g) ∘ DUP) (s × t) ∩ space a` by (
        rw[EXTENSION,DUP_DEF] >> eq_tac >> rw[] >> first_x_assum (dxrule_all_then assume_tac) >> fs[]) >>
    simp[] >> pop_assum kall_tac >>
    `PREIMAGE ((f ## g) ∘ DUP) (s × t) ∩ space a =
        (PREIMAGE f s ∩ space a) ∩ (PREIMAGE g t ∩ space a)`
        by (rw[EXTENSION,DUP_DEF] >> eq_tac >> rw[]) >>
    simp[] >> pop_assum kall_tac >>
    irule ALGEBRA_INTER >> simp[SIGMA_ALGEBRA_ALGEBRA]
);

val IN_MEASURABLE_BOREL_2D_PAIR_MAP_DUP_ALT = store_thm(
    "IN_MEASURABLE_BOREL_2D_PAIR_MAP_DUP_ALT",
    ``∀a f g. sigma_algebra a ∧ f ∈ measurable a Borel ∧ g ∈ measurable a Borel ⇒
        (f ## g) ∘ DUP ∈ measurable a Borel_2D``,
    rw[] >> irule IN_MEASURABLE_BOREL_2D_PAIR_MAP_DUP >> simp[] >>
    map_every qexists_tac [`f`,`g`] >> simp[]
);

val MEASURABLE_PREIMAGE_SIGMA = store_thm(
    "MEASURABLE_PREIMAGE_SIGMA",
    ``∀a b f. f ∈ measurable a b ⇒ f ∈ measurable (space a,{PREIMAGE f s ∩ space a | s ∈ subsets b}) b``,
    rw[measurable_def,sigma_algebra_def,algebra_def,subset_class_def,space_def,subsets_def]
    >- (rw[SUBSET_DEF])
    >- (qexists_tac `∅` >> simp[PREIMAGE_def])
    >- (rename [`s ∈ subsets b`] >> qexists_tac `space b DIFF s` >> simp[] >>
        rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[] >> fs[FUNSET])
    >- (rename [`PREIMAGE f s ∩ space a ∪ PREIMAGE f t ∩ space a = _`] >>
        qexists_tac `s ∪ t` >> simp[] >> rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[] >> simp[])
    >- (fs[COUNTABLE_ENUM]
        >- (qexists_tac `∅` >> simp[PREIMAGE_EMPTY,INTER_EMPTY]) >>
        rename [`c = IMAGE g 𝕌(:num)`] >> rw[] >>
        `∃h. ∀i. g i = PREIMAGE f (h i) ∩ space a ∧ h i ∈ subsets b` by (simp[GSYM SKOLEM_THM] >>
            rw[] >> fs[SUBSET_DEF] >> pop_assum irule >> qexists_tac `i` >> simp[]) >>
        qexists_tac `BIGUNION (IMAGE h 𝕌(:num))` >> rw[]
        >- (rw[EXTENSION,IN_BIGUNION,IN_PREIMAGE] >> eq_tac >> rw[] >> fs[] >> rename [`f x ∈ h n`]
            >- (qexists_tac `h n` >> simp[] >> qexists_tac `n` >> rw[])
            >- (qexists_tac `g n` >> simp[] >> qexists_tac `n` >> rw[]))
        >- (first_x_assum irule >> rw[SUBSET_DEF] >> fs[] >> qexists_tac `h` >> simp[]))
    >- (qexists_tac `s` >> simp[])
);

val IN_MEASURABLE_BOREL_EXTPROD_PREIMAGE_SIGMA = store_thm(
    "IN_MEASURABLE_BOREL_EXTPROD_PREIMAGE_SIGMA",
    ``∀n a fs. (0 < n) ∧ sigma_algebra a ∧ (∀i. i < n ⇒ (fs i) ∈ measurable a Borel) ⇒
        (λx. prod (0,n) (λi. fs i x)) ∈ measurable (sigma (space a)
        ({BIGINTER (IMAGE (λi. PREIMAGE (fs i) (ss i) ∩ space a) (count n)) |
        ss ∈ (𝕌(:num) → subsets Borel)})) Borel``,
    rw[] >>
    Q.ABBREV_TAC `sts = {BIGINTER (IMAGE (λi. PREIMAGE (fs i) (ss i) ∩ space a) (count n)) |
        ss ∈ (𝕌(:num) → subsets Borel)}` >>
    `sigma_algebra (sigma (space a) sts)` by (irule SIGMA_ALGEBRA_SIGMA >>
        Q.UNABBREV_TAC `sts` >> rw[subset_class_def] >> irule BIGINTER_SUBSET >>
        rw[SUBSET_DEF,INTER_DEF,count_def] >> fs[] >> simp[EXTENSION] >> qexists_tac `0` >> simp[]) >>
    irule IN_MEASURABLE_BOREL_EXTPROD_ALT >>
    simp[measurable_def,space_def,subsets_def,SPACE_SIGMA,SIGMA_ALGEBRA_BOREL] >>
    NTAC 2 strip_tac >> last_assum (drule_then assume_tac) >> fs[measurable_def] >> rw[] >>
    first_x_assum (drule_then assume_tac) >> irule IN_SIGMA >> Q.UNABBREV_TAC `sts` >>
    simp[] >> qexists_tac `(λj. if j = i then s else 𝕌(:extreal))` >>
    simp[EXTENSION,IN_PREIMAGE,IN_BIGINTER_IMAGE] >> rw[FUNSET]
    >- (eq_tac >> rw[] >> rw[] >> first_x_assum (drule_then assume_tac) >> fs[])
    >- (rw[] >> simp[GSYM SPACE_BOREL] >> simp[SIGMA_ALGEBRA_SPACE])
);

val FST_MBL = store_thm(
    "FST_MBL",
    ``FST ∈ measurable Borel_2D Borel``,
    rw[measurable_def,SIGMA_ALGEBRA_BOREL,SIGMA_ALGEBRA_BOREL_2D,SPACE_BOREL,SPACE_BOREL_2D,FUNSET] >>
    `s × 𝕌(:extreal) ∈ subsets Borel_2D` by (simp[Borel_2D_def] >> irule IN_SIGMA >>
        simp[prod_sets_def] >> map_every qexists_tac [`s`,`𝕌(:extreal)`] >> simp[GSYM SPACE_BOREL] >>
        irule ALGEBRA_SPACE >> irule SIGMA_ALGEBRA_ALGEBRA >> simp[SIGMA_ALGEBRA_BOREL]) >>
    fs[INTER_DEF,CROSS_DEF]
);

val SND_MBL = store_thm(
    "SND_MBL",
    ``SND ∈ measurable Borel_2D Borel``,
    rw[measurable_def,SIGMA_ALGEBRA_BOREL,SIGMA_ALGEBRA_BOREL_2D,SPACE_BOREL,SPACE_BOREL_2D,FUNSET] >>
    `𝕌(:extreal) × s ∈ subsets Borel_2D` by (simp[Borel_2D_def] >> irule IN_SIGMA >>
        simp[prod_sets_def] >> map_every qexists_tac [`𝕌(:extreal)`,`s`] >> simp[GSYM SPACE_BOREL] >>
        irule ALGEBRA_SPACE >> irule SIGMA_ALGEBRA_ALGEBRA >> simp[SIGMA_ALGEBRA_BOREL]) >>
    fs[INTER_DEF,CROSS_DEF]
);

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
    >- (`0 < exp r'` by fs[EXP_POS_LT] >>
        `ln (exp r') < ln r` by fs[LN_MONO_LT] >>
        fs[LN_EXP])
    >- (`exp r' < exp (ln r)` by fs[EXP_MONO_LT] >>
        `exp (ln r) = r` by fs[EXP_LN] >> fs[])
);

val ADDITIVE_SUM_ALT = store_thm(
    "ADDITIVE_SUM_ALT",
    ``∀m f n. algebra (m_space m,measurable_sets m) ∧ positive m ∧ additive m ∧
        f ∈ (count n -> measurable_sets m) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (f i) (f j)) ⇒
        (sum (0,n) (measure m ∘ f) =
         measure m (BIGUNION (IMAGE f (count n))))``,
    NTAC 2 strip_tac >> Induct_on `n` >> rw[]
    >- (fs[positive_def,sum]) >>
    rw[sum,BIGUNION_IMAGE_COUNT_SUC] >>
    `sum (0,n) (measure m ∘ f) + measure m (f n) = measure m (BIGUNION (IMAGE f (count n)) ∪ f n)`
        suffices_by (rw[] >> fs[UNION_COMM]) >>
    `measure m (BIGUNION (IMAGE f (count n)) ∪ f n) =
        measure m (BIGUNION (IMAGE f (count n))) + measure m (f n)` by (fs[additive_def] >>
        qpat_x_assum `∀s t. _` irule >> rw[]
        >- (qpat_x_assum `∀i j. _` irule >> rw[])
        >- (`BIGUNION (IMAGE f (count n)) ∈ subsets (m_space m,measurable_sets m)`
                suffices_by rw[subsets_def] >>
            irule ALGEBRA_FINITE_UNION >> rw[subsets_def,SUBSET_DEF] >> fs[FUNSET])
        >- (fs[FUNSET])) >>
    rw[] >> pop_assum kall_tac >> fs[FUNSET]
);

val MEASURE_ADDITIVE_SUM = store_thm(
    "MEASURE_ADDITIVE_SUM",
    ``∀m f n. measure_space m ∧ f ∈ (count n -> measurable_sets m) ∧
        (∀i j. i < n ∧ j < n ∧ i ≠ j ⇒ DISJOINT (f i) (f j)) ⇒
        (sum (0,n) (measure m ∘ f) = measure m (BIGUNION (IMAGE f (count n))))``,
    rw[] >> irule ADDITIVE_SUM_ALT >>
    rw[MEASURE_SPACE_ADDITIVE,MEASURE_SPACE_POSITIVE,MEASURE_SPACE_ALGEBRA]
);

val FN_PLUS_PROD = store_thm(
    "FN_PLUS_PROD",
    ``∀f g. fn_plus (λ(x,y). f x * g y) =
        (λz. (λ(x,y). fn_plus f x * fn_plus g y) z +
        (λ(x,y). fn_minus f x * fn_minus g y) z)``,
    rw[FUN_EQ_THM] >> (qspec_then `z` assume_tac) ABS_PAIR_THM >> rw[] >>
    Q.RENAME_TAC [`_ _ (x,y) = _`] >> fs[fn_plus_def,fn_minus_def] >>
    (qspecl_then [`f x`,`0`] assume_tac) lt_antisym >>
    (qspecl_then [`g y`,`0`] assume_tac) lt_antisym >>
    (qspecl_then [`f x`,`0`] assume_tac) lt_total >>
    (qspecl_then [`g y`,`0`] assume_tac) lt_total >>
    fs[mul_lzero,mul_rzero,add_lzero,add_rzero,lt_refl] >> fs[]
    >- (rw[lt_mul])
    >- (imp_res_tac mul_lt >> rw[] >>
        (qspecl_then [`f x * g y`,`0`] assume_tac) lt_antisym >> rfs[])
    >- (imp_res_tac mul_lt >> rw[] >>
        (qspecl_then [`f x * g y`,`0`] assume_tac) lt_antisym >> rfs[] >>
        fs[mul_comm])
    >- (rw[lt_mul_neg,mul_lneg,mul_rneg,neg_neg])
);

val FN_MINUS_PROD = store_thm(
    "FN_MINUS_PROD",
    ``∀f g. fn_minus (λ(x,y). f x * g y) =
        (λz. (λ(x,y). fn_plus f x * fn_minus g y) z +
        (λ(x,y). fn_minus f x * fn_plus g y) z)``,
    rw[FUN_EQ_THM] >> (qspec_then `z` assume_tac) ABS_PAIR_THM >> rw[] >>
    Q.RENAME_TAC [`_ _ (x,y) = _`] >> fs[fn_plus_def,fn_minus_def] >>
    (qspecl_then [`f x`,`0`] assume_tac) lt_antisym >>
    (qspecl_then [`g y`,`0`] assume_tac) lt_antisym >>
    (qspecl_then [`f x`,`0`] assume_tac) lt_total >>
    (qspecl_then [`g y`,`0`] assume_tac) lt_total >>
    fs[mul_lzero,mul_rzero,add_lzero,add_rzero,lt_refl] >> fs[mul_lneg,mul_rneg]
    >- ((qspecl_then [`f x`,`g y`] assume_tac) lt_mul >> rfs[] >>
        (qspecl_then [`f x * g y`,`0`] assume_tac) lt_antisym >> rfs[])
    >- (rw[mul_lt])
    >- (`f x * g y = g y * f x` by rw[mul_comm] >> fs[] >> rw[mul_lt])
    >- ((qspecl_then [`f x`,`g y`] assume_tac) lt_mul_neg >> rfs[] >>
        (qspecl_then [`f x * g y`,`0`] assume_tac) lt_antisym >> rfs[])
);

val FN_PLUS_MUL_INDICATOR = store_thm(
    "FN_PLUS_MUL_INDICATOR",
    ``∀f s. fn_plus (λx. f x * indicator_fn s x) = (λx. (fn_plus f) x * indicator_fn s x)``,
    rpt strip_tac >> fs[FUN_EQ_THM,fn_plus_def,indicator_fn_def] >> strip_tac >> rw[] >>
    fs[mul_lzero,mul_rzero,mul_lone,mul_rone]
);

val FN_MINUS_MUL_INDICATOR = store_thm(
    "FN_MINUS_MUL_INDICATOR",
    ``∀f s. fn_minus (λx. f x * indicator_fn s x) = (λx. (fn_minus f) x * indicator_fn s x)``,
    rpt strip_tac >> fs[FUN_EQ_THM,fn_minus_def,indicator_fn_def] >> strip_tac >> rw[] >>
    fs[mul_lzero,mul_rzero,mul_lone,mul_rone,neg_0]
);

val FN_PLUS_o = store_thm(
    "FN_PLUS_o",
    ``∀f g. (fn_plus f) ∘ g = fn_plus (f ∘ g)``,
    rw[o_DEF,FUN_EQ_THM,fn_plus_def]
);

val FN_MINUS_o = store_thm(
    "FN_MINUS_o",
    ``∀f g. (fn_minus f) ∘ g = fn_minus (f ∘ g)``,
    rw[o_DEF,FUN_EQ_THM,fn_minus_def]
);

val SUBSET_CLASS_RESTRICTED = store_thm(
    "SUBSET_CLASS_RESTRICTED",
    ``∀spa sts spb. subset_class spa sts ∧ spb ⊆ spa ⇒ subset_class spb (IMAGE (λt. spb ∩ t) sts)``,
    rpt strip_tac >> fs[subset_class_def] >> rpt strip_tac >> fs[INTER_DEF,SUBSET_DEF]
);

val ALGEBRA_RESTRICTED = store_thm(
    "ALGEBRA_RESTRICTED",
    ``∀a b. algebra a ∧ b ⊆ space a ⇒ algebra (b, IMAGE (λt. b ∩ t) (subsets a))``,
    rpt strip_tac >> fs[algebra_def,space_def,subsets_def] >>
    imp_res_tac SUBSET_CLASS_RESTRICTED >> fs[] >> rw[] >> rpt strip_tac
    >- (exists_tac ``∅`` >> fs[])
    >- (exists_tac ``space a DIFF t`` >> fs[DIFF_DEF,INTER_DEF,EXTENSION] >>
        strip_tac >> eq_tac >> rw[] >> fs[SUBSET_DEF])
    >- (exists_tac ``t' ∪ t''`` >> fs[INTER_DEF,UNION_DEF,EXTENSION] >>
        strip_tac >> eq_tac >> rw[] >> fs[SUBSET_DEF])
);

val SIGMA_ALGEBRA_RESTRICTED = store_thm(
    "SIGMA_ALGEBRA_RESTRICTED",
    ``∀a b. sigma_algebra a ∧ b ⊆ space a ⇒ sigma_algebra (b, IMAGE (λt. b ∩ t) (subsets a))``,
    rpt strip_tac >> fs[sigma_algebra_def] >> imp_res_tac ALGEBRA_RESTRICTED >> fs[] >>
    rpt strip_tac >> fs[SUBSET_DEF,subsets_def] >>
    `∀x. ∃t. x ∈ c ⇒ (x = b ∩ t) ∧ t ∈ subsets a` by (strip_tac >>
        (assume_tac o (ISPECL [``(x:α -> bool) ∈ c``,``λ(t:α -> bool). (x = b ∩ t) ∧ t ∈ subsets a``]))
            (GSYM RIGHT_EXISTS_IMP_THM) >> fs[] >>
        qpat_x_assum `∀(x:α -> bool). _` (qspec_then `x` assume_tac) >>
        metis_tac[]) >> qpat_x_assum `∀x. _ ⇒ ∃t. _` kall_tac >>
    `∃f. ∀x. x ∈ c ⇒ (x = b ∩ f x) ∧ f x ∈ subsets a` by (
        (assume_tac o (ISPEC ``λ (x:α -> bool) t. x ∈ c ⇒ (x = b ∩ t) ∧ t ∈ subsets a``))
            (SKOLEM_THM) >>
        rfs[] >> metis_tac[]) >>
    Q.ABBREV_TAC `nc = IMAGE f c` >> exists_tac ``BIGUNION nc`` >>
    `(BIGUNION c = b ∩ BIGUNION nc) ∧ countable nc ∧ (∀x. x ∈ nc ⇒ x ∈ subsets a)`
        suffices_by (strip_tac >> fs[]) >> rw[] >> Q.UNABBREV_TAC `nc`
    >- (fs[BIGUNION,INTER_DEF,EXTENSION] >> strip_tac >> metis_tac[])
    >- (fs[COUNTABLE_ENUM] >>
        exists_tac ``(f:(α -> bool) -> α -> bool) ∘ (f':num -> α -> bool)`` >>
        fs[IMAGE_COMPOSE])
    >- (fs[IN_DEF])
);

val MEASURABLE_RESTRICTED = store_thm(
    "MEASURABLE_RESTRICTED",
    ``∀m s f. measure_space m ∧ s ∈ measurable_sets m ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        f ∈ measurable (s,IMAGE (λt. s ∩ t) (measurable_sets m)) Borel``,
    rpt strip_tac >> fs[measurable_def] >> imp_res_tac MEASURE_SPACE_SUBSET_MSPACE >>
    (qspecl_then [`(m_space m,measurable_sets m)`,`s`] assume_tac) SIGMA_ALGEBRA_RESTRICTED >>
    rfs[space_def,subsets_def] >>
    `f ∈ (s -> space Borel)` by (fs[SUBSET_DEF,IN_DEF]) >> fs[] >>
    rpt strip_tac >> exists_tac ``PREIMAGE f (s':extreal -> bool) ∩ m_space m`` >>
    fs[PREIMAGE_def,INTER_DEF,EXTENSION,SUBSET_DEF] >> strip_tac >>
    eq_tac >> rw[] >> fs[]
);

val POSITIVE_SUBSET = store_thm(
    "POSITIVE_SUBSET",
    ``∀m s. positive m ∧ s ⊆ measurable_sets m ⇒ positive (m_space m, s, measure m)``,
    rpt strip_tac >> fs[positive_def,m_space_def,measurable_sets_def,measure_def] >>
    rpt strip_tac >> fs[SUBSET_DEF]
);

val ADDITIVE_SUBSET = store_thm(
    "ADDITIVE_SUBSET",
    ``∀m s. additive m ∧ s ⊆ measurable_sets m ⇒ additive (m_space m, s, measure m)``,
    rpt strip_tac >> fs[additive_def,m_space_def,measurable_sets_def,measure_def] >>
    rpt strip_tac >> fs[SUBSET_DEF]
);

val INCREASING_SUBSET = store_thm(
    "INCREASING_SUBSET",
    ``∀m s. increasing m ∧ s ⊆ measurable_sets m ⇒ increasing (m_space m, s, measure m)``,
    rpt strip_tac >> fs[increasing_def,m_space_def,measurable_sets_def,measure_def] >>
    rpt strip_tac >> fs[SUBSET_DEF]
);

val COUNTABLY_SUBADDITIVE_SUBSET = store_thm(
    "COUNTABLY_SUBADDITIVE_SUBSET",
    ``∀m s. countably_subadditive m ∧ s ⊆ measurable_sets m ⇒
        countably_subadditive (m_space m, s, measure m)``,
    rpt strip_tac >> fs[countably_subadditive_def,m_space_def,measurable_sets_def,measure_def] >>
    rpt strip_tac >> fs[SUBSET_DEF,FUNSET]
);

val COUNTABLY_ADDITIVE_SUBSET = store_thm(
    "COUNTABLY_ADDITIVE_SUBSET",
    ``∀m s. countably_additive m ∧ s ⊆ measurable_sets m ⇒
        countably_additive (m_space m, s, measure m)``,
    rpt strip_tac >> fs[countably_additive_def,m_space_def,measurable_sets_def,measure_def] >>
    rpt strip_tac >> fs[SUBSET_DEF,FUNSET]
);

val OUTER_MEASURE_SPACE_SUBSET = store_thm(
    "OUTER_MEASURE_SPACE_SUBSET",
    ``∀m s. outer_measure_space m ∧ s ⊆ measurable_sets m ⇒
        outer_measure_space (m_space m, s, measure m)``,
    rpt strip_tac >> fs[outer_measure_space_def,m_space_def,measurable_sets_def,measure_def] >>
    fs[POSITIVE_SUBSET,INCREASING_SUBSET,COUNTABLY_SUBADDITIVE_SUBSET]
);

val LAMBDA_SYSTEM_SUBSET = store_thm(
    "LAMBDA_SYSTEM_SUBSET",
    ``∀a f s sts. sts ⊆ lambda_system a f ∧ sts ⊆ s ∧ s ⊆ subsets a ⇒
        sts ⊆ lambda_system (space a,s) f``,
    rpt strip_tac >> fs[lambda_system_def,SUBSET_DEF] >>
    rpt strip_tac >> fs[space_def,subsets_def]
);

val MEASURE_SPACE_SIGMA_SUBSET = store_thm(
    "MEASURE_SPACE_SIGMA_SUBSET",
    ``∀m s. measure_space m ∧ s ⊆ measurable_sets m ∧ sigma_algebra (m_space m,s) ⇒
        measure_space (m_space m, s, measure m)``,
    rpt strip_tac >> fs[measure_space_def,m_space_def,measurable_sets_def,measure_def] >>
    fs[POSITIVE_SUBSET,COUNTABLY_ADDITIVE_SUBSET]
);

val SIGMA_ALGEBRA_SUBSET_POW = store_thm(
    "SIGMA_ALGEBRA_SUBSET_POW",
    ``∀a. subset_class (space a) (subsets a) ⇒
        subsets (sigma (space a) (subsets a)) ⊆ POW (space a)``,
    rpt strip_tac >> Q.RENAME_TAC [`subsets (sigma sp sts) ⊆ _`] >>
    imp_res_tac SIGMA_ALGEBRA_SIGMA >> fs[SIGMA_ALGEBRA] >>
    fs[sigma_def,space_def,subsets_def] >>  Q.RENAME_TAC [`sig ⊆ _`] >>
    NTAC 3 (pop_assum kall_tac) >> fs[SUBSET_DEF] >> rpt strip_tac >>
    fs[subset_class_def,POW_DEF]
);

val MEASURE_SPACE_FROM_ALGEBRA = store_thm(
    "MEASURE_SPACE_FROM_ALGEBRA",
    ``∀m. algebra (m_space m,measurable_sets m) ∧ positive m ∧ additive m ⇒
        measure_space (m_space m,subsets (sigma (m_space m) (measurable_sets m)),inf_measure m)``,
    rpt strip_tac >> imp_res_tac ADDITIVE_INCREASING >>
    imp_res_tac ALGEBRA_SUBSET_LAMBDA_SYSTEM >> imp_res_tac INF_MEASURE_OUTER >>
    `subsets (sigma (m_space m) (measurable_sets m)) ⊆ POW (m_space m)` by (
        (qspec_then `(m_space m,measurable_sets m)` assume_tac) SIGMA_ALGEBRA_SUBSET_POW >>
        rfs[algebra_def,space_def,subsets_def]) >>
    (qspecl_then [`(m_space m,POW (m_space m))`,`inf_measure m`,
        `subsets (sigma (m_space m) (measurable_sets m))`,
        `measurable_sets m`] assume_tac) LAMBDA_SYSTEM_SUBSET >>
    rfs[space_def,subsets_def,SIGMA_SUBSET_SUBSETS] >>
    imp_res_tac OUTER_MEASURE_SPACE_SUBSET >>
    rfs[m_space_def,measurable_sets_def,measure_def] >> pop_assum imp_res_tac >>
    `sigma_algebra (m_space m,subsets (sigma (m_space m) (measurable_sets m)))` by (
        (qspecl_then [`m_space m`,`measurable_sets m`] assume_tac) SIGMA_ALGEBRA_SIGMA >>
        rfs[algebra_def,space_def,subsets_def,SIGMA_REDUCE]) >>
    imp_res_tac CARATHEODORY_LEMMA >> rfs[space_def,subsets_def] >>
    pop_assum imp_res_tac >>
    Q.ABBREV_TAC `lsys = lambda_system
        (m_space m,subsets (sigma (m_space m) (measurable_sets m))) (inf_measure m)` >>
    pop_assum kall_tac >>
    `subsets (sigma (m_space m) (measurable_sets m)) ⊆ lsys` by (
        (qspecl_then [`measurable_sets m`,`(m_space m,lsys)`] assume_tac) SIGMA_SUBSET >>
        rfs[space_def,subsets_def,measure_space_def,m_space_def,measurable_sets_def]) >>
    Q.RENAME_TAC [`measure_space (m_space m,sigsts,inf_measure m)`] >>
    (qspecl_then [`(m_space m,lsys,inf_measure m)`,`sigsts`] assume_tac) MEASURE_SPACE_SIGMA_SUBSET >>
    rfs[m_space_def,measurable_sets_def,measure_def]
);

val SUBSET_IMP_SIGMA_SUBSET = store_thm(
    "SUBSET_IMP_SIGMA_SUBSET",
    ``∀sp a b. a ⊆ b ⇒ subsets (sigma sp a) ⊆ subsets (sigma sp b)``,
    rpt strip_tac >>
    fs[sigma_def,subsets_def,SUBSET_DEF]
);

val SIGMA_SIGMA = store_thm(
    "SIGMA_SIGMA",
    ``∀sp sts. sigma sp (subsets (sigma sp sts)) = sigma sp sts``,
    rpt strip_tac >>
    `sts ⊆ (subsets (sigma sp sts))` by fs[SUBSET_DEF,IN_SIGMA] >>
    imp_res_tac SUBSET_IMP_SIGMA_SUBSET >> pop_assum (qspec_then `sp` assume_tac) >>
    `subsets (sigma sp (subsets (sigma sp sts))) ⊆
        subsets (sigma sp sts)` suffices_by (strip_tac >>
        fs[sigma_def,subsets_def,SET_EQ_SUBSET]) >>
    rpt (pop_assum kall_tac) >> fs[SUBSET_DEF] >> rpt strip_tac >>
    fs[sigma_def,subsets_def] >> rpt strip_tac >> last_x_assum imp_res_tac >>
    `BIGINTER {s | sts ⊆ s ∧ sigma_algebra (sp,s)} ⊆ P` suffices_by fs[] >>
    pop_assum kall_tac >>
    `∀x. x ∈ BIGINTER {s | sts ⊆ s ∧ sigma_algebra (sp,s)} ⇒ x ∈ P`
        suffices_by fs[SUBSET_DEF] >> rpt strip_tac >>
    fs[IN_BIGINTER]
);

val MEASURE_SPACE_RECTS_EMPTY_MEASURABLE = store_thm(
    "MEASURE_SPACE_RECTS_EMPTY_MEASURABLE",
    ``∀m0 m1. measure_space m0 ∧ measure_space m1 ⇒
        ∅ ∈ prod_sets (measurable_sets m0) (measurable_sets m1)``,
    rw[] >> imp_res_tac MEASURE_SPACE_EMPTY_MEASURABLE >> fs[prod_sets_def] >>
    map_every EXISTS_TAC [``∅ : α -> bool``,``∅ : β  -> bool``] >> fs[]
);

val MEASURE_SPACE_FINITE_UNION = store_thm(
    "MEASURE_SPACE_FINITE_UNION",
    ``∀m n s. measure_space m ∧ s ∈ (count n -> measurable_sets m) ⇒
        BIGUNION (IMAGE s (count n)) ∈ measurable_sets m``,
    rw[] >> imp_res_tac MEASURE_SPACE_EMPTY_MEASURABLE >>
    (qspecl_then [`m`,`(λi. if i < n then s i else ∅)`] assume_tac) MEASURE_SPACE_BIGUNION >>
    rfs[FUNSET] >> `(∀n'. (if n' < n then s n' else ∅) ∈ measurable_sets m)` by rw[] >>
    fs[] >> pop_assum kall_tac >>
    `BIGUNION (IMAGE (λi. if i < n then s i else ∅) 𝕌(:num)) = BIGUNION (IMAGE s (count n))`
        suffices_by (rw[] >> fs[]) >> rpt (pop_assum kall_tac) >>
    (qspecl_then [`(λi. if i < n then s i else ∅)`,`n`] assume_tac) BIGUNION_IMAGE_UNIV >>
    fs[] >> pop_assum kall_tac >>
    `∀x. x ∈ (count n) ⇒ ((λi. if i < n then s i else ∅) x = s x)`
        suffices_by fs[BIGUNION_IMAGE_EQUAL] >>
    rw[]
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Integrals *)
(*---------------------------------------------------------------------------*)

val m_space_prod_measure_space = store_thm(
    "m_space_prod_measure_space",
    ``∀m0 m1. m_space (prod_measure_space m0 m1) = m_space m0 × m_space m1``,
    rw[prod_measure_space_def,m_space_def]
);

val measurable_sets_prod_measure_space = store_thm(
    "measurable_sets_prod_measure_space",
    ``∀m0 m1. measurable_sets (prod_measure_space m0 m1) = subsets
        (sigma (m_space m0 × m_space m1) (prod_sets (measurable_sets m0) (measurable_sets m1)))``,
    rw[prod_measure_space_def,measurable_sets_def]
);

val measure_prod_measure_space = store_thm(
    "measure_prod_measure_space",
    ``∀m0 m1. measure (prod_measure_space m0 m1) = prod_measure m0 m1``,
    rw[prod_measure_space_def,measure_def]
);

val prod_measure_space_rect = store_thm(
    "prod_measure_space_rect",
    ``∀m0 m1 s0 s1. measure_space m0 ∧ measure_space m1 ∧
        s0 ∈ measurable_sets m0 ∧ s1 ∈ measurable_sets m1 ⇒
        (s0 × s1) ∈ measurable_sets (prod_measure_space m0 m1)``,
    rw[measurable_sets_prod_measure_space,sigma_def,subsets_def,SUBSET_DEF] >>
    pop_assum kall_tac >> pop_assum irule >> rw[prod_sets_def] >>
    map_every qexists_tac [`s0`,`s1`] >> rw[]
);

val pos_simple_fn_prod = store_thm(
    "pos_simple_fn_prod",
    ``∀m0 m1 f0 f1 s0 s1 e0 e1 a0 a1. measure_space m0 ∧ measure_space m1 ∧
        pos_simple_fn m0 f0 s0 e0 a0 ∧ pos_simple_fn m1 f1 s1 e1 a1 ⇒
        ∃s01 e01 a01. pos_simple_fn (prod_measure_space m0 m1) (λ(x,y). f0 x * f1 y) s01 e01 a01``,
    rw[pos_simple_fn_alt] >>
    map_every qexists_tac [`{pair_to_num (x,y) | x ∈ s0 ∧ y ∈ s1}`,
        `(λk. e0 (FST (num_to_pair k)) × e1 (SND (num_to_pair k)))`,
        `(λk. a0 (FST (num_to_pair k)) * a1 (SND (num_to_pair k)))`] >>
    rw[] >> fs[pair_to_num_inv]
    >- ((qspec_then `t` assume_tac) ABS_PAIR_THM >> rw[] >> fs[] >>
        irule le_mul >> fs[])
    >- ((qspec_then `t` assume_tac) ABS_PAIR_THM >> rw[GSYM extreal_mul_def] >> fs[] >>
        Q.RENAME_TAC [`f0 x * f1 y = Normal (a0 k0) * Normal (a1 k1)`] >>
        RES_TAC >> rw[])
    >- (irule prod_measure_space_rect >> RES_TAC >> rw[])
    >- (`FINITE (s0 × s1)` by fs[FINITE_CROSS] >>
        `FINITE (IMAGE pair_to_num (s0 × s1))` by fs[IMAGE_FINITE] >>
        `{pair_to_num (x,y) | x ∈ s0 ∧ y ∈ s1} = (IMAGE pair_to_num (s0 × s1))` suffices_by fs[] >>
        rw[EXTENSION] >> eq_tac >> rw[]
        >- (qexists_tac `(x',y)` >> rw[])
        >- (map_every qexists_tac [`FST x'`,`SND x'`] >> rw[]))
    >- (irule REAL_LE_MUL >> fs[])
    >- (assume_tac PAIR_TO_NUM_BIJ >> dxrule_then assume_tac BIJ_IMP_121C >>
        rfs[] >> fs[DISJOINT_CROSS])
    >- (rw[EXTENSION,IN_BIGUNION_IMAGE] >>
        (qspec_then `x` assume_tac) ABS_PAIR_THM >> rw[] >> fs[] >>
        Q.RENAME_TAC [`_ ⇔ (x,y) ∈ _`] >> eq_tac >> rw[]
        >- (fs[pair_to_num_inv,EXTENSION,IN_BIGUNION_IMAGE,m_space_prod_measure_space] >>
            metis_tac[])
        >- (fs[m_space_prod_measure_space,EXTENSION,IN_BIGUNION_IMAGE] >>
            `∃k0. k0 ∈ s0 ∧ x ∈ e0 k0` by metis_tac[] >>
            `∃k1. k1 ∈ s1 ∧ y ∈ e1 k1` by metis_tac[] >>
            qexists_tac `pair_to_num (k0,k1)` >> rw[pair_to_num_inv] >>
            map_every qexists_tac [`k0`,`k1`] >> rw[]))
);

val measurable_sequence_pos = store_thm(
    "measurable_sequence_pos",
    ``∀m f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel ∧ (∀x. 0 ≤ f x) ⇒
        ∃fi. (∀i x. 0 ≤ fi i x) ∧ (∀i x. fi i x ≤ f x) ∧
        (∀x. mono_increasing (λi. fi i x)) ∧
        (∀i. ∃s a x. pos_simple_fn m (fi i) s a x) ∧
        (∀x. x ∈ m_space m ⇒ (sup (IMAGE (λi. fi i x) 𝕌(:num)) = f x)) ∧
        (pos_fn_integral m f = sup (IMAGE (λi. pos_fn_integral m (fi i)) 𝕌(:num)))``,
    rw[] >> drule_all_then assume_tac measurable_sequence >> fs[] >>
    `fn_plus f = f` by (rw[fn_plus_def,FUN_EQ_THM] >>
        (qspecl_then [`0`,`f x`] assume_tac) (GSYM lt_total) >> fs[] >>
        fs[extreal_lt_def] >> last_x_assum (qspec_then `x` assume_tac) >> fs[]) >>
    qexists_tac `fi` >> fs[] >> rw[] >> `ri i ∈ psfis m (fi i)` by rw[] >>
    pop_assum (fn th => rpt (pop_assum kall_tac) >> assume_tac th) >>
    fs[psfis_def,psfs_def] >> map_every qexists_tac [`s`,`a`,`x'`] >> rw[]
);

val integral_fn_plus_pos = store_thm(
    "integral_fn_plus_pos",
    ``∀m f. (measure_space m) ⇒ (0 ≤ pos_fn_integral m (fn_plus f))``,
    rpt strip_tac >>
    `pos_fn_integral m (λx. 0) ≤ pos_fn_integral m (fn_plus f)` by
        (`(∀x. 0 ≤ (λx. 0) x ∧ (λx. 0) x ≤ fn_plus f x)` suffices_by fs[pos_fn_integral_mono] >>
        fs[le_refl,FN_PLUS_POS]) >>
    imp_res_tac pos_fn_integral_zero >> fs[]
);

val integral_fn_plus_not_neginf = store_thm(
    "integral_fn_plus_not_neginf",
    ``∀m f. (measure_space m) ⇒ (pos_fn_integral m (fn_plus f) ≠ NegInf)``,
    rpt strip_tac >> imp_res_tac integral_fn_plus_pos >>
    pop_assum (qspec_then `f` assume_tac) >> rfs[] >>
    `Normal 0 ≤ NegInf` by fs[N0_EQ_0] >> fs[extreal_le_def]
);

val integral_fn_minus_pos = store_thm(
    "integral_fn_minus_pos",
    ``∀m f. (measure_space m) ⇒ (0 ≤ pos_fn_integral m (fn_minus f))``,
    rpt strip_tac >>
    `pos_fn_integral m (λx. 0) ≤ pos_fn_integral m (fn_minus f)` by
        (`(∀x. 0 ≤ (λx. 0) x ∧ (λx. 0) x ≤ fn_minus f x)` suffices_by fs[pos_fn_integral_mono] >>
        fs[le_refl,FN_MINUS_POS]) >>
    imp_res_tac pos_fn_integral_zero >> fs[]
);

val integral_fn_minus_not_neginf = store_thm(
    "integral_fn_minus_not_neginf",
    ``∀m f. (measure_space m) ⇒ (pos_fn_integral m (fn_minus f) ≠ NegInf)``,
    rpt strip_tac >> imp_res_tac integral_fn_minus_pos >>
    pop_assum (qspec_then `f` assume_tac) >> rfs[] >>
    `Normal 0 ≤ NegInf` by fs[N0_EQ_0] >> fs[extreal_le_def]
);

val integral_not_infty_integrable = store_thm(
    "integral_not_infty_integrable",
    ``∀m f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel
        ∧ (integral m f ≠ PosInf) ∧ (integral m f ≠ NegInf) ⇒ integrable m f``,
    rpt strip_tac >> fs[integral_def,integrable_def] >>
    Cases_on `pos_fn_integral m (fn_plus f)` >> Cases_on `pos_fn_integral m (fn_minus f)` >>
    fs[extreal_sub_def]
);

val integrable_integral_not_infty = store_thm(
    "integrable_integral_not_infty",
    ``∀m f. measure_space m ∧ integrable m f ⇒
        (integral m f ≠ PosInf) ∧ (integral m f ≠ NegInf)``,
    rpt strip_tac >> fs[integral_def,integrable_def] >>
    `pos_fn_integral m (fn_plus f) ≠ NegInf` by (
        `0 ≤ pos_fn_integral m (fn_plus f)` by fs[pos_fn_integral_pos,FN_PLUS_POS] >>
        CCONTR_TAC >> fs[extreal_le_def,GSYM N0_EQ_0]) >>
    `pos_fn_integral m (fn_minus f) ≠ NegInf` by (
        `0 ≤ pos_fn_integral m (fn_minus f)` by fs[pos_fn_integral_pos,FN_MINUS_POS] >>
        CCONTR_TAC >> fs[extreal_le_def,GSYM N0_EQ_0]) >>
    Cases_on `pos_fn_integral m (fn_plus f)` >> Cases_on `pos_fn_integral m (fn_minus f)` >>
    fs[extreal_sub_def]
);

val integral_finite_integrable = store_thm(
    "integral_finite_integrable",
    ``∀m f a. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel
        ∧ (integral m f = Normal a) ⇒ integrable m f``,
    rpt strip_tac >> fs[integral_def,integrable_def] >>
    Cases_on `pos_fn_integral m (fn_plus f)` >> Cases_on `pos_fn_integral m (fn_minus f)` >>
    fs[extreal_sub_def]
);

val integrable_integral_finite = store_thm(
    "integrable_integral_finite",
    ``∀m f. measure_space m ∧ integrable m f ⇒ ∃a. integral m f = Normal a``,
    rw[] >> dxrule_all_then assume_tac integrable_integral_not_infty >> fs[] >>
    Cases_on `integral m f` >> fs[]
);

val integrable_alt_abs = store_thm(
    "integrable_alt_abs",
    ``∀m f. measure_space m ⇒ (integrable m f ⇔
        f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        pos_fn_integral m (abs ∘ f) ≠ PosInf)``,
    rw[integrable_def,o_DEF] >> 
    Cases_on `f ∈ measurable (m_space m,measurable_sets m) Borel` >> rw[] >>
    `(λx. abs (f x)) = (λx. (fn_plus f) x + (fn_minus f) x)` by (rw[FUN_EQ_THM] >>
        (qspecl_then [`f x`,`0`] assume_tac) lt_total >> fs[fn_plus_def,fn_minus_def]
        >- (rw[lt_refl,add_rzero,abs_refl,le_refl]) >>
        rw[extreal_abs_alt,add_lzero,add_rzero] >> fs[extreal_lt_def] >>
        fs[GSYM extreal_lt_def] >> metis_tac[lt_antisym]) >>
    rw[] >> pop_assum kall_tac >>
    `pos_fn_integral m (λx. fn_plus f x + fn_minus f x) =
        pos_fn_integral m (fn_plus f) + pos_fn_integral m (fn_minus f)` by (
        irule pos_fn_integral_add >>
        rw[FN_PLUS_POS,FN_MINUS_POS,IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS]) >>
    rw[] >> pop_assum kall_tac >>
    Cases_on `pos_fn_integral m (fn_plus f)` >> Cases_on `pos_fn_integral m (fn_minus f)` >>
    rw[extreal_add_def]
);

val integrable_abs = store_thm(
    "integrable_abs",
    ``∀m f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        (integrable m f ⇔ integrable m (abs ∘ f))``,
    rw[] >> fs[integrable_alt_abs] >>
    drule_all_then assume_tac MEASURE_SPACE_SIGMA_ALGEBRA >>
    rw[IN_MEASURABLE_BOREL_ABS_ALT] >>
    `(abs ∘ abs ∘ f) = (abs ∘ f)` suffices_by rw[] >>
    rw[FUN_EQ_THM,abs_abs]
);

val integral_indicator_null_set = store_thm(
    "integral_indicator_null_set",
    ``∀m s f. measure_space m ∧ null_set m s ⇒ (integral m (indicator_fn s) = 0)``,
    rpt strip_tac >> fs[null_set_def,integral_indicator,extreal_eq_zero]
);

val integral_disjoint_sets = store_thm(
    "integral_disjoint_sets",
    ``∀m f s t. measure_space m ∧ DISJOINT s t ∧ s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        (integral m (λx. f x * indicator_fn (s ∪ t) x) =
        integral m (λx. f x * indicator_fn s x) + integral m (λx. f x * indicator_fn t x))``,
    rw[integral_def,FN_PLUS_MUL_INDICATOR,FN_MINUS_MUL_INDICATOR] >>
    `∀x. 0 ≤ fn_plus f x` by fs[FN_PLUS_POS] >> `∀x. 0 ≤ fn_minus f x` by fs[FN_MINUS_POS] >>
    `fn_plus f ∈ measurable (m_space m,measurable_sets m) Borel`
        by imp_res_tac IN_MEASURABLE_BOREL_FN_PLUS >>
    `fn_minus f ∈ measurable (m_space m,measurable_sets m) Borel`
        by imp_res_tac IN_MEASURABLE_BOREL_FN_MINUS >>
    (qspecl_then [`m`,`fn_plus f`,`s`,`t`] assume_tac) pos_fn_integral_disjoint_sets >>
    (qspecl_then [`m`,`fn_minus f`,`s`,`t`] assume_tac) pos_fn_integral_disjoint_sets >>
    rfs[] >> NTAC 2 (pop_assum kall_tac) >>
    `∀x. 0 ≤ (λx. fn_plus f x * indicator_fn s x) x` by (strip_tac >> fs[indicator_fn_def] >>
        Cases_on `x ∈ s` >> fs[mul_rzero,mul_rone,le_refl]) >>
    `∀x. 0 ≤ (λx. fn_plus f x * indicator_fn t x) x` by (strip_tac >> fs[indicator_fn_def] >>
        Cases_on `x ∈ t` >> fs[mul_rzero,mul_rone,le_refl]) >>
    `∀x. 0 ≤ (λx. fn_minus f x * indicator_fn s x) x` by (strip_tac >> fs[indicator_fn_def] >>
        Cases_on `x ∈ s` >> fs[mul_rzero,mul_rone,le_refl]) >>
    `∀x. 0 ≤ (λx. fn_minus f x * indicator_fn t x) x` by (strip_tac >> fs[indicator_fn_def] >>
        Cases_on `x ∈ t` >> fs[mul_rzero,mul_rone,le_refl]) >>
    imp_res_tac pos_fn_integral_pos >> fs[GSYM N0_EQ_0] >>
    Cases_on `pos_fn_integral m (λx. fn_plus f x * indicator_fn s x)` >>
    Cases_on `pos_fn_integral m (λx. fn_plus f x * indicator_fn t x)` >>
    Cases_on `pos_fn_integral m (λx. fn_minus f x * indicator_fn s x)` >>
    Cases_on `pos_fn_integral m (λx. fn_minus f x * indicator_fn t x)` >>
    fs[extreal_le_def,extreal_sub_def,extreal_add_def] >> rpt (pop_assum kall_tac) >>
    fs[REAL_ADD2_SUB2]
);

val integrable_disjoint_sets = store_thm(
    "integrable_disjoint_sets",
    ``∀m f s t. measure_space m ∧ DISJOINT s t ∧
        integrable m (λx. f x * indicator_fn s x) ∧
        integrable m (λx. f x * indicator_fn t x) ⇒
        integrable m (λx. f x * indicator_fn (s ∪ t) x)``,
    rw[] >> dxrule_all_then assume_tac integrable_add >>
    `(λx. (λx. f x * indicator_fn t x) x + (λx. f x * indicator_fn s x) x) =
        (λx. f x * indicator_fn (s ∪ t) x)` suffices_by (rw[] >> fs[]) >>
    rw[FUN_EQ_THM] >>
    `f x * indicator_fn t x + f x * indicator_fn s x =
        f x * (indicator_fn t x + indicator_fn s x)` by (irule (GSYM add_ldistrib) >>
        Cases_on `x ∈ s` >> Cases_on `x ∈ t` >> rw[indicator_fn_def,le_refl,le_01]) >>
    rw[] >> pop_assum kall_tac >>
    `indicator_fn t x + indicator_fn s x = indicator_fn (s ∪ t) x`
        suffices_by (rw[] >> fs[]) >>
    Cases_on `x ∈ s` >> Cases_on `x ∈ t` >> rw[indicator_fn_def,add_lzero,add_rzero] >>
    fs[DISJOINT_DEF,EXTENSION] >> last_x_assum (qspec_then `x` assume_tac) >> rfs[]
);

val integral_disjoint_sets_alt = store_thm(
    "integral_disjoint_sets_alt",
    ``∀m f s t. measure_space m ∧ DISJOINT s t ∧
        s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧
        (λx. f x * indicator_fn (s ∪ t) x) ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        (integral m (λx. f x * indicator_fn (s ∪ t) x) =
        integral m (λx. f x * indicator_fn s x) + integral m (λx. f x * indicator_fn t x))``,
    rw[] >> dxrule_all_then assume_tac integral_disjoint_sets >>
    `((λx. (λx. f x * indicator_fn (s ∪ t) x) x * indicator_fn (s ∪ t) x) =
        (λx. f x * indicator_fn (s ∪ t) x)) ∧
        ((λx. (λx. f x * indicator_fn (s ∪ t) x) x * indicator_fn s x) =
        (λx. f x * indicator_fn s x)) ∧
        ((λx. (λx. f x * indicator_fn (s ∪ t) x) x * indicator_fn t x) =
        (λx. f x * indicator_fn t x))` suffices_by (rw[] >> fs[]) >>
    rw[FUN_EQ_THM] >> Cases_on `x ∈ s` >> Cases_on `x ∈ t` >>
    rw[indicator_fn_def,mul_rzero,mul_rone]
);

val integral_const = store_thm(
    "integral_const",
    ``∀m c. measure_space m ⇒ (integral m (λx. Normal c) = Normal (c * measure m (m_space m)))``,
    rpt strip_tac >> imp_res_tac integral_mspace >>
    pop_assum (qspec_then `(λx. Normal c)` assume_tac) >>
    fs[] >> pop_assum kall_tac >>
    `m_space m ∈ measurable_sets m` by fs[MEASURE_SPACE_MSPACE_MEASURABLE] >>
    fs[integral_cmul_indicator]
);

val integral_sub = store_thm(
    "integral_sub",
    ``∀m f g. measure_space m ∧ integrable m f ∧ integrable m g ⇒
        (integral m (λx. f x - g x) = integral m f - integral m g)``,
    rpt strip_tac >>
    `integrable m (λx. -g x)` by (imp_res_tac integrable_cmul >>
        NTAC 2 (qpat_x_assum `∀c. _` (qspec_then `-1` assume_tac)) >>
        fs[NM1_EQ_M1] >> metis_tac[neg_minus1]) >>
    `integral m (λx. -g x) = -integral m g` by (imp_res_tac integral_cmul >>
        NTAC 3 (qpat_x_assum `∀c. _` (qspec_then `-1` assume_tac)) >>
        fs[NM1_EQ_M1] >> metis_tac[neg_minus1]) >>
    (qspecl_then [`m`,`f`,`(λx. -g x)`] assume_tac) integral_add >> rfs[extreal_sub_add]
);

val integral_eq_fun_eq_mspace = store_thm(
    "integral_eq_fun_eq_mspace",
    ``∀m f g. measure_space m ∧ (∀x. x ∈ m_space m ⇒ (f x = g x)) ⇒ (integral m f = integral m g)``,
    rpt strip_tac >>
    `integral m (λx. f x * indicator_fn (m_space m) x) =
        integral m (λx. g x * indicator_fn (m_space m) x)`
        suffices_by (strip_tac >> metis_tac[integral_mspace]) >>
    `(λx. f x * indicator_fn (m_space m) x) = (λx. g x * indicator_fn (m_space m) x)`
        suffices_by (strip_tac >> fs[]) >>
    fs[FUN_EQ_THM] >> strip_tac >> fs[indicator_fn_def] >>
    Cases_on `x ∈ m_space m` >> fs[mul_rzero,mul_rone]
);

val pos_fn_integral_null_set = store_thm(
    "pos_fn_integral_null_set",
    ``∀m s f. (measure_space m) ∧ (null_set m s) ∧ (∀x. 0 ≤ f x) ⇒
        (pos_fn_integral m (λx. f x * indicator_fn s x) = 0)``,
    rw[null_set_def] >>
    drule_all_then assume_tac pos_fn_integral_cmul_infty >> rfs[N0_EQ_0,mul_rzero] >>
    `pos_fn_integral m (λx. 0) ≤ pos_fn_integral m (λx. f x * indicator_fn s x)`
        by (irule pos_fn_integral_mono >> rw[indicator_fn_def,le_refl,mul_rzero,mul_rone]) >>
    `pos_fn_integral m (λx. f x * indicator_fn s x) ≤
        pos_fn_integral m (λx. PosInf * indicator_fn s x)` by (irule pos_fn_integral_mono >>
        rw[indicator_fn_def,le_refl,mul_rzero,mul_rone,le_infty]) >>
    rfs[pos_fn_integral_zero] >> rw[GSYM le_antisym]
);

val integral_null_set = store_thm(
    "integral_null_set",
    ``∀m s f. (measure_space m) ∧ (null_set m s) ⇒ (integral m (λx. f x * indicator_fn s x) = 0)``,
    rw[integral_def] >>
    `(pos_fn_integral m (fn_plus (λx. f x * indicator_fn s x)) = 0) ∧
        (pos_fn_integral m (fn_minus (λx. f x * indicator_fn s x)) = 0)`
        suffices_by (rw[] >> fs[extreal_sub_add,add_lzero,neg_0]) >>
    rw[FN_PLUS_MUL_INDICATOR,FN_MINUS_MUL_INDICATOR] >> irule pos_fn_integral_null_set >>
    rw[FN_PLUS_POS,FN_MINUS_POS]
);

val integrable_abs_infty_null = store_thm(
    "integrable_abs_infty_null",
    ``∀m f. measure_space m ∧ integrable m f ⇒
        null_set m {x | x ∈ m_space m ∧ (abs (f x) = PosInf)}``,
    rw[] >> (qspecl_then [`m`,`f`] assume_tac) integrable_fn_plus >>
    (qspecl_then [`m`,`f`] assume_tac) integrable_fn_minus >> rfs[] >>
    NTAC 2 (drule_then assume_tac integrable_infty_null >> pop_assum (dxrule_then assume_tac)) >>
    `{x | x ∈ m_space m ∧ (abs (f x) = PosInf)} =
        {x | x ∈ m_space m ∧ (fn_plus f x = PosInf)} ∪
        {x | x ∈ m_space m ∧ (fn_minus f x = PosInf)}` by (rw[EXTENSION] >>
        Cases_on `f x` >> rw[extreal_abs_def,fn_plus_def,fn_minus_def] >>
        fs[GSYM N0_EQ_0,extreal_lt_alt,extreal_le_def,extreal_ainv_def]) >>
    rw[MEASURE_SPACE_UNION_NULL]
);

val integral_eq_fun_eq_a_e = store_thm(
    "integral_eq_fun_eq_a_e",
    ``∀m f g. measure_space m ∧ a_e m {x | f x = g x} ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        g ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        (integral m f = integral m g)``,
    rw[a_e_def] >> drule_all_then assume_tac integral_null_set >> fs[null_set_def] >>
    map_every (fn tm => (qspecl_then [`m`,tm] assume_tac) integral_mspace) [`f`,`g`] >> rfs[] >>
    NTAC 2 (pop_assum kall_tac) >> Q.ABBREV_TAC `s = {x | f x = g x}` >>
    `m_space m ∩ s ∈ measurable_sets m` by (
        (qspecl_then [`m`,`m_space m`,`m_space m DIFF s`] assume_tac) MEASURE_SPACE_DIFF >>
        rfs[MEASURE_SPACE_MSPACE_MEASURABLE,DIFF_DIFF2]) >>
    `DISJOINT (m_space m ∩ s) (m_space m DIFF s)` by (rw[DISJOINT_DEF,EXTENSION] >>
        Cases_on `x ∈ s` >> rw[]) >>
    map_every (fn tm => (qspecl_then [`m`,tm,`m_space m ∩ s`,`m_space m DIFF s`] assume_tac)
        integral_disjoint_sets) [`f`,`g`] >>
    rfs[UNION_INTER_DIFF,add_rzero] >> NTAC 2 (pop_assum kall_tac) >> 
    irule integral_eq_fun_eq_mspace >> Q.UNABBREV_TAC `s` >> rw[indicator_fn_def,mul_rzero]
);

val integrable_mul_indicator = store_thm(
    "integrable_mul_indicator",
    ``∀m s f. (measure_space m) ∧ (s ∈ measurable_sets m) ∧ (integrable m f)
        ⇒ (integrable m (λx. f x * indicator_fn s x))``,
    rw[integrable_def]
    >- (irule IN_MEASURABLE_BOREL_MUL_INDICATOR >>
        rw[subsets_def,MEASURE_SPACE_SIGMA_ALGEBRA])
    >- (MATCH_MP_TAC LE_NE_POSINF_IMP_NE_POSINF >>
        qexists_tac `pos_fn_integral m (fn_plus f)` >> rw[] >>
        irule pos_fn_integral_mono >> rw[] >> Cases_on `x ∈ s` >>
        rw[indicator_fn_def,fn_plus_def,mul_rzero,mul_rone,le_refl,le_lt])
    >- (MATCH_MP_TAC LE_NE_POSINF_IMP_NE_POSINF >>
        qexists_tac `pos_fn_integral m (fn_minus f)` >> rw[] >>
        irule pos_fn_integral_mono >> rw[] >> Cases_on `x ∈ s` >>
        rw[indicator_fn_def,fn_minus_def,mul_rzero,mul_rone,le_refl,neg_0] >>
        `-0 ≤ -f x` suffices_by rw[neg_0] >> rw[le_neg] >> rw[le_lt])
);

val int_fn_plus_indic_le_int_fn_plus = store_thm(
    "int_fn_plus_indic_le_int_fn_plus",
    ``∀m f s. measure_space m ⇒
        pos_fn_integral m (fn_plus (λx. f x * indicator_fn s x)) ≤ pos_fn_integral m (fn_plus f)``,
    rw[] >> irule pos_fn_integral_mono >> rw[FN_PLUS_POS] >>
    Cases_on `x ∈ s` >> Cases_on `0 < f x` >>
    rw[fn_plus_def,indicator_fn_def,mul_rzero,mul_rone,le_lt]
);

val int_fn_minus_indic_le_int_fn_minus = store_thm(
    "int_fn_minus_indic_le_int_fn_minus",
    ``∀m f s. measure_space m ⇒
        pos_fn_integral m (fn_minus (λx. f x * indicator_fn s x)) ≤ pos_fn_integral m (fn_minus f)``,
    rw[] >> irule pos_fn_integral_mono >> rw[FN_MINUS_POS] >>
    Cases_on `x ∈ s` >> Cases_on `f x < 0` >>
    fs[fn_minus_def,indicator_fn_def,mul_rzero,mul_rone,neg_0,le_refl] >>
    `-0 ≤ -f x` suffices_by rw[neg_0] >> rw[le_neg] >> rw[le_lt]
);

val pos_simple_fn_part = store_thm(
    "pos_simple_fn_part",
    ``∀m f s a x. measure_space m ∧ pos_simple_fn m f s a x ⇒
        ∀y i. i ∈ s ∧ y ∈ a i ⇒ (f y = Normal (x i))``,
    rpt strip_tac >> fs[pos_simple_fn_def] >>
    `a i ∈ measurable_sets m` by RES_TAC >>
    `a i ⊆ m_space m` by fs[MEASURABLE_SETS_SUBSET_SPACE] >> fs[SUBSET_DEF] >>
    `SIGMA (λi. Normal (x i) * indicator_fn (a i) y) s =
        SIGMA (λi. Normal (x i) * indicator_fn (a i) y) ({i} ∪ (s DIFF {i}))` by (
        fs[UNION_DIFF]) >> fs[EXTREAL_SUM_IMAGE_DISJOINT_UNION] >> pop_assum kall_tac >>
    `SIGMA (λi. Normal (x i) * indicator_fn (a i) y) (s DIFF {i}) = 0` by (
        `FINITE (s DIFF {i})` by fs[DELETE_DEF,FINITE_DELETE] >>
        `(∀j. j ∈ (s DIFF {i}) ⇒ ((λi. Normal (x i) * indicator_fn (a i) y) j = 0))` by (
            rpt strip_tac >> fs[DIFF_DEF] >> `DISJOINT (a i) (a j)` by fs[] >>
            `y ∉ a j` by fs[DISJOINT_ALT] >> fs[indicator_fn_def,mul_rzero]) >>
        fs[EXTREAL_SUM_IMAGE_0]) >>
    fs[EXTREAL_SUM_IMAGE_SING,add_rzero,indicator_fn_def,mul_rone] 
);

val pos_simple_fn_not_part = store_thm(
    "pos_simple_fn_not_part",
    ``∀m f s a x y. measure_space m ∧ pos_simple_fn m f s a x ∧ y ∉ m_space m ⇒
        (SIGMA (λi. Normal (x i) * indicator_fn (a i) y) s = 0)``,
    rpt strip_tac >> fs[pos_simple_fn_def] >>
    `∀i. i ∈ s ⇒ ((λi. Normal (x i) * indicator_fn (a i) y) i = 0)` suffices_by (
        rpt strip_tac >> imp_res_tac EXTREAL_SUM_IMAGE_0) >>
    rpt strip_tac >> Cases_on `y ∈ a i` >> fs[indicator_fn_def,mul_rzero,mul_rone] >>
    `a i ∈ measurable_sets m` by RES_TAC >>
    `a i ⊆ m_space m` by fs[MEASURABLE_SETS_SUBSET_SPACE] >>
    fs[SUBSET_DEF]
);

val pos_simple_fn_restricted = store_thm(
    "pos_simple_fn_restricted",
    ``∀m r f s a x. measure_space m ∧ r ∈ measurable_sets m ∧ (∀x. 0 ≤ f x) ∧
        pos_simple_fn m (λx. f x * indicator_fn r x) s a x ⇒
        pos_simple_fn (r,IMAGE (λt. r ∩ t) (measurable_sets m),measure m) f s
        (λi. r ∩ a i) x``,
    rpt strip_tac >> fs[pos_simple_fn_def] >> rw[] >> rpt strip_tac
    >- (fs[m_space_def] >> `r ⊆ m_space m` by fs[MEASURABLE_SETS_SUBSET_SPACE] >>
        fs[SUBSET_DEF] >> NTAC 2 RES_TAC >>
        `SIGMA (λi. Normal (x i) * indicator_fn (r ∩ a i) t) s =
            SIGMA (λi. Normal (x i) * indicator_fn (a i) t) s` suffices_by (strip_tac >>
            fs[indicator_fn_def] >> pop_assum kall_tac >>
            qpat_x_assum `∀x. _ ⇒ x ∈ m_space m` kall_tac >>
            qpat_x_assum `∀x. x ∈ m_space m ⇒ _` kall_tac >>
            rfs[mul_rone]) >> pop_assum kall_tac >>
        `(λi. Normal (x i) * indicator_fn (r ∩ a i) t) =
            (λi. Normal (x i) * indicator_fn (a i) t)` suffices_by (strip_tac >> fs[]) >>
        fs[FUN_EQ_THM] >> strip_tac >>
        `indicator_fn (r ∩ a i) t = indicator_fn (a i) t` suffices_by fs[] >>
        fs[indicator_fn_def,INTER_DEF])
    >- (fs[measurable_sets_def,IMAGE_DEF] >> exists_tac ``(a : num -> α -> bool) i`` >> fs[])
    >- (`DISJOINT (a i) (a i')` by fs[] >> fs[DISJOINT_DEF,INTER_DEF,EXTENSION] >>
        strip_tac >> pop_assum (qspec_then `x'` assume_tac) >> fs[])
    >- (fs[m_space_def,EXTENSION,IN_BIGUNION_IMAGE] >> strip_tac >> Cases_on `x' ∈ r` >> fs[] >>
        `r ⊆ m_space m` by fs[MEASURABLE_SETS_SUBSET_SPACE] >> fs[SUBSET_DEF])
);

val pos_simple_fn_integral_restricted = store_thm(
    "pos_simple_fn_integral_restricted",
    ``∀m r s a x. measure_space m ∧ r ∈ measurable_sets m ∧
        (∃f. (∀x. 0 ≤ f x) ∧ pos_simple_fn m (λx. f x * indicator_fn r x) s a x) ⇒
        (pos_simple_fn_integral m s a x =
        pos_simple_fn_integral (r,IMAGE (λt. r ∩ t) (measurable_sets m),measure m) s (λi. r ∩ a i) x)``,
    rpt strip_tac >> imp_res_tac pos_simple_fn_restricted >> fs[pos_simple_fn_integral_def] >>
    `∀i. i ∈ s ⇒ ((λi. x i * measure m (a i)) i =
        (λi. x i * measure (r,IMAGE (λt. r ∩ t) (measurable_sets m),measure m) (r ∩ a i)) i)`
        suffices_by (rpt strip_tac >> `FINITE s` by fs[pos_simple_fn_def] >> fs[REAL_SUM_IMAGE_EQ]) >>
    rpt strip_tac >> fs[] >> Cases_on `x i = 0` >> fs[measure_def] >>
    `a i = r ∩ a i` suffices_by (strip_tac >> metis_tac[]) >>
    fs[INTER_DEF,EXTENSION] >> strip_tac >> Cases_on `x' ∈ a i` >> fs[] >> CCONTR_TAC >>
    `f x' * indicator_fn r x' = Normal (x i)` by (imp_res_tac pos_simple_fn_part >> fs[]) >>
    rfs[indicator_fn_def,mul_rzero] >> fs[GSYM N0_EQ_0]
);

val pos_simple_fn_extension = store_thm(
    "pos_simple_fn_extension",
    ``∀m r f s a x k. measure_space m ∧ r ∈ measurable_sets m ∧ k ∉ s ∧
        pos_simple_fn (r,IMAGE (λt. r ∩ t) (measurable_sets m),measure m) f s a x ⇒
        pos_simple_fn m (λx. f x * indicator_fn r x) (s ∪ {k})
        (λi. if i = k then m_space m DIFF r else a i) (λi. if i = k then 0 else x i)``,
    rpt strip_tac >> fs[pos_simple_fn_def] >> rw[] >> rpt strip_tac
    >- (Cases_on `x' ∈ r` >> fs[indicator_fn_def,mul_rzero,mul_rone,le_refl])
    >- (Q.ABBREV_TAC `sigf = (λi. Normal (if i = k then 0 else x i) *
            indicator_fn (if i = k then m_space m DIFF r else a i) x')` >>
        `SIGMA sigf (s ∪ {k}) = SIGMA sigf s + SIGMA sigf {k}` by (
            `FINITE {k}` by fs[FINITE_SING] >>
            `DISJOINT s {k}` suffices_by fs[EXTREAL_SUM_IMAGE_DISJOINT_UNION] >>
            fs[DISJOINT_DEF,EXTENSION]) >> fs[] >> pop_assum kall_tac >>
        Q.UNABBREV_TAC `sigf` >> fs[EXTREAL_SUM_IMAGE_SING,N0_EQ_0,mul_lzero,add_rzero] >>
        Q.ABBREV_TAC `fext = (λi. Normal (if i = k then 0 else x i) *
            indicator_fn (if i = k then m_space m DIFF r else a i) x')` >>
        Q.ABBREV_TAC `fres = (λi. Normal (x i) * indicator_fn (a i) x')` >>
        `SIGMA fext s = SIGMA fres s` by (
            `∀i. i ∈ s ⇒ (fext i = fres i)` suffices_by (rpt strip_tac >>
                imp_res_tac EXTREAL_SUM_IMAGE_EQ) >>
            rpt strip_tac >> Q.UNABBREV_TAC `fext` >> Q.UNABBREV_TAC `fres` >>
            `i ≠ k` by (CCONTR_TAC >> fs[]) >> fs[]) >> fs[] >>
        pop_assum kall_tac >> Q.UNABBREV_TAC `fext` >> Q.UNABBREV_TAC `fres` >>
        Cases_on `x' ∈ r` >> fs[indicator_fn_def,mul_rzero,mul_rone,m_space_def] >>
        (qspecl_then [`(r,IMAGE (λt. r ∩ t) (measurable_sets m),measure m)`,
            `f`,`s`,`a`,`x`,`x'`] assume_tac) pos_simple_fn_not_part >>
        imp_res_tac MEASURE_SPACE_RESTRICTED >> fs[m_space_def] >> rfs[] >> pop_assum kall_tac >>
        rfs[pos_simple_fn_def,indicator_fn_def,m_space_def])
    >- (imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >> fs[MEASURE_SPACE_DIFF])
    >- (RES_TAC >> fs[measurable_sets_def,MEASURE_SPACE_INTER])
    >- (fs[DISJOINT_DEF,EXTENSION] >> strip_tac >>
        Cases_on `x' ∈ a i'` >> fs[measurable_sets_def] >>
        RES_TAC >> fs[INTER_DEF,EXTENSION])
    >- (fs[DISJOINT_DEF,EXTENSION] >> strip_tac >>
        Cases_on `x' ∈ a i` >> fs[measurable_sets_def] >>
        RES_TAC >> fs[INTER_DEF,EXTENSION])
    >- (`BIGUNION (IMAGE (λi. if i = k then m_space m DIFF r else a i) s) = r`
            suffices_by (strip_tac >> fs[MEASURABLE_SETS_SUBSET_SPACE,UNION_DIFF]) >>
        `IMAGE (λi. if i = k then m_space m DIFF r else a i) s = IMAGE a s`
            suffices_by (strip_tac >> fs[m_space_def]) >>
        fs[IMAGE_DEF,EXTENSION] >> strip_tac >> eq_tac >> rpt strip_tac
        >- (exists_tac ``i:num`` >> fs[] >> strip_tac >>
            `i ≠ k` by (CCONTR_TAC >> fs[]) >>
            Cases_on `x'' ∈ a i` >> fs[])
        >- (exists_tac ``x'':num`` >> fs[] >> strip_tac >>
            `x'' ≠ k` by (CCONTR_TAC >> fs[]) >>
            Cases_on `x'³' ∈ a x''` >> fs[]))
);

val pos_simple_fn_integral_extension = store_thm(
    "pos_simple_fn_integral_extension",
    ``∀m r f s a x k. measure_space m ∧ r ∈ measurable_sets m ∧ k ∉ s ∧
        pos_simple_fn (r,IMAGE (λt. r ∩ t) (measurable_sets m),measure m) f s a x ⇒
        (pos_simple_fn_integral (r,IMAGE (λt. r ∩ t) (measurable_sets m),measure m) s a x =
        pos_simple_fn_integral m (s ∪ {k}) (λi. if i = k then m_space m DIFF r else a i)
        (λi. if i = k then 0 else x i))``,
    rpt strip_tac >> imp_res_tac pos_simple_fn_extension >> fs[pos_simple_fn_integral_def] >>
    Q.ABBREV_TAC `sigf = (λi. (if i = k then 0 else x i) *
        measure m (if i = k then m_space m DIFF r else a i))` >>
    `SIGMA sigf (s ∪ {k}) = SIGMA sigf s + SIGMA sigf {k}` by (
        `FINITE s` by fs[pos_simple_fn_def] >> `FINITE {k}` by fs[FINITE_SING] >>
        `DISJOINT s {k}` suffices_by fs[REAL_SUM_IMAGE_DISJOINT_UNION] >>
        fs[DISJOINT_DEF,EXTENSION]) >> fs[] >> pop_assum kall_tac >>
    Q.UNABBREV_TAC `sigf` >> fs[REAL_SUM_IMAGE_SING] >>
    `∀i. i ∈ s ⇒
        ((λi. x i * measure (r,IMAGE (λt. r ∩ t) (measurable_sets m),measure m) (a i)) i =
        (λi. (if i = k then 0 else x i) * measure m (if i = k then m_space m DIFF r else a i)) i)`
        suffices_by (rpt strip_tac >> `FINITE s` by fs[pos_simple_fn_def] >> fs[REAL_SUM_IMAGE_EQ]) >>
    rpt strip_tac >> `i ≠ k` by (CCONTR_TAC >> fs[]) >> fs[] >>
    Cases_on `x i = 0` >> fs[measure_def]
);

val pos_fn_integral_restricted = store_thm(
    "pos_fn_integral_restricted",
    ``∀m s f. measure_space m ∧ s ∈ measurable_sets m ∧ (∀x. 0 ≤ f x) ⇒
        (pos_fn_integral m (λx. f x * indicator_fn s x) =
        pos_fn_integral (s,IMAGE (λt. s ∩ t) (measurable_sets m),measure m) f)``,
    rpt strip_tac >> fs[pos_fn_integral_def] >>
    `{r | (∃g. r ∈ psfis m g ∧ ∀x. g x ≤ f x * indicator_fn s x)} =
        {r | (∃g. r ∈ psfis (s,IMAGE (λt. s ∩ t) (measurable_sets m),measure m) g ∧ ∀x. g x ≤ f x)}`
        suffices_by (strip_tac >> fs[]) >> fs[EXTENSION] >> strip_tac >>
    fs[IN_psfis_eq] >> eq_tac >> rpt strip_tac >> fs[]
    >- (exists_tac ``g: α -> extreal`` >>
        `∀x. g x ≤ f x` by (strip_tac >> `g x'' ≤ f x'' * indicator_fn s x''` by fs[] >>
            Cases_on `x'' ∈ s` >> fs[indicator_fn_def,mul_rzero,mul_rone] >>
            metis_tac[le_trans]) >> fs[] >>
        map_every exists_tac
            [``s': num -> bool``,``(λi. s ∩ a i): num -> α -> bool``,``x': num -> real``] >>
        (qspecl_then [`m`,`s`,`g`,`s'`,`a`,`x'`] assume_tac) pos_simple_fn_restricted >>
        `(∀x. 0 ≤ g x)` by fs[pos_simple_fn_def] >> rfs[] >> fs[] >>
        `(λx. g x * indicator_fn s x) = g` by (fs[FUN_EQ_THM] >> strip_tac >>
            Cases_on `x'' ∈ s` >> fs[indicator_fn_def,mul_rzero,mul_rone] >>
            NTAC 4 (qpat_x_assum `∀x. _` (qspec_then `x''` assume_tac)) >> rfs[mul_rzero] >>
            metis_tac[le_antisym]) >> fs[] >> qpat_x_assum `_ ⇒ _` kall_tac >>
        (qspecl_then [`m`,`s`,`s'`,`a`,`x'`] assume_tac) pos_simple_fn_integral_restricted >> rfs[] >>
        `(∃f. (∀x. 0 ≤ f x) ∧ pos_simple_fn m (λx. f x * indicator_fn s x) s' a x')`
            suffices_by (rpt strip_tac >> RES_TAC) >> pop_assum kall_tac >>
        exists_tac ``g: α -> extreal`` >> fs[])
    >- (exists_tac ``(λx. g x * indicator_fn s x): α -> extreal`` >> fs[] >>
        `∀x. g x * indicator_fn s x ≤ f x * indicator_fn s x` by (strip_tac >>
            Cases_on `x'' ∈ s` >> fs[indicator_fn_def,mul_rzero,mul_rone,le_refl]) >> fs[] >>
        `∃k. k ∉ s'` by (fs[pos_simple_fn_def] >> assume_tac INFINITE_NUM_UNIV >>
            imp_res_tac NOT_IN_FINITE >> exists_tac ``x'':num`` >> fs[]) >>
        imp_res_tac pos_simple_fn_extension >>
        map_every exists_tac [``(s' ∪ {k}): num -> bool``,
            ``(λi. if (i = k) then ((m_space m) DIFF s) else a i): num -> α -> bool``,
            ``(λi. if (i = k) then 0 else x' i): num -> real``] >>
        fs[] >> pop_assum kall_tac >> imp_res_tac pos_simple_fn_integral_extension)
);

val integral_restricted = store_thm(
    "integral_restricted",
    ``∀m s f. measure_space m ∧ s ∈ measurable_sets m ⇒ (integral m (λx. f x * indicator_fn s x) =
        integral (s,IMAGE (λt. s ∩ t) (measurable_sets m),measure m) f)``,
    rpt strip_tac >> fs[integral_def,FN_PLUS_MUL_INDICATOR,FN_MINUS_MUL_INDICATOR] >>
    `(∀x. 0 ≤ fn_plus f x)` by fs[FN_PLUS_POS] >>
    `(∀x. 0 ≤ fn_minus f x)` by fs[FN_MINUS_POS] >>
    fs[pos_fn_integral_restricted] >>
    `(λx. fn_plus f x) = (fn_plus f)` by fs[FUN_EQ_THM] >>
    `(λx. fn_minus f x) = (fn_minus f)` by fs[FUN_EQ_THM] >> fs[]
);

val integrable_restricted = store_thm(
    "integrable_restricted",
    ``∀m s f. measure_space m ∧ s ∈ measurable_sets m ∧ integrable m f ⇒
        integrable (s,IMAGE (λt. s ∩ t) (measurable_sets m),measure m) f``,
    rpt strip_tac >> fs[integrable_def,m_space_def,measurable_sets_def] >>
    fs[MEASURABLE_RESTRICTED] >> imp_res_tac MEASURE_SPACE_SUBSET_MSPACE >>
    (qspec_then `f` assume_tac) FN_PLUS_POS >> (qspec_then `f` assume_tac) FN_MINUS_POS >>
    fs[GSYM pos_fn_integral_restricted] >>
    imp_res_tac pos_fn_integral_mspace >> fs[] >> NTAC 2 (pop_assum kall_tac) >>
    Q.ABBREV_TAC `fp = fn_plus f` >> Q.ABBREV_TAC `fm = fn_minus f` >> Q.ABBREV_TAC `msp = m_space m` >>
    fs[SUBSET_DEF] >>
    `∀x. 0 ≤ (λx. fp x * indicator_fn s x) x` by (strip_tac >> Cases_on `x ∈ s` >>
        fs[indicator_fn_def,mul_rzero,mul_rone,le_refl]) >>
    `∀x. 0 ≤ (λx. fm x * indicator_fn s x) x` by (strip_tac >> Cases_on `x ∈ s` >>
        fs[indicator_fn_def,mul_rzero,mul_rone,le_refl]) >>
    `∀x. 0 ≤ (λx. fp x * indicator_fn msp x) x` by (strip_tac >> Cases_on `x ∈ msp` >>
        fs[indicator_fn_def,mul_rzero,mul_rone,le_refl]) >>
    `∀x. 0 ≤ (λx. fm x * indicator_fn msp x) x` by (strip_tac >> Cases_on `x ∈ msp` >>
        fs[indicator_fn_def,mul_rzero,mul_rone,le_refl]) >>
    `∀x. x ∈ m_space m ⇒ (λx. fp x * indicator_fn s x) x ≤ (λx. fp x * indicator_fn msp x) x` by (
        rpt strip_tac >> Cases_on `x ∈ s` >> fs[indicator_fn_def,mul_rzero,mul_rone,le_refl]) >>
    `∀x. x ∈ m_space m ⇒ (λx. fm x * indicator_fn s x) x ≤ (λx. fm x * indicator_fn msp x) x` by (
        rpt strip_tac >> Cases_on `x ∈ s` >> fs[indicator_fn_def,mul_rzero,mul_rone,le_refl]) >>
    `pos_fn_integral m (λx. fm x * indicator_fn s x) ≤ pos_fn_integral m (λx. fm x * indicator_fn msp x)`
        by (imp_res_tac pos_fn_integral_mono_mspace) >>
    `pos_fn_integral m (λx. fp x * indicator_fn s x) ≤ pos_fn_integral m (λx. fp x * indicator_fn msp x)`
        by (imp_res_tac pos_fn_integral_mono_mspace) >>
    Cases_on `pos_fn_integral m (λx. fm x * indicator_fn s x)` >>
    Cases_on `pos_fn_integral m (λx. fm x * indicator_fn msp x)` >>
    Cases_on `pos_fn_integral m (λx. fp x * indicator_fn s x)` >>
    Cases_on `pos_fn_integral m (λx. fp x * indicator_fn msp x)` >>
    fs[extreal_le_def]
);

val integral_pos = store_thm(
    "integral_pos",
    ``∀m f. measure_space m ∧ (∀t. t ∈ m_space m ⇒ 0 ≤ f t) ⇒ (0 ≤ integral m f)``,
    rpt strip_tac >> (qspecl_then [`m`,`(λx. 0)`,`f`] assume_tac) integral_mono >>
    rfs[integral_zero]
);

val integral_strict_pos = store_thm(
    "integral_strict_pos",
    ``∀m f. measure_space m ∧ (measure m (m_space m) ≠ 0) ∧ (∀t. t ∈ m_space m ⇒ 0 < f t) ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ⇒ 0 < integral m f``,
    rpt strip_tac >> Q.ABBREV_TAC `X = (λ(n:num). {x | Normal (1 / &SUC n) ≤ f x} ∩ m_space m)` >>
    `X ∈ (𝕌(:num) -> measurable_sets m)` by (Q.UNABBREV_TAC `X` >> fs[FUNSET] >>
        strip_tac >> imp_res_tac IN_MEASURABLE_BOREL_ALL_MEASURE >> fs[]) >>
    `∀n. X n ⊆ X (SUC n)` by (Q.UNABBREV_TAC `X` >> strip_tac >> fs[INTER_DEF,SUBSET_DEF] >>
        rpt strip_tac >>
        `Normal (1 / &SUC (SUC n)) ≤ Normal (1 / &SUC n)`
            suffices_by (strip_tac >> imp_res_tac le_trans) >>
        fs[extreal_le_def,le_rat]) >>
    `m_space m = BIGUNION (IMAGE X 𝕌(:num))` by (Q.UNABBREV_TAC `X` >> fs[EXTENSION] >>
        strip_tac >> Cases_on `x ∈ m_space m` >> fs[]
        >- (`∃n. Normal (1 / &SUC n) ≤ f x` by (Cases_on `f x` >> fs[extreal_le_def] >>
                RES_TAC >> qpat_x_assum `∀t. _ ⇒ _` kall_tac >> rfs[GSYM N0_EQ_0,extreal_lt_alt] >>
                (qspec_then `1 / r` assume_tac) REAL_BIGNUM >> fs[] >>
                `(&n):real < &SUC n` by fs[] >> `1 / r < &SUC n` by imp_res_tac REAL_LT_TRANS >>
                exists_tac ``n:num`` >> `1 / &SUC n < r` suffices_by fs[REAL_LE_LT] >>
                fs[GSYM REAL_INV_1OVER] >> `0 < r⁻¹` by fs[REAL_LT_INV_EQ] >>
                imp_res_tac REAL_LT_INV >> fs[REAL_INV_INV]) >>
            exists_tac ``{x | Normal (1 / &SUC n) ≤ f x ∧ x ∈ m_space m}`` >> fs[] >>
            exists_tac ``n:num`` >> fs[])
        >- (strip_tac >> Cases_on `x ∈ s` >> fs[] >> strip_tac >>
            exists_tac ``x`` >> fs[])) >>
    CCONTR_TAC >>
    `integral m f = 0` by (
        `∀t. t ∈ m_space m ⇒ 0 ≤ f t` by (rpt strip_tac >> RES_TAC >> fs[le_lt]) >>
        imp_res_tac integral_pos >> fs[extreal_lt_def] >> imp_res_tac le_antisym) >>
    qpat_x_assum `¬(_)` kall_tac >> imp_res_tac MONOTONE_CONVERGENCE >>
    qpat_x_assum `m_space m = _` (assume_tac o GSYM) >>
    `measure m ∘ X = (λx. 0)` suffices_by (strip_tac >> fs[] >>
        (qspec_then `0` assume_tac) SEQ_CONST >> imp_res_tac SEQ_UNIQ) >>
    `∀n. measure m (X n) = 0` suffices_by (strip_tac >> fs[o_DEF,FUN_EQ_THM]) >> strip_tac >>
    `integral m (λx. f x * indicator_fn (X n) x) ≤ integral m f` by (
        `(∀t. t ∈ m_space m ⇒ (λx. f x * indicator_fn (X n) x) t ≤ f t)`
            suffices_by (strip_tac >> fs[integral_mono]) >>
        rpt strip_tac >> fs[indicator_fn_def] >> Cases_on `t ∈ X n` >>
        fs[mul_rzero,mul_rone,le_refl] >> RES_TAC >> fs[le_lt]) >>
    `Normal ((1 / &SUC n) * measure m (X n)) ≤ integral m (λx. f x * indicator_fn (X n) x)` by (
        `(∀t. t ∈ m_space m ⇒ (λx. Normal (1 / &SUC n) * indicator_fn (X n) x) t ≤
            (λx. f x * indicator_fn (X n) x) t)` by (rpt strip_tac >> fs[indicator_fn_def] >>
            Cases_on `t ∈ X n` >> fs[mul_rzero,mul_rone,le_refl] >> Q.UNABBREV_TAC `X` >> fs[]) >>
        imp_res_tac integral_mono >> `X n ∈ measurable_sets m` by fs[IN_DEF] >>
        imp_res_tac integral_cmul_indicator >> fs[]) >>
    imp_res_tac le_trans >> NTAC 2 (pop_assum kall_tac) >>
    rfs[GSYM N0_EQ_0,extreal_le_def,GSYM REAL_INV_1OVER] >> fs[REAL_MUL_RINV] >>
    `measure m (X n) / (&SUC n) ≤ 0` by (fs[real_div,REAL_MUL_COMM]) >> fs[REAL_LE_LDIV_EQ] >>
    `X n ∈ measurable_sets m` by fs[IN_DEF] >> imp_res_tac MEASURE_POSITIVE >>
    imp_res_tac REAL_LE_ANTISYM
);

val integral_strict_mono = store_thm(
    "integral_strict_mono",
    ``∀m f g. measure_space m ∧ (measure m (m_space m) ≠ 0) ∧ (∀t. t ∈ m_space m ⇒ f t < g t) ∧
        integrable m f ∧ integrable m g ⇒ integral m f < integral m g``,
    rpt strip_tac >>
    `0 < integral m g - integral m f` suffices_by (strip_tac >>
        imp_res_tac integrable_integral_not_infty >>
        Cases_on `integral m f` >> Cases_on `integral m g` >>
        fs[extreal_lt_alt,extreal_sub_def,GSYM N0_EQ_0] >> rw[] >>
        imp_res_tac REAL_LT_SUB_LADD >> fs[]) >>
    imp_res_tac (GSYM integral_sub) >> fs[] >> NTAC 4 (pop_assum kall_tac) >>
    `integrable m (λx. g x − f x)` by (imp_res_tac integrable_sub) >>
    `∀t. t ∈ m_space m ⇒ 0 < (λx. g x − f x) t` by (rpt strip_tac >> RES_TAC >>
        fs[sub_zero_lt]) >>
    fs[integrable_def,integral_strict_pos]
);

val pos_fn_integral_strict_mono = store_thm(
    "pos_fn_integral_strict_mono",
    ``∀m f g. measure_space m ∧ measure m (m_space m) ≠ 0 ∧ (∀x. 0 ≤ f x) ∧ (∀x. 0 ≤ g x) ∧
        (∀t. t ∈ m_space m ⇒ f t < g t) ∧ pos_fn_integral m f ≠ PosInf ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        g ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        pos_fn_integral m f < pos_fn_integral m g``,
    rw[] >> Cases_on `pos_fn_integral m g = PosInf`
    >- (Cases_on `pos_fn_integral m f` >> rw[extreal_lt_alt]) >>
    (qspecl_then [`m`,`f`,`g`] assume_tac) integral_strict_mono >>
    rfs[integrable_def,integral_def,FN_PLUS_POS_ID,FN_MINUS_POS_ZERO] >>
    rfs[pos_fn_integral_zero,GSYM N0_EQ_0] >> fs[N0_EQ_0,sub_rzero]
);

val pos_fn_integral_strict_pos = store_thm(
    "pos_fn_integral_strict_pos",
    ``∀m f. measure_space m ∧ measure m (m_space m) ≠ 0 ∧ (∀t. t ∈ m_space m ⇒ 0 < f t) ∧
        (∀x. 0 ≤ f x) ∧ f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        0 < pos_fn_integral m f``,
    rw[] >> (qspecl_then [`m`,`(λx. 0)`,`f`] assume_tac) pos_fn_integral_strict_mono >>
    rfs[le_refl,pos_fn_integral_zero,GSYM N0_EQ_0] >> pop_assum irule >>
    irule IN_MEASURABLE_BOREL_CONST_ALT >> rw[MEASURE_SPACE_SIGMA_ALGEBRA]
);

val integral_split = store_thm(
    "integral_split",
    ``∀m f s. measure_space m ∧ s ∈ measurable_sets m ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        (integral m f = integral m (λx. f x * indicator_fn s x) +
        integral m (λx. f x * indicator_fn (m_space m DIFF s) x))``,
    rw[] >> drule_all_then assume_tac MEASURE_SPACE_COMPL >>
    (qspecl_then [`m`,`f`,`s`,`m_space m DIFF s`] assume_tac) integral_disjoint_sets >>
    `s ∪ (m_space m DIFF s) = m_space m` by (rw[DISJOINT_DEF,EXTENSION] >>
        Cases_on `x ∈ s` >> Cases_on `x ∈ m_space m` >> rw[] >>
        `s ⊆ m_space m` by rw[MEASURABLE_SETS_SUBSET_SPACE] >>
        fs[SUBSET_DEF] >> RES_TAC) >>
    fs[GSYM integral_mspace] >> pop_assum kall_tac >> pop_assum irule >>
    rw[DISJOINT_DEF,EXTENSION] >> Cases_on `x ∈ s` >> rw[]
);

val integral_strict_mono_restricted = store_thm(
    "integral_strict_mono_restricted",
    ``∀m f g s. measure_space m ∧ measure m s ≠ 0 ∧ s ∈ measurable_sets m ∧
        (∀t. t ∈ m_space m ⇒ f t ≤ g t) ∧ (∀t. t ∈ s ⇒ f t < g t) ∧
        integrable m f ∧ integrable m g ⇒ integral m f < integral m g``,
    rw[] >>
    `f ∈ measurable (m_space m,measurable_sets m) Borel` by fs[integrable_def] >>
    `g ∈ measurable (m_space m,measurable_sets m) Borel` by fs[integrable_def] >>
    imp_res_tac integral_split >> rw[] >> NTAC 2 (pop_assum kall_tac) >>
    map_every Q.ABBREV_TAC [`fs = (λx. f x * indicator_fn s x)`,
        `fsc = (λx. f x * indicator_fn (m_space m DIFF s) x)`,
        `gs = (λx. g x * indicator_fn s x)`,
        `gsc = (λx. g x * indicator_fn (m_space m DIFF s) x)`,
        `im = (λh. integral m h)`] >> rw[] >>
    `im fs < im gs ∧ im fsc ≤ im gsc` suffices_by (rw[] >>
        `im fsc + im fs < im gsc + im gs` suffices_by (rw[] >> fs[add_comm]) >>
        irule let_add2 >> fs[] >>
        map_every Q.UNABBREV_TAC [`im`,`fsc`] >> fs[] >>
        `integrable m (λx. f x * indicator_fn (m_space m DIFF s) x)`
            suffices_by (strip_tac >> fs[integrable_integral_not_infty]) >>
        irule integrable_mul_indicator >> rw[MEASURE_SPACE_COMPL]) >>
    Q.UNABBREV_TAC `im` >> rw[]
    >- (map_every Q.UNABBREV_TAC [`fs`,`gs`] >> rw[integral_restricted] >>
        irule integral_strict_mono >>
        rw[measure_def,m_space_def,MEASURE_SPACE_RESTRICTED,integrable_restricted])
    >- (map_every Q.UNABBREV_TAC [`fsc`,`gsc`] >> irule integral_mono >>
        rw[indicator_fn_def,mul_rzero,mul_rone,le_refl])
);

val pos_fn_integral_strict_mono_restricted = store_thm(
    "pos_fn_integral_strict_mono_restricted",
    ``∀m f g s. measure_space m ∧ measure m s ≠ 0 ∧ s ∈ measurable_sets m ∧
        (∀x. 0 ≤ f x) ∧ (∀x. 0 ≤ g x) ∧ pos_fn_integral m f ≠ PosInf ∧
        (∀t. t ∈ m_space m ⇒ f t ≤ g t) ∧ (∀t. t ∈ s ⇒ f t < g t) ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        g ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        pos_fn_integral m f < pos_fn_integral m g``,
    rw[] >> Cases_on `pos_fn_integral m g = PosInf`
    >- (Cases_on `pos_fn_integral m f` >> rw[extreal_lt_alt]) >>
    (qspecl_then [`m`,`f`,`g`,`s`] assume_tac) integral_strict_mono_restricted >>
    rfs[integrable_def,integral_def,FN_PLUS_POS_ID,FN_MINUS_POS_ZERO] >>
    rfs[pos_fn_integral_zero,GSYM N0_EQ_0] >> fs[N0_EQ_0,sub_rzero]
);

val pos_fn_integral_strict_pos_restricted = store_thm(
    "pos_fn_integral_strict_pos_restricted",
    ``∀m f s. measure_space m ∧ measure m s ≠ 0 ∧ s ∈ measurable_sets m ∧
        (∀x. 0 ≤ f x) ∧ (∀t. t ∈ s ⇒ 0 < f t) ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        0 < pos_fn_integral m f``,
    rw[] >> (qspecl_then [`m`,`(λx. 0)`,`f`,`s`] assume_tac) pos_fn_integral_strict_mono_restricted >>
    rfs[le_refl,pos_fn_integral_zero,GSYM N0_EQ_0] >> pop_assum irule >>
    irule IN_MEASURABLE_BOREL_CONST_ALT >> rw[MEASURE_SPACE_SIGMA_ALGEBRA]
);

val pos_fn_integral_eq_fun_eq_mspace = store_thm(
    "pos_fn_integral_eq_fun_eq_mspace",
    ``∀m f g. measure_space m ∧ (∀x. 0 ≤ f x) ∧ (∀x. 0 ≤ g x) ∧
        (∀x. x ∈ m_space m ⇒ (f x = g x)) ⇒
        (pos_fn_integral m f = pos_fn_integral m g)``,
    rw[] >>
    `pos_fn_integral m f = integral m f` by (irule (GSYM integral_pos_fn) >> rw[]) >>
    `pos_fn_integral m g = integral m g` by (irule (GSYM integral_pos_fn) >> rw[]) >>
    rw[integral_eq_fun_eq_mspace]
);

val pos_fn_integral_sub = store_thm(
    "pos_fn_integral_sub",
    ``∀m f g. measure_space m ∧ (∀x. 0 ≤ g x) ∧ (∀x. g x ≤ f x) ∧ pos_fn_integral m g ≠ PosInf ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        g ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        (pos_fn_integral m (λx. f x − g x) = pos_fn_integral m f − pos_fn_integral m g)``,
    rw[] >>
    `pos_fn_integral m g ≠ NegInf` by (
        `0 ≤ pos_fn_integral m g` by (irule pos_fn_integral_pos >> rw[]) >>
        CCONTR_TAC >> fs[GSYM N0_EQ_0,extreal_le_def]) >>
    rw[eq_sub_ladd] >>
    (qspecl_then [`m`,`(λx. f x − g x)`,`g`] assume_tac) (GSYM pos_fn_integral_add) >> rfs[] >>
    `(∀x. 0 ≤ f x − g x)` by rw[GSYM sub_zero_le] >>
    `(λx. f x − g x) ∈ measurable (m_space m,measurable_sets m) Borel`
        by (irule IN_MEASURABLE_BOREL_SUB_ALT >> rw[MEASURE_SPACE_SIGMA_ALGEBRA]) >>
    fs[] >> NTAC 3 (pop_assum kall_tac) >> irule pos_fn_integral_eq_fun_eq_mspace >> rw[] >>
    `0 ≤ g x ∧ g x ≤ f x ∧ 0 ≤ f x` by (rw[] >> irule le_trans >> qexists_tac `g x` >> rw[]) >>
    Cases_on `f x` >> Cases_on `g x` >>
    fs[GSYM N0_EQ_0,extreal_le_def,extreal_add_def,extreal_sub_def] >> rw[REAL_SUB_ADD]
);

val pos_fn_integral_pos_simple_fn_as_sum = store_thm(
    "pos_fn_integral_pos_simple_fn_as_sum",
    ``∀m f s e a. measure_space m ∧ pos_simple_fn m f s e a ⇒
        (pos_fn_integral m f =
        SIGMA (λi. Normal (a i) * pos_fn_integral m (indicator_fn (e i))) s)``,
    rw[] >> drule_all_then assume_tac pos_fn_integral_pos_simple_fn >>
    rw[pos_simple_fn_integral_def] >> pop_assum kall_tac >>
    fs[pos_simple_fn_def,GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
    irule EXTREAL_SUM_IMAGE_EQ >> rw[GSYM extreal_mul_def] >>
    `pos_fn_integral m (indicator_fn (e x)) = Normal (measure m (e x))`
        suffices_by (rw[] >> fs[]) >>
    irule pos_fn_integral_indicator >> rw[]
);

(* Halmos 27.B *)

val integral_zero_a_e = store_thm(
    "integral_zero_a_e",
    ``∀m f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        a_e m {x | f x = 0} ⇒ (integral m f = 0)``,
    rw[] >>
    `{x | f x = 0} ∩ m_space m ∈ measurable_sets m` by fs[IN_MEASURABLE_BOREL_ALL_MEASURE] >>
    `m_space m DIFF {x | f x = 0} ∈ measurable_sets m` by (
        (qspecl_then [`m`,`m_space m`,`{x | f x = 0} ∩ m_space m`] assume_tac)
            MEASURE_SPACE_DIFF >>
        rfs[MEASURE_SPACE_MSPACE_MEASURABLE] >>
        `m_space m DIFF {x | f x = 0} ∩ m_space m = m_space m DIFF {x | f x = 0}`
            suffices_by (rw[] >> fs[]) >>
        rw[EXTENSION] >> eq_tac >> rw[]) >>
    `integral m (λx. f x * indicator_fn (m_space m) x) = 0` suffices_by rw[GSYM integral_mspace] >>
    `integral m (λx. f x * indicator_fn ({x | f x = 0} ∩ m_space m) x) = 0` by (
        `(λx. f x * indicator_fn ({x | f x = 0} ∩ m_space m) x) = (λx. 0)`
            suffices_by rw[integral_zero] >>
        fs[FUN_EQ_THM] >> rw[] >> Cases_on `x ∈ {x | f x = 0} ∩ m_space m` >>
        rw[indicator_fn_def,mul_lzero,mul_rzero]) >>
    `integral m (λx. f x * indicator_fn (m_space m DIFF {x | f x = 0}) x) = 0` by (
        fs[a_e_def] >> dxrule_all_then assume_tac integral_null_set >>
        pop_assum (qspec_then `f` assume_tac) >>
        `(λx. f x * indicator_fn (m_space m DIFF {x | f x = 0}) x) =
            (λx. indicator_fn (m_space m DIFF {x | f x = 0}) x * f x)`
            suffices_by (rw[] >> fs[]) >>
        rw[FUN_EQ_THM] >> fs[mul_comm]) >>
    map_every Q.ABBREV_TAC [`g = (λx. f x * indicator_fn ({x | f x = 0} ∩ m_space m) x)`,
        `h = (λx. f x * indicator_fn (m_space m DIFF {x | f x = 0}) x)`] >>
    `integrable m g` by (irule integral_finite_integrable >> rw[]
        >- (qexists_tac `0` >> rw[N0_EQ_0]) >>
        Q.UNABBREV_TAC `g` >> irule IN_MEASURABLE_BOREL_MUL_INDICATOR >>
        rw[MEASURE_SPACE_SIGMA_ALGEBRA,subsets_def]) >>
    `integrable m h` by (irule integral_finite_integrable >> rw[]
        >- (qexists_tac `0` >> rw[N0_EQ_0]) >>
        Q.UNABBREV_TAC `h` >> irule IN_MEASURABLE_BOREL_MUL_INDICATOR >>
        rw[MEASURE_SPACE_SIGMA_ALGEBRA,subsets_def]) >>
    map_every Q.UNABBREV_TAC [`g`,`h`] >>
    `DISJOINT ({x | f x = 0} ∩ m_space m) (m_space m DIFF {x | f x = 0})` by (
        rw[DISJOINT_DEF,EXTENSION] >>
        map_every Cases_on [`x ∈ m_space m`,`f x = 0`] >> rw[]) >>
    drule_all_then assume_tac integrable_disjoint_sets >> fs[integrable_def] >>
    drule_all_then assume_tac integral_disjoint_sets_alt >> rfs[add_lzero] >>
    `{x | f x = 0} ∩ m_space m ∪ (m_space m DIFF {x | f x = 0}) = m_space m`
        suffices_by (rw[] >> fs[]) >>
    rw[EXTENSION] >> Cases_on `x ∈ m_space m` >> Cases_on `f x = 0` >> rw[]
);

val integral_pos_not_zero_a_e = store_thm(
    "integral_pos_not_zero_a_e",
    ``∀m f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧ ¬ a_e m {x | f x = 0} ⇒ (0 < integral m f)``,
    rw[] >>
    `m_space m DIFF {x | f x = 0} ∈ measurable_sets m` by (
        `{x | f x = 0} ∩ m_space m ∈ measurable_sets m` by fs[IN_MEASURABLE_BOREL_ALL_MEASURE] >>
        (qspecl_then [`m`,`m_space m`,`{x | f x = 0} ∩ m_space m`] assume_tac)
            MEASURE_SPACE_DIFF >>
        rfs[MEASURE_SPACE_MSPACE_MEASURABLE] >>
        `m_space m DIFF {x | f x = 0} ∩ m_space m = m_space m DIFF {x | f x = 0}`
            suffices_by (rw[] >> fs[]) >>
        rw[EXTENSION] >> eq_tac >> rw[]) >>
    `integral m f = integral m (λx. f x * indicator_fn (m_space m DIFF {x | f x = 0}) x)` by (
        irule integral_eq_fun_eq_mspace >> rw[FUN_EQ_THM] >>
        Cases_on `f x = 0` >> rw[indicator_fn_def,mul_rzero,mul_rone]) >>
    rw[] >> pop_assum kall_tac >>
    drule_all_then assume_tac integral_restricted >> rw[] >> pop_assum kall_tac >>
    irule integral_strict_pos >> rw[m_space_def,measurable_sets_def,measure_def]
    >- (qpat_x_assum `∀x. _` (qspec_then `t` assume_tac) >> rfs[] >> rw[lt_le])
    >- (rw[MEASURE_SPACE_RESTRICTED])
    >- (fs[a_e_def,null_set_def])
    >- (rw[MEASURABLE_RESTRICTED])
);

val integral_pos_eq_zero_iff_zero_a_e = store_thm(
    "integral_pos_eq_zero_iff_zero_a_e",
    ``∀m f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ⇒ (a_e m {x | f x = 0} ⇔ (integral m f = 0))``,
    rw[] >> eq_tac >> rw[integral_zero_a_e] >>
    CCONTR_TAC >> dxrule_all_then assume_tac integral_pos_not_zero_a_e >>
    rfs[GSYM N0_EQ_0,extreal_lt_alt]
);

val pos_fn_integral_zero_a_e = store_thm(
    "pos_fn_integral_zero_a_e",
    ``∀m f. measure_space m ∧ a_e m {x | f x = 0} ∧ (∀x. 0 ≤ f x) ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ⇒ (pos_fn_integral m f = 0)``,
    rw[] >> fs[GSYM integral_pos_fn,integral_zero_a_e]
);

val pos_fn_integral_not_zero_a_e = store_thm(
    "pos_fn_integral_not_zero_a_e",
    ``∀m f. measure_space m ∧ ¬a_e m {x | f x = 0} ∧ (∀x. 0 ≤ f x) ∧
         f ∈ measurable (m_space m,measurable_sets m) Borel ⇒ 0 < pos_fn_integral m f``,
    rw[] >> fs[GSYM integral_pos_fn,integral_pos_not_zero_a_e]
);

val pos_fn_integral_eq_zero_iff_zero_a_e = store_thm(
    "pos_fn_integral_eq_zero_iff_zero_a_e",
    ``∀m f. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel ∧
        (∀x. 0 ≤ f x) ⇒ (a_e m {x | f x = 0} ⇔ (pos_fn_integral m f = 0))``,
    rw[] >> (qspecl_then [`m`,`f`] assume_tac) integral_pos_eq_zero_iff_zero_a_e >>
    rfs[integral_pos_fn]
);

val pos_fn_integral_extcmul = store_thm(
    "pos_fn_integral_extcmul",
    ``∀m f c. measure_space m ∧ (∀x. 0 ≤ f x) ∧ 0 ≤ c ∧
        f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
        (pos_fn_integral m (λx. c * f x) = c * pos_fn_integral m f)``,
    rw[] >> Cases_on `c` >> fs[GSYM N0_EQ_0,extreal_le_def,pos_fn_integral_cmul] >>
    rw[] >> Cases_on `a_e m {x | f x = 0}` >> fs[N0_EQ_0]
    >- (fs[pos_fn_integral_zero_a_e,mul_rzero] >>
        irule pos_fn_integral_zero_a_e >> fs[] >> rw[]
        >- (rw[extreal_mul_alt,le_refl] >> fs[GSYM N0_EQ_0,extreal_le_def] >>
            rfs[le_lt] >> qpat_x_assum `∀x. _` (qspec_then `x` assume_tac) >> rfs[])
        >- (irule IN_MEASURABLE_BOREL_EXTCMUL_ALT >> rw[MEASURE_SPACE_SIGMA_ALGEBRA])
        >- (`{x | PosInf * f x = 0} = {x | f x = 0}` suffices_by rw[] >>
            rw[EXTENSION] >> eq_tac >> rw[mul_rzero] >> fs[entire,GSYM N0_EQ_0]))
    >- (drule_all_then assume_tac pos_fn_integral_not_zero_a_e >>
        `PosInf * pos_fn_integral m f = PosInf` by (fs[extreal_mul_alt] >> fs[lt_le]) >>
        rw[] >> pop_assum kall_tac >>
        `m_space m DIFF {x | f x = 0} ∈ measurable_sets m` by (
            `{x | f x ≠ 0} ∩ m_space m ∈ measurable_sets m` by rw[IN_MEASURABLE_BOREL_ALL_MEASURE] >>
            `m_space m DIFF {x | f x = 0} = {x | f x ≠ 0} ∩ m_space m` by (
                rw[EXTENSION] >> eq_tac >> rw[]) >>
            rw[]) >>
        fs[a_e_def,null_set_def] >>
        `pos_fn_integral m (λx. PosInf * f x) =
            pos_fn_integral m (λx. PosInf * indicator_fn (m_space m DIFF {x | f x = 0}) x)` by (
            irule pos_fn_integral_eq_fun_eq_mspace >> fs[] >> rw[]
            >- (rw[indicator_fn_def] >> fs[mul_rzero,mul_rone] >>
                `0 < f x` by rw[lt_le] >> fs[extreal_mul_alt])
            >- (irule le_mul >> rw[le_infty])
            >- (rw[indicator_fn_def,mul_rzero,mul_rone,le_refl,le_infty])) >>
        rw[] >> pop_assum kall_tac >> rw[pos_fn_integral_cmul_infty] >>
        Q.ABBREV_TAC `s = (m_space m DIFF {x | f x = 0})` >>
        `0 < measure m s` suffices_by (rw[] >> fs[extreal_mul_def]) >>
        rw[REAL_LT_LE] >> drule_then assume_tac MEASURE_SPACE_POSITIVE >>
        fs[positive_def])
);

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Probability *)
(*---------------------------------------------------------------------------*)

val indep_alt = store_thm(
    "indep_alt",
    ``∀m s t. indep m s t ⇔ s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧
        (measure m (s ∩ t) = measure m s * measure m t)``,
    rw[indep_def,events_def,prob_def]
);

val indep_rv_alt = store_thm(
    "indep_rv_alt",
    ``∀m f g a b. indep_rv m f g a b ⇔ ∀s t. s ∈ subsets a ∧ t ∈ subsets b ⇒
        indep m (PREIMAGE f s ∩ m_space m) (PREIMAGE g t ∩ m_space m)``,
    rw[indep_rv_def,p_space_def]
);

val mut_indep_def =  Define `mut_indep (n: num) p ss ⇔
    (∀i. i < n ⇒ ss i ∈ events p) ∧
    prob p (BIGINTER (IMAGE ss (count n))) = prod (0,n) ((prob p) ∘ ss)`;

val mut_indep_rv_def =  Define `mut_indep_rv (n: num) p Xs as ⇔
    ∀As. (∀i. i < n ⇒ As i ∈ subsets (as i)) ⇒
    mut_indep n p (λi. PREIMAGE (Xs i) (As i) ∩ p_space p)`;

val mut_indep_alt = store_thm(
    "mut_indep_alt",
    ``∀n m ss. mut_indep (n: num) m ss ⇔ (∀i. i < n ⇒ ss i ∈ measurable_sets m) ∧
        measure m (BIGINTER (IMAGE ss (count n))) = prod (0,n) ((measure m) ∘ ss)``,
    simp[mut_indep_def,events_def,prob_def]
);

val mut_indep_rv_alt = store_thm(
    "mut_indep_rv_alt",
    ``∀n m fs as. mut_indep_rv (n: num) m fs as ⇔ ∀ss. (∀i. i < n ⇒ ss i ∈ subsets (as i)) ⇒
        mut_indep n m (λi. PREIMAGE (fs i) (ss i) ∩ m_space m)``,
    simp[mut_indep_rv_def,p_space_def]
);

val mut_indep_1 = store_thm(
    "mut_indep_1",
    ``∀p ss. mut_indep 1 p ss ⇔ ss 0 ∈ events p``,
    rw[mut_indep_def] >> eq_tac >> rw[]
    >- (Cases_on `i` >> fs[])
    >- (simp[COUNT_ONE,IMAGE_SING,BIGINTER_SING] >>
        assume_tac prod_def >> fs[] >>
        pop_assum (qspecl_then [`0`,`0`,`prob p ∘ ss`] assume_tac) >> rfs[])
);

val mut_indep_rv_1 = store_thm(
    "mut_indep_rv_1",
    ``∀p fs as. fs 0 ∈ measurable (p_space p,events p) (as 0) ⇒ mut_indep_rv 1 p fs as``,
    rw[mut_indep_rv_def,measurable_def,space_def,subsets_def] >> simp[mut_indep_1]
);

val mut_indep_rv_recur = store_thm(
    "mut_indep_rv_recur",
    ``∀n p fs as. prob_space p ∧ (0 < n) ∧
        (∀i. i < SUC n ⇒ (fs i) ∈ measurable (p_space p,events p) (as i)) ⇒
        (mut_indep_rv (SUC n) p fs as ⇔
        mut_indep_rv n p fs as ∧ ∀ss. (∀i. i < SUC n ⇒ ss i ∈ subsets (as i)) ⇒
        indep p (BIGINTER (IMAGE (λi. PREIMAGE (fs i) (ss i) ∩ p_space p) (count n)))
        (PREIMAGE (fs n) (ss n) ∩ p_space p))``,
    rw[mut_indep_rv_def,mut_indep_def,indep_def] >> eq_tac >> rw[]
    >- (first_x_assum (drule_then assume_tac) >>
        last_x_assum (qspec_then `i` assume_tac) >> rfs[measurable_def,space_def,subsets_def])
    >- (first_x_assum (qspec_then `(λi. if i < n then As i else space (as n))` assume_tac) >>
        `(∀i. i < SUC n ⇒ (λi. if i < n then As i else space (as n)) i ∈ subsets (as i))` by (
            rw[] >> `i = n` by fs[] >> rw[] >> fs[] >> rw[] >> rename [`space (as n) ∈ _`] >>
            last_x_assum (qspec_then `n` assume_tac) >> fs[measurable_def] >>
            irule ALGEBRA_SPACE >> simp[SIGMA_ALGEBRA_ALGEBRA]) >>
        fs[BIGINTER_IMAGE_COUNT_SUC_COMM,prod_def] >> pop_assum kall_tac >>
        `PREIMAGE (fs n) (space (as n)) ∩ p_space p = p_space p` by (
            rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[] >>
            last_x_assum (qspec_then `n` assume_tac) >>
            fs[measurable_def,space_def,subsets_def,FUNSET]) >>
        fs[] >> pop_assum kall_tac >>
        `count n ≠ ∅` by (rw[EXTENSION] >> qexists_tac `0` >> simp[]) >>
        rfs[prob_space_def,GSYM prob_def] >> fs[GSYM INTER_BIGINTER_IMAGE_COMM] >>
        `IMAGE (λi. PREIMAGE (fs i) (if i < n then As i else space (as n)) ∩ p_space p ∩ p_space p)
            (count n) = IMAGE (λi. PREIMAGE (fs i) (As i) ∩ p_space p) (count n)` by (
            irule IMAGE_CONG >> rw[count_def] >> rename [`i < n`] >>
            rw[EXTENSION] >> eq_tac >> rw[]) >>
        fs[] >> NTAC 3 (pop_assum kall_tac) >> irule PROD_EQ >> rw[])
    >- (irule EVENTS_COUNTABLE_INTER >> rw[]
        >- (simp[COUNTABLE_IMAGE_NUM])
        >- (simp[count_def,EXTENSION] >> qexists_tac `0` >> simp[])
        >- (rw[SUBSET_DEF,IN_IMAGE] >> first_x_assum (qspec_then `ss` assume_tac) >> rfs[]))
    >- (first_assum (qspec_then `ss` assume_tac) >> rfs[BIGINTER_IMAGE_COUNT_SUC_COMM,prod_def] >>
        `prob p (BIGINTER (IMAGE (λi. PREIMAGE (fs i) (ss i) ∩ p_space p) (count n))) =
            prod (0,n) (prob p ∘ (λi. PREIMAGE (fs i) (ss i) ∩ p_space p))` suffices_by rw[] >>
        rw[] >> rename [`∀i. i < SUC n ⇒ As i ∈ subsets (as i)`] >>
        first_x_assum (qspec_then `(λi. if i < n then As i else space (as n))` assume_tac) >>
        `(∀i. i < SUC n ⇒ (λi. if i < n then As i else space (as n)) i ∈ subsets (as i))` by (
            rw[] >> `i = n` by fs[] >> rw[] >> fs[] >> rw[] >> rename [`space (as n) ∈ _`] >>
            last_x_assum (qspec_then `n` assume_tac) >> fs[measurable_def] >>
            irule ALGEBRA_SPACE >> simp[SIGMA_ALGEBRA_ALGEBRA]) >>
        fs[BIGINTER_IMAGE_COUNT_SUC_COMM,prod_def] >> pop_assum kall_tac >>
        `PREIMAGE (fs n) (space (as n)) ∩ p_space p = p_space p` by (
            rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[] >>
            last_x_assum (qspec_then `n` assume_tac) >>
            fs[measurable_def,space_def,subsets_def,FUNSET]) >>
        fs[] >> pop_assum kall_tac >>
        `count n ≠ ∅` by (rw[EXTENSION] >> qexists_tac `0` >> simp[]) >>
        rfs[prob_space_def,GSYM prob_def] >> fs[GSYM INTER_BIGINTER_IMAGE_COMM] >>
        `IMAGE (λi. PREIMAGE (fs i) (if i < n then As i else space (as n)) ∩ p_space p ∩ p_space p)
            (count n) = IMAGE (λi. PREIMAGE (fs i) (As i) ∩ p_space p) (count n)` by (
            irule IMAGE_CONG >> rw[count_def] >> rename [`i < n`] >>
            rw[EXTENSION] >> eq_tac >> rw[]) >>
        fs[] >> NTAC 3 (pop_assum kall_tac) >> irule PROD_EQ >> rw[])
    >- (first_x_assum (drule_then assume_tac) >> last_x_assum (drule_then assume_tac) >>
        rfs[measurable_def,space_def,subsets_def])
    >- (first_x_assum (drule_then assume_tac) >> simp[BIGINTER_IMAGE_COUNT_SUC_COMM,prod_def])
);

val mut_indep_rv_o = store_thm(
    "mut_indep_rv_o",
    ``∀n m fs gs as bs. 0 < n ∧ mut_indep_rv n m fs as ∧
        (∀i. i < n ⇒ fs i ∈ measurable (m_space m,measurable_sets m) (as i)) ∧
        (∀i. i < n ⇒ gs i ∈ measurable (as i) (bs i)) ⇒
        mut_indep_rv n m (λi. (gs i) ∘ (fs i)) bs``,
    rw[] >> 
    `∀i. i < n ⇒ fs i ∈ measurable
        (m_space m,{PREIMAGE (fs i) s ∩ m_space m | s | s ∈ subsets (as i)}) (as i)` by (rw[] >>
        last_x_assum (dxrule_then assume_tac) >> (dxrule_then assume_tac) MEASURABLE_PREIMAGE_SIGMA >>
        rfs[space_def]) >>
    `∀i. i < n ⇒ (gs i) ∘ (fs i) ∈ measurable
        (m_space m,{PREIMAGE (fs i) s ∩ m_space m | s | s ∈ subsets (as i)}) (bs i)` by (rw[] >>
        irule MEASURABLE_COMP >> qexists_tac `as i` >> simp[]) >>
    fs[mut_indep_rv_alt,mut_indep_alt] >> NTAC 2 strip_tac >>
    `∃ts. ∀i. i < n ⇒ ts i = PREIMAGE (gs i) (ss i) ∩ space (as i)` by (rw[GSYM SKOLEM_THM] >>
        Cases_on `i < n` >> simp[]) >>
    `(∀i. i < n ⇒ ts i ∈ subsets (as i))` by (rw[] >> fs[measurable_def]) >>
    last_x_assum (dxrule_then assume_tac) >> fs[] >>
    `∀i. i < n ⇒ PREIMAGE (gs i ∘ fs i) (ss i) ∩ m_space m = PREIMAGE (fs i) (ts i) ∩ m_space m` by (
        rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[] >>
        fs[measurable_def,space_def,subsets_def,FUNSET]) >>
    rw[]
    >- (NTAC 3 (first_x_assum (drule_then assume_tac)) >> fs[]) >>
    `(IMAGE (λi. PREIMAGE (gs i ∘ fs i) (ss i) ∩ m_space m) (count n)) =
        (IMAGE (λi. PREIMAGE (fs i) (ts i) ∩ m_space m) (count n)) ∧
        prod (0,n) (measure m ∘ (λi. PREIMAGE (gs i ∘ fs i) (ss i) ∩ m_space m)) =
        prod (0,n) (measure m ∘ (λi. PREIMAGE (fs i) (ts i) ∩ m_space m))` suffices_by (rw[] >> fs[]) >>
    rw[]
    >- (irule IMAGE_CONG >> rw[IN_COUNT])
    >- (irule PROD_EQ >> rw[])
);

val PROB_GE_0 = store_thm(
    "PROB_GE_0",
    ``∀p s. prob_space p ∧ s ∈ events p ⇒ 0 ≤ prob p s``,
    fs[prob_space_def,events_def,prob_def,MEASURE_POSITIVE]
);

val PROB_COMPL_SUBSET = store_thm(
    "PROB_COMPL_SUBSET",
    ``∀p s t. prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧ t ⊆ s ⇒
        prob p (s DIFF t) = prob p s − prob p t``,
    rw[prob_space_def,events_def,prob_def,MEASURE_COMPL_SUBSET]
);

val EVENTS_SUBSET_SPACE = store_thm(
    "EVENTS_SUBSET_SPACE",
    ``∀p s. prob_space p ∧ s ∈ events p ⇒ s ⊆ p_space p``,
    rw[prob_space_def,events_def,p_space_def,MEASURABLE_SETS_SUBSET_SPACE]
);

val PROB_SPACE_IN_P_SPACE = store_thm(
    "PROB_SPACE_IN_P_SPACE",
    ``∀p s x. prob_space p ∧ s ∈ events p ∧ x ∈ s ⇒ x ∈ p_space p``,
    rw[prob_space_def,events_def,p_space_def] >> irule MEASURE_SPACE_IN_M_SPACE >>
    simp[] >> qexists_tac `s` >> simp[]
);

val PROB_SUBSET_PSPACE = store_thm(
    "PROB_SUBSET_PSPACE",
    ``∀p s. prob_space p ∧ s ∈ events p ⇒ s ⊆ p_space p``,
    rpt strip_tac >> fs[prob_space_def,p_space_def,events_def,prob_def] >>
    fs[MEASURE_SPACE_SUBSET_MSPACE]
);

val PROBABLY_SUBSET = store_thm(
    "PROBABLY_SUBSET",
    ``∀p s t. prob_space p ∧ probably p s ∧ t ∈ events p ∧ s ⊆ t ⇒ probably p t``,
    rpt strip_tac >> fs[probably_def] >> imp_res_tac PROB_LE_1 >>
    imp_res_tac PROB_INCREASING >> rfs[] >> rw[] >> imp_res_tac REAL_LE_ANTISYM
);

val PROBABLY_COMPL_NULL = store_thm(
    "PROBABLY_COMPL_NULL",
    ``∀p s. prob_space p ∧ probably p s ⇒ null_set p (p_space p DIFF s)``,
    rw[probably_def,null_set_def]
    >- (fs[prob_space_def,prob_def,p_space_def,events_def] >> rw[MEASURE_SPACE_COMPL])
    >- (dxrule_all_then assume_tac PROB_COMPL >> rfs[prob_def])
);

val EXPECTATION_1 = store_thm(
    "EXPECTATION_1",
    ``∀p. prob_space p ⇒ (expectation p (indicator_fn (m_space p)) = 1)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >>
    imp_res_tac integral_indicator >> fs[extreal_of_num_def]
);

val EXPECTATION_CONST = store_thm(
    "EXPECTATION_CONST",
    ``∀p c. prob_space p ⇒ (expectation p (λx. Normal c) = Normal c)``,
    rpt strip_tac >> fs[expectation_def,prob_space_def,p_space_def] >>
    imp_res_tac integral_mspace >>
    pop_assum (fn a => ASSUME_TAC (ISPEC ``(λx. Normal c)`` a)) >> fs[] >>
    imp_res_tac MEASURE_SPACE_MSPACE_MEASURABLE >>
    imp_res_tac integral_cmul_indicator >> fs[]
);

val EXPECTATION_EQ_EXPECTATION_PROBABLY = store_thm(
    "EXPECTATION_EQ_EXPECTATION_PROBABLY",
    ``∀p s f. prob_space p ∧ probably p s ∧ f ∈ measurable (p_space p,events p) Borel ⇒
        (expectation p f = expectation p (λx. f x * indicator_fn s x))``,
    rw[] >> drule_all_then assume_tac PROBABLY_COMPL_NULL >>
    fs[expectation_def,prob_space_def,probably_def,prob_def,p_space_def,events_def] >>
    `DISJOINT s (m_space p DIFF s)` by (rw[DISJOINT_DEF,EXTENSION] >> Cases_on `x ∈ s` >> rw[]) >>
    map_every (drule_all_then assume_tac) [MEASURE_SPACE_COMPL,integral_disjoint_sets] >>
    `(s ∪ (m_space p DIFF s)) = m_space p` suffices_by
        (rw[] >> fs[] >> rfs[integral_null_set,add_rzero,GSYM integral_mspace]) >>
    rw[EXTENSION] >> Cases_on `x ∈ s` >> Cases_on `x ∈ m_space p` >> rw[] >>
    imp_res_tac MEASURABLE_SETS_SUBSET_SPACE >> fs[SUBSET_DEF] >> RES_TAC
);

val PROBABLY_INTER = store_thm(
    "PROBABLY_INTER",
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

val PROBABLY_INTERVAL = store_thm(
    "PROBABLY_INTERVAL",
    ``∀p X a b. prob_space p ∧ probably p {x | X x ∈ closed_interval (Normal a) (Normal b)} ⇒ (a ≤ b)``,
    rpt strip_tac >> Cases_on `a ≤ b` >> fs[] >>
    fs[prob_space_def,p_space_def,events_def,prob_def,probably_def,closed_interval_def] >>
    `{x | Normal a ≤ X x ∧ X x ≤ Normal b} = ∅` by (fs[EXTENSION] >> strip_tac >>
        fs[REAL_NOT_LE] >> `Normal b < Normal a` by fs[extreal_lt_alt] >>
        Cases_on `Normal a ≤ X x` >> fs[] >> imp_res_tac lte_trans >> fs[extreal_lt_def]) >>
    imp_res_tac MEASURE_EMPTY >> fs[]
);

val PROBABLY_CLOSED_INTERVAL_EXPECTATION_RANGE = store_thm(
    "PROBABLY_CLOSED_INTERVAL_EXPECTATION_RANGE",
    ``∀p X a b. prob_space p ∧ X ∈ measurable (p_space p,events p) Borel ∧
        probably p {x | X x ∈ closed_interval (Normal a) (Normal b)} ⇒
        (Normal a ≤ expectation p X) ∧ (expectation p X ≤ Normal b)``,
    NTAC 5 strip_tac >> drule_all_then assume_tac EXPECTATION_EQ_EXPECTATION_PROBABLY >>
    Q.ABBREV_TAC `s = {x | X x ∈ closed_interval (Normal a) (Normal b)}` >>
    fs[prob_space_def,p_space_def,probably_def,events_def,prob_def,expectation_def] >> rw[]
    >- (`integral p (λx. Normal a * indicator_fn s x) ≤
            integral p (λx. X x * indicator_fn s x)` suffices_by rw[integral_cmul_indicator] >>
        irule integral_mono >> rw[indicator_fn_def,mul_rone,mul_rzero,le_refl] >>
        Q.UNABBREV_TAC `s` >> fs[closed_interval_def])
    >- (`integral p (λx. X x * indicator_fn s x) ≤
            integral p (λx. Normal b * indicator_fn s x)` suffices_by rw[integral_cmul_indicator] >>
        irule integral_mono >> rw[indicator_fn_def,mul_rone,mul_rzero,le_refl] >>
        Q.UNABBREV_TAC `s` >> fs[closed_interval_def])
);

val PROBABLY_CLOSED_INTERVAL_EXPECTATION_MAX = store_thm(
    "PROBABLY_CLOSED_INTERVAL_EXPECTATION_MAX",
    ``∀p X a b. prob_space p ∧ (expectation p X = Normal b) ∧
        X ∈ measurable (p_space p,events p) Borel ∧
        probably p {x | X x ∈ closed_interval (Normal a) (Normal b)} ⇒
        probably p {x | X x = Normal b}``,
    rw[] >> drule_all_then assume_tac EXPECTATION_EQ_EXPECTATION_PROBABLY >>
    fs[] >> pop_assum kall_tac >> drule_all_then assume_tac PROBABLY_INTERVAL >>
    fs[prob_space_def,probably_def,expectation_def,p_space_def,events_def,prob_def] >>
    `{x | X x = Normal b} ∈ measurable_sets p` by (
        `{x | X x = Normal b} ∩ m_space p ∈ measurable_sets p`
            by rw[IN_MEASURABLE_BOREL_ALL_MEASURE] >>
        `{x | X x = Normal b} ∩ m_space p = {x | X x = Normal b}` suffices_by (rw[] >> fs[]) >>
        rw[EXTENSION] >> pop_assum kall_tac >> eq_tac >> rw[] >>
        dxrule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >> fs[SUBSET_DEF] >>
        pop_assum irule >> rw[closed_interval_def,le_refl,extreal_le_def]) >> rw[] >>
    map_every Q.ABBREV_TAC [`sab = {x | X x ∈ closed_interval (Normal a) (Normal b)}`,
        `sb = {x | X x = Normal b}`] >>
    `sb ⊆ sab` by (map_every Q.UNABBREV_TAC [`sb`,`sab`] >>
        rw[SUBSET_DEF,closed_interval_def,le_refl,extreal_le_def]) >>
    (qspecl_then [`p`,`X`,`sb`,`sab DIFF sb`] assume_tac) integral_disjoint_sets >>
    rfs[MEASURE_SPACE_DIFF] >>
    `DISJOINT sb (sab DIFF sb)` by (rw[DISJOINT_DEF,EXTENSION] >> Cases_on `x ∈ sb` >> rw[]) >>
    fs[] >> pop_assum kall_tac >>
    `(sb ∪ (sab DIFF sb)) = sab` by (rw[EXTENSION] >> Cases_on `x ∈ sb` >> Cases_on `x ∈ sab` >>
        rw[] >> map_every Q.UNABBREV_TAC [`sb`,`sab`] >> rfs[closed_interval_def,extreal_le_def]) >>
    fs[] >> NTAC 2 (pop_assum kall_tac) >>
    `(λx. X x * indicator_fn sb x) = (λx. Normal b * indicator_fn sb x)` by (
        rw[FUN_EQ_THM,indicator_fn_def] >> Cases_on `x ∈ sb` >>
        rw[mul_rzero,mul_rone] >> Q.UNABBREV_TAC `sb` >> fs[]) >>
    drule_all_then assume_tac integral_cmul_indicator >> fs[] >>
    NTAC 2 (pop_assum kall_tac) >> CCONTR_TAC >>
    `sab DIFF sb ∈ measurable_sets p` by (irule MEASURE_SPACE_DIFF >> rw[]) >>
    Cases_on `integral p (λx. X x * indicator_fn (sab DIFF sb) x)` >> fs[extreal_add_def] >> 
    `integral p (λx. X x * indicator_fn (sab DIFF sb) x) <
        integral p (λx. Normal b * indicator_fn (sab DIFF sb) x)` by (
        irule integral_strict_mono_restricted >> rw[]
        >- (rw[indicator_fn_def,mul_rzero,mul_rone,le_refl] >>
            Q.UNABBREV_TAC `sab` >> fs[closed_interval_def])
        >- (qexists_tac `sab DIFF sb` >> rw[]
            >- (rw[indicator_fn_def,mul_rzero,mul_rone] >> map_every Q.UNABBREV_TAC [`sab`,`sb`] >>
                fs[closed_interval_def] >> rw[lt_le])
            >- (drule_all_then assume_tac MEASURE_COMPL_SUBSET >> rw[]))
        >- (irule integral_not_infty_integrable >> rw[] >>
            irule IN_MEASURABLE_BOREL_MUL_INDICATOR >>
            rw[MEASURE_SPACE_SIGMA_ALGEBRA,subsets_def])
        >- (irule integral_finite_integrable >> rw[integral_cmul_indicator] >>
            irule IN_MEASURABLE_BOREL_CMUL_INDICATOR >>
            rw[MEASURE_SPACE_SIGMA_ALGEBRA,subsets_def])) >>
    rfs[integral_cmul_indicator,MEASURE_COMPL_SUBSET,extreal_lt_alt] >>
    dxrule_then assume_tac REAL_LT_IADD >> pop_assum (qspec_then `b * measure p sb` assume_tac) >>
    Q.ABBREV_TAC `tmp = b * measure p sb + r` >> rfs[GSYM REAL_ADD_LDISTRIB] >>
    `measure p sb + (1 − measure p sb) = 1` suffices_by (rw[] >> CCONTR_TAC >> fs[]) >>
    Q.ABBREV_TAC `msb = measure p sb` >> rpt (pop_assum kall_tac) >>
    rw[real_sub,REAL_ADD_ASSOC] >> rw[GSYM real_sub,REAL_ADD_SUB]
);

val PROBABLY_CLOSED_INTERVAL_EXPECTATION_MIN = store_thm(
    "PROBABLY_CLOSED_INTERVAL_EXPECTATION_MIN",
    ``∀p X a b. prob_space p ∧ (expectation p X = Normal a) ∧
        X ∈ measurable (p_space p,events p) Borel ∧
        probably p {x | X x ∈ closed_interval (Normal a) (Normal b)} ⇒
        probably p {x | X x = Normal a}``,
    rw[] >>
    `(λx. (λx. 0) x - X x) ∈ measurable (p_space p,events p) Borel` by (
        irule IN_MEASURABLE_BOREL_SUB_ALT >> fs[prob_space_def,p_space_def,events_def,prob_def] >>
        rw[MEASURE_SPACE_SIGMA_ALGEBRA] >> irule IN_MEASURABLE_BOREL_CONST_ALT >>
        rw[MEASURE_SPACE_SIGMA_ALGEBRA]) >> fs[sub_lzero] >>
    `{x | X x ∈ closed_interval (Normal a) (Normal b)} =
        {x | (λx. -X x) x ∈ closed_interval (-Normal b) (-Normal a)}` by (rw[EXTENSION] >>
        fs[closed_interval_def,le_neg] >> metis_tac[]) >>
    fs[extreal_ainv_def] >> pop_assum kall_tac >>
    `expectation p (λx. -X x) = Normal (-a)` by (
        fs[expectation_def,prob_space_def,real_random_variable_def,p_space_def,events_def] >>
        `integrable p X` by imp_res_tac integral_finite_integrable >>
        imp_res_tac integral_cmul >> pop_assum (qspec_then `-1` assume_tac) >> rfs[] >>
        fs[NM1_EQ_M1] >> `∀x. -1 * x = -x` by metis_tac[neg_minus1] >> fs[extreal_ainv_def]) >>
    (qspecl_then [`p`,`(λx. -X x)`,`-b`,`-a`] assume_tac) PROBABLY_CLOSED_INTERVAL_EXPECTATION_MAX >>
    rfs[] >>
    `{x | -X x = Normal (-a)} = {x | X x = Normal a}` by (fs[EXTENSION] >>
        strip_tac >> metis_tac[eq_neg,neg_neg,extreal_ainv_def]) >> fs[]
);

(* sum/prod finite functions stuff *)

val sumfin_def = Define `(sumfin (n,0) f = 0) ∧
    (sumfin (n,SUC m) f = sumfin (n,m) f + f (n + m))`;
    
val prodfin_def = Define `(prodfin (n,0) f = 1) ∧
    (prodfin (n,SUC m) f = prodfin (n,m) f * f (n + m))`;

val sumfinfun_def = Define `(sumfinfun (n,0) f x = 0) ∧
    (sumfinfun (n,SUC m) f x = sumfinfun (n,m) f x + f (n + m) x)`;
    
val prodfinfun_def = Define `(prodfinfun (n,0) f x = 1) ∧
    (prodfinfun (n,SUC m) f x = prodfinfun (n,m) f x * f (n + m) x)`;

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

val sumfin_replace = store_thm(
    "sumfin_replace",
    ``∀n f g. (∀i. i < n ⇒ (f i = g i)) ⇒ (sumfin (0,n) f = sumfin (0,n) g)``,
    Induct_on `n` >> rpt strip_tac >> fs[sumfin_def] >>
    `sumfin (0,n) f = sumfin (0,n) g` suffices_by (strip_tac >> fs[]) >> fs[]
);

val sumfinfun_cmul = store_thm(
    "sumfinfun_cmul",
    ``∀f n x c. (∀i. i < n ⇒ (f i x ≠ PosInf) ∧ (f i x ≠ NegInf)) ⇒
        (sumfinfun (0,n) (λn x. Normal c * f n x) x = Normal c * sumfinfun (0,n) f x)``,
    Induct_on `n` >> rpt strip_tac >> fs[sumfinfun_def,mul_rzero] >>
    `f n x ≠ PosInf ∧ f n x ≠ NegInf` by fs[] >>
    Cases_on `sumfinfun (0,n) f x` >> Cases_on `f n x` >>
    fs[extreal_add_def,extreal_mul_def] >> rw[] >> fs[extreal_add_def,REAL_ADD_LDISTRIB]
);

val sumfin_normal = store_thm(
    "sumfin_normal",
    ``∀f n. sumfin (0,n) (λi. Normal (f i)) = Normal (sum (0,n) f)``,
    Induct_on `n` >> rpt strip_tac >> fs[sum,sumfin_def,N0_EQ_0,extreal_add_def]
);

val prodfinfun_exp = store_thm(
    "prodfinfun_exp",
    ``∀f n x c. (∀i. i < n ⇒ (f i x ≠ PosInf) ∧ (f i x ≠ NegInf)) ⇒
        (prodfinfun (0,n) (λn x. exp (f n x)) x = exp (sumfinfun (0,n) f x))``,
    Induct_on `n` >> rpt strip_tac >> fs[sumfinfun_def,prodfinfun_def]
    >- (fs[GSYM N0_EQ_0,GSYM N1_EQ_1,extreal_exp_def,EXP_0])
    >- (`f n x ≠ PosInf ∧ f n x ≠ NegInf` by fs[] >>
        Cases_on `sumfinfun (0,n) f x` >> Cases_on `f n x` >>
        fs[extreal_add_def,extreal_mul_def,extreal_exp_def] >> rw[]
        >- (`0 < exp r` by fs[EXP_POS_LT] >> fs[REAL_LT_LE])
        >- (`0 < exp r` by fs[EXP_POS_LT])
        >- (fs[EXP_ADD]))
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

val sumfinfun_sub_sumfin = store_thm(
    "sumfinfun_sub_sumfin",
    ``∀f g n x. (∀i. i < n ⇒ (g i ≠ PosInf) ∧ (g i ≠ NegInf)) ∧
        (∀i. i < n ⇒ (f i x ≠ PosInf) ∧ (f i x ≠ NegInf)) ⇒
        ((sumfinfun (0,n) f x) - (sumfin (0,n) g) = sumfinfun (0,n) (λn x. f n x - g n) x)``,
    Induct_on `n` >> rpt strip_tac >> fs[sumfinfun_def,sumfin_def,sub_rzero] >>
    `sumfinfun (0,n) f x + f n x − (sumfin (0,n) g + g n) =
        sumfinfun (0,n) f x − sumfin (0,n) g + (f n x − g n)`
        suffices_by (strip_tac >> fs[]) >>
    `g n ≠ PosInf ∧ g n ≠ NegInf` by fs[] >>
    `f n x ≠ PosInf ∧ f n x ≠ NegInf` by fs[] >>
    Cases_on `sumfinfun (0,n) f x` >> Cases_on `f n x` >>
    Cases_on `sumfin (0,n) g` >> Cases_on `g n` >>
    fs[extreal_add_def,extreal_sub_def] >> rw[] >>
    rpt (pop_assum kall_tac) >> fs[real_sub,REAL_NEG_ADD,REAL_ADD_ASSOC] >>
    metis_tac[REAL_ADD_ASSOC,REAL_ADD_COMM]
);

val exp_sum = store_thm(
    "exp_sum",
    ``∀f n. prodfin (0,n) (λi. Normal (exp (f i))) = exp (sumfin (0,n) (λi. Normal (f i)))``,
    Induct_on `n` >> rpt strip_tac >> fs[prodfin_def,sumfin_def]
    >- (`Normal 1 = exp (Normal 0)` suffices_by fs[N0_EQ_0,N1_EQ_1] >>
        fs[extreal_exp_def,EXP_0])
    >- (fs[sumfin_normal,extreal_exp_def,extreal_mul_def,extreal_add_def,EXP_ADD])
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
            `{x | X n x = Normal (a n)}`] assume_tac) PROBABLY_INTER >>
        rfs[prob_space_def,probably_def,p_space_def,events_def,prob_def])
);

val prodfinfun_cull = store_thm(
    "prodfinfun_cull",
    ``∀n m f. prodfinfun (n,m) f = (λx. prod (n,m) (λn. f n x))``,
    Induct_on `m` >> rw[prodfinfun_alt,extreal_prod_def]
);

val prodfin_cull = store_thm(
    "prodfin_cull",
    ``∀n m f. prodfin (n,m) f = prod (n,m) f``,
    Induct_on `m` >> rw[prodfin_def,extreal_prod_def]
);

val sumfinfun_cull = store_thm(
    "sumfinfun_cull",
    ``∀n m f. sumfinfun (n,m) f = (λx. sum (n,m) (λn. f n x))``,
    Induct_on `m` >>  rw[sumfinfun_alt,extreal_sum_def]
);

val _ = export_theory();
