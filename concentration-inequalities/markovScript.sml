open HolKernel Parse boolLib bossLib;

open measureTheory;
open lebesgueTheory;
open extrealTheory;
open realTheory;
open pred_setTheory;

open trivialTheory;

val _ = new_theory "markov";

val s_ep_def = Define ` s_ep f ep x = if (Normal ep) ≤ f x then (Normal ep) else 0`;
val s_ep_indic_def = Define `s_ep_indic f ep = (λx. if x ∈ {y | (Normal ep) ≤ f y} then 1 else 0)`;

val ALGEBRA_LEMMMA_1 = store_thm(
    "ALGEBRA_LEMMMA_1",
    ``∀a b c d. ((0 < a:extreal) ∧ (a ≠ PosInf)) ⇒ ((b ≤ (1/a) * c) ∧ (c ≤ d) ⇒ (b ≤ (1/a) * d))``,
    rpt strip_tac >> imp_res_tac inv_pos >> imp_res_tac le_rmul_imp >> NTAC 5 (pop_assum kall_tac) >>
    `(1 / a) * c ≤ (1 / a) * d` by fs[mul_comm] >> metis_tac[le_trans]
);

val ALGEBRA_LEMMMA_2 = store_thm(
    "ALGEBRA_LEMMMA_2",
    ``∀a b. (0 < a) ⇒ (1 / Normal a * Normal (a * b) = Normal b)``,
    rpt strip_tac >> `a ≠ 0` by fs[REAL_LT_LE] >>
    `1 / Normal a * (Normal a * Normal b) = Normal b` suffices_by fs[extreal_mul_def] >>
    `1 / Normal a * Normal a * Normal b = Normal b` suffices_by fs[mul_assoc] >>
    `Normal a * (1 / Normal a) * Normal b = Normal b` suffices_by fs[mul_comm] >>
    `Normal a * inv (Normal a) * Normal b = Normal b` suffices_by fs[inv_1over] >>
    `Normal a / Normal a * Normal b = Normal b` suffices_by fs[extreal_div_def] >>
    `Normal (a / a) * Normal b = Normal b` suffices_by fs[extreal_div_eq] >>
    `Normal 1 * Normal b = Normal b` suffices_by fs[REAL_DIV_REFL] >>
    `Normal (1 * b) = Normal b` suffices_by fs[extreal_mul_def] >>
    `Normal b = Normal b` suffices_by fs[REAL_MUL_LID] >> fs[]
);

val S_EP_MONO = store_thm(
    "S_EP_MONO",
    ``∀f ep x. (∀y. 0 ≤ f y) ∧ (0 < ep) ⇒ (0 ≤ s_ep f ep x) ∧ (s_ep f ep x ≤ f x)``,
    rpt strip_tac >> Cases_on `Normal ep ≤ f x` >> fs[s_ep_def,le_lt] >>
    metis_tac[extreal_eq_zero,extreal_lt_eq]
);

val S_EP_INDIC_IS_INDIC = store_thm(
    "S_EP_INDIC_IS_INDIC",
    ``∀f ep. s_ep_indic f ep = indicator_fn {y | Normal ep ≤ f y}``,
    fs[s_ep_indic_def,indicator_fn_def]
);

val S_EP_EQ_INDIC = store_thm(
    "S_EP_EQ_INDIC",
    ``∀f ep x. s_ep f ep x = (Normal ep) * s_ep_indic f ep x``,
    rpt strip_tac >> fs[s_ep_indic_def,s_ep_def] >>
    Cases_on `Normal ep ≤ f x` >> fs[mul_rone,mul_rzero]
);

val S_EP_INDIC_MONO = store_thm(
    "S_EP_INDIC_MONO",
    ``∀f ep x X. (∀y. 0 ≤ f y) ∧ (0 < ep) ⇒
        ((λx. Normal ep * indicator_fn {x | Normal ep ≤ f x ∧ x ∈ X} x) x ≤ f x)``,
    rpt strip_tac >> fs[indicator_fn_def] >>
    Cases_on `x ∈ X` >> fs[]
    >- (
        `(λx. Normal ep * indicator_fn {x | Normal ep ≤ f x} x) x ≤ f x`
            suffices_by fs[indicator_fn_def] >>
        imp_res_tac S_EP_MONO >>
        first_x_assum (qspec_then `x` assume_tac) >>
        fs[S_EP_EQ_INDIC,S_EP_INDIC_IS_INDIC]
    )
    >- (fs[mul_rzero])
);

val MARKOV_MEAS_LEMMA = store_thm(
    "MARKOV_MEAS_LEMMA",
    ``∀sp sts mu f ep. measure_space (sp,sts,mu) ∧ measurable (sp,sts) Borel f ⇒
        {x | Normal ep ≤ f x ∧ x ∈ sp} ∈ sts``,
    rpt strip_tac >> `{y | Normal ep ≤ y} ∈ subsets Borel` by fs[BOREL_MEASURABLE_SETS] >>
    fs[measurable_def] >> RES_TAC >>
    fs[PREIMAGE_def,space_def,subsets_def] >> fs[INTER_DEF]
);

val MARKOVS_INEQUALITY = store_thm(
    "MARKOVS_INEQUALITY",
    ``∀sp sts mu f ep. measure_space (sp,sts,mu) ∧ measurable (sp,sts) Borel f ∧ (∀x. 0 ≤ f x) ∧ 0 < ep ⇒
        Normal (mu {x | Normal ep ≤ f x ∧ x ∈ sp}) ≤ 1 / Normal ep * integral (sp,sts,mu) f``,
    rpt strip_tac >> imp_res_tac MARKOV_MEAS_LEMMA >> pop_assum (qspec_then `ep` assume_tac) >>
    imp_res_tac S_EP_INDIC_MONO >> imp_res_tac integral_mono >>
    pop_assum (qspecl_then
        [`f:α -> extreal`,`(λx. Normal ep * indicator_fn {x | Normal ep ≤ f x ∧ x ∈ sp} x):α -> extreal`]
        assume_tac) >>
    `integral (sp,sts,mu) (λx. Normal ep * indicator_fn {x | Normal ep ≤ f x ∧ x ∈ sp} x) ≤
        integral (sp,sts,mu) f` by metis_tac[] >>
    `(Normal ep) ≠ PosInf` by fs[] >>
    `0 < Normal ep` by metis_tac[extreal_lt_eq,N0_EQ_0] >>
    qpat_x_assum `∀x X. _` kall_tac >> qpat_x_assum `_ ⇒ _` kall_tac >>
    `Normal (mu {x | Normal ep ≤ f x ∧ x ∈ sp}) ≤
        1 / Normal ep * integral (sp,sts,mu) (λx. Normal ep * indicator_fn {x | Normal ep ≤ f x ∧ x ∈ sp} x)`
        suffices_by metis_tac[ALGEBRA_LEMMMA_1] >>
    NTAC 3 (pop_assum kall_tac) >>
    fs[integral_cmul_indicator,measure_def,measurable_sets_def,ALGEBRA_LEMMMA_2,le_lt]
);

val _ = export_theory();
