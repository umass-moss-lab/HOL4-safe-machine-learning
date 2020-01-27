open HolKernel Parse boolLib bossLib;

(* collects together necessary ancestor theories *)
open c487306_measureTheory;
open markovTheory
open pred_setTheory
open hoeffdingTheory

val _ = new_theory "prettyPrinting";

(* prettier theorems *)

val MARKOVS_INEQUALITY_ALT = store_thm(
    "MARKOVS_INEQUALITY_ALT",
    ``∀m f ep. measure_space m ∧ f ∈ measurable (m_space m,measurable_sets m) Borel ∧ (∀x. 0 ≤ f x) ∧ 0 < ep ⇒
        Normal (measure m {x | Normal ep ≤ f x ∧ x ∈ m_space m}) ≤ 1 / Normal ep * integral m f``,
    rw[] >>
    (qspecl_then [`m_space m`,`measurable_sets m`,`measure m`,`f`,`ep`] assume_tac) MARKOVS_INEQUALITY >>
    rfs[m_space_def,measurable_sets_def,measure_def,MEASURE_SPACE_REDUCE,IN_DEF]
);

(* can also insert grammar manipulations here to fiddle with pretty-printing *)

val _ = add_rule{term_name = "closed_interval",
                 pp_elements = [TOK "(CI1)", TM, TOK "(CI2)", BreakSpace(1,0),
                                TM, TOK "(CI3)"],
                 fixity = Closefix,
                 block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                 paren_style = OnlyIfNecessary}

Theorem pushIMAGE :
  IMAGE f (GSPEC (P:'a -> 'b # bool)) = GSPEC ((f ## I) o P)
Proof
  simp[EXTENSION, GSPECIFICATION, EQ_IMP_THM, PULL_EXISTS] >>
  rw[] >- (rename [‘(y,T) = P a’] >> qexists_tac ‘a’ >> simp[] >>
           pop_assum (SUBST1_TAC o SYM ) >> simp[]) >>
  rename [‘(x, T) = (f ## I) (P a)’] >> Cases_on ‘P a’ >> fs[] >>
  map_every qexists_tac [‘q’, ‘a’] >> simp[]
QED

Theorem mut_indep_def =
   trivialTheory.mut_indep_def
   |> SIMP_RULE (srw_ss()) [combinTheory.o_DEF]
   |> SIMP_RULE (srw_ss()) [combinTheory.o_ABS_R, pushIMAGE, count_def];

(* \int_{prod-measure-space m_0 m_1} f *)

Overload CROSS = “prod_measure_space”

val _ = add_rule{term_name = "integral",
                 pp_elements = [TOK "(integral1)", TM, TOK "(integral2)"],
                 fixity = Prefix 2200,
                 block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                 paren_style = OnlyIfNecessary}

val _ = add_rule{term_name = "expectation",
                 pp_elements = [TOK "(expectation1)", TM, TOK "(expectation2)",
                                TM, TOK "(expectation3)"],
                 fixity = Closefix,
                 block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                 paren_style = OnlyIfNecessary}

val _ = add_rule{term_name = "prob",
                 pp_elements = [TOK "(prob1)", TM, TOK "(prob2)",
                                TM, TOK "(prob3)"],
                 fixity = Closefix,
                 block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                 paren_style = OnlyIfNecessary}

val _ = add_rule {term_name = "PREIMAGE",
                  pp_elements = [TOK"(PREIMAGE1)", BreakSpace(1,0)],
                  fixity = Infixl 2000,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                  paren_style = OnlyIfNecessary}

Overload nmul = “arithmetic$*”
Overload rmul = “realax$real_mul”
Overload ermul = “c487306_extreal$extreal_mul”

val _ = set_fixity "nmul" (Infixl 600);
val _ = set_fixity "rmul" (Infixl 600);
val _ = set_fixity "ermul" (Infixl 600);

val _ = add_rule {term_name = "indicator_fn",
                  pp_elements = [TOK "(IFN1)", TM, TOK "(IFN2)", TM,
                                 TOK "(IFN3)"],
                  fixity = Closefix,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                  paren_style = OnlyIfNecessary}

val _ = add_rule {term_name = "fn_plus", pp_elements = [TOK "(fnplus)"],
                  fixity = Suffix 2100,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                  paren_style = OnlyIfNecessary}
val _ = add_rule {term_name = "fn_minus", pp_elements = [TOK "(fnminus)"],
                  fixity = Suffix 2100,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                  paren_style = OnlyIfNecessary}

Theorem countably_additive_def =
  c487306_measureTheory.countably_additive_def
  |> SIMP_RULE (srw_ss()) [combinTheory.o_DEF]
  |> CONV_RULE (STRIP_QUANT_CONV (RAND_CONV (BINDER_CONV (LAND_CONV (EVERY_CONJ_CONV (TRY_CONV (RENAME_VARS_CONV ["i", "j"])))))))

val _ = export_theory();
