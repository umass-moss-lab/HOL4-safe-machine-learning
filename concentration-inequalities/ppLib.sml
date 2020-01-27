structure ppLib =
struct

open prettyPrintingTheory HolKernel Parse boolLib


fun normal_pprinter (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
    in
      printer {gravs = (pgr,lgr,rgr), depth = depth,
               binderp = false} (rand tm)
    end


val _ = temp_add_user_printer("normal", “(Normal : real -> extreal) _”,
                                         normal_pprinter);

fun sum_pprinter (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      val (lb,ub) = pairSyntax.dest_pair (lhand tm)
                    handle HOL_ERR _ => raise UserPP_Failed
      val (bv, body) = dest_abs (rand tm)
                       handle HOL_ERR _ => raise UserPP_Failed
    in
      add_string "(SIGMA)" >>
      block PP.INCONSISTENT 0 (
        printer {gravs = (Top,Top,Prec(450,"<=")),
                 binderp = false, depth = decdepth depth} lb >>
        add_string " " >> add_string "<=" >> add_break (1,0) >>

        printer {gravs = (Top,Prec(450,"<="),Prec(450,"<")),
                 binderp = true, depth = decdepth depth} bv >>
        add_string " " >> add_string "<" >> add_break (1,0) >>

        printer {gravs = (Top,Top,Prec(450,"<=")),
                 binderp = false, depth = decdepth depth} ub
      ) >> add_string "(SIGMA_EB)" >>
      printer {gravs = (Prec(2000,"sum"),Prec(2000,"sum"),rgr),
               depth = decdepth depth,
               binderp = false} body
    end

val _ = temp_add_user_printer ("sum", “real$sum (x,y) f”, sum_pprinter)
val _ = temp_add_user_printer ("trivsum", “trivial$extreal_sum (x,y) f”, sum_pprinter)

fun prod_pprinter (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      val (lb,ub) = pairSyntax.dest_pair (lhand tm)
                    handle HOL_ERR _ => raise UserPP_Failed
      val (bv, body) = dest_abs (rand tm)
                       handle HOL_ERR _ => raise UserPP_Failed
    in
      add_string "(PRODUCT)" >>
      block PP.INCONSISTENT 0 (
        printer {gravs = (Top,Top,Prec(450,"<=")),
                 binderp = false, depth = decdepth depth} lb >>
        add_string " " >> add_string "<=" >> add_break (1,0) >>

        printer {gravs = (Top,Prec(450,"<="),Prec(450,"<")),
                 binderp = true, depth = decdepth depth} bv >>
        add_string " " >> add_string "<" >> add_break (1,0) >>

        printer {gravs = (Top,Top,Prec(450,"<=")),
                 binderp = false, depth = decdepth depth} ub
      ) >> add_string "(PRODUCT_EB)" >>
      printer {gravs = (Prec(2000,"prod"),Prec(2000,"prod"),rgr),
               depth = decdepth depth,
               binderp = false} body
    end

val _ = temp_add_user_printer ("prodreal", “trivial$prod (x,y) f”, prod_pprinter)
val _ = temp_add_user_printer ("prodfin", “trivial$prodfin (x,y) f”, prod_pprinter)
val _ = temp_add_user_printer ("prodextreal", “trivial$extreal_prod (x,y) f”, prod_pprinter)

fun sigma_pprinter (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      val s = rand tm
      val (bv, body) = dest_abs (lhand tm)
                       handle HOL_ERR _ => raise UserPP_Failed
    in
      add_string "(SIGMA)" >>
      block PP.INCONSISTENT 0 (
        printer {gravs = (Top,Top,Prec(425,"∈")),
                 binderp = false, depth = decdepth depth} bv >>
        add_string " " >> add_string "∈" >> add_break (1,0) >>

        printer {gravs = (Top,Top,Prec(425,"∈")),
                 binderp = false, depth = decdepth depth} s
      ) >> add_string "(SIGMA_EB)" >>
      printer {gravs = (Prec(2000,"sigma"),Prec(2000,"sigma"),rgr),
               depth = decdepth depth,
               binderp = false} body
    end

val _ = temp_add_user_printer ("sigma_real_sumimage",
                               “real_sigma$REAL_SUM_IMAGE f s”,
                                sigma_pprinter)
val _ = temp_add_user_printer ("sigma_ereal_sumimage",
                               “c487306_extreal$EXTREAL_SUM_IMAGE f s”,
                                sigma_pprinter)

fun subindex_printer (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      val (f,x) = dest_comb tm
      val (xnm,xty) = dest_var x handle HOL_ERR _ => raise UserPP_Failed
      val _ = xty = numSyntax.num andalso mem xnm ["i", "j"] orelse
              raise UserPP_Failed
      val _ = is_var f orelse raise UserPP_Failed
    in
      trace ("pp_avoids_symbol_merges", 0) (
        printer {gravs = (pgr,lgr,rgr), depth = depth, binderp = false} f >>
        add_string "(SUBINDEX1)" >>
        add_string xnm >> add_string "(SUBINDEX2)"
      )
    end

val _ = temp_add_user_printer ("subindex", “f (x:num) : 'a”, subindex_printer)



fun sumsto_pprinter (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      val result = rand tm
      val (bv, body) = dest_abs (lhand tm)
                       handle HOL_ERR _ => raise UserPP_Failed
    in
      block PP.INCONSISTENT 2 (
      add_string "(SIGMAsum1)" >>
      block PP.INCONSISTENT 0 (
        printer {gravs = (Top,Top,Prec(450,"=")),
                 binderp = false, depth = decdepth depth} bv >>
        add_string " " >> add_string "=" >> add_break (1,0) >> add_string "0"
      ) >> add_string "(SIGMAsum2)" >>
      printer {gravs = (Prec(2000,"sigma"),Prec(2000,"sigma"),Prec(450,"=")),
               depth = decdepth depth,
               binderp = false} body >> add_string " " >>
      add_string "=" >> add_break(1,0) >>
      printer {gravs = (Prec(450,"="), Prec(450,"="), rgr),
               depth = decdepth depth,
               binderp = false} result
      )
    end

val _ = temp_add_user_printer ("sumsto_sigma", “seq$sums f r”, sumsto_pprinter)

end
