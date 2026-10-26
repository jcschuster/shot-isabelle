theory Shot
  imports Main
begin

text \<open>
  Proof method \<open>shot\<close>: sends the subgoal and relevant facts to Shot---0.1.4 on SystemOnTPTP
  via Sledgehammer. Shot's proofs are not TSTP, so Isabelle cannot reconstruct them; a
  "Theorem" verdict is trusted through the oracle \<open>shot_oracle\<close>.

  \<^item> \<open>shot facts\<close>: chained facts and \<open>facts\<close> plus those picked by the relevance filter
  \<^item> \<open>shot only: facts\<close>: chained facts and \<open>facts\<close>, nothing else
\<close>

oracle shot_oracle = \<open>I\<close>

ML \<open>
structure Shot =
struct

local
  open Sledgehammer_ATP_Systems
in

val name = "remote_shot"

(* Without proof delimiters, Shot's "SZS status Theorem" maps to ProofMissing, which
   Sledgehammer treats as success; with them, its non-TSTP proof would be unparsable. *)
fun without_proof_delims (c : atp_config) : atp_config =
  {exec = #exec c, arguments = #arguments c, proof_delims = [],
   known_failures = #known_failures c, prem_role = #prem_role c,
   generate_isabelle_info = #generate_isabelle_info c, good_slices = #good_slices c,
   good_max_mono_iters = #good_max_mono_iters c,
   good_max_new_mono_instances = #good_max_new_mono_instances c}

val _ =
  remote_atp "shot" "Shot" ["0.1.4"] [] [] ATP_Problem.Hypothesis false
    (K ((1000, false, false, 32, "mepo"),
        (ATP_Problem.THF (ATP_Problem.Monomorphic, {with_ite = false, with_let = false},
           ATP_Problem.THF_Without_Choice),
         "mono_native_higher", ATP_Problem_Generate.keep_lamsN, false, "")))
  |> apsnd (fn config => without_proof_delims o config)
  |> add_atp
  |> Theory.setup

fun relevant_facts chained ctxt (params as {max_facts, ...} : Sledgehammer_Prover.params)
    default_max_facts goal =
  let
    val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal 1 ctxt
    val fact_override = Sledgehammer_Fact.no_fact_override
  in
    Sledgehammer_Fact.nearly_all_facts ctxt false fact_override (Thy_Header.get_keywords' ctxt)
      (Sledgehammer_Fact.clasimpset_rule_table_of ctxt) chained hyp_ts concl_t
    |> Sledgehammer_MaSh.relevant_facts ctxt params name
      (the_default default_max_facts max_facts) fact_override hyp_ts concl_t
  end

fun given_facts ths _ _ _ _ =
  [("", map (fn th => ((Thm_Name.print (Thm.get_name_hint th), (ATP_Problem_Generate.Local,
     ATP_Problem_Generate.General)), th)) ths)]

(* Sledgehammer_Tactics would go through Sledgehammer_Prover_Minimize.get_prover, which only
   knows the built-in ATPs. *)
fun proves ctxt factss_of goal =
  let
    val thy = Proof_Context.theory_of ctxt
    val params =
      Sledgehammer_Commands.default_params thy [("provers", name), ("fact_filter", "mepo")]
    val slice as ((_, _, _, default_max_facts, _), _) =
      hd (#good_slices (get_atp thy name ()) ctxt) |> apsnd Sledgehammer_Prover.ATP_Slice
    val problem =
      {comment = "", state = Proof.init ctxt, goal = goal, subgoal = 1, subgoal_count = 1,
       factss = factss_of ctxt params default_max_facts goal,
       has_already_found_something = K false, found_something = K (), memoize_fun_call = I}
    val {outcome, ...} =
      Sledgehammer_Prover_ATP.run_atp Sledgehammer_Prover.Try name params problem slice
  in
    (case outcome of
      NONE => true
    | SOME failure => (warning ("Shot: " ^ ATP_Proof.string_of_atp_failure failure); false))
  end

end

fun tac ctxt factss_of =
  SELECT_GOAL (fn st =>
    if proves ctxt factss_of st then
      Seq.single (Thm.implies_elim st (shot_oracle (Thm.cprem_of st 1)))
    else Seq.empty)

end
\<close>

method_setup shot =
  \<open>Scan.optional (Scan.lift (Args.$$$ "only" -- Args.colon) >> K Shot.given_facts) Shot.relevant_facts
    -- Attrib.thms >> (fn (factss_of, ths) => fn ctxt =>
      METHOD (fn chained => HEADGOAL (Shot.tac ctxt (factss_of (chained @ ths)))))\<close>
  "prove subgoal with Shot on SystemOnTPTP (trusted oracle)"

end
