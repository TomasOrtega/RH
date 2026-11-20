import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CtEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RegCt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ExistsUnitOrdLEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.GeneralLocalHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.InertLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RChoice
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ConstantTermParabolicAverage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

namespace UpperTheory.V.Z.Mult

section Generic

variable {G V : Type} [Group G]

private abbrev ind (H : Subgroup G) : G → ℂ := (H : Set G).indicator 1

/- English proof (translation)
The claim follows from `Set.indicator_of_mem (show x ∈ (H : Set G) from hx) _`.
-/
private theorem ind_mem {H : Subgroup G} {x : G} (hx : x ∈ H) : ind H x = 1 :=
  Set.indicator_of_mem (show x ∈ (H : Set G) from hx) _

/- English proof (translation)
The claim follows from `Set.indicator_of_notMem (show x ∉ (H : Set G) from hx) _`.
-/
private theorem ind_notMem {H : Subgroup G} {x : G} (hx : x ∉ H) : ind H x = 0 :=
  Set.indicator_of_notMem (show x ∉ (H : Set G) from hx) _

/- English proof (translation)
Distinguish the cases in `hx : x ∈ H`. Rewrite using `[ind_mem (H.mul_mem hk hx), ind_mem hx]`. Rewrite using `[ind_notMem (fun h => hx ((H.mul_mem_cancel_left hk).1 h)), ind_notMem hx]`.
-/
private theorem ind_mul_left (H : Subgroup G) {k : G} (hk : k ∈ H) (x : G) :
    ind H (k * x) = ind H x := by
  by_cases hx : x ∈ H
  · rw [ind_mem (H.mul_mem hk hx), ind_mem hx]
  · rw [ind_notMem (fun h => hx ((H.mul_mem_cancel_left hk).1 h)), ind_notMem hx]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ H`. Rewrite using `[ind_mem (H.mul_mem hx hk), ind_mem hx]`. Rewrite using `[ind_notMem (fun h => hx ((H.mul_mem_cancel_right hk).1 h)), ind_notMem hx]`.
-/
private theorem ind_mul_right (H : Subgroup G) {k : G} (hk : k ∈ H) (x : G) :
    ind H (x * k) = ind H x := by
  by_cases hx : x ∈ H
  · rw [ind_mem (H.mul_mem hx hk), ind_mem hx]
  · rw [ind_notMem (fun h => hx ((H.mul_mem_cancel_right hk).1 h)), ind_notMem hx]

/- English proof (translation)
Use extensionality with `k`. Prove the components needed by the constructor for the conclusion. Introduce `hk`. Assume the negation of the conclusion as `hn`. Establish `h` using `hk 1`.

Rewrite `h` using `[one_mul, ind_notMem hn, ind_mem H.one_mem]`. Conclude with `zero_ne_one h`. Introduce `hk x`. Conclude with `ind_mul_right H hk x`.
-/
private theorem rStab_ind (H : Subgroup G) : rStab (ind H) = H := by
  ext k
  constructor
  · intro hk
    by_contra hn
    have h := hk 1
    rw [one_mul, ind_notMem hn, ind_mem H.one_mem] at h
    exact zero_ne_one h
  · intro hk x
    exact ind_mul_right H hk x

/- English proof (translation)
Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ H`. Rewrite using `[ind_mem (H.inv_mem hy), ind_mem hy]`. Rewrite using `[ind_notMem (fun h => hy (by simpa using H.inv_mem h)), ind_notMem hy]`.
-/
private theorem ind_inv (H : Subgroup G) : (fun y : G => ind H y⁻¹) = ind H := by
  funext y
  by_cases hy : y ∈ H
  · rw [ind_mem (H.inv_mem hy), ind_mem hy]
  · rw [ind_notMem (fun h => hy (by simpa using H.inv_mem h)), ind_notMem hy]

variable [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hfx : ∀ h ∈ H, ρ h x = x` using `fun h hh => by simpa using hx ⟨h, hh⟩`. Establish `hout : ∀ q : G ⧸ H, q.out ∈ H ↔ q = (QuotientGroup.mk 1 : G ⧸ H)`. Introduce `q`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h2 : ((q.out : G) : G ⧸ H) = QuotientGroup.mk 1` using `QuotientGroup.eq.2 (by simpa using H.inv_mem h)`. Rewrite `h2` using `[QuotientGroup.out_eq']`. Then use the resulting hypothesis. Introduce and unpack `rfl`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H (1 : G)`. Rewrite using `[hh]`.

Simplify using `using h.2`. Unfold `levOp`. Rewrite using `[finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ H)]`. Rewrite using `[ind_mem ((hout _).2 rfl)]`. Simplify using `[hfx _ ((hout _).2 rfl)]`.

Introduce `q hq`. Rewrite using `[ind_notMem (fun h => hq ((hout q).1 h))]`. Simplify using the standard rewrite rules.
-/
private theorem levOp_ind (ρ : Representation ℂ G V) (K H : Subgroup G) (x : V) (hx : x ∈ fixed ρ H) :
    levOp ρ K H (ind H) LinearMap.id x = ((H.relIndex K : ℕ) : ℂ)⁻¹ • x := by
  have hfx : ∀ h ∈ H, ρ h x = x := fun h hh => by simpa using hx ⟨h, hh⟩
  have hout : ∀ q : G ⧸ H, q.out ∈ H ↔ q = (QuotientGroup.mk 1 : G ⧸ H) := by
    intro q
    constructor
    · intro h
      have h2 : ((q.out : G) : G ⧸ H) = QuotientGroup.mk 1 :=
        QuotientGroup.eq.2 (by simpa using H.inv_mem h)
      rwa [QuotientGroup.out_eq'] at h2
    · rintro rfl
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (1 : G)
      rw [hh]
      simpa using h.2
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ H)]
  · rw [ind_mem ((hout _).2 rfl)]
    simp [hfx _ ((hout _).2 rfl)]
  · intro q hq
    rw [ind_notMem (fun h => hq ((hout q).1 h))]
    simp

/- English proof (translation)
Establish `hlev : K ⊓ rStab (ind H) ⊓ rStab (fun y : G => ind H y⁻¹) = H`. Rewrite using `[ind_inv, rStab_ind, inf_assoc, inf_idem]`. Conclude with `inf_eq_right.2 hle`. Unfold `trc`. Rewrite using `[hlev]`.

Establish `hc : ∀ v ∈ fixed ρ H, levOp ρ K H (ind H) LinearMap.id v ∈ fixed ρ H`. Introduce `v hv`. Rewrite using `[levOp_ind ρ K H v hv]`. Conclude with `Submodule.smul_mem _ _ hv`. Establish `hr : (levOp ρ K H (ind H) LinearMap.id).restrict hc = ((H.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id`.

Use extensionality with `v`. Simplify using `[LinearMap.restrict_apply, levOp_ind ρ K H v v.2]`. Unfold `twTr`. Rewrite using `[dif_pos hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]`. Establish `hpos : Module.finrank ℂ (fixed ρ H) ≠ 0` using `fun h0 => hne (Submodule.finrank_eq_zero.1 h0)`.

Conclude with `mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)`.
-/
private theorem trc_ind_ne (ρ : Representation ℂ G V) (K H : Subgroup G) (hle : H ≤ K) (hi : H.relIndex K ≠ 0)
    (hfd : FiniteDimensional ℂ (fixed ρ H)) (hne : fixed ρ H ≠ ⊥) : trc ρ K (ind H) ≠ 0 := by
  have hlev : K ⊓ rStab (ind H) ⊓ rStab (fun y : G => ind H y⁻¹) = H := by
    rw [ind_inv, rStab_ind, inf_assoc, inf_idem]
    exact inf_eq_right.2 hle
  unfold trc
  rw [hlev]
  have hc : ∀ v ∈ fixed ρ H, levOp ρ K H (ind H) LinearMap.id v ∈ fixed ρ H := by
    intro v hv
    rw [levOp_ind ρ K H v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K H (ind H) LinearMap.id).restrict hc = ((H.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_ind ρ K H v v.2]
  unfold twTr
  rw [dif_pos hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hpos : Module.finrank ℂ (fixed ρ H) ≠ 0 := fun h0 => hne (Submodule.finrank_eq_zero.1 h0)
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)

/- English proof (translation)
Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 h`. Use `(Submodule.ne_bot_iff _).2 ⟨x, ?_, hx0⟩` and prove the remaining obligations. Introduce and unpack `⟨_, u, hu, rfl⟩`. Simplify using `using hx ⟨u, hu⟩`.
-/
private theorem fixed_map_ne (ρ : Representation ℂ G V) (U : Subgroup G) (K : Subgroup U)
    (h : fixed (ρ.comp U.subtype) K ≠ ⊥) : fixed ρ (K.map U.subtype) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨x, ?_, hx0⟩
  rintro ⟨_, u, hu, rfl⟩
  simpa using hx ⟨u, hu⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Substitute `hU` using the available equality. Rewrite using `[Subgroup.coe_map]`. Conclude with `(IsOpen.isOpenMap_subtype_val (by simp)) _ ho`.
-/
private theorem map_top_open (U : Subgroup G) (hU : U = ⊤) (K : Subgroup U) (ho : IsOpen (K : Set U)) :
    IsOpen ((K.map U.subtype : Subgroup G) : Set G) := by
  subst hU
  rw [Subgroup.coe_map]
  exact (IsOpen.isOpenMap_subtype_val (by simp)) _ ho

/- English proof (translation)
Rewrite `hc` using `[Subgroup.coe_map]`. Conclude with `Topology.IsInducing.subtypeVal.isCompact_iff.2 hc`.
-/
private theorem compact_of_map (U : Subgroup G) (K : Subgroup U)
    (hc : IsCompact ((K.map U.subtype : Subgroup G) : Set G)) : IsCompact (K : Set U) := by
  rw [Subgroup.coe_map] at hc
  exact Topology.IsInducing.subtypeVal.isCompact_iff.2 hc

end Generic

end UpperTheory.V.Z.Mult

/- English proof (translation)
Introduce `E _ _ _ n w hw K hKo hKle`. Take `⟨ho, hc⟩` from `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n`. Establish `hU : UL n w = ⊤` using `if_pos hw`. Set `H : Subgroup (GLw n w)` to `K.map (UL n w).subtype`. Establish `hHo : IsOpen (H : Set (GLw n w))` using `map_top_open _ hU K hKo`.

Establish `hle : H ≤ GlobalTheory.LFun.KGL w n`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `Subgroup.mem_subgroupOf.1 (hKle hu)`. Establish `hHc : IsCompact (H : Set (GLw n w))` using `hc.of_isClosed_subset (H.isClosed_of_isOpen hHo) hle`. Establish `hKc : IsCompact (K : Set (UL n w))` using `compact_of_map _ K hHc`.

Establish `hmem : ∀ x : UL n w, x.1 ∈ H ↔ x ∈ K` using `fun x => by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hux⟩`. Establish `: u = x` using `Subtype.ext hux`. Conclude with `this ▸ hu`.

Conclude with `fun hx => ⟨x, hx, rfl⟩`. Establish `hi : H.relIndex (GlobalTheory.LFun.KGL w n) ≠ 0` using `by haveI : CompactSpace (GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hc haveI : Finite ((GlobalTheory.LFun.KGL w n) ⧸ H.subgroupOf (GlobalTheory.LFun.KGL w n)) := Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)`. Conclude with `(Subgroup.finiteIndex_of_finite_quotient (H := H.subgroupOf (GlobalTheory.LFun.KGL w n))).index_ne_zero`. Use `⟨ind H, ⟨H, hHo, hle, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `HasCompactSupport.intro' hHc (H.isClosed_of_isOpen hHo) fun x hx => ind_notMem hx`.

Conclude with `fun k hk x => ⟨ind_mul_left H hk x, ind_mul_right H hk x⟩`. Introduce `K₁ hK₁`. Use `⟨HasCompactSupport.intro' hKc (K.isClosed_of_isOpen hKo) fun x hx => ind_notMem fun h => hx ((hmem x).1 h), ?_⟩` and prove the remaining obligations. Introduce `k hk x`. Establish `hkH : k.1 ∈ H` using `(hmem k).2 (hK₁ hk)`.

Conclude with `⟨ind_mul_left H hkH x.1, ind_mul_right H hkH x.1⟩`. Introduce `τ hτ`. Conclude with `trc_ind_ne τ.ρ _ H hle hi (finiteDimensional_fixed_openSubgroup_GLw E n w τ H hHo) (fixed_map_ne τ.ρ _ K hτ)`.
-/
theorem UpperTheory.V.Z.Mult.levInd :
    UpperTheory.V.Z.Mult.LevInd := by
  intro E _ _ _ n w hw K hKo hKle
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hU : UL n w = ⊤ := if_pos hw
  let H : Subgroup (GLw n w) := K.map (UL n w).subtype
  have hHo : IsOpen (H : Set (GLw n w)) := map_top_open _ hU K hKo
  have hle : H ≤ GlobalTheory.LFun.KGL w n := by
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hKle hu)
  have hHc : IsCompact (H : Set (GLw n w)) := hc.of_isClosed_subset (H.isClosed_of_isOpen hHo) hle
  have hKc : IsCompact (K : Set (UL n w)) := compact_of_map _ K hHc
  have hmem : ∀ x : UL n w, x.1 ∈ H ↔ x ∈ K := fun x => by
    constructor
    · rintro ⟨u, hu, hux⟩
      have : u = x := Subtype.ext hux
      exact this ▸ hu
    · exact fun hx => ⟨x, hx, rfl⟩
  have hi : H.relIndex (GlobalTheory.LFun.KGL w n) ≠ 0 := by
    haveI : CompactSpace (GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hc
    haveI : Finite ((GlobalTheory.LFun.KGL w n) ⧸ H.subgroupOf (GlobalTheory.LFun.KGL w n)) :=
      Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)
    exact (Subgroup.finiteIndex_of_finite_quotient (H := H.subgroupOf (GlobalTheory.LFun.KGL w n))).index_ne_zero
  refine ⟨ind H, ⟨H, hHo, hle, ?_, ?_⟩, ?_, ?_⟩
  · exact HasCompactSupport.intro' hHc (H.isClosed_of_isOpen hHo) fun x hx => ind_notMem hx
  · exact fun k hk x => ⟨ind_mul_left H hk x, ind_mul_right H hk x⟩
  · intro K₁ hK₁
    refine ⟨HasCompactSupport.intro' hKc (K.isClosed_of_isOpen hKo) fun x hx => ind_notMem fun h => hx ((hmem x).1 h), ?_⟩
    intro k hk x
    have hkH : k.1 ∈ H := (hmem k).2 (hK₁ hk)
    exact ⟨ind_mul_left H hkH x.1, ind_mul_right H hkH x.1⟩
  · intro τ hτ
    exact trc_ind_ne τ.ρ _ H hle hi (finiteDimensional_fixed_openSubgroup_GLw E n w τ H hHo) (fixed_map_ne τ.ρ _ K hτ)
