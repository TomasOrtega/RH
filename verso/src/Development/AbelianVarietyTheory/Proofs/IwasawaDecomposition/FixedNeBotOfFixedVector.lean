import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixedAtSplit

open Filter Topology IsDedekindDomain

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Use `⟨(π : v.adicCompletion F), ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Use `v.valuedAdicCompletion_eq_valuation' π` as an intermediate fact. Rewrite `this` using `[h0, map_zero, hπ]`.

Conclude with `WithZero.coe_ne_zero this.symm`. Rewrite using `[Valued.toNormedField.norm_lt_one_iff, v.valuedAdicCompletion_eq_valuation', hπ]`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.
-/
theorem exists_ne_zero_norm_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F), ?_, ?_⟩
  · intro h0
    have := v.valuedAdicCompletion_eq_valuation' π
    rw [h0, map_zero, hπ] at this
    exact WithZero.coe_ne_zero this.symm
  · rw [Valued.toNormedField.norm_lt_one_iff, v.valuedAdicCompletion_eq_valuation', hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

/- English proof (translation)
Rewrite `hz`, the goal using `[← Valued.toNormedField.norm_lt_one_iff]`. Establish `h1 : ∀ y : v.adicCompletion F, ‖y‖ < 1 → ‖c y‖ < 1` using `fun y hy => by`. Establish `h2` using `(hc.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.2 hy)`. Rewrite `h2` using `[map_zero]`. Use `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ?_` and prove the remaining obligations.

Simplify `h2` using `[Function.comp_def, map_pow]`. Take `⟨ϖ, hϖ0, hϖ1⟩` from `exists_ne_zero_norm_lt_one v`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hz0 : z ≠ 0`.

Introduce and unpack `rfl`. Rewrite `h` using `[norm_zero]`. Evaluate the numerical expressions using `at h`. Establish `hcz0 : 0 < ‖c z‖` using `norm_pos_iff.2 ((map_ne_zero c).2 hz0)`. Establish `hcϖ : 0 < ‖c ϖ‖` using `norm_pos_iff.2 ((map_ne_zero c).2 hϖ0)`.

Establish `key : ∀ N : ℕ, ‖c ϖ‖ < ‖c z‖ ^ N`. Introduce `N`. Establish `hzN : 1 ≤ ‖z‖ ^ N` using `one_le_pow₀ h`. Establish `hq : ‖ϖ / z ^ N‖ < 1`. Rewrite using `[norm_div, norm_pow, div_lt_one (by positivity)]`.

Conclude with `lt_of_lt_of_le hϖ1 hzN`. Use `h1 _ hq` as an intermediate fact. Rewrite `this` using `[map_div₀, map_pow, norm_div, norm_pow, div_lt_one (by positivity)]`. Conclude with `this`. Establish `ht` using `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (c z)) hz`.

Take `⟨N, hN⟩` from `(ht.eventually (gt_mem_nhds hcϖ)).exists`. Conclude with `lt_asymm hN (key N)`.
-/
theorem valued_lt_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (z : v.adicCompletion F)
    (hz : Valued.v (c z) < 1) : Valued.v z < 1 := by
  rw [← Valued.toNormedField.norm_lt_one_iff] at hz ⊢
  have h1 : ∀ y : v.adicCompletion F, ‖y‖ < 1 → ‖c y‖ < 1 := fun y hy => by
    have h2 := (hc.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.2 hy)
    rw [map_zero] at h2
    refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ?_
    simpa [Function.comp_def, map_pow] using h2
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_ne_zero_norm_lt_one v
  by_contra h
  push_neg at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    norm_num at h
  have hcz0 : 0 < ‖c z‖ := norm_pos_iff.2 ((map_ne_zero c).2 hz0)
  have hcϖ : 0 < ‖c ϖ‖ := norm_pos_iff.2 ((map_ne_zero c).2 hϖ0)
  have key : ∀ N : ℕ, ‖c ϖ‖ < ‖c z‖ ^ N := by
    intro N
    have hzN : 1 ≤ ‖z‖ ^ N := one_le_pow₀ h
    have hq : ‖ϖ / z ^ N‖ < 1 := by
      rw [norm_div, norm_pow, div_lt_one (by positivity)]
      exact lt_of_lt_of_le hϖ1 hzN
    have := h1 _ hq
    rw [map_div₀, map_pow, norm_div, norm_pow, div_lt_one (by positivity)] at this
    exact this
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (c z)) hz
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hcϖ)).exists
  exact lt_asymm hN (key N)

end GlobalTheory.FixedAtSplit

namespace GlobalTheory.FixedAtSplit

open IsDedekindDomain ValuativeRel

/- English proof (translation)
Establish `: (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`. Establish `he` using `isEquiv (valuation (w.adicCompletion E)) (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))`. Rewrite using `[GlobalTheory.StepData.mem_KOne]`. Conclude with `forall_congr' fun a => forall_congr' fun b => he.lt_one_iff_lt_one`.
-/
theorem mem_KOne_iff' {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (κ : GL (Fin n) (w.adicCompletion E)) :
    κ ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n) ↔
      ∀ a b, Valued.v (((κ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) a b) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [GlobalTheory.StepData.mem_KOne]
  exact forall_congr' fun a => forall_congr' fun b => he.lt_one_iff_lt_one

/- English proof (translation)
Use `(mem_KOne_iff' A).2 fun a b => valued_lt_one_of_map c hc _ ?_` and prove the remaining obligations. Use `(mem_KOne_iff' _).1 h a b` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Simplify using `only [Matrix.sub_apply, Matrix.one_apply, Matrix.GeneralLinearGroup.map_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mem_KOne_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) {n : ℕ}
    (A : GL (Fin n) (v.adicCompletion F))
    (h : Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) :
    A ∈ GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n) := by
  refine (mem_KOne_iff' A).2 fun a b => valued_lt_one_of_map c hc _ ?_
  have := (mem_KOne_iff' _).1 h a b
  convert this using 2
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.GeneralLinearGroup.map_apply]
  split_ifs <;> simp

end GlobalTheory.FixedAtSplit

namespace GlobalTheory.FixedAtSplit

/- English proof (translation)
Introduce `L _ _ _ n π s τ hloc f hf hf0 hfix`. Take `⟨c, _, hc, hci, _⟩` from `id hloc`. Establish `hspan` using `GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent L n π s τ hloc c hc hci hf`. Set `H : Subgroup (GAf L n)` to `{ carrier := {x | TrivOutside {s.v} x} mul_mem' := fun {x y} hx hy v hv => by`. Simplify using `only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]`.

Use the proof step `one_mem' := fun v _ => by simp`. Use the proof step `inv_mem' := fun {x} hx v hv => by`. Establish `h1 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1` using `by simp`. Establish `h2` using `congrArg (fun M => Matrix.map M (compAt L v)) h1`. Simplify using `only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2`.

Conclude with `h2 }`. Set `φ : H →* GL (Fin n) (s.w.adicCompletion L)` to `(Matrix.GeneralLinearGroup.map c.toRingHom).comp ((s.loc n).comp H.subtype)`. Establish `hφ : Function.Surjective φ`. Introduce `h`. Take `⟨x, hx, e⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)`.

Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h`. Rewrite using `[e]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Set `σ' : Representation ℂ H τ.V` to `τ.ρ.comp φ`. Establish `hσ' : σ'.IsIrreducible` using `GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr φ hφ`. Set `ρ' : Representation ℂ H (GAf L n → ℂ)` to `{ toFun := fun x => NG.rt L n (x : GAf L n) map_one' := by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`.

Use function extensionality and compare the values at `a`. Simplify using `[NG.rt]`. Use the proof step `map_mul' := fun x y => by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`.

Use function extensionality and compare the values at `a`. Simplify using `[NG.rt, mul_assoc] }`. Rewrite `hspan` using `[iSup_subtype']`. Take `⟨t, ht⟩` from `Submodule.mem_iSup_iff_exists_finset.1 hspan`. Set `T : t → σ'.IntertwiningMap ρ'` to `fun j => LinearMap.intertwiningMap_of_isIntertwiningMap σ' ρ' j.1.1 fun g v => j.1.2.2 g.1 g.2 v`.

Establish `hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap`. Rewrite `ht` using `[iSup_subtype']`. Conclude with `ht`. Set `K : Subgroup H` to `(GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)).comap φ`. Establish `hfixK : ∀ k ∈ K, ρ' k f = f` using `fun k hk => hfix k.1 k.2 (mem_KOne_of_map c hc _ hk)`.

Establish `hne` using `GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK`. Rewrite `hne`, the goal using `[Submodule.ne_bot_iff]`. Take `⟨y, hy, hy0⟩` from `hne`. Use `⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hy0⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hφ h`.

Conclude with `GlobalTheory.Parabolic.mem_fixed.1 hy x hh`.
-/
theorem fixed_ne_bot_of_fixed_vector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → s.loc n κ ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ hloc f hf hf0 hfix
  classical
  obtain ⟨c, _, hc, hci, _⟩ := id hloc
  have hspan := GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent L n π s τ hloc c hc hci hf
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun {x y} hx hy v hv => by
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]
      one_mem' := fun v _ => by simp
      inv_mem' := fun {x} hx v hv => by
        have h1 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
        have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
        simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
        exact h2 }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map c.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h
    rw [e]
    ext i j
    simp
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr φ hφ
  let ρ' : Representation ℂ H (GAf L n → ℂ) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [iSup_subtype'] at hspan
  obtain ⟨t, ht⟩ := Submodule.mem_iSup_iff_exists_finset.1 hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    LinearMap.intertwiningMap_of_isIntertwiningMap σ' ρ' j.1.1 fun g v => j.1.2.2 g.1 g.2 v
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)).comap φ
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk =>
    hfix k.1 k.2 (mem_KOne_of_map c hc _ hk)
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hy0⟩
  obtain ⟨x, rfl⟩ := hφ h
  exact GlobalTheory.Parabolic.mem_fixed.1 hy x hh

end GlobalTheory.FixedAtSplit
