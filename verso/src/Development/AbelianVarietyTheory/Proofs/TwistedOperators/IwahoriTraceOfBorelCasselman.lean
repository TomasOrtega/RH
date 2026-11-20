import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

namespace GlobalTheory.IwahoriTraceProof

section Exponents

/- English proof (translation)
Take `⟨l, hl⟩ : ∃ l : Module.Dual ℂ V, l v = 1` from `Module.Projective.exists_dual_eq_one ℂ hv`. Set `P : V →ₗ[ℂ] V` to `l.smulRight v`. Set `s : (V ⧸ Submodule.span ℂ {v}) →ₗ[ℂ] V` to `(Submodule.span ℂ {v}).liftQ (LinearMap.id - P) (by`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Simplify using `[P, hl])`.

Establish `h1 : f = c • P + (f ∘ₗ s) ∘ₗ (Submodule.span ℂ {v}).mkQ`. Use extensionality with `x`. Simplify using `[s, P, hc, smul_smul, mul_comm]`. Establish `h2 : (Submodule.span ℂ {v}).mkQ ∘ₗ f ∘ₗ s = g`. Use `Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)` and prove the remaining obligations.

Establish `h0 : (Submodule.Quotient.mk v : V ⧸ Submodule.span ℂ {v}) = 0` using `(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self v)`. Simplify using `[s, P, hc, hg, h0]`. Use `conv_lhs => rw [h1]`. Rewrite using `[map_add, map_smul, LinearMap.trace_comp_comm', h2, LinearMap.trace_smulRight, hl, smul_eq_mul, mul_one]`.
-/
theorem trace_eq_add_quot {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) {v : V} (hv : v ≠ 0) {c : ℂ} (hc : f v = c • v)
    (g : (V ⧸ Submodule.span ℂ {v}) →ₗ[ℂ] V ⧸ Submodule.span ℂ {v})
    (hg : ∀ x, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x)) :
    LinearMap.trace ℂ V f = c + LinearMap.trace ℂ _ g := by
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ V, l v = 1 := Module.Projective.exists_dual_eq_one ℂ hv
  let P : V →ₗ[ℂ] V := l.smulRight v
  let s : (V ⧸ Submodule.span ℂ {v}) →ₗ[ℂ] V := (Submodule.span ℂ {v}).liftQ (LinearMap.id - P) (by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    simp [P, hl])
  have h1 : f = c • P + (f ∘ₗ s) ∘ₗ (Submodule.span ℂ {v}).mkQ := by
    ext x
    simp [s, P, hc, smul_smul, mul_comm]
  have h2 : (Submodule.span ℂ {v}).mkQ ∘ₗ f ∘ₗ s = g := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    have h0 : (Submodule.Quotient.mk v : V ⧸ Submodule.span ℂ {v}) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self v)
    simp [s, P, hc, hg, h0]
  conv_lhs => rw [h1]
  rw [map_add, map_smul, LinearMap.trace_comp_comm', h2, LinearMap.trace_smulRight, hl, smul_eq_mul, mul_one]

open scoped Classical in

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `V _ _ _ ρ h`. Use `haveI : Subsingleton V := Module.finrank_zero_iff.1 h`. Use `⟨0, fun χ => ?_, fun t => ?_⟩` and prove the remaining obligations.

Simplify using `[jhMult_of_subsingleton (isIrreducible_ofChar χ)]`. Simplify using `[Subsingleton.elim (ρ t) 0]`. Consider the case `succ d ih`. Introduce `V _ _ _ ρ h`. Use `haveI : Nontrivial V := Module.finrank_pos_iff.1 (by rw [h]; exact d.succ_pos)`.

Take `⟨ψ, v, hv, hψ⟩` from `GlobalTheory.exists_character_eigenvector_of_commute ℂ G V ρ fun a b => by`. Rewrite using `[← map_mul, mul_comm, map_mul]`. Establish `hst : ∀ g, Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap (ρ g)` using `fun g => by`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hψ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)`.

Set `σ` to `ρ.quotient _ hst`. Establish `hd : Module.finrank ℂ (V ⧸ Submodule.span ℂ {v}) = d`. Use `(Submodule.span ℂ {v}).finrank_quotient_add_finrank` as an intermediate fact. Rewrite `this` using `[finrank_span_singleton hv, h]`. Use linear arithmetic over natural numbers and integers.

Take `⟨E, h1, h2⟩` from `ih _ σ hd`. Set `ι : (ofChar ψ).IntertwiningMap ρ` to `⟨LinearMap.toSpanSingleton ℂ V v, fun g => by ext; simp [hψ]⟩`. Set `p : ρ.IntertwiningMap σ` to `⟨Submodule.mkQ _, fun _ => rfl⟩`. Establish `hp : ∀ x, p x = 0 ↔ x ∈ Submodule.span ℂ {v}` using `fun x => Submodule.Quotient.mk_eq_zero _`. Use `⟨ψ ::ₘ E, fun χ => ?_, fun t => ?_⟩` and prove the remaining obligations.

Rewrite using `[JHMult.jhMult_exact ι p (isIrreducible_ofChar χ) (smul_left_injective ℂ hv) (Submodule.Quotient.mk_surjective _) (fun u => (hp _).2 (Submodule.smul_mem _ u (Submodule.mem_span_singleton_self v))) (fun x hx => Submodule.mem_span_singleton.1 ((hp x).1 hx)), ← h1, Multiset.count_co …`. Distinguish the cases in `hχ : χ = ψ`. Rewrite using `[hχ, jhMult_self (isIrreducible_ofChar _)]`. Simplify using the standard rewrite rules. Rewrite using `[Model.jhMult_ofChar_ne hχ]`.

Simplify using `[hχ]`. Rewrite using `[trace_eq_add_quot (ρ t) hv (hψ t) (σ t) fun _ => rfl, h2, Multiset.map_cons, Multiset.sum_cons]`.
-/
theorem exists_exponents {G : Type} [CommGroup G] (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V), Module.finrank ℂ V = d →
    ∃ E : Multiset (G →* ℂˣ), (∀ χ, (E.count χ : ℕ∞) = jhMult (ofChar χ) ρ) ∧
      ∀ t, LinearMap.trace ℂ V (ρ t) = (E.map fun χ => (χ t : ℂ)).sum := by
  induction d with
  | zero =>
    intro V _ _ _ ρ h
    haveI : Subsingleton V := Module.finrank_zero_iff.1 h
    refine ⟨0, fun χ => ?_, fun t => ?_⟩
    · simp [jhMult_of_subsingleton (isIrreducible_ofChar χ)]
    · simp [Subsingleton.elim (ρ t) 0]
  | succ d ih =>
    intro V _ _ _ ρ h
    haveI : Nontrivial V := Module.finrank_pos_iff.1 (by rw [h]; exact d.succ_pos)
    obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ G V ρ fun a b => by
      rw [← map_mul, mul_comm, map_mul]
    have hst : ∀ g, Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap (ρ g) := fun g => by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hψ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    let σ := ρ.quotient _ hst
    have hd : Module.finrank ℂ (V ⧸ Submodule.span ℂ {v}) = d := by
      have := (Submodule.span ℂ {v}).finrank_quotient_add_finrank
      rw [finrank_span_singleton hv, h] at this
      omega
    obtain ⟨E, h1, h2⟩ := ih _ σ hd
    let ι : (ofChar ψ).IntertwiningMap ρ := ⟨LinearMap.toSpanSingleton ℂ V v, fun g => by
      ext; simp [hψ]⟩
    let p : ρ.IntertwiningMap σ := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hp : ∀ x, p x = 0 ↔ x ∈ Submodule.span ℂ {v} := fun x => Submodule.Quotient.mk_eq_zero _
    refine ⟨ψ ::ₘ E, fun χ => ?_, fun t => ?_⟩
    · rw [JHMult.jhMult_exact ι p (isIrreducible_ofChar χ) (smul_left_injective ℂ hv)
        (Submodule.Quotient.mk_surjective _)
        (fun u => (hp _).2 (Submodule.smul_mem _ u (Submodule.mem_span_singleton_self v)))
        (fun x hx => Submodule.mem_span_singleton.1 ((hp x).1 hx)), ← h1, Multiset.count_cons, add_comm]
      by_cases hχ : χ = ψ
      · rw [hχ, jhMult_self (isIrreducible_ofChar _)]
        simp
      · rw [Model.jhMult_ofChar_ne hχ]
        simp [hχ]
    · rw [trace_eq_add_quot (ρ t) hv (hψ t) (σ t) fun _ => rfl, h2, Multiset.map_cons, Multiset.sum_cons]

end Exponents

section Abstract

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hint : ∀ (v : V) (φ : V → ℂ), IntegrableOn (fun g => φ (π g v)) D μ` using `fun v φ => ((IwahoriInj.isLocallyConstant_orbit hπ v).comp φ).continuous.continuousOn.integrableOn_compact' hD hm`. Establish `hex : ∀ v : V, ∃ w : V, ∀ l : Module.Dual ℂ V, l w = ∫ g in D, l (π g v) ∂μ`. Introduce `v`. Use `haveI : CompactSpace D := isCompact_iff_compactSpace.1 hD`. Establish `hf` using `((IwahoriInj.isLocallyConstant_orbit hπ v).comp_continuous (f := fun h : D => (h : G)) continuous_subtype_val).range_finite`.

Use `⟨∑ u ∈ hf.toFinset, (∫ g in D, (if π g v = u then 1 else 0 : ℂ) ∂μ) • u, fun l => ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_smul, smul_eq_mul, ← integral_mul_const]`. Rewrite using `[← integral_finset_sum _ fun u _ => hint v fun x => (if x = u then 1 else 0 : ℂ) * l u]`. Use `setIntegral_congr_fun hm fun g hg => ?_` and prove the remaining obligations. Establish `: π g v ∈ hf.toFinset` using `hf.mem_toFinset.2 ⟨⟨g, hg⟩, rfl⟩`.

Simplify using `[this]`. Use `choose a ha using hex`. Establish `hsep : ∀ x y : V, (∀ l : Module.Dual ℂ V, l x = l y) → x = y` using `fun x y h => by`. Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l`.

Rewrite using `[map_sub, h l, sub_self]`. Use `⟨⟨⟨a, fun x y => hsep _ _ fun l => ?_⟩, fun c x => hsep _ _ fun l => ?_⟩, fun v l => ⟨hint v l, ha v l⟩⟩` and prove the remaining obligations. Simplify using `only [map_add, ha]`. Conclude with `integral_add (hint x l) (hint y l)`. Simplify using `only [map_smul, ha, RingHom.id_apply]`.

Conclude with `integral_smul _ _`.
-/
theorem exists_setOp (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {π : Representation ℂ G V}
    (hπ : IsSmooth π) {D : Set G} (hD : IsCompact D) (hm : MeasurableSet D) :
    ∃ A : V →ₗ[ℂ] V, ∀ (v : V) (l : Module.Dual ℂ V),
      IntegrableOn (fun g => l (π g v)) D μ ∧ l (A v) = ∫ g in D, l (π g v) ∂μ := by
  classical
  have hint : ∀ (v : V) (φ : V → ℂ), IntegrableOn (fun g => φ (π g v)) D μ := fun v φ =>
    ((IwahoriInj.isLocallyConstant_orbit hπ v).comp φ).continuous.continuousOn.integrableOn_compact' hD hm
  have hex : ∀ v : V, ∃ w : V, ∀ l : Module.Dual ℂ V, l w = ∫ g in D, l (π g v) ∂μ := by
    intro v
    haveI : CompactSpace D := isCompact_iff_compactSpace.1 hD
    have hf := ((IwahoriInj.isLocallyConstant_orbit hπ v).comp_continuous (f := fun h : D => (h : G))
      continuous_subtype_val).range_finite
    refine ⟨∑ u ∈ hf.toFinset, (∫ g in D, (if π g v = u then 1 else 0 : ℂ) ∂μ) • u, fun l => ?_⟩
    simp only [map_sum, map_smul, smul_eq_mul, ← integral_mul_const]
    rw [← integral_finset_sum _ fun u _ => hint v fun x => (if x = u then 1 else 0 : ℂ) * l u]
    refine setIntegral_congr_fun hm fun g hg => ?_
    have : π g v ∈ hf.toFinset := hf.mem_toFinset.2 ⟨⟨g, hg⟩, rfl⟩
    simp [this]
  choose a ha using hex
  have hsep : ∀ x y : V, (∀ l : Module.Dual ℂ V, l x = l y) → x = y := fun x y h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, h l, sub_self]
  refine ⟨⟨⟨a, fun x y => hsep _ _ fun l => ?_⟩, fun c x => hsep _ _ fun l => ?_⟩,
    fun v l => ⟨hint v l, ha v l⟩⟩
  · simp only [map_add, ha]
    exact integral_add (hint x l) (hint y l)
  · simp only [map_smul, ha, RingHom.id_apply]
    exact integral_smul _ _

/- English proof (translation)
Take `⟨A, hA⟩` from `exists_setOp μ hπ hD hm`. Establish `e : ∀ φ : G → ℂ, (fun g => D.indicator (fun _ => (1 : ℂ)) g * φ g) = D.indicator φ` using `fun φ => by`. Use function extensionality and compare the values at `g`. Apply the tactic sequence `by_cases h : g ∈ D <;> simp [h]`. Establish `hfix : ∀ v, A v ∈ fixed π I` using `fun v => IwahoriInj.mem_fixed.2 fun a ha => by`.

Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l`. Rewrite using `[map_sub, sub_eq_zero, (hA v l).2]`. Use `(hA v (l ∘ₗ π a)).2.trans ?_` and prove the remaining obligations. Rewrite using `[← integral_indicator hm, ← integral_indicator hm, ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) a]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Distinguish the cases in `h : g ∈ D`. Simplify using `[h, hI a ha g h]`. Establish `: a * g ∉ D` using `fun h' => h (by simpa using hI _ (inv_mem ha) _ h')`.

Simplify using `[h, this]`. Establish `hle : LinearMap.range A ≤ fixed π I`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `hfix v`. Use `⟨A, fun v l => ?_, Submodule.finiteDimensional_of_le hle, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, integral_indicator hm, integrable_indicator_iff hm]`. Conclude with `hA v l`. Set `A' : fixed π I →ₗ[ℂ] fixed π I` to `A.restrict fun v _ => hfix v`. Set `φ` to `LinearEquiv.ofBijective _ hb`. Establish `h1 : φ.conj A' = (μ.real D : ℂ) • B`.

Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `φ.surjective u`. Rewrite using `[LinearEquiv.conj_apply_apply, φ.symm_apply_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`.

Introduce `l`. Rewrite using `[map_sub, sub_eq_zero]`. Use `(hA y (l ∘ₗ p)).2.trans ?_` and prove the remaining obligations. Use `(setIntegral_congr_fun (g := fun _ => l (B (φ y))) hm fun g hg => congrArg l (hB g hg y)).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[← smul_eq_mul, ← map_smul, ← h1, LinearMap.trace_conj']`. Use `haveI := Submodule.finiteDimensional_of_le hle`. Set `j` to `Submodule.inclusion hle`. Set `q : fixed π I →ₗ[ℂ] LinearMap.range A` to `A.rangeRestrict ∘ₗ (fixed π I).subtype`. Conclude with `LinearMap.trace_comp_comm' j q`.
-/
theorem hasTrace_indicator (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    {π : Representation ℂ G V} (hπ : IsSmooth π) {D : Set G} (hD : IsCompact D) (hm : MeasurableSet D)
    {I : Subgroup G} [FiniteDimensional ℂ (fixed π I)] (hI : ∀ a ∈ I, ∀ g ∈ D, a * g ∈ D)
    {W : Type} [AddCommGroup W] [Module ℂ W] (p : V →ₗ[ℂ] W) {U : Submodule ℂ W}
    (hp : ∀ v ∈ fixed π I, p v ∈ U) (hb : Function.Bijective (p.restrict hp)) (B : U →ₗ[ℂ] U)
    (hB : ∀ g ∈ D, ∀ v : fixed π I, p (π g v) = B (p.restrict hp v)) :
    HasTrace μ π (D.indicator fun _ => 1) ((μ.real D : ℂ) * LinearMap.trace ℂ U B) := by
  obtain ⟨A, hA⟩ := exists_setOp μ hπ hD hm
  have e : ∀ φ : G → ℂ, (fun g => D.indicator (fun _ => (1 : ℂ)) g * φ g) = D.indicator φ := fun φ => by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  have hfix : ∀ v, A v ∈ fixed π I := fun v => IwahoriInj.mem_fixed.2 fun a ha => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2]
    refine (hA v (l ∘ₗ π a)).2.trans ?_
    rw [← integral_indicator hm, ← integral_indicator hm, ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) a]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, hI a ha g h]
    · have : a * g ∉ D := fun h' => h (by simpa using hI _ (inv_mem ha) _ h')
      simp [h, this]
  have hle : LinearMap.range A ≤ fixed π I := by
    rintro _ ⟨v, rfl⟩
    exact hfix v
  refine ⟨A, fun v l => ?_, Submodule.finiteDimensional_of_le hle, ?_⟩
  · rw [e, integral_indicator hm, integrable_indicator_iff hm]
    exact hA v l
  let A' : fixed π I →ₗ[ℂ] fixed π I := A.restrict fun v _ => hfix v
  let φ := LinearEquiv.ofBijective _ hb
  have h1 : φ.conj A' = (μ.real D : ℂ) • B := by
    refine LinearMap.ext fun u => ?_
    obtain ⟨y, rfl⟩ := φ.surjective u
    rw [LinearEquiv.conj_apply_apply, φ.symm_apply_apply]
    apply Subtype.ext
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero]
    refine (hA y (l ∘ₗ p)).2.trans ?_
    refine (setIntegral_congr_fun (g := fun _ => l (B (φ y))) hm fun g hg => congrArg l (hB g hg y)).trans ?_
    simp
  rw [← smul_eq_mul, ← map_smul, ← h1, LinearMap.trace_conj']
  haveI := Submodule.finiteDimensional_of_le hle
  let j := Submodule.inclusion hle
  let q : fixed π I →ₗ[ℂ] LinearMap.range A := A.rangeRestrict ∘ₗ (fixed π I).subtype
  exact LinearMap.trace_comp_comm' j q

open scoped ENNReal in

/- English proof (translation)
Set `S : Set (N × G)` to `{x | (x.1 : G) ∈ I ∧ (x.1 * t)⁻¹ * x.2 ∈ I}`. Establish `hS : MeasurableSet S` using `((hI.preimage (f := fun x : N × G => (x.1 : G)) (by fun_prop)).inter (hI.preimage (f := fun x : N × G => (x.1 * t)⁻¹ * x.2) (by fun_prop))).measurableSet`. Establish `h0 : MeasurableSet {s : N | (s : G) ∈ I}` using `(hI.preimage continuous_subtype_val).measurableSet`. Rewrite using `[← lintegral_indicator_const hm, ← lintegral_indicator_const h0]`. Use `Eq.trans ?_ (((Measure.prod_apply_symm (μ := ν) (ν := μ) hS).symm.trans (Measure.prod_apply hS)).trans ?_)` and prove the remaining obligations.

Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ D`. Rewrite using `[Set.indicator_of_mem hg]`. Take `⟨u, hu, huI, i, hi, rfl⟩` from `(hD g).1 hg`. Rewrite using `[← measure_preimage_mul ν (⟨u, hu⟩ : N)⁻¹]`.

Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, e⟩`. Establish `e' : (x : G) = u * (t * s * t⁻¹)` using `by rw [← e]; simp`.

Use `⟨e' ▸ mul_mem huI (hc _ s.2 hs), ?_⟩` and prove the remaining obligations. Use `show ((x : G) * t)⁻¹ * (u * t * i) ∈ I`. Use `mul_mem (inv_mem hs) hi using 1` and compare the differences between its conclusion and the goal. Rewrite using `[e']`. Use `group`.

Introduce and unpack `⟨-, h2⟩`. Use `⟨⟨_, ht _ (mul_mem (inv_mem hu) x.2)⟩, ?_, by simp [mul_assoc]⟩` and prove the remaining obligations. Use `show t⁻¹ * (u⁻¹ * x) * t ∈ I`. Use `mul_mem hi (inv_mem h2) using 1` and compare the differences between its conclusion and the goal. Use `group`.

Rewrite using `[Set.indicator_of_notMem hg, Set.eq_empty_of_forall_notMem (s := _ ⁻¹' S), measure_empty]`. Introduce and unpack `x ⟨h1, h2⟩`. Conclude with `hg ((hD g).2 ⟨x, x.2, h1, _, h2, (mul_inv_cancel_left _ _).symm⟩)`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : (x : G) ∈ I`.

Rewrite using `[Set.indicator_of_mem (show x ∈ {s : N | (s : G) ∈ I} from hx), ← measure_preimage_mul μ ((x : G) * t)⁻¹ I]`. Use `congr 1`. Use extensionality with `g`. Conclude with `⟨fun h => h.2, fun h => ⟨hx, h⟩⟩`. Rewrite using `[Set.indicator_of_notMem (show x ∉ {s : N | (s : G) ∈ I} from hx), Set.eq_empty_of_forall_notMem (s := _ ⁻¹' S) fun g h => hx h.1, measure_empty]`.
-/
theorem measure_mul_eq [SecondCountableTopology G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    {N I : Subgroup G} [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [SFinite ν] [ν.IsMulLeftInvariant]
    (hI : IsOpen (I : Set G)) {t : G} (ht : ∀ u ∈ N, t⁻¹ * u * t ∈ N)
    (hc : ∀ u ∈ N, u ∈ I → t * u * t⁻¹ ∈ I) {D : Set G} (hm : MeasurableSet D)
    (hD : ∀ g, g ∈ D ↔ ∃ u ∈ N, u ∈ I ∧ ∃ i ∈ I, g = u * t * i) :
    ν {u : N | ∃ s ∈ {s : N | (s : G) ∈ I}, (u : G) = t * s * t⁻¹} * μ D = μ I * ν {s : N | (s : G) ∈ I} := by
  let S : Set (N × G) := {x | (x.1 : G) ∈ I ∧ (x.1 * t)⁻¹ * x.2 ∈ I}
  have hS : MeasurableSet S :=
    ((hI.preimage (f := fun x : N × G => (x.1 : G)) (by fun_prop)).inter
      (hI.preimage (f := fun x : N × G => (x.1 * t)⁻¹ * x.2) (by fun_prop))).measurableSet
  have h0 : MeasurableSet {s : N | (s : G) ∈ I} := (hI.preimage continuous_subtype_val).measurableSet
  rw [← lintegral_indicator_const hm, ← lintegral_indicator_const h0]
  refine Eq.trans ?_ (((Measure.prod_apply_symm (μ := ν) (ν := μ) hS).symm.trans (Measure.prod_apply hS)).trans ?_)
  · refine lintegral_congr fun g => ?_
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg]
      obtain ⟨u, hu, huI, i, hi, rfl⟩ := (hD g).1 hg
      rw [← measure_preimage_mul ν (⟨u, hu⟩ : N)⁻¹]
      congr 1
      ext x
      constructor
      · rintro ⟨s, hs, e⟩
        have e' : (x : G) = u * (t * s * t⁻¹) := by rw [← e]; simp
        refine ⟨e' ▸ mul_mem huI (hc _ s.2 hs), ?_⟩
        show ((x : G) * t)⁻¹ * (u * t * i) ∈ I
        convert mul_mem (inv_mem hs) hi using 1
        rw [e']; group
      · rintro ⟨-, h2⟩
        refine ⟨⟨_, ht _ (mul_mem (inv_mem hu) x.2)⟩, ?_, by simp [mul_assoc]⟩
        show t⁻¹ * (u⁻¹ * x) * t ∈ I
        convert mul_mem hi (inv_mem h2) using 1
        group
    · rw [Set.indicator_of_notMem hg, Set.eq_empty_of_forall_notMem (s := _ ⁻¹' S), measure_empty]
      rintro x ⟨h1, h2⟩
      exact hg ((hD g).2 ⟨x, x.2, h1, _, h2, (mul_inv_cancel_left _ _).symm⟩)
  · refine lintegral_congr fun x => ?_
    by_cases hx : (x : G) ∈ I
    · rw [Set.indicator_of_mem (show x ∈ {s : N | (s : G) ∈ I} from hx), ← measure_preimage_mul μ ((x : G) * t)⁻¹ I]
      congr 1
      ext g
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    · rw [Set.indicator_of_notMem (show x ∉ {s : N | (s : G) ∈ I} from hx),
        Set.eq_empty_of_forall_notMem (s := _ ⁻¹' S) fun g h => hx h.1, measure_empty]

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [LinearOrder n] in
/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diag_mul_mul_diag (s t : n → kˣ) (c : GL n k) (i j : n) :
    (diagT k n s * c * diagT k n t).val i j = (s i * t j : kˣ) * c.val i j := by
  rw [Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul, Units.val_mul]
  ring

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
The claim follows from `(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (points n) _) u).1 hu`.
-/
theorem conj_mem_unipB (t : n → kˣ) {u : GL n k} (hu : u ∈ unipB k n) :
    diagT k n t * u * (diagT k n t)⁻¹ ∈ unipB k n :=
  (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (points n) _) u).1 hu

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
The claim follows from `(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer_lower k (points n) _) u).1 hu`.
-/
theorem conj_mem_unipBLower (t : n → kˣ) {u : GL n k} (hu : u ∈ unipBLower k n) :
    diagT k n t * u * (diagT k n t)⁻¹ ∈ unipBLower k n :=
  (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer_lower k (points n) _) u).1 hu

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
The claim follows from `(mem_unipB (n := nᵒᵈ) k).trans ⟨fun h => ⟨fun i j => h.1 i j, h.2⟩, fun h => ⟨fun i j => h.1 i j, h.2⟩⟩`.
-/
theorem mem_unipBLower {g : GL n k} :
    g ∈ unipBLower k n ↔ (∀ i j, i < j → g.val i j = 0) ∧ ∀ i, g.val i i = 1 :=
  (mem_unipB (n := nᵒᵈ) k).trans ⟨fun h => ⟨fun i j => h.1 i j, h.2⟩, fun h => ⟨fun i j => h.1 i j, h.2⟩⟩

/- English proof (translation)
Introduce `ϖ hϖ a ha`. Establish `hv : ∀ x y : ℤ, y ≤ x → valuation k ((ϖ ^ x * (ϖ ^ y)⁻¹ : kˣ) : k) ≤ 1` using `fun x y h => by`. Rewrite using `[← _root_.zpow_sub, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]`. Conclude with `zpow_le_one₀ uniformizer_pos uniformizer_lt_one.le (by omega)`. Prove the components needed by the constructor for the conclusion.

Establish `key : ∀ u ∈ unipO k n, StepData.IntM (diagT k n (fun i => ϖ ^ a i) * u * (diagT k n fun i => ϖ ^ a i)⁻¹).val` using `fun u hu i j => by`. Rewrite using `[← map_inv, diag_mul_mul_diag]`. Break down `lt_or_ge j i with h | h` into its components or cases. Rewrite using `[((mem_unipB k).1 hu.1).1 i j h, mul_zero]`. Conclude with `zero_mem _`.

Conclude with `mul_mem (hv _ _ (ha h)) (StepData.intM_of_mem_KO hu.2 i j)`. Introduce `u hu`. Use `⟨conj_mem_unipB _ hu.1, StepData.mem_KO.2 ⟨key u hu, ?_⟩⟩` and prove the remaining obligations. Use `key _ (inv_mem hu) using 2` and compare the differences between its conclusion and the goal. Use `group`.

Introduce `u hu`. Establish `h1` using `conj_mem_unipBLower (fun i => ϖ ^ a i)⁻¹ hu.1`. Rewrite `h1` using `[map_inv, inv_inv]`. Use `⟨h1, StepData.mem_KOne.2 fun i j => ?_⟩` and prove the remaining obligations. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases.

Simplify using `only [Matrix.sub_apply, (mem_unipBLower.1 h1).1 i j h, one_apply_ne h.ne, sub_self, map_zero, zero_lt_one]`. Simplify using `only [Matrix.sub_apply, (mem_unipBLower.1 h1).2 i, one_apply_eq, sub_self, map_zero, zero_lt_one]`. Establish `h2` using `StepData.mem_KOne.1 hu.2 i j`. Rewrite `h2`, the goal using `[Matrix.sub_apply, one_apply_ne h.ne', sub_zero]`. Rewrite using `[← map_inv, diag_mul_mul_diag, mul_comm (_ : kˣ), map_mul]`.

Conclude with `(mul_le_of_le_one_left' (hv _ _ (ha h.le))).trans_lt h2`.
-/
theorem dominantContracts : DominantContracts k n := by
  intro ϖ hϖ a ha
  have hv : ∀ x y : ℤ, y ≤ x → valuation k ((ϖ ^ x * (ϖ ^ y)⁻¹ : kˣ) : k) ≤ 1 := fun x y h => by
    rw [← _root_.zpow_sub, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    exact zpow_le_one₀ uniformizer_pos uniformizer_lt_one.le (by omega)
  constructor
  · have key : ∀ u ∈ unipO k n, StepData.IntM
        (diagT k n (fun i => ϖ ^ a i) * u * (diagT k n fun i => ϖ ^ a i)⁻¹).val := fun u hu i j => by
      rw [← map_inv, diag_mul_mul_diag]
      rcases lt_or_ge j i with h | h
      · rw [((mem_unipB k).1 hu.1).1 i j h, mul_zero]
        exact zero_mem _
      · exact mul_mem (hv _ _ (ha h)) (StepData.intM_of_mem_KO hu.2 i j)
    intro u hu
    refine ⟨conj_mem_unipB _ hu.1, StepData.mem_KO.2 ⟨key u hu, ?_⟩⟩
    convert key _ (inv_mem hu) using 2
    group
  · intro u hu
    have h1 := conj_mem_unipBLower (fun i => ϖ ^ a i)⁻¹ hu.1
    rw [map_inv, inv_inv] at h1
    refine ⟨h1, StepData.mem_KOne.2 fun i j => ?_⟩
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [Matrix.sub_apply, (mem_unipBLower.1 h1).1 i j h, one_apply_ne h.ne, sub_self, map_zero, zero_lt_one]
    · simp only [Matrix.sub_apply, (mem_unipBLower.1 h1).2 i, one_apply_eq, sub_self, map_zero, zero_lt_one]
    · have h2 := StepData.mem_KOne.1 hu.2 i j
      rw [Matrix.sub_apply, one_apply_ne h.ne', sub_zero] at h2 ⊢
      rw [← map_inv, diag_mul_mul_diag, mul_comm (_ : kˣ), map_mul]
      exact (mul_le_of_le_one_left' (hv _ _ (ha h.le))).trans_lt h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨hu, iwahori_le_KO k n h⟩, fun h => mem_iwahori.2 ⟨h.2, fun i j hij => by rw [((mem_unipB k).1 hu).1 i j hij, map_zero]; exact zero_lt_one⟩⟩`.
-/
theorem mem_unipO_iff {u : GL n k} (hu : u ∈ unipB k n) : u ∈ iwahori k n ↔ u ∈ unipO k n :=
  ⟨fun h => ⟨hu, iwahori_le_KO k n h⟩, fun h => mem_iwahori.2 ⟨h.2, fun i j hij => by
    rw [((mem_unipB k).1 hu).1 i j hij, map_zero]; exact zero_lt_one⟩⟩

/- English proof (translation)
Take `⟨d, hd, x, hx, c, ⟨h1, h2, h3⟩, rfl⟩` from `IwahoriOnto.iwahori_factor k n g hg`. Establish `hc : c ∈ KO k n`. Set `A : Matrix n n 𝒪[k]` to `fun i j => ⟨c.val i j, h1 i j⟩`. Establish `hA : A.det = 1`. Rewrite using `[det_of_lowerTriangular A fun i j hij => Subtype.ext (h2 i j hij)]`.

Conclude with `Finset.prod_eq_one fun i _ => Subtype.ext (h3 i)`. Conclude with `⟨GeneralLinearGroup.mk'' A (by rw [hA]; exact isUnit_one), Units.ext rfl⟩`. Establish `hu : diagT k n d * x * (diagT k n d)⁻¹ ∈ unipO k n`. Use `⟨conj_mem_unipB d hx, ?_⟩` and prove the remaining obligations. Use `mul_mem (mul_mem (iwahori_le_KO k n hg) (inv_mem hc)) (inv_mem (iwahori_le_KO k n (diagT_mem_iwahori hd)))` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel_right]`. Then use the resulting hypothesis. Establish `hcI : c ∈ iwahori k n`. Use `mul_mem (inv_mem (mul_mem ((mem_unipO_iff hu.1).2 hu) (diagT_mem_iwahori hd))) hg` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right, inv_mul_cancel_left]`. Then use the resulting hypothesis. Use `⟨_, hu, d, hd, c, ⟨mem_unipBLower.2 ⟨h2, h3⟩, StepData.mem_KOne.2 fun i j => ?_⟩, by group⟩` and prove the remaining obligations.

Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Simplify using `[h2 i j h, one_apply_ne h.ne]`. Simplify using `[h3 i]`. Simplify `(mem_iwahori.1 hcI).2 i j h` using `[one_apply_ne h.ne']`.
-/
theorem iwahori_factorisation {g : GL n k} (hg : g ∈ iwahori k n) :
    ∃ u ∈ unipO k n, ∃ d ∈ torusO k n, ∃ c ∈ unipLowerOne k n, g = u * diagT k n d * c := by
  obtain ⟨d, hd, x, hx, c, ⟨h1, h2, h3⟩, rfl⟩ := IwahoriOnto.iwahori_factor k n g hg
  have hc : c ∈ KO k n := by
    let A : Matrix n n 𝒪[k] := fun i j => ⟨c.val i j, h1 i j⟩
    have hA : A.det = 1 := by
      rw [det_of_lowerTriangular A fun i j hij => Subtype.ext (h2 i j hij)]
      exact Finset.prod_eq_one fun i _ => Subtype.ext (h3 i)
    exact ⟨GeneralLinearGroup.mk'' A (by rw [hA]; exact isUnit_one), Units.ext rfl⟩
  have hu : diagT k n d * x * (diagT k n d)⁻¹ ∈ unipO k n := by
    refine ⟨conj_mem_unipB d hx, ?_⟩
    have := mul_mem (mul_mem (iwahori_le_KO k n hg) (inv_mem hc))
      (inv_mem (iwahori_le_KO k n (diagT_mem_iwahori hd)))
    rwa [mul_inv_cancel_right] at this
  have hcI : c ∈ iwahori k n := by
    have := mul_mem (inv_mem (mul_mem ((mem_unipO_iff hu.1).2 hu) (diagT_mem_iwahori hd))) hg
    rwa [inv_mul_cancel_right, inv_mul_cancel_left] at this
  refine ⟨_, hu, d, hd, c, ⟨mem_unipBLower.2 ⟨h2, h3⟩, StepData.mem_KOne.2 fun i j => ?_⟩, by group⟩
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h2 i j h, one_apply_ne h.ne]
  · simp [h3 i]
  · simpa [one_apply_ne h.ne'] using (mem_iwahori.1 hcI).2 i j h

/- English proof (translation)
Use `⟨?_, fun ⟨u, _, hu, i, hi, e⟩ => ⟨u, hu, i, hi, e⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Take `⟨u, hu, d, hd, c, hc, rfl⟩` from `iwahori_factorisation ha`. Use `⟨u, hu.1, (mem_unipO_iff hu.1).2 hu, _, mul_mem (mul_mem (diagT_mem_iwahori hd) (KOne_le_iwahori k n (ht.2 c hc).2)) hb, ?_⟩` and prove the remaining obligations. Establish `: diagT k n t * diagT k n d = diagT k n d * diagT k n t` using `by rw [← map_mul, mul_comm, map_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mem_iwahoriCoset {t : n → kˣ} (ht : Contracts t) (g : GL n k) :
    g ∈ iwahoriCoset t ↔ ∃ u ∈ unipB k n, u ∈ iwahori k n ∧ ∃ i ∈ iwahori k n, g = u * diagT k n t * i := by
  refine ⟨?_, fun ⟨u, _, hu, i, hi, e⟩ => ⟨u, hu, i, hi, e⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := iwahori_factorisation ha
  refine ⟨u, hu.1, (mem_unipO_iff hu.1).2 hu, _, mul_mem (mul_mem (diagT_mem_iwahori hd)
    (KOne_le_iwahori k n (ht.2 c hc).2)) hb, ?_⟩
  have : diagT k n t * diagT k n d = diagT k n d * diagT k n t := by rw [← map_mul, mul_comm, map_mul]
  calc u * diagT k n d * c * diagT k n t * b
      = u * (diagT k n d * diagT k n t) * ((diagT k n t)⁻¹ * c * diagT k n t) * b := by group
    _ = _ := by rw [← this]; group

/- English proof (translation)
Establish `h` using `IwahoriOnto.isCompact_iwahori k n`. Use `(h.prod h).image (f := fun x : GL n k × GL n k => x.1 * diagT k n t * x.2) (by fun_prop) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Conclude with `⟨fun ⟨a, ha, b, hb, e⟩ => ⟨(a, b), ⟨ha, hb⟩, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x.1, hx.1, x.2, hx.2, e.symm⟩⟩`.
-/
theorem isCompact_iwahoriCoset (t : n → kˣ) : IsCompact (iwahoriCoset t) := by
  have h := IwahoriOnto.isCompact_iwahori k n
  convert (h.prod h).image (f := fun x : GL n k × GL n k => x.1 * diagT k n t * x.2) (by fun_prop) using 1
  ext g
  exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨(a, b), ⟨ha, hb⟩, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x.1, hx.1, x.2, hx.2, e.symm⟩⟩

/- English proof (translation)
Use `haveI := secondCountable k`. Use `haveI := t2Space k`. Use `letI : MeasurableSpace (unipRad k (points n)) := _root_.borel _`. Use `haveI : BorelSpace (unipRad k (points n)) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (unipRad k (points n)) := (UnipHaar.unipHomeo (points n)).isClosedEmbedding.locallyCompactSpace`.

Use `haveI : SecondCountableTopology (unipRad k (points n)) := (UnipHaar.unipHomeo (points n)).secondCountableTopology`. Set `ν : Measure (unipRad k (points n))` to `Measure.haar`. Establish `ho : IsOpen {s : unipRad k (points n) | (s : GL n k) ∈ iwahori k n}` using `(IwahoriOnto.isOpen_iwahori k n).preimage continuous_subtype_val`. Establish `hcl : IsClosed (unipRad k (points n) : Set (GL n k))`. Establish `e : (unipRad k (points n) : Set (GL n k)) = (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL n k | g.val i j = 0}) ∩ ⋂ i, {g : GL n k | g.val i i = 1}`.

Use extensionality with `g`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter]`. Conclude with `mem_unipB k`. Rewrite using `[e]`. Conclude with `(isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)`.

Establish `hc : IsCompact {s : unipRad k (points n) | (s : GL n k) ∈ iwahori k n}` using `hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (IwahoriOnto.isCompact_iwahori k n)`. Establish `h1` using `measure_mul_eq μ ν (IwahoriOnto.isOpen_iwahori k n) (t := diagT k n t) (fun u hu => by simpa [unipB] using conj_mem_unipB t⁻¹ hu) (fun u hu hI => (mem_unipO_iff (conj_mem_unipB t hu)).2 (ht.1 u ((mem_unipO_iff hu).1 hI))) (isCompact_iwahoriCoset t).measurableSet (mem_iwahoriCoset …`. Establish `h2` using `UnipHaar.haar_conj_eq_modulus_mul k n n (fun _ => Unit) (points n) ν (leviTorus k n t) _ ho.measurableSet`. Rewrite `h2` using `[← deltaB_eq_modulus]`. Establish `h3` using `(congrArg (· * μ (iwahoriCoset t)) h2).symm.trans h1`.

Rewrite `h3` using `[mul_right_comm, ENNReal.mul_left_inj (ho.measure_pos ν ⟨1, one_mem (iwahori k n)⟩).ne' hc.measure_lt_top.ne]`. Rewrite using `[measureReal_def, measureReal_def, ← h3, ENNReal.toReal_mul, ENNReal.toReal_ofReal (deltaB_pos t).le, mul_right_comm, mul_inv_cancel₀ (deltaB_pos t).ne', one_mul]`.
-/
theorem measure_iwahoriCoset [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k))
    [μ.IsHaarMeasure] {t : n → kˣ} (ht : Contracts t) :
    μ.real (iwahoriCoset t) = μ.real (iwahori k n : Set (GL n k)) * (deltaB t)⁻¹ := by
  haveI := secondCountable k
  haveI := t2Space k
  letI : MeasurableSpace (unipRad k (points n)) := _root_.borel _
  haveI : BorelSpace (unipRad k (points n)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipRad k (points n)) :=
    (UnipHaar.unipHomeo (points n)).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k (points n)) :=
    (UnipHaar.unipHomeo (points n)).secondCountableTopology
  let ν : Measure (unipRad k (points n)) := Measure.haar
  have ho : IsOpen {s : unipRad k (points n) | (s : GL n k) ∈ iwahori k n} :=
    (IwahoriOnto.isOpen_iwahori k n).preimage continuous_subtype_val
  have hcl : IsClosed (unipRad k (points n) : Set (GL n k)) := by
    have e : (unipRad k (points n) : Set (GL n k)) = (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL n k | g.val i j = 0}) ∩
        ⋂ i, {g : GL n k | g.val i i = 1} := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter]
      exact mem_unipB k
    rw [e]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter
      (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)
  have hc : IsCompact {s : unipRad k (points n) | (s : GL n k) ∈ iwahori k n} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (IwahoriOnto.isCompact_iwahori k n)
  have h1 := measure_mul_eq μ ν (IwahoriOnto.isOpen_iwahori k n) (t := diagT k n t)
    (fun u hu => by simpa [unipB] using conj_mem_unipB t⁻¹ hu)
    (fun u hu hI => (mem_unipO_iff (conj_mem_unipB t hu)).2 (ht.1 u ((mem_unipO_iff hu).1 hI)))
    (isCompact_iwahoriCoset t).measurableSet (mem_iwahoriCoset ht)
  have h2 := UnipHaar.haar_conj_eq_modulus_mul k n n (fun _ => Unit) (points n) ν (leviTorus k n t) _
    ho.measurableSet
  rw [← deltaB_eq_modulus] at h2
  have h3 := (congrArg (· * μ (iwahoriCoset t)) h2).symm.trans h1
  rw [mul_right_comm, ENNReal.mul_left_inj (ho.measure_pos ν ⟨1, one_mem (iwahori k n)⟩).ne' hc.measure_lt_top.ne] at h3
  rw [measureReal_def, measureReal_def, ← h3, ENNReal.toReal_mul, ENNReal.toReal_ofReal (deltaB_pos t).le,
    mul_right_comm, mul_inv_cancel₀ (deltaB_pos t).ne', one_mul]

/- English proof (translation)
Introduce `_ _ μ _ V _ _ π hπ`. Use `haveI := hπ.2 _ (IwahoriOnto.isOpen_iwahori k n) (IwahoriOnto.isCompact_iwahori k n)`. Establish `hb` using `h k n V π hπ`. Use `haveI hfd : FiniteDimensional ℂ (fixed (jacBU π) (torusO k n)) := Module.Finite.of_surjective _ hb.2`. Establish `key : ∀ t : n → kˣ, Contracts t → HasTrace μ π (cosetInd t) ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ * LinearMap.trace ℂ (fixed (jacBU π) (torusO k n)) (jacBUFixed π t))`.

Introduce `t ht`. Establish `h1` using `hasTrace_indicator μ hπ.1 (isCompact_iwahoriCoset t) (isCompact_iwahoriCoset t).measurableSet (I := iwahori k n) (by`. Introduce and unpack `a ha _ ⟨b, hb, c, hc, rfl⟩`. Conclude with `⟨_, mul_mem ha hb, c, hc, by simp only [mul_assoc]⟩)`. Use the proof step `(twKer π (unipB k n) 1).mkQ _ hb (jacBUFixed π t) fun g hg v => by`.

Take `⟨u, hu, -, i, hi, rfl⟩` from `(mem_iwahoriCoset ht g).1 hg`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, IwahoriInj.mem_fixed.1 v.2 i hi]`. Conclude with `(Submodule.Quotient.eq _).2 (IwahoriInj.sub_mem_twKer hu _)`. Rewrite `h1` using `[measure_iwahoriCoset μ ht, Complex.ofReal_mul, Complex.ofReal_inv]`. Then use the resulting hypothesis. Take `⟨E, h1, h2⟩` from `exists_exponents _ _ (jacBUFixed π) rfl`.

Use `⟨hfd, key, E, ⟨fun χ hχ s hs => ?_, h1⟩, fun t ht => h2 t ▸ key t ht⟩` and prove the remaining obligations. Establish `h0 : jhMult (ofChar χ) (jacBUFixed π) ≠ 0` using `by classical`. Rewrite using `[← h1, Nat.cast_ne_zero]`. Use `Multiset.count_ne_zero.2 hχ` and compare the differences between its conclusion and the goal. Establish `h3` using `Model.scalar_of_isSubquotient (g := s) (c := 1) (JHMult.jhMult_ne_zero_iff.1 h0) (fun v => Subtype.ext ((IwahoriInj.mem_fixed.1 v.2 s hs).trans (by simp))) 1`.

Use `ext`. Simplify using `using h3`.
-/
theorem traceFormula (h : GlobalTheory.Published.BorelCasselman) : TraceFormula k n := by
  intro _ _ μ _ V _ _ π hπ
  haveI := hπ.2 _ (IwahoriOnto.isOpen_iwahori k n) (IwahoriOnto.isCompact_iwahori k n)
  have hb := h k n V π hπ
  haveI hfd : FiniteDimensional ℂ (fixed (jacBU π) (torusO k n)) := Module.Finite.of_surjective _ hb.2
  have key : ∀ t : n → kˣ, Contracts t → HasTrace μ π (cosetInd t)
      ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
        LinearMap.trace ℂ (fixed (jacBU π) (torusO k n)) (jacBUFixed π t)) := by
    intro t ht
    have h1 := hasTrace_indicator μ hπ.1 (isCompact_iwahoriCoset t) (isCompact_iwahoriCoset t).measurableSet
      (I := iwahori k n) (by
        rintro a ha _ ⟨b, hb, c, hc, rfl⟩
        exact ⟨_, mul_mem ha hb, c, hc, by simp only [mul_assoc]⟩)
      (twKer π (unipB k n) 1).mkQ _ hb (jacBUFixed π t) fun g hg v => by
        obtain ⟨u, hu, -, i, hi, rfl⟩ := (mem_iwahoriCoset ht g).1 hg
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, IwahoriInj.mem_fixed.1 v.2 i hi]
        exact (Submodule.Quotient.eq _).2 (IwahoriInj.sub_mem_twKer hu _)
    rwa [measure_iwahoriCoset μ ht, Complex.ofReal_mul, Complex.ofReal_inv] at h1
  obtain ⟨E, h1, h2⟩ := exists_exponents _ _ (jacBUFixed π) rfl
  refine ⟨hfd, key, E, ⟨fun χ hχ s hs => ?_, h1⟩, fun t ht => h2 t ▸ key t ht⟩
  have h0 : jhMult (ofChar χ) (jacBUFixed π) ≠ 0 := by
    classical
    rw [← h1, Nat.cast_ne_zero]
    convert Multiset.count_ne_zero.2 hχ
  have h3 := Model.scalar_of_isSubquotient (g := s) (c := 1) (JHMult.jhMult_ne_zero_iff.1 h0)
    (fun v => Subtype.ext ((IwahoriInj.mem_fixed.1 v.2 s hs).trans (by simp))) 1
  ext
  simpa using h3

end Local

/- English proof (translation)
Introduce `h _ _ _ _ _ _` and use `⟨dominantContracts, traceFormula h⟩`.
-/
theorem iwahoriTrace_of_borelCasselman : GlobalTheory.Published.BorelCasselman → IwahoriTrace :=
  fun h _ _ _ _ _ _ => ⟨dominantContracts, traceFormula h⟩

/- English proof (translation)
The claim follows from `iwahoriTrace_of_borelCasselman GlobalTheory.Published.BorelCasselman_holds`.
-/
theorem iwahoriTrace : IwahoriTrace := iwahoriTrace_of_borelCasselman GlobalTheory.Published.BorelCasselman_holds

end GlobalTheory.IwahoriTraceProof
