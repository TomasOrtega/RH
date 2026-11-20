import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeCupProps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorOfChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitMulPowOfKummerVanishesOnInertiaCurve
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeEqZeroOfInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter

open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.K4.TopSpec

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.K4.TopW.mem_geo]`. Introduce `z`. Conclude with `g.commutes z`.
-/
theorem _root_.GlobalTheory.K4.TopSpec.res_mem_geo (g : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictScalarsHom F g ∈ _root_.GlobalTheory.K4.geo F K Ω := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo]
  intro z
  exact g.commutes z

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
/- English proof (translation)
Rewrite `hg` using `[_root_.GlobalTheory.K4.TopW.mem_geo]`. Use `⟨{ g.toRingEquiv with commutes' := hg }, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.K4.TopSpec.exists_res {g : Ω ≃ₐ[F] Ω}
    (hg : g ∈ _root_.GlobalTheory.K4.geo F K Ω) :
    ∃ g' : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g' = g := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo] at hg
  refine ⟨{ g.toRingEquiv with commutes' := hg }, ?_⟩
  ext y
  rfl

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
/- English proof (translation)
Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`. Rewrite `hs` using `[krullTopology_mem_nhds_one_iff]`. Take `⟨E, hE, hEs⟩` from `hs`.

Rewrite using `[Filter.mem_map, krullTopology_mem_nhds_one_iff]`. Set `b` to `Module.finBasis F E`. Use `⟨IntermediateField.adjoin K (Set.range fun i => (b i : Ω)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Introduce `g hg`.

Apply `hEs` to reduce the goal to its premises. Establish `hfix : ∀ i, g (b i : Ω) = b i` using `fun i => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`. Establish `key : ∀ z : E, AlgEquiv.restrictScalarsHom F g (z : Ω) = z`.

Introduce `z`. Proceed by induction on `(b.mem_span z) using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨i, rfl⟩` from `hu`. Conclude with `hfix i`.

Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [IntermediateField.coe_add, map_add, hu, hv]`. Consider the case `smul a u _ hu => rw [IntermediateField.coe_smul, map_smul, hu]`. Conclude with `key ⟨y, hy⟩`.
-/
theorem _root_.GlobalTheory.K4.TopSpec.continuous_res [Algebra.IsAlgebraic K Ω] :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  classical
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis F E
  refine ⟨IntermediateField.adjoin K (Set.range fun i => (b i : Ω)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · intro g hg
    apply hEs
    have hfix : ∀ i, g (b i : Ω) = b i := fun i =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have key : ∀ z : E, AlgEquiv.restrictScalarsHom F g (z : Ω) = z := by
      intro z
      induction (b.mem_span z) using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        exact hfix i
      | zero => simp
      | add u v _ _ hu hv => rw [IntermediateField.coe_add, map_add, hu, hv]
      | smul a u _ hu => rw [IntermediateField.coe_smul, map_smul, hu]
    exact key ⟨y, hy⟩

end GlobalTheory.K4.TopSpec

open Polynomial in

/- English proof (translation)
Introduce `k K Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ hfix _ a b α β ha hb _ _ _ _ hα hβ x y hx hy η hcob hη _ σ`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective`. Use `haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic`.

Use `haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F K Ω`. Use `set H := _root_.GlobalTheory.K4.geo F K Ω with hH`. Use `haveI : H.Normal := ⟨fun h hh g => _root_.GlobalTheory.K4.TopW.conj_mem_geo g hh⟩`. Take `⟨hhom, -, -⟩` from `_root_.GlobalTheory.KEdge.edge_cup_props _ N H x y η hcob`. Establish `hres` using `_root_.GlobalTheory.K4.TopSpec.continuous_res (F := F) (K := K) (Ω := Ω)`.

Establish `hmem : ∀ g : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g ∈ H` using `_root_.GlobalTheory.K4.TopSpec.res_mem_geo`. Establish `hne : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c → γ ≠ 0`. Introduce `γ c hc hγ h0`. Rewrite `hγ` using `[h0, zero_pow hN.ne']`. Conclude with `hc ((algebraMap F Ω).injective (hγ.symm.trans (map_zero _).symm))`.

Establish `hkum : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c → IsLocallyConstant (_root_.GlobalTheory.NeedB.kum (K` using `F) (N := N) ζ γ) := fun hc hγ => (_root_.GlobalTheory.NeedB.KumLemma.kummer_character_main F Ω N ζ _ hN hζ hfix (hne hc hγ) ⟨_, hγ.symm⟩).1`. Establish `hx_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g))`. Establish `hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g))) = _root_.GlobalTheory.NeedB.kum ζ α ∘ AlgEquiv.restrictScalarsHom F` using `funext fun g => hx _`. Rewrite using `[hfun]`. Conclude with `(hkum ha hα).comp_continuous hres`.

Establish `hy_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g))`. Establish `hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g))) = _root_.GlobalTheory.NeedB.kum ζ β ∘ AlgEquiv.restrictScalarsHom F` using `funext fun g => hy _`. Rewrite using `[hfun]`. Conclude with `(hkum hb hβ).comp_continuous hres`. Establish `hη₁ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (AlgEquiv.restrictScalarsHom F g)` using `hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω => (⟨AlgEquiv.restrictScalarsHom F g, hmem g⟩ : H)) (hres.subtype_mk _)`.

Establish `hη₂ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹)` using `hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω => (⟨σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹, _root_.GlobalTheory.K4.TopW.conj_mem_geo σ (hmem g)⟩ : H)) (((continuous_const.mul hres).mul continuous_const).subtype_mk _)`. Set `χ : (Ω ≃ₐ[K] Ω) → ZMod N` to `fun g => _root_.GlobalTheory.KEdge.edge x y η σ (AlgEquiv.restrictScalarsHom F g)`. Establish `hlc : IsLocallyConstant χ`. Establish `hfun : χ = fun g => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) - η (AlgEquiv.restrictScalarsHom F g) - Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) * Multiplicative.toAdd (y σ) + Multiplicative.toAdd (x σ) * Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F …`. Both sides reduce to the same expression.

Rewrite using `[hfun]`. Conclude with `((hη₂.comp₂ hη₁ (· - ·)).comp₂ (hx_lc.comp (· * Multiplicative.toAdd (y σ))) (· - ·)).comp₂ (hy_lc.comp (Multiplicative.toAdd (x σ) * ·)) (· + ·)`. Establish `hadd : ∀ g ∈ (⊥ : IntermediateField K Ω).fixingSubgroup, ∀ h ∈ (⊥ : IntermediateField K Ω).fixingSubgroup, χ (g * h) = χ g + χ h`. Introduce `g _ h _`. Simplify using `only [χ, map_mul]`.

Conclude with `hhom σ _ (hmem g) _ (hmem h)`. Take `⟨θ, hθ0, hθN, hθ⟩` from `_root_.GlobalTheory.kummer_generator_of_char K Ω N ζ hN hζ (fun g => hfix (AlgEquiv.restrictScalarsHom F g)) ⊥ χ hlc hadd`. Take `⟨w, hw⟩` from `IntermediateField.mem_bot.mp hθN`. Apply `_root_.GlobalTheory.K4.TopW.isTopW_topW_of_exists` to reduce the goal to its premises. Use `⟨w, ?_, θ, hw.symm, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `hw` using `[map_zero]`. Conclude with `hθ0 ((pow_eq_zero_iff hN.ne').mp hw.symm)`. Introduce `g hg`. Take `⟨g', rfl⟩` from `_root_.GlobalTheory.K4.TopSpec.exists_res hg`.

Apply `_root_.GlobalTheory.NeedB.kum_eq_of hζ hθ0` to reduce the goal to its premises. Conclude with `hθ g' (by rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _)`.
-/
theorem _root_.GlobalTheory.K4.isTopW_topW : ∀ (k K Ω F : Type) [Field k]
    [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
    (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K,
      τ x ∈ FunctionField.ringOfIntegers k K) →
    ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      algebraMap F K b ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
    ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)),
      (∀ g, (x g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ α g) →
      (∀ g, (y g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ β g) →
    ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N,
      _root_.GlobalTheory.KEdge.CobOn (_root_.GlobalTheory.K4.geo F K Ω) x y η →
      IsLocallyConstant (fun g : _root_.GlobalTheory.K4.geo F K Ω => η g) →
      (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω),
        _root_.GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) →
        g ∈ _root_.GlobalTheory.K4.geo F K Ω → η g = 0) →
    ∀ σ : Ω ≃ₐ[F] Ω, _root_.GlobalTheory.K4.IsTopW (K := K) ζ x y η σ
      (_root_.GlobalTheory.K4.topW (K := K) ζ x y η σ) := by
  intro k K Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ hfix _ a b α β ha hb _ _ _ _ hα hβ
    x y hx hy η hcob hη _ σ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : CharZero (RatFunc k) :=
    charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F K Ω
  set H := _root_.GlobalTheory.K4.geo F K Ω with hH
  haveI : H.Normal := ⟨fun h hh g => _root_.GlobalTheory.K4.TopW.conj_mem_geo g hh⟩
  obtain ⟨hhom, -, -⟩ := _root_.GlobalTheory.KEdge.edge_cup_props _ N H x y η hcob
  have hres := _root_.GlobalTheory.K4.TopSpec.continuous_res (F := F) (K := K) (Ω := Ω)
  have hmem : ∀ g : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g ∈ H :=
    _root_.GlobalTheory.K4.TopSpec.res_mem_geo
  have hne : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c → γ ≠ 0 := by
    intro γ c hc hγ h0
    rw [h0, zero_pow hN.ne'] at hγ
    exact hc ((algebraMap F Ω).injective (hγ.symm.trans (map_zero _).symm))
  have hkum : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c →
      IsLocallyConstant (_root_.GlobalTheory.NeedB.kum (K := F) (N := N) ζ γ) :=
    fun hc hγ => (_root_.GlobalTheory.NeedB.KumLemma.kummer_character_main F Ω N ζ _ hN hζ hfix
      (hne hc hγ) ⟨_, hγ.symm⟩).1
  have hx_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ α ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hx _
    rw [hfun]
    exact (hkum ha hα).comp_continuous hres
  have hy_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ β ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hy _
    rw [hfun]
    exact (hkum hb hβ).comp_continuous hres
  have hη₁ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (AlgEquiv.restrictScalarsHom F g) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω => (⟨AlgEquiv.restrictScalarsHom F g, hmem g⟩ : H))
      (hres.subtype_mk _)
  have hη₂ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω =>
      (⟨σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹,
        _root_.GlobalTheory.K4.TopW.conj_mem_geo σ (hmem g)⟩ : H))
      (((continuous_const.mul hres).mul continuous_const).subtype_mk _)
  let χ : (Ω ≃ₐ[K] Ω) → ZMod N := fun g =>
    _root_.GlobalTheory.KEdge.edge x y η σ (AlgEquiv.restrictScalarsHom F g)
  have hlc : IsLocallyConstant χ := by
    have hfun : χ = fun g => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) -
        η (AlgEquiv.restrictScalarsHom F g) -
        Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) * Multiplicative.toAdd (y σ) +
        Multiplicative.toAdd (x σ) * Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) :=
      rfl
    rw [hfun]
    exact ((hη₂.comp₂ hη₁ (· - ·)).comp₂ (hx_lc.comp (· * Multiplicative.toAdd (y σ))) (· - ·)).comp₂
      (hy_lc.comp (Multiplicative.toAdd (x σ) * ·)) (· + ·)
  have hadd : ∀ g ∈ (⊥ : IntermediateField K Ω).fixingSubgroup,
      ∀ h ∈ (⊥ : IntermediateField K Ω).fixingSubgroup, χ (g * h) = χ g + χ h := by
    intro g _ h _
    simp only [χ, map_mul]
    exact hhom σ _ (hmem g) _ (hmem h)
  obtain ⟨θ, hθ0, hθN, hθ⟩ :=
    _root_.GlobalTheory.kummer_generator_of_char K Ω N ζ hN hζ (fun g => hfix (AlgEquiv.restrictScalarsHom F g)) ⊥ χ hlc hadd
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hθN
  apply _root_.GlobalTheory.K4.TopW.isTopW_topW_of_exists
  refine ⟨w, ?_, θ, hw.symm, ?_⟩
  · rintro rfl
    rw [map_zero] at hw
    exact hθ0 ((pow_eq_zero_iff hN.ne').mp hw.symm)
  · intro g hg
    obtain ⟨g', rfl⟩ := _root_.GlobalTheory.K4.TopSpec.exists_res hg
    apply _root_.GlobalTheory.NeedB.kum_eq_of hζ hθ0
    exact hθ g' (by rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _)
