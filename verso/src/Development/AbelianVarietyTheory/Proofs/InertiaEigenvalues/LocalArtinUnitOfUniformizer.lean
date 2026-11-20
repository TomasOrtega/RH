import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeTate

/- English proof (translation)
Set `f : kˣ →* Multiplicative ℤ` to `{ toFun := fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord k y) map_one' := by rw [GlobalTheory.SmGL.ord_eq_zero (by simp)]; rfl map_mul' := fun y z => by rw [GlobalTheory.SmGL.ord_mul]; rfl }`. Use `congrArg Multiplicative.toAdd (map_zpow f x n)` as an intermediate fact. Simplify `this` using `[f]`.
-/
theorem ord_zpow_units {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) (n : ℤ) : GlobalTheory.SmGL.ord k (x ^ n) = n * GlobalTheory.SmGL.ord k x := by
  let f : kˣ →* Multiplicative ℤ :=
    { toFun := fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord k y)
      map_one' := by rw [GlobalTheory.SmGL.ord_eq_zero (by simp)]; rfl
      map_mul' := fun y z => by rw [GlobalTheory.SmGL.ord_mul]; rfl }
  have := congrArg Multiplicative.toAdd (map_zpow f x n)
  simpa [f] using this

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h a ha σ π u hπ hu`. Use `set K := w.adicCompletion E`. Establish `hint` using `Valuation.integer.integers (valuation K)`. Establish `hπ0 : (π : K) ≠ 0` using `fun h0 => hπ.ne_zero (Subtype.ext h0)`. Establish `hπle : valuation K (π : K) ≤ 1` using `π.2`.

Establish `hπlt : valuation K (π : K) < 1`. Use `hπ.not_isUnit` as an intermediate fact. Rewrite `this` using `[hint.isUnit_iff_valuation_eq_one]`. Conclude with `lt_of_le_of_ne hπle this`. Take `⟨ϖ, hϖ⟩` from `GlobalTheory.Published.JacquetShalikaLocalBound.exists_uniformizer K`.

Establish `hπv : valuation K (π : K) = uniformizer K`. Apply `le_antisymm (le_uniformizer_iff.2 hπlt)` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hϖ0 : (ϖ : K) ≠ 0` using `ϖ.ne_zero`.

Establish `hpos : (0 : ValueGroupWithZero K) < valuation K (ϖ : K)`. Rewrite using `[hϖ]`. Conclude with `zero_lt_iff.2 uniformizer_ne_zero`. Establish `hq : valuation K ((π : K) * (ϖ : K)⁻¹) < 1`. Rewrite using `[map_mul, map_inv₀]`.

Conclude with `(mul_inv_lt_iff₀ hpos).2 (by rw [one_mul, hϖ]; exact hlt)`. Set `x : 𝒪[K]` to `⟨ϖ, by show valuation K (ϖ : K) ≤ 1; rw [hϖ]; exact uniformizer_lt_one.le⟩`. Set `y : 𝒪[K]` to `⟨(π : K) * (ϖ : K)⁻¹, hq.le⟩`. Establish `hxy : π = x * y` using `Subtype.ext (by show (π : K) = (ϖ : K) * ((π : K) * (ϖ : K)⁻¹) field_simp)`. Break down `hπ.isUnit_or_isUnit hxy with hx | hy` into its components or cases.

Rewrite `hx` using `[hint.isUnit_iff_valuation_eq_one]`. Conclude with `uniformizer_lt_one.ne (hϖ ▸ hx)`. Rewrite `hy` using `[hint.isUnit_iff_valuation_eq_one]`. Conclude with `hq.ne hy`. Set `p : Kˣ` to `Units.mk0 _ hπ0`.

Establish `hp1 : GlobalTheory.SmGL.ord K p = 1` using `GlobalTheory.SmGL.ord_eq_one hπv`. Establish `hd` using `ha.ord_eq σ`. Establish `hz : GlobalTheory.SmGL.ord K (a σ * p ^ deg σ) = 0`. Rewrite using `[GlobalTheory.SmGL.ord_mul, ord_zpow_units, hd, hp1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hv` using `GlobalTheory.SmGL.ord_eq_zero_iff.1 hz`. Rewrite using `[hint.isUnit_iff_valuation_eq_one]`. Use `show valuation K (u : K) = 1`. Rewrite using `[hu]`. Simplify `hv` using `[p, Units.val_zpow_eq_zpow_val]`.
-/
theorem isUnit_artin_mul_zpow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (σ : Weil h) (π u : 𝒪[w.adicCompletion E]),
    Irreducible π → (u : w.adicCompletion E) = (a σ : w.adicCompletion E) * (π : w.adicCompletion E) ^ deg σ →
    IsUnit u := by
  intro E Ω _ _ _ _ _ A w h a ha σ π u hπ hu
  set K := w.adicCompletion E
  have hint := Valuation.integer.integers (valuation K)
  have hπ0 : (π : K) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  have hπle : valuation K (π : K) ≤ 1 := π.2
  have hπlt : valuation K (π : K) < 1 := by
    have := hπ.not_isUnit
    rw [hint.isUnit_iff_valuation_eq_one] at this
    exact lt_of_le_of_ne hπle this
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.Published.JacquetShalikaLocalBound.exists_uniformizer K
  have hπv : valuation K (π : K) = uniformizer K := by
    apply le_antisymm (le_uniformizer_iff.2 hπlt)
    by_contra hlt
    push_neg at hlt
    have hϖ0 : (ϖ : K) ≠ 0 := ϖ.ne_zero
    have hpos : (0 : ValueGroupWithZero K) < valuation K (ϖ : K) := by
      rw [hϖ]; exact zero_lt_iff.2 uniformizer_ne_zero
    have hq : valuation K ((π : K) * (ϖ : K)⁻¹) < 1 := by
      rw [map_mul, map_inv₀]
      exact (mul_inv_lt_iff₀ hpos).2 (by rw [one_mul, hϖ]; exact hlt)
    let x : 𝒪[K] := ⟨ϖ, by show valuation K (ϖ : K) ≤ 1; rw [hϖ]; exact uniformizer_lt_one.le⟩
    let y : 𝒪[K] := ⟨(π : K) * (ϖ : K)⁻¹, hq.le⟩
    have hxy : π = x * y := Subtype.ext (by
      show (π : K) = (ϖ : K) * ((π : K) * (ϖ : K)⁻¹)
      field_simp)
    rcases hπ.isUnit_or_isUnit hxy with hx | hy
    · rw [hint.isUnit_iff_valuation_eq_one] at hx
      exact uniformizer_lt_one.ne (hϖ ▸ hx)
    · rw [hint.isUnit_iff_valuation_eq_one] at hy
      exact hq.ne hy
  let p : Kˣ := Units.mk0 _ hπ0
  have hp1 : GlobalTheory.SmGL.ord K p = 1 := GlobalTheory.SmGL.ord_eq_one hπv
  have hd := ha.ord_eq σ
  have hz : GlobalTheory.SmGL.ord K (a σ * p ^ deg σ) = 0 := by
    rw [GlobalTheory.SmGL.ord_mul, ord_zpow_units, hd, hp1]; ring
  have hv := GlobalTheory.SmGL.ord_eq_zero_iff.1 hz
  rw [hint.isUnit_iff_valuation_eq_one]
  show valuation K (u : K) = 1
  rw [hu]
  simpa [p, Units.val_zpow_eq_zpow_val] using hv

end GlobalTheory.HeckeTate
