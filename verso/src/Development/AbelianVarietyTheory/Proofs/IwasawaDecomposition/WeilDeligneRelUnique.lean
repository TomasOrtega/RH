import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAevalEqSmulOnEigenspace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionElementFrobeniusPowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivialStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjWD

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

/- English proof (translation)
Use `⟨(Dec (F := E) A).mul_mem ((Dec (F := E) A).mul_mem hg hσ.1) ((Dec (F := E) A).inv_mem hg), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hy : A.valuation ((g⁻¹ : G E Ω) x) ≤ 1` using `val_apply_le_one ((Dec (F := E) A).inv_mem hg) hx`. Establish `h1` using `hσ.2 _ hy`. Rewrite `h1` using `[← valuation_apply_lt_one_iff hg, map_sub, map_pow, map_pow, mul_inv_apply]`. Conclude with `h1`.
-/
theorem actsAs_conj {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hg : g ∈ Dec (F := E) A)
    {a b : ℕ} (hσ : ActsAs A q σ a b) : ActsAs A q (g * σ * g⁻¹) a b := by
  refine ⟨(Dec (F := E) A).mul_mem ((Dec (F := E) A).mul_mem hg hσ.1) ((Dec (F := E) A).inv_mem hg),
    fun x hx => ?_⟩
  have hy : A.valuation ((g⁻¹ : G E Ω) x) ≤ 1 := val_apply_le_one ((Dec (F := E) A).inv_mem hg) hx
  have h1 := hσ.2 _ hy
  rw [← valuation_apply_lt_one_iff hg, map_sub, map_pow, map_pow, mul_inv_apply] at h1
  exact h1

end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def conjW (g : G E Ω) (hg : g ∈ Dec (F := E) A) (σ : Weil h) : Weil h :=
  ⟨g * σ * g⁻¹, by obtain ⟨a, b, hab⟩ := σ.2; exact ⟨a, b, actsAs_conj hg hab⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_conjW (g : G E Ω) (hg : g ∈ Dec (F := E) A) (σ : Weil h) :
    (conjW g hg σ : G E Ω) = g * σ * g⁻¹ := rfl

end GlobalTheory.ConjWD

namespace GlobalTheory.ConjWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Take `⟨k, hk⟩` from `GlobalTheory.T.decomposition_element_frobenius_power E Ω A w h L inferInstance g hg`. Use `set φ : Weil h := frob h ^ k`. Establish `hφ : ActsAs A (normV w) (φ : G E Ω) k 0` using `actsAs_of_deg (by simp [φ])`. Establish `hψ : ((φ : G E Ω) * g) ∈ Dec (F` using `E) A := (Dec (F := E) A).mul_mem hφ.1 hg`. Take `⟨ι, hι, hιL⟩` from `GlobalTheory.T.inertia_lift_of_residual_trivial E Ω A w h L _ hψ fun x hx hxi => by`.

Establish `hx1 : A.valuation x ≤ 1` using `(A.valuation_le_one_iff x).mpr (mem_of_isIntegral_int A hxi)`. Establish `hgx : A.valuation (g x) ≤ 1` using `val_apply_le_one hg hx1`. Establish `h1` using `hφ.2 _ hgx`. Simplify using `only [pow_zero, pow_one] at h1`. Conclude with `cong_trans h1 (hk x hx hxi)`.

Use `⟨φ⁻¹ * ineIncl h ⟨ι, hι⟩, fun x hx => ?_⟩` and prove the remaining obligations. Use `show (φ : G E Ω)⁻¹ (ι x) = g x`. Rewrite using `[hιL x hx, AlgEquiv.mul_apply]`. Use `show ((φ : G E Ω)⁻¹ * (φ : G E Ω)) (g x) = g x`. Simplify using the standard rewrite rules.
-/
theorem exists_weil_eq_on {g : G E Ω} (hg : g ∈ Dec (F := E) A) (L : IntermediateField E Ω)
    [FiniteDimensional E L] : ∃ τ : Weil h, ∀ x ∈ L, (τ : G E Ω) x = g x := by
  obtain ⟨k, hk⟩ := GlobalTheory.T.decomposition_element_frobenius_power E Ω A w h L inferInstance g hg
  set φ : Weil h := frob h ^ k
  have hφ : ActsAs A (normV w) (φ : G E Ω) k 0 := actsAs_of_deg (by simp [φ])
  have hψ : ((φ : G E Ω) * g) ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem hφ.1 hg
  obtain ⟨ι, hι, hιL⟩ := GlobalTheory.T.inertia_lift_of_residual_trivial E Ω A w h L _ hψ fun x hx hxi => by
    have hx1 : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr (mem_of_isIntegral_int A hxi)
    have hgx : A.valuation (g x) ≤ 1 := val_apply_le_one hg hx1
    have h1 := hφ.2 _ hgx
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (hk x hx hxi)
  refine ⟨φ⁻¹ * ineIncl h ⟨ι, hι⟩, fun x hx => ?_⟩
  show (φ : G E Ω)⁻¹ (ι x) = g x
  rw [hιL x hx, AlgEquiv.mul_apply]
  show ((φ : G E Ω)⁻¹ * (φ : G E Ω)) (g x) = g x
  simp

end GlobalTheory.ConjWD
