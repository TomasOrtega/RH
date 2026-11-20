import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₄

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def DDsp {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => σ g w0) '' UH (Hpk k r))

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨g, hg, rfl⟩`.
-/
theorem mem_DDsp {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : σ g w0 ∈ DDsp σ w0 :=
  Submodule.subset_span ⟨g, hg, rfl⟩

def DoubleCosetSpanBesselBound {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∃ l : H → Wp, IsBesselMapSm z (psi k r z c) σ π l ∧
    (∀ u ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0,
      Integrable (fun p : Mt k r × Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹)
        (μW.prod μN) ∧
      ∫ p : Mt k r × Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
        ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l u)) ∧
    ∀ u ∈ DDsp σ w0, u ≠ 0 → ∀ v ∈ DDsp σ w0,
      ENNReal.ofReal (‖l v‖ ^ 2) * l2SG νq (fun g => l (σ g u)) =
        ENNReal.ofReal (‖u‖ ^ 2 * ‖l v‖ ^ 2 / fdegH μG σ u)

def DoubleCosetBesselBound (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      DoubleCosetSpanBesselBound L.z L.c L.π L.μW L.μN μG νq σ w0 ∧ DoubleCosetSpanBesselBound L.z' L.c L.π' L.μW' L.μN μG νq' σ w0

def ExtSm (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      (DoubleCosetSpanBesselBound L.z L.c L.π L.μW L.μN μG νq σ w0 → atFormAtPoint L.z L.c L.π L.μW L.μN μG νq σ) ∧
      (DoubleCosetSpanBesselBound L.z' L.c L.π' L.μW' L.μN μG νq' σ w0 → atFormAtPoint L.z' L.c L.π' L.μW' L.μN μG νq' σ)

/- English proof (translation)
Take `⟨P, hP, hDS⟩` from `hσ`. Take `⟨S, hS⟩` from `hDS.2.2.2.2.2.1`. Take `⟨v, hvS, hv0, -⟩` from `hS.2.2.2.1`. Use `⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, P, hP, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]`.

Conclude with `inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)`. Conclude with `(le_sSup (show S ∈ {S | IsKTypeOf ε _ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS)) (S.smul_mem _ hvS)`.
-/
theorem lowUnitH_exists {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : IsDSHpk k r ε lam σ) : ∃ w0 : H, IsLowUnitH k r ε lam σ w0 := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, P, hP, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  · exact (le_sSup (show S ∈ {S | IsKTypeOf ε _ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS)) (S.smul_mem _ hvS)

/- English proof (translation)
Introduce `L lam0 μ ka b κ H _ _ _ σ μG νq νq' hN hσ hG hq hq'`. Take `⟨w0, hw0⟩` from `lowUnitH_exists hσ`. Establish `h1` using `hDD L lam0 μ ka b κ H σ μG νq νq' w0 hN hσ hw0 hG hq hq'`. Establish `h2` using `hE L lam0 μ ka b κ H σ μG νq νq' w0 hN hσ hw0 hG hq hq'`. Conclude with `⟨h2.1 h1.1, h2.2 h1.2⟩`.
-/
theorem bessel_bound_of_double_coset (D : D7) (Ch Cg Cq : ℝ) (hDD : DoubleCosetBesselBound D Ch Cg Cq) (hE : ExtSm D Ch Cg Cq) :
    adm22 D Ch Cg Cq := by
  intro L lam0 μ ka b κ H _ _ _ σ μG νq νq' hN hσ hG hq hq'
  obtain ⟨w0, hw0⟩ := lowUnitH_exists hσ
  have h1 := hDD L lam0 μ ka b κ H σ μG νq νq' w0 hN hσ hw0 hG hq hq'
  have h2 := hE L lam0 μ ka b κ H σ μG νq νq' w0 hN hσ hw0 hG hq hq'
  exact ⟨h2.1 h1.1, h2.2 h1.2⟩

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyDoubleCosetBesselBound (Ch Cg Cq : ℝ) : Prop := ∀ x (i : Fm.Ix x), DoubleCosetBesselBound (Fm.D x i) Ch Cg Cq

def ExtSmF (Ch Cg Cq : ℝ) : Prop := ∀ x (i : Fm.Ix x), ExtSm (Fm.D x i) Ch Cg Cq

/- English proof (translation)
Introduce `Cg hCg x i` and use `bessel_bound_of_double_coset _ _ _ _ (hDD Cg hCg x i) (hE Cg hCg x i)`.
-/
theorem bessel_bound_family_of_double_coset (Ch Cg0 Cq : ℝ) (hDD : ∀ Cg ≥ Cg0, FamilyDoubleCosetBesselBound Fm Ch Cg Cq) (hE : ∀ Cg ≥ Cg0, ExtSmF Fm Ch Cg Cq) :
    ∀ Cg ≥ Cg0, ∀ x (i : Fm.Ix x), adm22 (Fm.D x i) Ch Cg Cq :=
  fun Cg hCg x i => bessel_bound_of_double_coset _ _ _ _ (hDD Cg hCg x i) (hE Cg hCg x i)

end Family

end Formalism.MainNotions.BridgeLemma₄
