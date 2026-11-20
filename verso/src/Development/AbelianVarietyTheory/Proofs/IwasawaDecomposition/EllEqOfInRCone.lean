import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

/- English proof (translation)
Take `⟨c, hc, hsum⟩` from `hβ`. Establish `h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i • toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X) ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0`. Simplify using `[Fin.sum_univ_succ, hsum]`. Establish `h2` using `sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1`. Simplify using `only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2`.

Establish `h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i)`. Rewrite using `[← evalR_toReal, hsum]`. Conclude with `(linearOn_iff φ γ).1 hlin c hc`. Establish `h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i)` using `by simp at h2; linarith`. Rewrite using `[h4, h3, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [hsw.1 i]; ring`.
-/
theorem ell_eq_of_inRCone {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hlin : φ.LinearOn γ) (hsw : StrictWith bar φ N ℓ γ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hsw.1 i]; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨![3], fun i => by fin_cases i; norm_num, LinearMap.ext₂ fun a b => by simp⟩`.
-/
example : InRCone ![mulForm] ((3 : ℤ) • mulForm) :=
  ⟨![3], fun i => by fin_cases i; norm_num, LinearMap.ext₂ fun a b => by simp⟩

end GlobalTheory.PolFan.StarKey
