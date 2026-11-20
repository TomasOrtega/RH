import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord.Pair

/- English proof (translation)
Establish `h1 : ∀ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * (X i k * Y i m)` using `fun i => by`. Rewrite using `[Finset.sum_mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring`. Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.mul_sum]`.
-/
theorem sum_bilin {R : Type*} [CommRing R] {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (F : κ → R) (G : μ → R) (X : ι → κ → R) (Y : ι → μ → R) :
    ∑ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * ∑ i, X i k * Y i m := by
  have h1 : ∀ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * (X i k * Y i m) := fun i => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end GlobalTheory.KerStd.HypCoord.Pair

open GlobalTheory.KerStd.HypCoord.Pair in

/- English proof (translation)
Introduce `D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hL w z a b₀ a₁ b₁`. Establish `hunit : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E) (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), StdBases D lam L₀ Q → ∀ v, IsUnit ((Q (tauPl D v)).map (rhoK D lam v)).det`. Introduce `n Q L₀ hQ v`. Take `⟨ρ, hρ⟩` from `exists_ringHom_rhoK D lam σ hσ hcl v`. Establish `hf : rhoK D lam v = ⇑ρ` using `funext fun y => (hρ y).1`.

Establish `h1` using `hQ.2.1 hcl v`. Establish `hdet : IsUnit (Q (tauPl D v)).det` using `Matrix.isUnit_det_of_left_inverse h1`. Rewrite using `[hf, show ((Q (tauPl D v)).map ⇑ρ).det = ρ (Q (tauPl D v)).det from (RingHom.map_det ρ _).symm]`. Conclude with `hdet.map ρ`. Establish `hker : ∀ (k m : Fin N' × Fin N), ∑ i, rhoK D lam w (b i k.1 k.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) = if (tauPl D w, k.1, k.2) = (tauPl D z, m.1, m.2) then 1 else 0`.

Introduce `k m`. Establish `e` using `hL (tauPl D w, k.1, k.2) (tauPl D z, m.1, m.2)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubmonoidClass.coe_finsetSum]`. Simplify using `only [MulMemClass.coe_mul, coe_rhoK D lam σ hσ hcl]`.

Apply the tactic sequence `convert e using 1 <;> first | rfl | (split_ifs <;> simp)`. Use `set A := ((P' (tauPl D w)).map (rhoK D lam w))⁻¹ with hA`. Use `set B := ((P (tauPl D z)).map (rhoK D lam z))⁻¹ with hB`. Establish `eh : ∀ i, hK D lam P P' b w a b₀ i = ∑ k : Fin N' × Fin N, (A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a)) * rhoK D lam w (b i k.1 k.2)` using `fun i => by`. Rewrite using `[hK, Fintype.sum_prod_type]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Establish `eg : ∀ i, gK D lam P P' b z a₁ b₁ i = ∑ m : Fin N' × Fin N, (rhoK D lam z (P' (tauPl D z) m.1 b₁) * B a₁ m.2) * rhoK D lam z (D.host.conj (b i m.1 m.2))` using `fun i => by`. Rewrite using `[gK, Fintype.sum_prod_type]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `only [eh, eg]`.

Rewrite using `[sum_bilin]`. Simplify using `only [hker]`. Distinguish the cases in `hwz : w = z`. Substitute `hwz` using the available equality. Establish `hsimp : ∀ k m : Fin N' × Fin N, ((tauPl D w, k.1, k.2) = (tauPl D w, m.1, m.2)) ↔ k = m`.

Introduce `k m`. Simplify using `[Prod.ext_iff]`. Simplify using `only [hsimp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `e1 : ∑ k : Fin N' × Fin N, A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a) * (rhoK D lam w (P' (tauPl D w) k.1 b₁) * B a₁ k.2) = (A * (P' (tauPl D w)).map (rhoK D lam w)) b₀ b₁ * (B * (P (tauPl D w)).map (rhoK D lam w)) a₁ a`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp only [Matrix.map_apply]; ring`. Rewrite using `[e1, hA, hB, Matrix.nonsing_inv_mul _ (hunit P' L' hP' w), Matrix.nonsing_inv_mul _ (hunit P L hP w), Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `by_cases h1 : b₀ = b₁ <;> by_cases h2 : a = a₁ <;> simp [h1, h2, eq_comm]`. Establish `hne : tauPl D w ≠ tauPl D z` using `fun h => hwz ((tauPl_bij D).1 h)`. Rewrite using `[if_neg (fun h => hwz h.1)]`.

Use `Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (fun h => hne (congrArg Prod.fst h)), mul_zero]`.
-/
theorem GlobalTheory.KerStd.HypCoord.hK_gK_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ w z a b₀ a₁ b₁, ∑ i, hK D lam P P' b w a b₀ i * gK D lam P P' b z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b₀ = b₁ then 1 else 0 := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hL w z a b₀ a₁ b₁

  have hunit : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E) (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      StdBases D lam L₀ Q → ∀ v, IsUnit ((Q (tauPl D v)).map (rhoK D lam v)).det := by
    intro n Q L₀ hQ v
    obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl v
    have hf : rhoK D lam v = ⇑ρ := funext fun y => (hρ y).1
    have h1 := hQ.2.1 hcl v
    have hdet : IsUnit (Q (tauPl D v)).det :=
      Matrix.isUnit_det_of_left_inverse h1
    rw [hf, show ((Q (tauPl D v)).map ⇑ρ).det = ρ (Q (tauPl D v)).det from (RingHom.map_det ρ _).symm]
    exact hdet.map ρ

  have hker : ∀ (k m : Fin N' × Fin N), ∑ i, rhoK D lam w (b i k.1 k.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) =
      if (tauPl D w, k.1, k.2) = (tauPl D z, m.1, m.2) then 1 else 0 := by
    intro k m
    have e := hL (tauPl D w, k.1, k.2) (tauPl D z, m.1, m.2)
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul, coe_rhoK D lam σ hσ hcl]
    convert e using 1 <;> first | rfl | (split_ifs <;> simp)
  set A := ((P' (tauPl D w)).map (rhoK D lam w))⁻¹ with hA
  set B := ((P (tauPl D z)).map (rhoK D lam z))⁻¹ with hB
  have eh : ∀ i, hK D lam P P' b w a b₀ i =
      ∑ k : Fin N' × Fin N, (A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a)) * rhoK D lam w (b i k.1 k.2) := fun i => by
    rw [hK, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have eg : ∀ i, gK D lam P P' b z a₁ b₁ i =
      ∑ m : Fin N' × Fin N, (rhoK D lam z (P' (tauPl D z) m.1 b₁) * B a₁ m.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) := fun i => by
    rw [gK, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [eh, eg]
  rw [sum_bilin]
  simp only [hker]
  by_cases hwz : w = z
  · subst hwz
    have hsimp : ∀ k m : Fin N' × Fin N, ((tauPl D w, k.1, k.2) = (tauPl D w, m.1, m.2)) ↔ k = m := by
      intro k m
      simp [Prod.ext_iff]
    simp only [hsimp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : ∑ k : Fin N' × Fin N, A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a) *
        (rhoK D lam w (P' (tauPl D w) k.1 b₁) * B a₁ k.2) =
        (A * (P' (tauPl D w)).map (rhoK D lam w)) b₀ b₁ * (B * (P (tauPl D w)).map (rhoK D lam w)) a₁ a := by
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp only [Matrix.map_apply]; ring
    rw [e1, hA, hB, Matrix.nonsing_inv_mul _ (hunit P' L' hP' w), Matrix.nonsing_inv_mul _ (hunit P L hP w),
      Matrix.one_apply, Matrix.one_apply]
    by_cases h1 : b₀ = b₁ <;> by_cases h2 : a = a₁ <;> simp [h1, h2, eq_comm]
  · have hne : tauPl D w ≠ tauPl D z := fun h => hwz ((tauPl_bij D).1 h)
    rw [if_neg (fun h => hwz h.1)]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg (fun h => hne (congrArg Prod.fst h)), mul_zero]
