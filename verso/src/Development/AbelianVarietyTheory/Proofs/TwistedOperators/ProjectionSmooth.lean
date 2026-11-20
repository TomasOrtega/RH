import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SepReal.ProjSm

variable {m : ℕ}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_iff (ε : Fin m → Bool) (g : Mat m) : g ∈ UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

/- English proof (translation)
Rewrite `*` using `[mem_iff]`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mem' {ε : Fin m → Bool} {g h : Mat m} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  rw [mem_iff] at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

/- English proof (translation)
Rewrite using `[mem_iff]`. Simplify using the standard rewrite rules.
-/
theorem one_mem' (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := by
  rw [mem_iff]; simp

/- English proof (translation)
Establish `JJ` using `Formalism.REAL.Jm_mul_self ε`. Establish `hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0` using `hX`. Use `set Y : Mat m := t • X with hY`. Establish `hYh : Yᴴ = Formalism.REAL.Jm ε * (-Y) * Formalism.REAL.Jm ε`. Establish `: Xᴴ = -(Formalism.REAL.Jm ε * X) * Formalism.REAL.Jm ε`.

Establish `h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X)` using `eq_neg_of_add_eq_zero_left hX'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hY, Matrix.conjTranspose_smul, this]`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg]`. Establish `hc : NormedSpace.exp Yᴴ = Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε`.

Establish `hJi : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε` using `Matrix.inv_eq_left_inv JJ`. Use `Matrix.exp_conj (Formalism.REAL.Jm ε) (-Y) ⟨⟨_, _, JJ, JJ⟩, rfl⟩` as an intermediate fact. Rewrite `this` using `[hJi]`. Rewrite using `[hYh, this]`. Rewrite using `[mem_iff, ← Matrix.exp_conjTranspose, hc]`.

Establish `he : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [JJ, Matrix.mul_one, he, Matrix.mul_one]`.
-/
theorem exp_mem {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ lieOf (Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have JJ := Formalism.REAL.Jm_mul_self ε
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  set Y : Mat m := t • X with hY
  have hYh : Yᴴ = Formalism.REAL.Jm ε * (-Y) * Formalism.REAL.Jm ε := by
    have : Xᴴ = -(Formalism.REAL.Jm ε * X) * Formalism.REAL.Jm ε := by
      have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
      calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, JJ, Matrix.mul_one]
        _ = _ := by rw [h1]
    rw [hY, Matrix.conjTranspose_smul, this]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg]
  have hc : NormedSpace.exp Yᴴ = Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε := by
    have hJi : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv JJ
    have := Matrix.exp_conj (Formalism.REAL.Jm ε) (-Y) ⟨⟨_, _, JJ, JJ⟩, rfl⟩
    rw [hJi] at this
    rw [hYh, this]
  rw [mem_iff, ← Matrix.exp_conjTranspose, hc]
  have he : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp Y
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-Y) * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * NormedSpace.exp Y) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [JJ, Matrix.mul_one, he, Matrix.mul_one]

/- English proof (translation)
The claim follows from `| [], _ => by simpa using one_mem' ε | a :: l, h => by rw [List.prod_cons] exact mul_mem' (h a (by simp)) (list_mem l fun x hx => h x (by simp [hx]))`.
-/
theorem list_mem {m : ℕ} {ε : Fin m → Bool} : ∀ l : List (Mat m), (∀ x ∈ l, x ∈ UJset ε) → l.prod ∈ UJset ε
  | [], _ => by simpa using one_mem' ε
  | a :: l, h => by
    rw [List.prod_cons]
    exact mul_mem' (h a (by simp)) (list_mem l fun x hx => h x (by simp [hx]))

/- English proof (translation)
The claim follows from `| [] => by simp [embH_one] | a :: l => by rw [List.prod_cons, embH_mul, embH_list e l, List.map_cons, List.prod_cons]`.
-/
theorem embH_list {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) : ∀ l : List (Mat n), embH e l.prod = (l.map (embH e)).prod
  | [] => by simp [embH_one]
  | a :: l => by rw [List.prod_cons, embH_mul, embH_list e l, List.map_cons, List.prod_cons]

variable {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}
  {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {π : Mat (n + 1) → (H →L[ℂ] H)} {σ : Mat n → (H' →L[ℂ] H')} {j : H' →L[ℂ] H} {P : H →L[ℂ] H'}

end GlobalTheory.SepReal.ProjSm
