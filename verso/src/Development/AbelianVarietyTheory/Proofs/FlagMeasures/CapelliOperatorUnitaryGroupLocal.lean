import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth

open Matrix Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CapelliLocality

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `h1 : Yᴴ = H * (-Y) * K`. Combine the equalities or inequalities in the displayed calculation. Unfold `inUH`. Rewrite using `[← Matrix.exp_conjTranspose, h1, ioh_exp_conj H K (-Y) hKH hHK]`. Establish `h2 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1`.

Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma exp_inUH (H K Y : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hY : Yᴴ * H = -(H * Y)) : inUH H (NormedSpace.exp Y) := by
  have h1 : Yᴴ = H * (-Y) * K := by
    calc Yᴴ = Yᴴ * H * K := by rw [Matrix.mul_assoc, hHK, Matrix.mul_one]
      _ = H * (-Y) * K := by rw [hY, Matrix.mul_neg]
  unfold inUH
  rw [← Matrix.exp_conjTranspose, h1, ioh_exp_conj H K (-Y) hKH hHK]
  have h2 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  calc H * NormedSpace.exp (-Y) * K * H * NormedSpace.exp Y
      = H * (NormedSpace.exp (-Y) * (K * H) * NormedSpace.exp Y) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hKH, Matrix.mul_one, h2, Matrix.mul_one]

/- English proof (translation)
Unfold `inUH at *`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = H := by rw [ha, hb]`.
-/
lemma inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  unfold inUH at *
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha, hb]

/- English proof (translation)
Unfold `RdV`. Use `congr 1`. Use function extensionality and compare the values at `t`. Use `hF _ (inUH_mul hg (exp_inUH H K _ hKH hHK ?_))` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hX, smul_neg]`.

Simplify using the standard rewrite rules.
-/
lemma rdV_congr (H K X : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hX : Xᴴ * H = -(H * X)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUH H g) :
    RdV X F₁ g = RdV X F₂ g := by
  unfold RdV
  congr 1
  funext t
  refine hF _ (inUH_mul hg (exp_inUH H K _ hKH hHK ?_))
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hX, smul_neg]
  simp

/- English proof (translation)
Establish `hi : (H⁻¹)ᴴ = H⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hH]`. Establish `e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H` using `by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]`. Unfold `hpart1`. Simplify using `only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hi, hH, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hKH, e, Matrix.mul_one]`. Rewrite using `[← smul_neg, neg_sub]`.

Simplify using the standard rewrite rules.
-/
lemma hpart1_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart1 H Z)ᴴ * H = -(H * hpart1 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  unfold hpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [← smul_neg, neg_sub]
  simp

/- English proof (translation)
Establish `hi : (H⁻¹)ᴴ = H⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hH]`. Establish `e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H` using `by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]`. Establish `hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I))`. Simplify using the standard rewrite rules. Unfold `hpart2`.

Simplify using `only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hi, hH, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hKH, e, Matrix.mul_one]`. Rewrite using `[hs, neg_smul, add_comm]`.
-/
lemma hpart2_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart2 H Z)ᴴ * H = -(H * hpart2 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  unfold hpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [hs, neg_smul, add_comm]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using hF`. Consider the case `cons p l ih`. Introduce `x hx`. Simplify using `only [List.map_cons, List.foldr_cons]`.

Generalize the expression as in `(l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ = G₁ at ih ⊢`. Generalize the expression as in `(l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ = G₂ at ih ⊢`. Unfold `Formalism.QuantumDeterminants.Top EabH`. Rewrite using `[ih x hx, rdV_congr H H⁻¹ _ hKH hHK (hpart1_mem H _ hKH hHK hH) ih hx, rdV_congr H H⁻¹ _ hKH hHK (hpart2_mem H _ hKH hHK hH) ih hx]`.
-/
lemma foldr_congr (H : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) (l : List (ℂ × Fin n × Fin n)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) :
    ∀ x, inUH H x →
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ x =
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ x := by
  induction l with
  | nil => simpa using hF
  | cons p l ih =>
    intro x hx
    simp only [List.map_cons, List.foldr_cons]
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ = G₁ at ih ⊢
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ = G₂ at ih ⊢
    unfold Formalism.QuantumDeterminants.Top EabH
    rw [ih x hx, rdV_congr H H⁻¹ _ hKH hHK (hpart1_mem H _ hKH hHK hH) ih hx,
      rdV_congr H H⁻¹ _ hKH hHK (hpart2_mem H _ hKH hHK hH) ih hx]

/- English proof (translation)
Introduce `n ε E _ _ H P Q F₁ F₂ u g hQP hPQ hH hF hg`. Establish `hinv` using `ioh_Hinv ε H P Q hQP hPQ hH`. Establish `hc : Pᴴ * Qᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one]`. Establish `hHK : H * H⁻¹ = 1`. Rewrite using `[hinv]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hH]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Pᴴ * Qᴴ := by`. Rewrite using `[hPQ, Matrix.one_mul, ← Matrix.mul_assoc (Jm ε), Jm_mul_self, Matrix.one_mul]`.

Use `_ = 1 := hc`. Establish `hKH : H⁻¹ * H = 1` using `mul_eq_one_comm.mp hHK`. Establish `hJ : (Jm ε)ᴴ = Jm ε`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : ε i <;> simp [h]`. Establish `hHh : Hᴴ = H`. Rewrite using `[hH]`.

Simplify using `only [Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Unfold `capelliH qdetOp qminorOp`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `e1 : (List.ofFn fun k : Fin n => Formalism.QuantumDeterminants.Top (E` using `E) (EabH H) (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)) = (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), σ k, k)).map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2 := by`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `foldr_congr H hKH hHK hHh _ hF g hg`.
-/
theorem capelliH_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  intro n ε E _ _ H P Q F₁ F₂ u g hQP hPQ hH hF hg
  have hinv := ioh_Hinv ε H P Q hQP hPQ hH
  have hc : Pᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one]
  have hHK : H * H⁻¹ = 1 := by
    rw [hinv]
    calc H * (Q * Jm ε * Qᴴ) = Pᴴ * (Jm ε * ((P * Q) * (Jm ε * Qᴴ))) := by
          rw [hH]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * Qᴴ := by
          rw [hPQ, Matrix.one_mul, ← Matrix.mul_assoc (Jm ε), Jm_mul_self, Matrix.one_mul]
      _ = 1 := hc
  have hKH : H⁻¹ * H = 1 := mul_eq_one_comm.mp hHK
  have hJ : (Jm ε)ᴴ = Jm ε := by
    unfold Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : ε i <;> simp [h]
  have hHh : Hᴴ = H := by
    rw [hH]
    simp only [Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold capelliH qdetOp qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : (List.ofFn fun k : Fin n => Formalism.QuantumDeterminants.Top (E := E) (EabH H) (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)) =
        (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), σ k, k)).map
          fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2 := by
    rw [List.map_ofFn]; rfl
  rw [e1]
  exact foldr_congr H hKH hHK hHh _ hF g hg

end GlobalTheory.CapelliLocality

end
