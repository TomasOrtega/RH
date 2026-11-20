import Formalism.PeriodIntegrals.SymDist
import Formalism.PeriodIntegrals.ExpTri
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds

open Matrix

noncomputable section

namespace PI.SymDistWork

open Formalism.REAL

variable {n : ℕ}

/- English proof (translation)
Conclude with `⟨Matrix.mem_unitaryGroup_iff'.mp hk.1, Matrix.mem_unitaryGroup_iff.mp hk.1⟩`.
-/
lemma kset_inv {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * k = 1 ∧ k * kᴴ = 1 := by
  exact ⟨Matrix.mem_unitaryGroup_iff'.mp hk.1, Matrix.mem_unitaryGroup_iff.mp hk.1⟩

/- English proof (translation)
Establish `hJ : (Jm ε)ᴴ = Jm ε`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `by_cases hεa : ε a = true <;> simp [hεa]`. Establish `h2` using `congrArg Matrix.conjTranspose hk.2`. Simplify using `only [Matrix.conjTranspose_mul, hJ] at h2`. Conclude with `⟨Unitary.star_mem hk.1, h2.symm⟩`.
-/
lemma kset_ct {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  have hJ : (Jm ε)ᴴ = Jm ε := by
    unfold Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases hεa : ε a = true <;> simp [hεa]
  have h2 := congrArg Matrix.conjTranspose hk.2
  simp only [Matrix.conjTranspose_mul, hJ] at h2
  exact ⟨Unitary.star_mem hk.1, h2.symm⟩

/- English proof (translation)
Unfold `PI.symD`. Establish `hset : {t | ∃ k' X' : Matrix (Fin n) (Fin n) ℂ, k' ∈ Kset ε ∧ inP ε X' ∧ ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k' * NormedSpace.exp X' ∧ t = Real.sqrt (hs X')} = {Real.sqrt (hs X)}`. Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k', X', hk', hX', hg', rfl⟩`. Use `polar_decomposition_unique k' k X' X hk' hk hX' hX (hg'.symm.trans hg)` as an intermediate fact. Rewrite using `[this.2]`. Introduce and unpack `rfl`. Conclude with `⟨k, X, hk, hX, hg, rfl⟩`.

Rewrite using `[hset]`. Conclude with `csInf_singleton _`.
-/
lemma symD_eq {ε : Fin n → Bool} (g : UJ ε) {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hX : inP ε X)
    (hg : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X) :
    PI.symD ε g = Real.sqrt (hs X) := by
  unfold PI.symD
  have hset : {t | ∃ k' X' : Matrix (Fin n) (Fin n) ℂ, k' ∈ Kset ε ∧ inP ε X' ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k' * NormedSpace.exp X' ∧
      t = Real.sqrt (hs X')} = {Real.sqrt (hs X)} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k', X', hk', hX', hg', rfl⟩
      have := polar_decomposition_unique k' k X' X hk' hk hX' hX (hg'.symm.trans hg)
      rw [this.2]
    · rintro rfl
      exact ⟨k, X, hk, hX, hg, rfl⟩
  rw [hset]
  exact csInf_singleton _

/- English proof (translation)
Conclude with `g.2`.
-/
lemma inUJ_coe {ε : Fin n → Bool} (g : UJ ε) :
    inUJ ε ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  exact g.2

/- English proof (translation)
Introduce `n ε g h`. Establish `hpol : ∀ x : UJ ε, ∃ k X, k ∈ Kset ε ∧ inP ε X ∧ ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X`. Introduce `x`. Use `⟨((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (-polarLog ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)), polarLog _, mul_exp_neg_polarLog_mem_compact (inUJ_coe x), polarLog_mem_hermitian_part (inUJ_coe x), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, matrix_exp_neg_mul_exp, Matrix.mul_one]`.

Establish `hUJmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, inUJ ε A → inUJ ε B → inUJ ε (A * B)`. Introduce `A B hA hB`. Unfold `inUJ at *`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hUJk : ∀ k, k ∈ Kset ε → inUJ ε k`. Introduce `k hk`. Unfold `inUJ`. Rewrite using `[Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, (kset_inv hk).1, Matrix.one_mul]`. Establish `hKmul : ∀ a b, a ∈ Kset ε → b ∈ Kset ε → a * b ∈ Kset ε`.

Introduce `a b ha hb`. Use `⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]`. Establish `hcancel : ∀ k, k ∈ Kset ε → ∀ X : Matrix (Fin n) (Fin n) ℂ, kᴴ * (k * X) = X`. Introduce `k hk X`.

Rewrite using `[← Matrix.mul_assoc, (kset_inv hk).1, Matrix.one_mul]`. Take `⟨k1, X1, hk1, hX1, hg1⟩` from `hpol g`. Take `⟨k2, X2, hk2, hX2, hh1⟩` from `hpol h`. Take `⟨hk2a, hk2b⟩` from `kset_inv hk2`. Set `u2 : (Matrix (Fin n) (Fin n) ℂ)ˣ` to `⟨k2, k2ᴴ, hk2b, hk2a⟩`.

Establish `hexpc : NormedSpace.exp (k2ᴴ * X1 * k2) = k2ᴴ * NormedSpace.exp X1 * k2` using `Matrix.exp_units_conj' u2 X1`. Establish `hconj : NormedSpace.exp X1 * k2 = k2 * NormedSpace.exp (k2ᴴ * X1 * k2)`. Rewrite using `[hexpc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hk2b, Matrix.one_mul]`. Establish `hgh : (((g * h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = (k1 * k2) * (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2)`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, hg1, hh1]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hM : inUJ ε (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2)`. Establish `e : NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 = (k2ᴴ * k1ᴴ) * (((g * h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[hgh]`. Simplify using `only [Matrix.mul_assoc, hcancel _ hk1, hcancel _ hk2]`.

Rewrite using `[e]`. Conclude with `hUJmul _ _ (hUJmul _ _ (hUJk _ (kset_ct hk2)) (hUJk _ (kset_ct hk1))) (inUJ_coe _)`. Establish `hk3` using `mul_exp_neg_polarLog_mem_compact hM`. Establish `hX3` using `polarLog_mem_hermitian_part hM`. Establish `hM3 : NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 = (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 * NormedSpace.exp (-polarLog (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2))) * NormedSpace.exp (polarLog (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp …`.

Rewrite using `[Matrix.mul_assoc _ (NormedSpace.exp (-_)), matrix_exp_neg_mul_exp, Matrix.mul_one]`. Establish `hYh : (k2ᴴ * X1 * k2)ᴴ = k2ᴴ * X1 * k2`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hermitian_of_mem_hermitian_part hX1, Matrix.mul_assoc]`. Establish `htri` using `hE n (k2ᴴ * X1 * k2) X2 _ _ hYh (hermitian_of_mem_hermitian_part hX2) (hermitian_of_mem_hermitian_part hX3) hk3.1 hM3`. Establish `hsY : hs (k2ᴴ * X1 * k2) = hs X1`.

Rewrite using `[((hermitian_small_ball n ε).2 (k2ᴴ * X1) k2 hk2).1, ((hermitian_small_ball n ε).2 X1 k2ᴴ (kset_ct hk2)).2]`. Establish `hd1` using `symD_eq g hk1 hX1 hg1`. Establish `hd2` using `symD_eq h hk2 hX2 hh1`. Establish `hd3` using `symD_eq (g * h) (hKmul _ _ (hKmul _ _ hk1 hk2) hk3) hX3 (by`. Rewrite using `[hgh, Matrix.mul_assoc (k1 * k2), Matrix.mul_assoc (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2), matrix_exp_neg_mul_exp, Matrix.mul_one])`.

Rewrite using `[hd1, hd2, hd3]`. Establish `e2 : Real.sqrt (hs (k2ᴴ * X1 * k2)) = Real.sqrt (hs X1)` using `by rw [hsY]`. Rewrite using `[← e2]`. Conclude with `htri`.
-/
theorem symDist_of (hE : PI.ExpTri) : PI.SymDist := by
  intro n ε g h
  have hpol : ∀ x : UJ ε, ∃ k X, k ∈ Kset ε ∧ inP ε X ∧
      ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X := by
    intro x
    refine ⟨((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      NormedSpace.exp (-polarLog ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)),
      polarLog _, mul_exp_neg_polarLog_mem_compact (inUJ_coe x), polarLog_mem_hermitian_part (inUJ_coe x), ?_⟩
    rw [Matrix.mul_assoc, matrix_exp_neg_mul_exp, Matrix.mul_one]
  have hUJmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, inUJ ε A → inUJ ε B → inUJ ε (A * B) := by
    intro A B hA hB
    unfold inUJ at *
    rw [Matrix.conjTranspose_mul]
    calc Bᴴ * Aᴴ * Jm ε * (A * B) = Bᴴ * (Aᴴ * Jm ε * A) * B := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hA, hB]
  have hUJk : ∀ k, k ∈ Kset ε → inUJ ε k := by
    intro k hk
    unfold inUJ
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, (kset_inv hk).1, Matrix.one_mul]
  have hKmul : ∀ a b, a ∈ Kset ε → b ∈ Kset ε → a * b ∈ Kset ε := by
    intro a b ha hb
    refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
    rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
  have hcancel : ∀ k, k ∈ Kset ε → ∀ X : Matrix (Fin n) (Fin n) ℂ, kᴴ * (k * X) = X := by
    intro k hk X
    rw [← Matrix.mul_assoc, (kset_inv hk).1, Matrix.one_mul]
  obtain ⟨k1, X1, hk1, hX1, hg1⟩ := hpol g
  obtain ⟨k2, X2, hk2, hX2, hh1⟩ := hpol h
  obtain ⟨hk2a, hk2b⟩ := kset_inv hk2
  let u2 : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨k2, k2ᴴ, hk2b, hk2a⟩
  have hexpc : NormedSpace.exp (k2ᴴ * X1 * k2) = k2ᴴ * NormedSpace.exp X1 * k2 :=
    Matrix.exp_units_conj' u2 X1
  have hconj : NormedSpace.exp X1 * k2 = k2 * NormedSpace.exp (k2ᴴ * X1 * k2) := by
    rw [hexpc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hk2b, Matrix.one_mul]
  have hgh : (((g * h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      (k1 * k2) * (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2) := by
    rw [Subgroup.coe_mul, Units.val_mul, hg1, hh1]
    calc k1 * NormedSpace.exp X1 * (k2 * NormedSpace.exp X2)
        = k1 * (NormedSpace.exp X1 * k2) * NormedSpace.exp X2 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hconj]; simp only [Matrix.mul_assoc]
  have hM : inUJ ε (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2) := by
    have e : NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 =
        (k2ᴴ * k1ᴴ) * (((g * h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hgh]
      simp only [Matrix.mul_assoc, hcancel _ hk1, hcancel _ hk2]
    rw [e]
    exact hUJmul _ _ (hUJmul _ _ (hUJk _ (kset_ct hk2)) (hUJk _ (kset_ct hk1))) (inUJ_coe _)
  have hk3 := mul_exp_neg_polarLog_mem_compact hM
  have hX3 := polarLog_mem_hermitian_part hM
  have hM3 : NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 =
      (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 *
        NormedSpace.exp (-polarLog (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2))) *
      NormedSpace.exp (polarLog (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2)) := by
    rw [Matrix.mul_assoc _ (NormedSpace.exp (-_)), matrix_exp_neg_mul_exp, Matrix.mul_one]
  have hYh : (k2ᴴ * X1 * k2)ᴴ = k2ᴴ * X1 * k2 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hermitian_of_mem_hermitian_part hX1, Matrix.mul_assoc]
  have htri := hE n (k2ᴴ * X1 * k2) X2 _ _ hYh (hermitian_of_mem_hermitian_part hX2) (hermitian_of_mem_hermitian_part hX3) hk3.1 hM3
  have hsY : hs (k2ᴴ * X1 * k2) = hs X1 := by
    rw [((hermitian_small_ball n ε).2 (k2ᴴ * X1) k2 hk2).1, ((hermitian_small_ball n ε).2 X1 k2ᴴ (kset_ct hk2)).2]
  have hd1 := symD_eq g hk1 hX1 hg1
  have hd2 := symD_eq h hk2 hX2 hh1
  have hd3 := symD_eq (g * h) (hKmul _ _ (hKmul _ _ hk1 hk2) hk3) hX3 (by
    rw [hgh, Matrix.mul_assoc (k1 * k2), Matrix.mul_assoc (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2),
      matrix_exp_neg_mul_exp, Matrix.mul_one])
  rw [hd1, hd2, hd3]
  have e2 : Real.sqrt (hs (k2ᴴ * X1 * k2)) = Real.sqrt (hs X1) := by rw [hsY]
  rw [← e2]
  exact htri

end PI.SymDistWork

end
