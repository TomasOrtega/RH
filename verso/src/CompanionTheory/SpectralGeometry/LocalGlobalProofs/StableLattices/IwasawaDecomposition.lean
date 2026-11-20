import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuIwa

open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder

/- English proof (translation)
Use `set A := dp p 0 c with hAdef`. Establish `hA : A * A = 1` using `h.mul_self`. Establish `hAH : Aᴴ = A` using `h.herm`. Establish `hg' : g * A * gᴴ = A` using `flip hA hg`. Establish `hgu : IsUnit g`.

Use `⟨⟨g, A * gᴴ * A, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Take `⟨B, a, hB, ha, hBd, hBS⟩` from `exists_cholesky (PosDef.conjTranspose_mul_self g (mulVec_injective_of_isUnit hgu))`. Establish `hBdet : IsUnit B.det`.

Rewrite using `[det_of_isUpperTriangular hB]`. Conclude with `IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by`. Rewrite using `[hBd i]`. Conclude with `RCLike.ofReal_ne_zero.2 (ha i).ne')`. Establish `hBi : B⁻¹ * B = 1` using `Matrix.nonsing_inv_mul _ hBdet`.

Establish `hBi' : B * B⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hBdet`. Establish `hBiH : B⁻¹ᴴ * Bᴴ = 1` using `by rw [← conjTranspose_mul, hBi', conjTranspose_one]`. Establish `hS : Bᴴ * B * A * (Bᴴ * B) = A`. Rewrite using `[hBS]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hS1 : A * (Bᴴ * B) * A * Bᴴ * B = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hu : B * (A * (Bᴴ * B) * A * Bᴴ) = 1` using `mul_eq_one_comm.1 hS1`. Establish `hw : (B * (A * Bᴴ * A))ᴴ * (B * (A * Bᴴ * A)) = 1`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hu, Matrix.mul_one, hA]`. Establish `hw1 : B * (A * Bᴴ * A) = 1` using `eq_one_of_posSemidef hw (h.posSemidef hB ha hBd fun i j hij => eq_zero_of_unitary_blockTriangular hw ((h.tri hB).mul (h.conj_tri hB)) hij)`. Establish `hw2 : (A * Bᴴ * A) * B = 1` using `mul_eq_one_comm.1 hw1`.

Establish `hBA : Bᴴ * A * B = A`. Combine the equalities or inequalities in the displayed calculation. Use `⟨g * B⁻¹, B, ?_, ?_, hBA, ?_, hB⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, hBi, Matrix.mul_one]`.
-/
theorem adapted_dec_one {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * dp p 0 c * g = dp p 0 c) :
    ∃ k B : Matrix (Fin n) (Fin n) ℂ, kᴴ * k = 1 ∧ kᴴ * dp p 0 c * k = dp p 0 c ∧
      Bᴴ * dp p 0 c * B = dp p 0 c ∧ g = k * B ∧ B.BlockTriangular id := by
  set A := dp p 0 c with hAdef
  have hA : A * A = 1 := h.mul_self
  have hAH : Aᴴ = A := h.herm
  have hg' : g * A * gᴴ = A := flip hA hg
  have hgu : IsUnit g := by
    refine ⟨⟨g, A * gᴴ * A, ?_, ?_⟩, rfl⟩
    · calc g * (A * gᴴ * A) = (g * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', hA]
    · calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg, hA]
  obtain ⟨B, a, hB, ha, hBd, hBS⟩ :=
    exists_cholesky (PosDef.conjTranspose_mul_self g (mulVec_injective_of_isUnit hgu))
  have hBdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [hBd i]; exact RCLike.ofReal_ne_zero.2 (ha i).ne')
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hBiH : B⁻¹ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBi', conjTranspose_one]

  have hS : Bᴴ * B * A * (Bᴴ * B) = A := by
    rw [hBS]
    calc gᴴ * g * A * (gᴴ * g) = gᴴ * (g * A * gᴴ) * g := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hg', hg]
  have hS1 : A * (Bᴴ * B) * A * Bᴴ * B = 1 := by
    calc A * (Bᴴ * B) * A * Bᴴ * B = A * (Bᴴ * B * A * (Bᴴ * B)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS, hA]
  have hu : B * (A * (Bᴴ * B) * A * Bᴴ) = 1 := mul_eq_one_comm.1 hS1
  have hw : (B * (A * Bᴴ * A))ᴴ * (B * (A * Bᴴ * A)) = 1 := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
    calc A * (B * A) * Bᴴ * (B * (A * Bᴴ * A)) = A * (B * (A * (Bᴴ * B) * A * Bᴴ)) * A := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one, hA]
  have hw1 : B * (A * Bᴴ * A) = 1 :=
    eq_one_of_posSemidef hw (h.posSemidef hB ha hBd fun i j hij =>
      eq_zero_of_unitary_blockTriangular hw ((h.tri hB).mul (h.conj_tri hB)) hij)
  have hw2 : (A * Bᴴ * A) * B = 1 := mul_eq_one_comm.1 hw1
  have hBA : Bᴴ * A * B = A := by
    calc Bᴴ * A * B = (A * A) * (Bᴴ * A * B) := by rw [hA, Matrix.one_mul]
      _ = A * ((A * Bᴴ * A) * B) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hw2, Matrix.mul_one]
  refine ⟨g * B⁻¹, B, ?_, ?_, hBA, ?_, hB⟩
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᴴ * Bᴴ) * (B * B⁻¹) := by rw [← hBS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiH, hBi', Matrix.one_mul]
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * A * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * A * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ᴴ * (Bᴴ * A * B) * B⁻¹ := by rw [hg, hBA]
      _ = (B⁻¹ᴴ * Bᴴ) * A * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hBiH, hBi', Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hBi, Matrix.mul_one]

/- English proof (translation)
Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_mem {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1) (hAH : Aᴴ = A)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A)ᴴ * A * (A * gᴴ * A) = A := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
  calc A * (g * A) * A * (A * gᴴ * A) = A * (g * (A * A) * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hA, Matrix.mul_one, CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hg, hA, Matrix.one_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_mul {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A) * g = 1 := by
  calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hA]

/- English proof (translation)
Establish `hA` using `h.mul_self`. Establish `hAH` using `h.herm`. Take `⟨k, B, hk, hkA, hBA, hg, hB⟩` from `adapted_dec_one h _ (conj_mem hA hAH hx)`. Use `set A := dp p 0 c`. Establish `hBl` using `conj_mul hA hBA`.

Establish `hk' : k * kᴴ = 1` using `mul_eq_one_comm.1 hk`. Use `⟨A * Bᴴ * A, kᴴ, conj_mem hA hAH hBA, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_conjTranspose]`. Conclude with `CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hkA`. Set `_ : Invertible B` to `invertibleOfLeftInverse B _ hBl`.

Rewrite using `[← inv_eq_left_inv hBl]`. Conclude with `blockTriangular_inv_of_blockTriangular hB`. Rewrite using `[conjTranspose_conjTranspose]`. Conclude with `hk'`. Establish `h1 : k * B * x = 1` using `by rw [← hg]; exact conj_mul hA hx`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem adapted_dec_left {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : xᴴ * dp p 0 c * x = dp p 0 c) :
    ∃ s κ : Matrix (Fin n) (Fin n) ℂ, sᴴ * dp p 0 c * s = dp p 0 c ∧ κᴴ * dp p 0 c * κ = dp p 0 c ∧
      s.BlockTriangular id ∧ κᴴ * κ = 1 ∧ x = s * κ := by
  have hA := h.mul_self
  have hAH := h.herm
  obtain ⟨k, B, hk, hkA, hBA, hg, hB⟩ := adapted_dec_one h _ (conj_mem hA hAH hx)
  set A := dp p 0 c
  have hBl := conj_mul hA hBA
  have hk' : k * kᴴ = 1 := mul_eq_one_comm.1 hk
  refine ⟨A * Bᴴ * A, kᴴ, conj_mem hA hAH hBA, ?_, ?_, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]; exact CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hkA
  · let _ : Invertible B := invertibleOfLeftInverse B _ hBl
    rw [← inv_eq_left_inv hBl]
    exact blockTriangular_inv_of_blockTriangular hB
  · rw [conjTranspose_conjTranspose]; exact hk'
  · have h1 : k * B * x = 1 := by rw [← hg]; exact conj_mul hA hx
    calc x = (A * Bᴴ * A * B) * x := by rw [hBl, Matrix.one_mul]
      _ = A * Bᴴ * A * ((kᴴ * k) * B * x) := by rw [hk, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = A * Bᴴ * A * kᴴ * (k * B * x) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]

def pq (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := if outer k r i then i.rev else i

def bq (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ := if outer k r i then 2 * (i.val : ℤ) - (2 * r + k) else 0

/- English proof (translation)
Unfold `pq`. Distinguish the cases in `h : outer k r i`. Rewrite using `[if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h), Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]`.
-/
theorem pq_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (pq k r i).val = if i.val ≤ r ∨ r + k ≤ i.val then 2 * r + k - i.val else i.val := by
  unfold pq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h), Fin.val_rev]; omega
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

/- English proof (translation)
Unfold `bq`. Distinguish the cases in `h : outer k r i`. Rewrite using `[if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]`. Rewrite using `[if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]`.
-/
theorem bq_eq (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    bq k r i = if i.val ≤ r ∨ r + k ≤ i.val then 2 * (i.val : ℤ) - (2 * r + k) else 0 := by
  unfold bq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Use `i.2` as an intermediate fact. Rewrite using `[pq_val, pq_val]`. Apply the tactic sequence `split_ifs <;> omega`. Use `mono i j hij := by`.

Establish `h : i.val ≤ j.val` using `hij`. Rewrite using `[bq_eq, bq_eq]`. Apply the tactic sequence `split_ifs <;> omega`. Use `neg i := by`. Use `i.2` as an intermediate fact.

Rewrite using `[bq_eq, bq_eq, pq_val]`. Apply the tactic sequence `split_ifs <;> omega`. Use `fix i hi := by`. Apply `Fin.ext` to reduce the goal to its premises. Use `i.2` as an intermediate fact.

Rewrite `hi` using `[bq_eq]`. Rewrite using `[pq_val]`. Apply the tactic sequence `split_ifs at hi ⊢ <;> omega`. Use `inj i j hi hij := by`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite `hi` using `[bq_eq]`. Rewrite `hij` using `[bq_eq, bq_eq]`. Apply the tactic sequence `split_ifs at hi hij <;> omega`. Use `sq _ := by simp`. Use `star_eq _ := by simp`.

Use symmetry as in `_ := rfl`. Use `mid _ _ _ _ := rfl`.
-/
theorem adapted_pq (k r : ℕ) : Adapted (pq k r) (bq k r) (fun _ => 1) where
  invol i := by
    apply Fin.ext
    have := i.2
    rw [pq_val, pq_val]
    split_ifs <;> omega
  mono i j hij := by
    have h : i.val ≤ j.val := hij
    rw [bq_eq, bq_eq]
    split_ifs <;> omega
  neg i := by
    have := i.2
    rw [bq_eq, bq_eq, pq_val]
    split_ifs <;> omega
  fix i hi := by
    apply Fin.ext
    have := i.2
    rw [bq_eq] at hi
    rw [pq_val]
    split_ifs at hi ⊢ <;> omega
  inj i j hi hij := by
    apply Fin.ext
    rw [bq_eq] at hi
    rw [bq_eq, bq_eq] at hij
    split_ifs at hi hij <;> omega
  sq _ := by simp
  star_eq _ := by simp
  symm _ := rfl
  mid _ _ _ _ := rfl

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Simplify using `only [Hq, dp, Matrix.of_apply, Pi.zero_apply, ite_self, zero_add, Fin.ext_iff, pq_val]`. Distinguish the cases in `h : outer k r i`.

Rewrite using `[if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]`. Conclude with `if_congr (by omega) rfl rfl`. Rewrite using `[if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]`. Conclude with `if_congr eq_comm rfl rfl`.
-/
theorem Hq_eq_dp (k r : ℕ) : Hq k r = dp (pq k r) 0 (fun _ => 1) := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Hq, dp, Matrix.of_apply, Pi.zero_apply, ite_self, zero_add, Fin.ext_iff, pq_val]
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
    exact if_congr (by omega) rfl rfl
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]
    exact if_congr eq_comm rfl rfl

/- English proof (translation)
Introduce `k r _ x hx`. Establish `hx' : xᴴ * Hq k r * x = Hq k r` using `hx`. Rewrite `hx'` using `[Hq_eq_dp]`. Take `⟨s, κ, hs, hκ, h1, h2, h3⟩` from `adapted_dec_left (adapted_pq k r) x hx'`. Rewrite `hs`, `hκ` using `[← Hq_eq_dp]`.

Conclude with `⟨s, hs, κ, hκ, h1, h2, h3⟩`.
-/
theorem iwaQ : IwaQ := by
  intro k r _ x hx
  have hx' : xᴴ * Hq k r * x = Hq k r := hx
  rw [Hq_eq_dp] at hx'
  obtain ⟨s, κ, hs, hκ, h1, h2, h3⟩ := adapted_dec_left (adapted_pq k r) x hx'
  rw [← Hq_eq_dp] at hs hκ
  exact ⟨s, hs, κ, hκ, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.BmuIwa
