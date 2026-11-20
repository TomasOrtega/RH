import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormEigenvalueLeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical
open Matrix

namespace GlobalTheory.BoundedUnitary

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one`. Consider the case `exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one`. Consider the case `(apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one ..)`.
-/
theorem norm_eigenvalue_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (C : ℝ)
    (hC : ∀ k : ℕ, ∀ i j, ‖(M ^ k) i j‖ ≤ C) (v : Fin n → ℂ) (hv : v ≠ 0) (μ : ℂ)
    (h : M *ᵥ v = μ • v) : ‖μ‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one ..)

open scoped ComplexOrder in

/- English proof (translation)
Establish `hH` using `hp.isHermitian`. Establish `hev : ∀ j, hH.eigenvalues j = 1`. Introduce `j`. Use `set v : Fin n → ℂ := ⇑(hH.eigenvectorBasis j) with hvdef`. Establish `hv : v ≠ 0`.

Introduce `h0`. Establish `h1 : hH.eigenvectorBasis j = 0`. Use extensionality with `i`. Conclude with `congrFun h0 i`. Conclude with `hH.eigenvectorBasis.orthonormal.ne_zero j h1`.

Establish `h1 : p *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ) • v`. Use `hH.mulVec_eigenvectorBasis j` as an intermediate fact. Rewrite using `[hvdef, this]`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Establish `h0 : 0 ≤ hH.eigenvalues j` using `hp.eigenvalues_nonneg j`. Establish `h2 : v = ((hH.eigenvalues j : ℝ) : ℂ) • (q *ᵥ v)`. Rewrite using `[← Matrix.mulVec_smul, ← h1, Matrix.mulVec_mulVec, hqp, Matrix.one_mulVec]`. Establish `hne : ((hH.eigenvalues j : ℝ) : ℂ) ≠ 0`. Introduce `h`.

Rewrite `h2` using `[h, zero_smul]`. Conclude with `hv h2`. Establish `h3 : q *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ)⁻¹ • v` using `by conv_rhs => rw [h2]`. Rewrite using `[smul_smul, inv_mul_cancel₀ hne, one_smul]`. Establish `a1` using `norm_eigenvalue_le_one p C hC v hv _ h1`.

Establish `a2` using `norm_eigenvalue_le_one q C hC' v hv _ h3`. Rewrite `a2` using `[norm_inv, Complex.norm_real, Real.norm_of_nonneg h0]`. Rewrite `a1` using `[Complex.norm_real, Real.norm_of_nonneg h0]`. Establish `hpos : 0 < hH.eigenvalues j` using `lt_of_le_of_ne h0 (fun h => hne (by rw [← h]; simp))`. Conclude with `le_antisymm a1 ((inv_le_one₀ hpos).mp a2)`.

Establish `hbasis : ∀ j, p *ᵥ ⇑(hH.eigenvectorBasis j) = ⇑(hH.eigenvectorBasis j)`. Introduce `j`. Rewrite using `[hH.mulVec_eigenvectorBasis j, hev j, one_smul]`. Establish `hU : p * (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)`. Use extensionality with `i j`.

Use `congrFun (hbasis j) i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hU2` using `Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_one_of_posSemidef {n : ℕ} (p q : Matrix (Fin n) (Fin n) ℂ) (hp : p.PosSemidef)
    (hqp : q * p = 1) (C : ℝ) (hC : ∀ k : ℕ, ∀ i j, ‖(p ^ k) i j‖ ≤ C)
    (hC' : ∀ k : ℕ, ∀ i j, ‖(q ^ k) i j‖ ≤ C) : p = 1 := by
  have hH := hp.isHermitian
  have hev : ∀ j, hH.eigenvalues j = 1 := by
    intro j
    set v : Fin n → ℂ := ⇑(hH.eigenvectorBasis j) with hvdef
    have hv : v ≠ 0 := by
      intro h0
      have h1 : hH.eigenvectorBasis j = 0 := by
        ext i
        exact congrFun h0 i
      exact hH.eigenvectorBasis.orthonormal.ne_zero j h1
    have h1 : p *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ) • v := by
      have := hH.mulVec_eigenvectorBasis j
      rw [hvdef, this]
      ext i
      simp
    have h0 : 0 ≤ hH.eigenvalues j := hp.eigenvalues_nonneg j
    have h2 : v = ((hH.eigenvalues j : ℝ) : ℂ) • (q *ᵥ v) := by
      rw [← Matrix.mulVec_smul, ← h1, Matrix.mulVec_mulVec, hqp, Matrix.one_mulVec]
    have hne : ((hH.eigenvalues j : ℝ) : ℂ) ≠ 0 := by
      intro h
      rw [h, zero_smul] at h2
      exact hv h2
    have h3 : q *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ)⁻¹ • v := by
      conv_rhs => rw [h2]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    have a1 := norm_eigenvalue_le_one p C hC v hv _ h1
    have a2 := norm_eigenvalue_le_one q C hC' v hv _ h3
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h0] at a2
    rw [Complex.norm_real, Real.norm_of_nonneg h0] at a1
    have hpos : 0 < hH.eigenvalues j := lt_of_le_of_ne h0 (fun h => hne (by rw [← h]; simp))
    exact le_antisymm a1 ((inv_le_one₀ hpos).mp a2)
  have hbasis : ∀ j, p *ᵥ ⇑(hH.eigenvectorBasis j) = ⇑(hH.eigenvectorBasis j) := by
    intro j
    rw [hH.mulVec_eigenvectorBasis j, hev j, one_smul]
  have hU : p * (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    have := congrFun (hbasis j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hU2 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  calc p = p * ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) := by rw [hU2, mul_one]
    _ = 1 := by rw [← mul_assoc, hU, hU2]

open scoped ComplexOrder in

/- English proof (translation)
Introduce `n ε G' hU hK hmul hinv ⟨C, hC⟩`. Use `Set.Subset.antisymm (fun a ha => ?_) hK` and prove the remaining obligations. Establish `hJJ` using `Formalism.REAL.Jm_mul_self ε`. Establish `hJH` using `Formalism.REAL.Jm_conjTranspose ε`. Use `set J := Formalism.REAL.Jm ε with hJ`.

Establish `hJG : J ∈ G'` using `hK ⟨by`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hJH, hJJ], rfl⟩`. Establish `h1G : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G'` using `hJJ ▸ hmul _ hJG _ hJG`. Establish `hpow : ∀ b ∈ G', ∀ k : ℕ, b ^ k ∈ G'`. Introduce `b hb k`.

Proceed by induction on `k with`. Consider the case `zero => simpa using h1G`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `hmul _ ih _ hb`. Establish `hleft : ∀ b ∈ G', (J * bᴴ * J) * b = 1`.

Introduce `b hb`. Establish `hb' : bᴴ * J * b = J` using `hU hb`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv_eq : ∀ b ∈ G', b⁻¹ = J * bᴴ * J` using `fun b hb => Matrix.inv_eq_left_inv (hleft b hb)`. Establish `haH : aᴴ ∈ G'`.

Establish `: aᴴ = J * a⁻¹ * J`. Rewrite using `[hinv_eq a ha]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `hmul _ (hmul _ hJG _ (hinv a ha)) _ hJG`.

Establish `hpG : aᴴ * a ∈ G'` using `hmul _ haH _ ha`. Establish `hp1 : aᴴ * a = 1`. Use `eq_one_of_posSemidef (aᴴ * a) (aᴴ * a)⁻¹ (Matrix.posSemidef_conjTranspose_mul_self a) ?_ C (fun k => hC _ (hpow _ hpG k)) (fun k => hC _ (hpow _ (hinv _ hpG) k))` and prove the remaining obligations. Rewrite using `[hinv_eq _ hpG]`. Conclude with `hleft _ hpG`.

Establish `hp2 : a * aᴴ = 1` using `mul_eq_one_comm.mp hp1`. Use `⟨by rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hp1], ?_⟩` and prove the remaining obligations. Establish `ha' : aᴴ * J * a = J` using `hU ha`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_Kset_of_bounded : ∀ (n : ℕ) (ε : Fin n → Bool) (G' : Set (Matrix (Fin n) (Fin n) ℂ)), G' ⊆ Formalism.MainNotions.S.UJset ε → Formalism.REAL.Kset ε ⊆ G' → (∀ a ∈ G', ∀ b ∈ G', a * b ∈ G') → (∀ a ∈ G', a⁻¹ ∈ G') → (∃ C : ℝ, ∀ a ∈ G', ∀ i j, ‖a i j‖ ≤ C) → G' = Formalism.REAL.Kset ε := by
  intro n ε G' hU hK hmul hinv ⟨C, hC⟩
  refine Set.Subset.antisymm (fun a ha => ?_) hK
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJH := Formalism.REAL.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJ
  have hJG : J ∈ G' := hK ⟨by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hJH, hJJ], rfl⟩
  have h1G : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G' := hJJ ▸ hmul _ hJG _ hJG
  have hpow : ∀ b ∈ G', ∀ k : ℕ, b ^ k ∈ G' := by
    intro b hb k
    induction k with
    | zero => simpa using h1G
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hb
  have hleft : ∀ b ∈ G', (J * bᴴ * J) * b = 1 := by
    intro b hb
    have hb' : bᴴ * J * b = J := hU hb
    calc (J * bᴴ * J) * b = J * (bᴴ * J * b) := by simp only [mul_assoc]
      _ = 1 := by rw [hb', hJJ]
  have hinv_eq : ∀ b ∈ G', b⁻¹ = J * bᴴ * J := fun b hb => Matrix.inv_eq_left_inv (hleft b hb)
  have haH : aᴴ ∈ G' := by
    have : aᴴ = J * a⁻¹ * J := by
      rw [hinv_eq a ha]
      calc aᴴ = (J * J) * aᴴ * (J * J) := by rw [hJJ, one_mul, mul_one]
        _ = _ := by simp only [mul_assoc]
    rw [this]
    exact hmul _ (hmul _ hJG _ (hinv a ha)) _ hJG
  have hpG : aᴴ * a ∈ G' := hmul _ haH _ ha
  have hp1 : aᴴ * a = 1 := by
    refine eq_one_of_posSemidef (aᴴ * a) (aᴴ * a)⁻¹ (Matrix.posSemidef_conjTranspose_mul_self a) ?_ C
      (fun k => hC _ (hpow _ hpG k)) (fun k => hC _ (hpow _ (hinv _ hpG) k))
    rw [hinv_eq _ hpG]
    exact hleft _ hpG
  have hp2 : a * aᴴ = 1 := mul_eq_one_comm.mp hp1
  refine ⟨by rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hp1], ?_⟩
  have ha' : aᴴ * J * a = J := hU ha
  calc a * J = a * (aᴴ * J * a) := by rw [ha']
    _ = (a * aᴴ) * J * a := by simp only [mul_assoc]
    _ = J * a := by rw [hp2, one_mul]

end GlobalTheory.BoundedUnitary
