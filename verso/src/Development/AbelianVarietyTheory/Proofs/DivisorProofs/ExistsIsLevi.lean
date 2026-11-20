import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviUnitary

open Matrix

section Ring

variable {R : Type} [CommRing R] {n m : ℕ} {ι : Matrix (Fin n) (Fin m) R} {π : Matrix (Fin m) (Fin n) R}

/- English proof (translation)
Establish `h1 : ι * (g - 1) * π * (ι * (h - 1) * π) = ι * ((g - 1) * (h - 1)) * π`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : g * h - 1 = (h - 1) + (g - 1) + (g - 1) * (h - 1)` using `by noncomm_ring`. Rewrite using `[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, h1, h2]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, add_assoc]`.
-/
theorem ext_mul (hπ : π * ι = 1) (g h : Matrix (Fin m) (Fin m) R) :
    (1 + ι * (g - 1) * π) * (1 + ι * (h - 1) * π) = 1 + ι * (g * h - 1) * π := by
  have h1 : ι * (g - 1) * π * (ι * (h - 1) * π) = ι * ((g - 1) * (h - 1)) * π := by
    calc _ = ι * (g - 1) * (π * ι) * (h - 1) * π := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hπ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : g * h - 1 = (h - 1) + (g - 1) + (g - 1) * (h - 1) := by noncomm_ring
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, add_assoc]

/- English proof (translation)
Establish `hm : (1 + ι * (g - 1) * π).map c = 1 + ι.map c * (g.map c - 1) * π.map c`. Rewrite using `[Matrix.map_add _ (map_add c), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_one _ (map_zero c) (map_one c)]`. Establish `h3 : π.map c * ι.map c = 1` using `by rw [← Matrix.map_mul, hπ, Matrix.map_one _ (map_zero c) (map_one c)]`. Establish `ht : (1 + ι * (g - 1) * π)ᵀ = 1 + πᵀ * (gᵀ - 1) * ιᵀ`. Simplify using `only [transpose_add, transpose_mul, transpose_sub, transpose_one, Matrix.mul_assoc]`.

Establish `e1 : πᵀ * (gᵀ - 1) * ιᵀ * J = πᵀ * ((gᵀ - 1) * J₁) * π.map c`. Rewrite using `[Matrix.mul_assoc _ ιᵀ, h2]`. Simplify using `only [Matrix.mul_assoc]`. Establish `e2 : J * (ι.map c * (g.map c - 1) * π.map c) = πᵀ * (J₁ * (g.map c - 1)) * π.map c`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `e3 : πᵀ * ((gᵀ - 1) * J₁) * π.map c * (ι.map c * (g.map c - 1) * π.map c) = πᵀ * ((gᵀ - 1) * J₁ * (g.map c - 1)) * π.map c`. Combine the equalities or inequalities in the displayed calculation. Establish `e4 : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = 0`. Establish `: (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = gᵀ * J₁ * g.map c - J₁` using `by noncomm_ring`.

Rewrite using `[this, hg, sub_self]`. Rewrite using `[hm, ht, Matrix.add_mul, Matrix.one_mul, e1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, e2, e3, add_assoc, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, e4]`. Simplify using the standard rewrite rules.
-/
theorem ext_unitary (c : R →+* R) {J : Matrix (Fin n) (Fin n) R} {J₁ : Matrix (Fin m) (Fin m) R} (hπ : π * ι = 1)
    (h1 : J * ι.map c = πᵀ * J₁) (h2 : ιᵀ * J = J₁ * π.map c) {g : Matrix (Fin m) (Fin m) R} (hg : gᵀ * J₁ * g.map c = J₁) :
    (1 + ι * (g - 1) * π)ᵀ * J * (1 + ι * (g - 1) * π).map c = J := by
  have hm : (1 + ι * (g - 1) * π).map c = 1 + ι.map c * (g.map c - 1) * π.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub c),
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : π.map c * ι.map c = 1 := by rw [← Matrix.map_mul, hπ, Matrix.map_one _ (map_zero c) (map_one c)]
  have ht : (1 + ι * (g - 1) * π)ᵀ = 1 + πᵀ * (gᵀ - 1) * ιᵀ := by
    simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, Matrix.mul_assoc]
  have e1 : πᵀ * (gᵀ - 1) * ιᵀ * J = πᵀ * ((gᵀ - 1) * J₁) * π.map c := by
    rw [Matrix.mul_assoc _ ιᵀ, h2]; simp only [Matrix.mul_assoc]
  have e2 : J * (ι.map c * (g.map c - 1) * π.map c) = πᵀ * (J₁ * (g.map c - 1)) * π.map c := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]; simp only [Matrix.mul_assoc]
  have e3 : πᵀ * ((gᵀ - 1) * J₁) * π.map c * (ι.map c * (g.map c - 1) * π.map c) =
      πᵀ * ((gᵀ - 1) * J₁ * (g.map c - 1)) * π.map c := by
    calc _ = πᵀ * ((gᵀ - 1) * J₁) * (π.map c * ι.map c) * (g.map c - 1) * π.map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e4 : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = 0 := by
    have : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = gᵀ * J₁ * g.map c - J₁ := by noncomm_ring
    rw [this, hg, sub_self]
  rw [hm, ht, Matrix.add_mul, Matrix.one_mul, e1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, e2, e3, add_assoc,
    ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, e4]
  simp

end Ring

/- English proof (translation)
Take `⟨rfl, A, hA⟩` from `h`. Introduce `h0`. Set `A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ` to `A.submatrix id finSumFinEquiv.symm`. Establish `h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Rewrite using `[← hA]`.

Use extensionality with `i j`. Simplify using `[A', Matrix.mul_apply]`. Establish `h2` using `congrArg Matrix.det h1`. Rewrite `h2` using `[det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, det_neg, det_one]`. Simplify using `at h2`.

Conclude with `absurd h2.symm (by simp)`.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, det_neg, det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem incM_mul {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E) :
    incM F (A * A') = incM F A * incM F A' := Matrix.map_mul

/- English proof (translation)
Use extensionality with `i j`. Conclude with `GlobalTheory.LeviTorus.cA_incl σ (A i j)`.
-/
theorem incM_conj {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) :
    (incM F A).map (cA σ).toRingHom = incM F (A.map σ) := by
  ext i j
  exact GlobalTheory.LeviTorus.cA_incl σ (A i j)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incM, incV, mulVec, dotProduct, map_sum, map_mul]`.
-/
theorem incM_mulVec {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) (x : Fin l → E) :
    incM F A *ᵥ incV F x = incV F (A *ᵥ x) := by
  funext i
  simp [incM, incV, mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Establish `hσ` using `GlobalTheory.LeviTorus.sigma_invol hB.cm`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdet : IsUnit W₁.J.det`. Establish `h` using `det_ne_zero_of_hasSig (hW₁.sig w)`. Rewrite `h` using `[det_smul]`.

Establish `h'` using `right_ne_zero_of_mul h`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Apply `h'` to reduce the goal to its premises. Use `RingHom.map_det (B.emb w).1 W₁.J` as an intermediate fact.

Rewrite `this` using `[h0, map_zero]`. Conclude with `this.symm`. Establish `mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A` using `fun A => by`. Use extensionality with `i j`. Conclude with `hσ _`.

Establish `mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E), (A * A').map σ = A.map σ * A'.map σ` using `fun A A' => Matrix.map_mul (f := σ.toRingHom)`. Establish `sk : W.J.map σ = -W.Jᵀ` using `by ext i j; exact hW.skew j i`. Establish `sk₁ : W₁.J.map σ = -W₁.Jᵀ` using `by ext i j; exact hW₁.skew j i`. Use `set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP`. Establish `h2 : H'.ιᵀ * W.J = W₁.J * P` using `by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]`.

Establish `hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0`. Introduce `z hz`. Establish `e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0`. Use function extensionality and compare the values at `j`. Use `hz (Pi.single j 1)` as an intermediate fact.

Rewrite `this` using `[form, mulVec_single_one]`. Rewrite using `[← mulVec_mulVec]`. Conclude with `this`. Establish `e2 : P *ᵥ (fun i => σ (z i)) = 0` using `by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]`. Use function extensionality and compare the values at `j`.

Use `congrArg σ (congrFun e2 j)` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct, map_sum, map_mul, hσ]`. Use `⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (hA.orth u).1, hz _ fun u => (hA.orth u).2⟩` and prove the remaining obligations. Establish `: P * H'.ι.map σ = 1` using `by rw [hP, Matrix.mul_assoc, hA.gram, Matrix.nonsing_inv_mul _ hdet]`. Rewrite using `[← mm H'.ι, ← mul, this]`.

Conclude with `Matrix.map_one _ (map_zero σ) (map_one σ)`. Use `congrArg (fun A => (Matrix.map A σ)ᵀ) h2` as an intermediate fact. Simplify using `only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_inj] at this`. Conclude with `this`.
-/
theorem exists_proj {B : Base F E} (hB : B.IsGood σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {r s r₁ s₁ : ℕ}
    (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ W.J * H'.ι.map σ = πᵀ * W₁.J ∧ H'.ιᵀ * W.J = W₁.J * π.map σ ∧
      π *ᵥ H'.x = 0 ∧ π *ᵥ H'.y = 0 := by
  have hσ := GlobalTheory.LeviTorus.sigma_invol hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit W₁.J.det := by
    have h := det_ne_zero_of_hasSig (hW₁.sig w)
    rw [det_smul] at h
    have h' := right_ne_zero_of_mul h
    rw [isUnit_iff_ne_zero]
    intro h0
    apply h'
    have := RingHom.map_det (B.emb w).1 W₁.J
    rw [h0, map_zero] at this
    exact this.symm
  have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A := fun A => by
    ext i j; exact hσ _
  have mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E),
      (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
  have sk : W.J.map σ = -W.Jᵀ := by ext i j; exact hW.skew j i
  have sk₁ : W₁.J.map σ = -W₁.Jᵀ := by ext i j; exact hW₁.skew j i
  set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP
  have h2 : H'.ιᵀ * W.J = W₁.J * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0 := by
    intro z hz
    have e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0 := by
      funext j
      have := hz (Pi.single j 1)
      rw [form, mulVec_single_one] at this
      rw [← mulVec_mulVec]
      exact this
    have e2 : P *ᵥ (fun i => σ (z i)) = 0 := by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]
    funext j
    have := congrArg σ (congrFun e2 j)
    simpa [mulVec, dotProduct, map_sum, map_mul, hσ] using this
  refine ⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (hA.orth u).1, hz _ fun u => (hA.orth u).2⟩
  · have : P * H'.ι.map σ = 1 := by rw [hP, Matrix.mul_assoc, hA.gram, Matrix.nonsing_inv_mul _ hdet]
    rw [← mm H'.ι, ← mul, this]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  · have := congrArg (fun A => (Matrix.map A σ)ᵀ) h2
    simp only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg,
      neg_inj] at this
    exact this

/- English proof (translation)
Take `⟨π, p1, p2, p3, p4, p5⟩` from `exists_proj hB hW hW₁ hA`. Establish `q1 : incM F π * incM F H'.ι = 1`. Rewrite using `[← incM_mul, p1]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J`.

Rewrite using `[incM_conj, ← incM_mul, p2, incM_mul]`. Both sides reduce to the same expression. Establish `q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom`. Rewrite using `[incM_conj, ← incM_mul, ← p3, incM_mul]`. Both sides reduce to the same expression.

Establish `hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z`. Introduce `z hz`. Establish `h0 : incV F (0 : Fin d₁ → E) = 0` using `by funext i; exact map_zero _`. Rewrite using `[add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]`. Use `⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[ext_mul q1, mat, Units.mul_inv]`. Simplify using the standard rewrite rules. Rewrite using `[ext_mul q1, mat, Units.inv_mul]`. Simplify using the standard rewrite rules. Conclude with `ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2`.

Rewrite using `[Units.val_one, one_smul]`. Conclude with `hfix _ p4`. Rewrite using `[inv_one, Units.val_one, map_one, one_smul]`. Conclude with `hfix _ p5`. Use `show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _`.

Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]`.
-/
theorem exists_isLevi {B : Base F E} (hB : B.IsGood σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {r s r₁ s₁ : ℕ}
    (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (h₁ : UA σ W₁.J) : ∃ m : UA σ W.J, IsLevi H' 1 h₁ m := by
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := exists_proj hB hW hW₁ hA
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

end GlobalTheory.LeviUnitary

end
