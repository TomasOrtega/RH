import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfB

noncomputable section

open Matrix Formalism.MainNotions.S
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ}

/- English proof (translation)
Simplify using `[uMat]`.
-/
theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by simp [uMat]

/- English proof (translation)
Unfold `eN`. Rewrite using `[Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem eN_single (i0 : Fin k) (z : ℂ) : eN (Pi.single i0 z) = ‖z‖ := by
  unfold eN
  rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same,
    Real.sqrt_sq (norm_nonneg _)]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = L`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.
-/
theorem single_last_smul (L : Fin (r + 1)) (d : ℂ) : Pi.single L d = d • Pi.single L (1 : ℂ) := by
  funext j
  by_cases hj : j = L
  · subst hj; simp
  · simp [hj]

/- English proof (translation)
Use `set L := Fin.last r with hL`. Use `set c := Z⁻¹ *ᵥ Pi.single L 1 with hcdef`. Establish `hZc : Z *ᵥ c = Pi.single L 1` using `by rw [hcdef, mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]`. Establish `hc0 : c ≠ 0`. Introduce `h`.

Rewrite `hZc` using `[h, mulVec_zero]`. Use `congrFun hZc L` as an intermediate fact. Simplify using `at this`. Take `⟨N, hNdef⟩ : ∃ N : ℂ, N = star c ⬝ᵥ c` from `⟨_, rfl⟩`. Establish `hN : N ≠ 0` using `by rw [hNdef]; exact fun h => hc0 (dotProduct_star_self_eq_zero.1 h)`.

Take `⟨t, htdef⟩ : ∃ t : Fin (r + 1) → ℂ, t = ((σ : ℂ) / N) • star c` from `⟨_, rfl⟩`. Establish `htc : t ⬝ᵥ c = σ` using `by rw [htdef, smul_dotProduct, smul_eq_mul, ← hNdef, div_mul_cancel₀ _ hN]`. Take `⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Γ = Matrix.of fun b c' => if b = L then (if c' = L then -(B.T : ℂ) else 0) else 0` from `⟨_, rfl⟩`. Take `⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Q = Γ + ((A.T : ℂ)⁻¹) • vecMulVec (star (Z L)) (Z L) - vecMulVec (star t) t` from `⟨_, rfl⟩`. Establish `hAstar : star ((A.T : ℂ)⁻¹) = (A.T : ℂ)⁻¹` using `by rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]`.

Establish `hBstar : star (-(B.T : ℂ)) = -(B.T : ℂ)` using `by rw [star_neg, Complex.star_def, Complex.conj_ofReal]`. Establish `hQ : Qᴴ = Q`. Use extensionality with `b c'`. Simplify using `only [hQdef, hΓ, conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, of_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub, star_mul', star_star, hAstar]`. Apply the tactic sequence `by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc, hBstar] <;> ring`.

Establish `hzc : Z L ⬝ᵥ c = 1`. Use `congrFun hZc L` as an intermediate fact. Simplify `this` using `[mulVec]`. Establish `hΓv : Γ *ᵥ c = Pi.single L (-(B.T : ℂ) * c L)`. Use function extensionality and compare the values at `b`.

Distinguish the cases in `hb : b = L`. Substitute `hb` using the available equality. Simplify using `[hΓ, mulVec, dotProduct, Finset.sum_ite_eq']`. Simplify using `[hΓ, mulVec, dotProduct, hb]`. Establish `hcQ : star c ⬝ᵥ (Q *ᵥ c) = 0`.

Rewrite using `[hQdef, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dot_vmv, dot_vmv, hΓv, dotProduct_single, star_dotProduct_star, star_dotProduct_star, hzc, htc, smul_eq_mul, star_one, mul_one, mul_one]`. Establish `h1 : star (c L) * c L = ((‖c L‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression.

Establish `h2 : star (σ : ℂ) * σ = ((σ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, hσ2, Pi.star_apply, show star (c L) * (-(B.T : ℂ) * c L) = -(B.T : ℂ) * (star (c L) * c L) by ring, h1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨Aα, hAlast, hAeq⟩` from `solveHerm Z Q hZ hQ hcQ`. Use `set y := A.yv i0 Z Aα t with hydef`. Establish `hgram : ∀ b c', hJ ε (y b) (y c') = hJ ε (fam B.e B.z b) (fam B.e B.z c')`.

Introduce `b c'`. Rewrite using `[hydef, A.gram i0 Z Aα t hAlast, B.gf]`. Establish `hq` using `congrFun (congrFun hAeq b) c'`. Rewrite `hq` using `[Matrix.add_apply]`. Establish `hQbc : Q b c' = Γ b c' + (A.T : ℂ)⁻¹ * (star (Z L b) * Z L c') - star (t b) * t c'`.

Simplify using `[hQdef, vecMulVec_apply]`. Establish `hΓbc : Γ b c' = if b = L ∧ c' = L then -(B.T : ℂ) else 0`. Rewrite using `[hΓ, of_apply]`. Apply the tactic sequence `by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc]`. Rewrite using `[← hΓbc]`.

Take the linear combination `hq + hQbc`. Set `s : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ` to `Sum.elim (fam B.e B.z) (fun i => B.wb i.1)`. Set `tt : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ` to `Sum.elim y (fun i => A.wb i.1)`. Establish `hs : LinearIndependent ℂ s` using `li_of_pair ε s (Sum.elim B.Fv (fun i => B.wb i.1)) 1 (by simp) (by`. Introduce and unpack `(a|j) (b|i)`.

Simplify using `[s, B.Fv_fam, one_apply]`. Simplify using `[s, B.Fv_w, one_apply]`. Simplify using `[s, B.w_fam, one_apply]`. Simplify using `[s, B.ww, one_apply, Subtype.ext_iff])`. Establish `ht : LinearIndependent ℂ tt` using `li_of_pair ε tt (Sum.elim (fam A.e A.z) (fun i => A.wb i.1)) (Matrix.fromBlocks Z 0 0 1) (by rw [det_fromBlocks_zero₂₁, det_one, mul_one]; exact hZ) (by`.

Introduce and unpack `(a|j) (b|i)`. Simplify using `[tt, hydef, A.p1]`. Simplify using `[tt, A.fam_w]`. Simplify using `[tt, hydef, A.p4, j.2]`. Simplify using `[tt, A.ww, one_apply, Subtype.ext_iff])`.

Establish `hG : ∀ i j, hJ ε (tt i) (tt j) = hJ ε (s i) (s j)`. Introduce and unpack `(b|i) (c'|j)`. Conclude with `hgram b c'`. Use `show hJ ε (y b) (A.wb j.1) = hJ ε (fam B.e B.z b) (B.wb j.1)`. Rewrite using `[swapJ (A.p4 i0 Z Aα t j.1 b), if_neg j.2, star_zero, B.fam_w]`.

Use `show hJ ε (A.wb i.1) (y c') = hJ ε (B.wb i.1) (fam B.e B.z c')`. Rewrite using `[hydef, A.p4, if_neg i.2, B.w_fam]`. Use `show hJ ε (A.wb i.1) (A.wb j.1) = hJ ε (B.wb i.1) (B.wb j.1)`. Rewrite using `[A.ww, B.ww]`. Take `⟨g, hg⟩` from `wittFam ε s tt hs ht hG`.

Conclude with `⟨g, y, t, htc, fun b => hg (Sum.inl b), fun i hi => hg (Sum.inr ⟨i, hi⟩), A.p1 i0 Z Aα t, A.p4 i0 Z Aα t⟩`.
-/
theorem realize (A B : Fr ε r k) (i0 : Fin k) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det)
    (σ : ℝ) (hσ2 : σ ^ 2 = (A.T)⁻¹ - B.T * ‖(Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) (Fin.last r)‖ ^ 2) :
    ∃ g : Formalism.REAL.UJ ε, ∃ y : Fin (r + 1) → Fin n → ℂ, ∃ t : Fin (r + 1) → ℂ,
      t ⬝ᵥ (Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) = σ ∧
      (∀ b, uMat g *ᵥ fam B.e B.z b = y b) ∧ (∀ i, i ≠ i0 → uMat g *ᵥ B.wb i = A.wb i) ∧
      (∀ a b, hJ ε (fam A.e A.z a) (y b) = Z a b) ∧
      (∀ i b, hJ ε (A.wb i) (y b) = if i = i0 then t b else 0) := by
  classical
  set L := Fin.last r with hL
  set c := Z⁻¹ *ᵥ Pi.single L 1 with hcdef
  have hZc : Z *ᵥ c = Pi.single L 1 := by rw [hcdef, mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mulVec_zero] at hZc
    have := congrFun hZc L
    simp at this
  obtain ⟨N, hNdef⟩ : ∃ N : ℂ, N = star c ⬝ᵥ c := ⟨_, rfl⟩
  have hN : N ≠ 0 := by rw [hNdef]; exact fun h => hc0 (dotProduct_star_self_eq_zero.1 h)
  obtain ⟨t, htdef⟩ : ∃ t : Fin (r + 1) → ℂ, t = ((σ : ℂ) / N) • star c := ⟨_, rfl⟩
  have htc : t ⬝ᵥ c = σ := by rw [htdef, smul_dotProduct, smul_eq_mul, ← hNdef, div_mul_cancel₀ _ hN]
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      Γ = Matrix.of fun b c' => if b = L then (if c' = L then -(B.T : ℂ) else 0) else 0 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      Q = Γ + ((A.T : ℂ)⁻¹) • vecMulVec (star (Z L)) (Z L) - vecMulVec (star t) t := ⟨_, rfl⟩
  have hAstar : star ((A.T : ℂ)⁻¹) = (A.T : ℂ)⁻¹ := by rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hBstar : star (-(B.T : ℂ)) = -(B.T : ℂ) := by rw [star_neg, Complex.star_def, Complex.conj_ofReal]
  have hQ : Qᴴ = Q := by
    ext b c'
    simp only [hQdef, hΓ, conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, of_apply,
      vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub, star_mul', star_star, hAstar]
    by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc, hBstar] <;> ring
  have hzc : Z L ⬝ᵥ c = 1 := by
    have := congrFun hZc L
    simpa [mulVec] using this
  have hΓv : Γ *ᵥ c = Pi.single L (-(B.T : ℂ) * c L) := by
    funext b
    by_cases hb : b = L
    · subst hb; simp [hΓ, mulVec, dotProduct, Finset.sum_ite_eq']
    · simp [hΓ, mulVec, dotProduct, hb]
  have hcQ : star c ⬝ᵥ (Q *ᵥ c) = 0 := by
    rw [hQdef, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dot_vmv,
      dot_vmv, hΓv, dotProduct_single, star_dotProduct_star, star_dotProduct_star, hzc, htc, smul_eq_mul,
      star_one, mul_one, mul_one]
    have h1 : star (c L) * c L = ((‖c L‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    have h2 : star (σ : ℂ) * σ = ((σ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [h2, hσ2, Pi.star_apply, show star (c L) * (-(B.T : ℂ) * c L) = -(B.T : ℂ) * (star (c L) * c L) by ring, h1]
    push_cast
    ring
  obtain ⟨Aα, hAlast, hAeq⟩ := solveHerm Z Q hZ hQ hcQ
  set y := A.yv i0 Z Aα t with hydef
  have hgram : ∀ b c', hJ ε (y b) (y c') = hJ ε (fam B.e B.z b) (fam B.e B.z c') := by
    intro b c'
    rw [hydef, A.gram i0 Z Aα t hAlast, B.gf]
    have hq := congrFun (congrFun hAeq b) c'
    rw [Matrix.add_apply] at hq
    have hQbc : Q b c' = Γ b c' + (A.T : ℂ)⁻¹ * (star (Z L b) * Z L c') - star (t b) * t c' := by
      simp [hQdef, vecMulVec_apply]
    have hΓbc : Γ b c' = if b = L ∧ c' = L then -(B.T : ℂ) else 0 := by
      rw [hΓ, of_apply]
      by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc]
    rw [← hΓbc]
    linear_combination hq + hQbc
  let s : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ := Sum.elim (fam B.e B.z) (fun i => B.wb i.1)
  let tt : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ := Sum.elim y (fun i => A.wb i.1)
  have hs : LinearIndependent ℂ s :=
    li_of_pair ε s (Sum.elim B.Fv (fun i => B.wb i.1)) 1 (by simp) (by
      rintro (a|j) (b|i)
      · simp [s, B.Fv_fam, one_apply]
      · simp [s, B.Fv_w, one_apply]
      · simp [s, B.w_fam, one_apply]
      · simp [s, B.ww, one_apply, Subtype.ext_iff])
  have ht : LinearIndependent ℂ tt :=
    li_of_pair ε tt (Sum.elim (fam A.e A.z) (fun i => A.wb i.1)) (Matrix.fromBlocks Z 0 0 1)
      (by rw [det_fromBlocks_zero₂₁, det_one, mul_one]; exact hZ) (by
      rintro (a|j) (b|i)
      · simp [tt, hydef, A.p1]
      · simp [tt, A.fam_w]
      · simp [tt, hydef, A.p4, j.2]
      · simp [tt, A.ww, one_apply, Subtype.ext_iff])
  have hG : ∀ i j, hJ ε (tt i) (tt j) = hJ ε (s i) (s j) := by
    rintro (b|i) (c'|j)
    · exact hgram b c'
    · show hJ ε (y b) (A.wb j.1) = hJ ε (fam B.e B.z b) (B.wb j.1)
      rw [swapJ (A.p4 i0 Z Aα t j.1 b), if_neg j.2, star_zero, B.fam_w]
    · show hJ ε (A.wb i.1) (y c') = hJ ε (B.wb i.1) (fam B.e B.z c')
      rw [hydef, A.p4, if_neg i.2, B.w_fam]
    · show hJ ε (A.wb i.1) (A.wb j.1) = hJ ε (B.wb i.1) (B.wb j.1)
      rw [A.ww, B.ww]
  obtain ⟨g, hg⟩ := wittFam ε s tt hs ht hG
  exact ⟨g, y, t, htc, fun b => hg (Sum.inl b), fun i hi => hg (Sum.inr ⟨i, hi⟩), A.p1 i0 Z Aα t,
    A.p4 i0 Z Aα t⟩

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
