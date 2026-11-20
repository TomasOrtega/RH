import Mathlib
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds

open Formalism.BasicNotions Formalism.MainNotions.S
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoOrthHyp

open Matrix

/- English proof (translation)
Use `set e : Fin S.rank ≃ Fin n := finCongr h with he`. Use `set M : Matrix (Fin n) (Fin n) E := ((C⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hM`. Use `set i₀ : Fin n := ⟨0, hn⟩ with hi₀`. Use `⟨∑ j : Fin n, M j i₀ • S.frame (e.symm j), ?_⟩` and prove the remaining obligations. Establish `hCM : C.1 * M = 1`.

Rewrite using `[hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hstar : (C.1.map (starRingEnd E))ᵀ = C.1ᴴ` using `rfl`. Establish `hprod : Mᴴ * S.gram.reindex e e * M = (C.1 * M)ᴴ * (C.1 * M)`. Rewrite using `[← hC, hstar, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `key : (Mᴴ * S.gram.reindex e e * M) i₀ i₀ = 1`. Rewrite using `[hprod, hCM]`. Simplify using the standard rewrite rules. Rewrite using `[← key]`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply, HSpace.gram, starRingEnd_apply]`.

Simplify using `only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_norm_one {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (n : ℕ) (h : S.rank = n)
    (hn : 0 < n) (C : GL (Fin n) E)
    (hC : (C.1.map (starRingEnd E))ᵀ * C.1 = S.gram.reindex (finCongr h) (finCongr h)) :
    ∃ x : S.V, S.hT x x = 1 := by
  classical
  set e : Fin S.rank ≃ Fin n := finCongr h with he
  set M : Matrix (Fin n) (Fin n) E := ((C⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hM
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  refine ⟨∑ j : Fin n, M j i₀ • S.frame (e.symm j), ?_⟩
  have hCM : C.1 * M = 1 := by
    rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hstar : (C.1.map (starRingEnd E))ᵀ = C.1ᴴ := rfl
  have hprod : Mᴴ * S.gram.reindex e e * M = (C.1 * M)ᴴ * (C.1 * M) := by
    rw [← hC, hstar, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have key : (Mᴴ * S.gram.reindex e e * M) i₀ i₀ = 1 := by
    rw [hprod, hCM]
    simp
  rw [← key]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Use `D.host.isCMField_hostE` as an intermediate fact. Take `⟨ψ⟩` from `(inferInstance : Nonempty (D.host.E →+* ℂ))`. Apply `ψ.injective` to reduce the goal to its premises. Establish `h1 : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y)` using `(D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)`. Rewrite using `[h1]`.

Conclude with `NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ x`.
-/
theorem star_eq_hostConj (D : D7) (x : D.host.E) : starRingEnd D.host.E x = D.host.conj x := by
  have := D.host.isCMField_hostE
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  apply ψ.injective
  have h1 : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  rw [h1]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ x

/- English proof (translation)
Introduce `D hF`. Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Establish `hi : (0 : ℕ) ≤ D.R.m` using `Nat.zero_le _`. Take `⟨C, hC, -⟩` from `hF.val0.de`. Establish `hN : 0 < D.R.N 0` using `by show 0 < D.R.k + 0 * (D.R.t + 1)`.

Use `D.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hC' : (C.1.map (starRingEnd D.host.E))ᵀ * C.1 = (D.sp.X 0).gram.reindex (finCongr (Formalism.L2.Forms.rankN D 0 hi)) (finCongr (Formalism.L2.Forms.rankN D 0 hi))` using `hC`. Take `⟨x, hx⟩` from `exists_norm_one (D.sp.X 0) (D.R.N 0) (Formalism.L2.Forms.rankN D 0 hi) hN C hC'`. Establish `hπ : (hF.atT.piU : D.host.E) * D.host.conj (hF.atT.piU : D.host.E) = ((D.mem D.u₀).A.T : D.host.E)` using `hF.atT.piU_norm`.

Establish `hT0 : ((D.mem D.u₀).A.T : D.host.E) ≠ 0`. Rewrite using `[← D.sp_T]`. Conclude with `D.sp.T_prime.ne_zero` after adjusting the coercions. Establish `hsym : ∀ a b : (VS D).V, (VS D).hT a b = 0 → (VS D).hT b a = 0`. Introduce `a b hab`.

Rewrite using `[← (VS D).herm.eq a b, hab, map_zero]`. Establish `hvv : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) = ((D.mem D.u₀).A.T : D.host.E)`. Rewrite using `[D.sp.iXY_isom 0 hm]`. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hx, mul_one, RingHom.id_apply, star_eq_hostConj]`. Take the linear combination `hπ`.

Establish `hvz : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) D.sp.zm = 0` using `D.sp.zm_orth _`. Establish `hzv` using `hsym _ _ hvz`. Establish `hzz : (VS D).hT D.sp.zm D.sp.zm = -((D.mem D.u₀).A.T : D.host.E)`. Rewrite using `[D.sp.zm_norm, D.sp_T]`. Use `⟨D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Establish `h1 : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm) D.sp.zm = 0`. Rewrite using `[h0, map_zero, LinearMap.zero_apply]`. Rewrite `h1` using `[map_add, LinearMap.add_apply, hvz, hzz, zero_add, neg_eq_zero]`. Conclude with `hT0 h1`.

Simplify using `only [map_add, LinearMap.add_apply, hvv, hvz, hzv, hzz]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i`. Prove the components needed by the constructor for the conclusion. Rewrite using `[map_add, hsym _ _ (D.sp.hyp_orthX i _).1, hsym _ _ (D.sp.hyp_orthz i).1, add_zero]`.

Rewrite using `[map_add, hsym _ _ (D.sp.hyp_orthX i _).2, hsym _ _ (D.sp.hyp_orthz i).2, add_zero]`.
-/
theorem exists_isotropic_orth_hyp : ∀ (D : D7), Formalism.L2.Forms.Forms0 D D.u₀ → ∃ w : (VS D).V, w ≠ 0 ∧ (VS D).hT w w = 0 ∧ ∀ i, (VS D).hT (D.sp.hypE i) w = 0 ∧ (VS D).hT (D.sp.hypF i) w = 0 := by
  intro D hF
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hi : (0 : ℕ) ≤ D.R.m := Nat.zero_le _
  obtain ⟨C, hC, -⟩ := hF.val0.de
  have hN : 0 < D.R.N 0 := by
    show 0 < D.R.k + 0 * (D.R.t + 1)
    have := D.R.m_add_three_le_k
    omega
  have hC' : (C.1.map (starRingEnd D.host.E))ᵀ * C.1 =
      (D.sp.X 0).gram.reindex (finCongr (Formalism.L2.Forms.rankN D 0 hi))
        (finCongr (Formalism.L2.Forms.rankN D 0 hi)) := hC
  obtain ⟨x, hx⟩ := exists_norm_one (D.sp.X 0) (D.R.N 0) (Formalism.L2.Forms.rankN D 0 hi) hN C hC'
  have hπ : (hF.atT.piU : D.host.E) * D.host.conj (hF.atT.piU : D.host.E) =
      ((D.mem D.u₀).A.T : D.host.E) := hF.atT.piU_norm
  have hT0 : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
    rw [← D.sp_T]
    exact_mod_cast D.sp.T_prime.ne_zero
  have hsym : ∀ a b : (VS D).V, (VS D).hT a b = 0 → (VS D).hT b a = 0 := by
    intro a b hab
    rw [← (VS D).herm.eq a b, hab, map_zero]
  have hvv : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x))
      (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) = ((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.iXY_isom 0 hm]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hx, mul_one, RingHom.id_apply,
      star_eq_hostConj]
    linear_combination hπ
  have hvz : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) D.sp.zm = 0 := D.sp.zm_orth _
  have hzv := hsym _ _ hvz
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.zm_norm, D.sp_T]
  refine ⟨D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm, ?_, ?_, ?_⟩
  · intro h0
    have h1 : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm) D.sp.zm = 0 := by
      rw [h0, map_zero, LinearMap.zero_apply]
    rw [map_add, LinearMap.add_apply, hvz, hzz, zero_add, neg_eq_zero] at h1
    exact hT0 h1
  · simp only [map_add, LinearMap.add_apply, hvv, hvz, hzv, hzz]
    ring
  · intro i
    constructor
    · rw [map_add, hsym _ _ (D.sp.hyp_orthX i _).1, hsym _ _ (D.sp.hyp_orthz i).1, add_zero]
    · rw [map_add, hsym _ _ (D.sp.hyp_orthX i _).2, hsym _ _ (D.sp.hyp_orthz i).2, add_zero]

end GlobalTheory.IsoOrthHyp
