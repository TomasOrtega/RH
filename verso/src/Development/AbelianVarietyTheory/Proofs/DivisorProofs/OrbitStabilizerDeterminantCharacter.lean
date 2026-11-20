import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt

noncomputable section

open Matrix

namespace GlobalTheory.StabPair

/- English proof (translation)
Rewrite using `[vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]`.
-/
theorem det_one_add_vecMulVec {m : Type} [Fintype m] [DecidableEq m] {k : Type} [Field k] (a b : m → k) :
    (1 + vecMulVec a b).det = 1 + b ⬝ᵥ a := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

/- English proof (translation)
Use `set e := GlobalTheory.ThK.MidJac.e2 x x' with he`. Distinguish the cases in `h : ∃ i j, X i (e ⟨1, j⟩) ≠ 0`. Take `⟨I, j, hIj⟩` from `h set J : Fin (x + x') := e ⟨1, j⟩ with hJ set c : k := ((t⁻¹ : kˣ) : k) - 1 with hc set u : Fin (x + x') → k := Pi.single J 1 with hu set ψ : Fin n → k := Pi.single I (X I J)⁻¹ with hψ`. Establish `hψu : ψ ⬝ᵥ (X *ᵥ u) = 1`. Rewrite using `[hψ, single_dotProduct, hu]`.

Simplify using `[mulVec, dotProduct_single, inv_mul_cancel₀ hIj]`. Use `set G0 : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (c • (X *ᵥ u)) ψ with hG0`. Use `set P : Matrix (Fin (x + x')) (Fin (x + x')) k := 1 + vecMulVec (ψ ᵥ* X) (c • u) with hP`. Establish `hdetG0 : G0.det = ((t⁻¹ : kˣ) : k)`. Rewrite using `[hG0, det_one_add_vecMulVec, dotProduct_smul, hψu, hc]`.

Simplify using the standard rewrite rules. Establish `hdetP : P.det = ((t⁻¹ : kˣ) : k)`. Rewrite using `[hP, det_one_add_vecMulVec, smul_dotProduct, hc]`. Establish `: u ⬝ᵥ (ψ ᵥ* X) = ψ ⬝ᵥ (X *ᵥ u)`. Rewrite using `[dotProduct_comm, dotProduct_mulVec]`.

Rewrite using `[this, hψu]`. Simplify using the standard rewrite rules. Establish `hne : ((t⁻¹ : kˣ) : k) ≠ 0` using `Units.ne_zero _`. Use `set g0 : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero G0 (hdetG0 ▸ hne)`. Use `set pG : GL (Fin (x + x')) k := Matrix.GeneralLinearGroup.mkOfDetNeZero P (hdetP ▸ hne)`.

Establish `hpG : (pG : Matrix _ _ k) = P` using `rfl`. Establish `hg0 : (g0 : Matrix _ _ k) = G0` using `rfl`. Establish `hmem : pG ∈ GlobalTheory.SmGL.parab k e`. Rewrite using `[GlobalTheory.SmGL.mem_parab]`. Introduce `a b hab`.

Establish `hb : b ≠ J`. Introduce and unpack `rfl`. Rewrite `hab` using `[hJ, GlobalTheory.SmGL.blk_apply]`. Use `(GlobalTheory.SmGL.blk e a).isLt` as an intermediate fact. Rewrite `hab` using `[Fin.lt_def]`.

Simplify using `at hab`. Use linear arithmetic over natural numbers and integers. Establish `hab' : a ≠ b` using `by rintro rfl; exact lt_irrefl _ hab`. Rewrite using `[hpG, hP]`. Simplify using `[vecMulVec_apply, hu, Pi.single_apply, hb, one_apply, hab']`.

Use `⟨g0⁻¹, ⟨pG, hmem⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hT : (P)ᵀ = 1 + vecMulVec (c • u) (ψ ᵥ* X)`. Rewrite using `[hP, transpose_add, transpose_one, transpose_vecMulVec]`. Establish `hXQ : X * (1 + vecMulVec (c • u) (ψ ᵥ* X)) = G0 * X`. Rewrite using `[hG0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_vecMulVec, vecMulVec_mul, mulVec_smul]`.

Express the relevant statement in the definitionally equal form `((g0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X * Matrix.transpose (pG : Matrix (Fin (x + x')) (Fin (x + x')) k) = X`. Rewrite using `[hpG, hT, Matrix.mul_assoc, hXQ, ← Matrix.mul_assoc, ← hg0, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Establish `hblk : GlobalTheory.SmGL.leviProj k e ⟨pG, hmem⟩ 0 = 1`. Apply `Matrix.GeneralLinearGroup.ext` to reduce the goal to its premises. Introduce `i i'`.

Rewrite using `[GlobalTheory.SmGL.leviProj_apply]`. Establish `hne' : e ⟨0, i'⟩ ≠ J`. Rewrite using `[hJ]`. Introduce `hh`. Use `congrArg Sigma.fst (e.injective hh)` as an intermediate fact.

Simplify using `at this`. Simplify using `only [hpG, hP, Matrix.add_apply, vecMulVec_apply, Pi.smul_apply, hu, Pi.single_apply, hne', if_false, smul_eq_mul, mul_zero, add_zero, Units.val_one]`. Distinguish the cases in `hii : i = i'`. Substitute `hii` using the available equality. Simplify using the standard rewrite rules.

Establish `: e ⟨0, i⟩ ≠ e ⟨0, i'⟩` using `fun hh => hii (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective hh)).2)`. Rewrite using `[one_apply_ne this, one_apply_ne hii]`. Rewrite using `[hblk, map_one, mul_one, map_inv]`. Establish `: Matrix.GeneralLinearGroup.det g0 = t⁻¹` using `by ext; rw [Matrix.GeneralLinearGroup.val_det_apply, hg0, hdetG0]`. Rewrite using `[this, inv_inv]`.

Use `push_neg at h`. Set `Y : Matrix (Fin n) (Fin x) k` to `fun a i => X a (e ⟨0, i⟩)`. Establish `hker : LinearMap.ker (Yᵀ).mulVecLin ≠ ⊥` using `LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hx)`. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hker`. Rewrite `hw` using `[LinearMap.mem_ker, Matrix.mulVecLin_apply]`.

Establish `hwX : w ᵥ* X = 0`. Use function extensionality and compare the values at `b`. Take `⟨⟨a, i⟩, rfl⟩` from `e.surjective b`. Use `match a, i with`. Consider the case `0, i`.

Establish `hi : ∑ r, X r (e ⟨0, i⟩) * w r = 0` using `congrFun hw i`. Simplify using `only [vecMul, dotProduct, Pi.zero_apply]`. Rewrite using `[← hi]`. Conclude with `Finset.sum_congr rfl (fun r _ => mul_comm _ _)`. Consider the case `1, i => simp [vecMul, dotProduct, h]`.

Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r, w r ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hw0 (funext hcon)`. Use `set v : Fin n → k := Pi.single r (w r)⁻¹ with hv`.

Establish `hwv : w ⬝ᵥ v = 1` using `by rw [hv, dotProduct_single, mul_inv_cancel₀ hr]`. Use `set G : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (((t : k) - 1) • v) w with hG`. Establish `hdetG : G.det = (t : k)`. Rewrite using `[hG, det_one_add_vecMulVec, dotProduct_smul, hwv]`. Simplify using the standard rewrite rules.

Use `set gG : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero G (hdetG ▸ Units.ne_zero t)`. Establish `hgG : (gG : Matrix (Fin n) (Fin n) k) = G` using `rfl`. Use `⟨gG, 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[OneMemClass.coe_one, Units.val_one, transpose_one, Matrix.mul_one, hgG, hG, Matrix.add_mul, Matrix.one_mul, vecMulVec_mul, hwX]`. Use extensionality with `a b`.

Simplify using `[vecMulVec_apply]`. Rewrite using `[map_one, Pi.one_apply, map_one, mul_one] ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hgG]`. Conclude with `hdetG`.
-/
theorem stab (k : Type) [Field k] (n x x' : ℕ) (hx : x < n) (t : kˣ) (X : Matrix (Fin n) (Fin (x + x')) k) :
    ∃ (g : GL (Fin n) k) (p : GlobalTheory.SmGL.parab k (GlobalTheory.ThK.MidJac.e2 x x')),
      (g : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose ((p : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) = X ∧
      Matrix.GeneralLinearGroup.det g *
        Matrix.GeneralLinearGroup.det (GlobalTheory.SmGL.leviProj k (GlobalTheory.ThK.MidJac.e2 x x') p 0) = t := by
  set e := GlobalTheory.ThK.MidJac.e2 x x' with he
  by_cases h : ∃ i j, X i (e ⟨1, j⟩) ≠ 0
  · obtain ⟨I, j, hIj⟩ := h
    set J : Fin (x + x') := e ⟨1, j⟩ with hJ
    set c : k := ((t⁻¹ : kˣ) : k) - 1 with hc
    set u : Fin (x + x') → k := Pi.single J 1 with hu
    set ψ : Fin n → k := Pi.single I (X I J)⁻¹ with hψ
    have hψu : ψ ⬝ᵥ (X *ᵥ u) = 1 := by
      rw [hψ, single_dotProduct, hu]
      simp [mulVec, dotProduct_single, inv_mul_cancel₀ hIj]
    set G0 : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (c • (X *ᵥ u)) ψ with hG0
    set P : Matrix (Fin (x + x')) (Fin (x + x')) k := 1 + vecMulVec (ψ ᵥ* X) (c • u) with hP
    have hdetG0 : G0.det = ((t⁻¹ : kˣ) : k) := by
      rw [hG0, det_one_add_vecMulVec, dotProduct_smul, hψu, hc]; simp
    have hdetP : P.det = ((t⁻¹ : kˣ) : k) := by
      rw [hP, det_one_add_vecMulVec, smul_dotProduct, hc]
      have : u ⬝ᵥ (ψ ᵥ* X) = ψ ⬝ᵥ (X *ᵥ u) := by
        rw [dotProduct_comm, dotProduct_mulVec]
      rw [this, hψu]; simp
    have hne : ((t⁻¹ : kˣ) : k) ≠ 0 := Units.ne_zero _
    set g0 : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero G0 (hdetG0 ▸ hne)
    set pG : GL (Fin (x + x')) k := Matrix.GeneralLinearGroup.mkOfDetNeZero P (hdetP ▸ hne)
    have hpG : (pG : Matrix _ _ k) = P := rfl
    have hg0 : (g0 : Matrix _ _ k) = G0 := rfl
    have hmem : pG ∈ GlobalTheory.SmGL.parab k e := by
      rw [GlobalTheory.SmGL.mem_parab]
      intro a b hab
      have hb : b ≠ J := by
        rintro rfl
        rw [hJ, GlobalTheory.SmGL.blk_apply] at hab
        have := (GlobalTheory.SmGL.blk e a).isLt
        rw [Fin.lt_def] at hab
        simp at hab
        omega
      have hab' : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
      rw [hpG, hP]
      simp [vecMulVec_apply, hu, Pi.single_apply, hb, one_apply, hab']
    refine ⟨g0⁻¹, ⟨pG, hmem⟩, ?_, ?_⟩
    · have hT : (P)ᵀ = 1 + vecMulVec (c • u) (ψ ᵥ* X) := by
        rw [hP, transpose_add, transpose_one, transpose_vecMulVec]
      have hXQ : X * (1 + vecMulVec (c • u) (ψ ᵥ* X)) = G0 * X := by
        rw [hG0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_vecMulVec, vecMulVec_mul, mulVec_smul]
      change ((g0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose (pG : Matrix (Fin (x + x')) (Fin (x + x')) k) = X
      rw [hpG, hT, Matrix.mul_assoc, hXQ, ← Matrix.mul_assoc, ← hg0, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    · have hblk : GlobalTheory.SmGL.leviProj k e ⟨pG, hmem⟩ 0 = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i i'
        rw [GlobalTheory.SmGL.leviProj_apply]
        have hne' : e ⟨0, i'⟩ ≠ J := by
          rw [hJ]; intro hh
          have := congrArg Sigma.fst (e.injective hh)
          simp at this
        simp only [hpG, hP, Matrix.add_apply, vecMulVec_apply, Pi.smul_apply, hu, Pi.single_apply, hne',
          if_false, smul_eq_mul, mul_zero, add_zero, Units.val_one]
        by_cases hii : i = i'
        · subst hii; simp
        · have : e ⟨0, i⟩ ≠ e ⟨0, i'⟩ := fun hh => hii (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective hh)).2)
          rw [one_apply_ne this, one_apply_ne hii]
      rw [hblk, map_one, mul_one, map_inv]
      have : Matrix.GeneralLinearGroup.det g0 = t⁻¹ := by
        ext; rw [Matrix.GeneralLinearGroup.val_det_apply, hg0, hdetG0]
      rw [this, inv_inv]
  · push_neg at h

    let Y : Matrix (Fin n) (Fin x) k := fun a i => X a (e ⟨0, i⟩)
    have hker : LinearMap.ker (Yᵀ).mulVecLin ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hx)
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    have hwX : w ᵥ* X = 0 := by
      funext b
      obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective b
      match a, i with
      | 0, i =>
        have hi : ∑ r, X r (e ⟨0, i⟩) * w r = 0 := congrFun hw i
        simp only [vecMul, dotProduct, Pi.zero_apply]
        rw [← hi]
        exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
      | 1, i => simp [vecMul, dotProduct, h]
    obtain ⟨r, hr⟩ : ∃ r, w r ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hw0 (funext hcon)
    set v : Fin n → k := Pi.single r (w r)⁻¹ with hv
    have hwv : w ⬝ᵥ v = 1 := by rw [hv, dotProduct_single, mul_inv_cancel₀ hr]
    set G : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (((t : k) - 1) • v) w with hG
    have hdetG : G.det = (t : k) := by
      rw [hG, det_one_add_vecMulVec, dotProduct_smul, hwv]; simp
    set gG : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero G (hdetG ▸ Units.ne_zero t)
    have hgG : (gG : Matrix (Fin n) (Fin n) k) = G := rfl
    refine ⟨gG, 1, ?_, ?_⟩
    · rw [OneMemClass.coe_one, Units.val_one, transpose_one, Matrix.mul_one, hgG, hG, Matrix.add_mul,
        Matrix.one_mul, vecMulVec_mul, hwX]
      ext a b; simp [vecMulVec_apply]
    · rw [map_one, Pi.one_apply, map_one, mul_one]
      ext; rw [Matrix.GeneralLinearGroup.val_det_apply, hgG]; exact hdetG

end GlobalTheory.StabPair
