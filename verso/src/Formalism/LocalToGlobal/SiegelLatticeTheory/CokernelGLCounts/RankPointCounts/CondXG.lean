import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentMatrixMapSecondComponent

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ}

/- English proof (translation)
Conclude with `fun h => g.q_irr.ne_zero (Subtype.ext h)`.
-/
theorem q_ne (g : Formalism.MainNotions.S.Loc.SplitG M.L) : ((g.q : F)) ≠ 0 := by
  exact fun h => g.q_irr.ne_zero (Subtype.ext h)

/- English proof (translation)
Establish `hq : (g.q : F) ≠ 0` using `q_ne M g`. Establish `hπ1 : ∀ x : E, π1 M g x = (g.e x).1` using `fun x => rfl`. Establish `hπ2 : ∀ x : E, π2 M g x = (g.e x).2` using `fun x => rfl`. Establish `hZ : ∀ (Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)), Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T' a b = g.e.symm ((g.e (Y a b)).1 / (g.q : F), -((g.e (Y b a)).2 / (g.q : F))) - (if a = Fin.last r ∧ b = Fin.last r then g.e.symm (-T / (g.q : F), T' / (g.q …`. Introduce `Y a b`.

Simplify using `only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, Matrix.of_apply]`. Set `Ec : Matrix (Fin (r + 1)) (Fin (r + 1)) F` to `Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0`. Establish `hZ1 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π1 M g) = (g.q : F)⁻¹ • Y.map (π1 M g) + (T / (g.q : F)) • Ec`. Introduce `Y`. Use extensionality with `a b`.

Distinguish the cases in `hab : a = Fin.last r ∧ b = Fin.last r`. Simplify using `only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_pos hab, Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_neg hab, map_zero, Prod.fst_zero, sub_zero, Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_zero, add_zero]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hZ2 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π2 M g) = -((g.q : F)⁻¹ • (Y.map (π2 M g))ᵀ) - (T' / (g.q : F)) • Ec`. Introduce `Y`. Use extensionality with `a b`. Distinguish the cases in `hab : a = Fin.last r ∧ b = Fin.last r`. Simplify using `only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_pos hab, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_one]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_neg hab, map_zero, Prod.snd_zero, sub_zero, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hE : ∀ φ : E →+* F, L.map φ * Ec * P.map φ = Ec`. Introduce `φ`.

Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Ec, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Apply the tactic sequence `simp only [and_self, if_true, mul_one, hL, hP] split_ifs <;> simp_all`.

Introduce `k _ hk`. Simplify using `[hk]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Simplify using `[hl]`.

Simplify using the standard rewrite rules. Establish `hinv : (g.q : F)⁻¹ ≠ 0` using `inv_ne_zero hq`. Prove the components needed by the constructor for the conclusion. Establish `hmap` using `congrArg (fun Z => Matrix.map Z (π1 M g)) h`. Simplify using `only [Matrix.map_mul] at hmap`.

Rewrite `hmap` using `[hZ1, hZ1]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hE] at hmap`. Conclude with `smul_right_injective _ hinv (add_right_cancel hmap)`. Establish `hmap` using `congrArg (fun Z => Matrix.map Z (π2 M g)) h`. Simplify using `only [Matrix.map_mul] at hmap`.

Rewrite `hmap` using `[hZ2, hZ2]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, hE] at hmap`. Conclude with `smul_right_injective _ hinv (neg_inj.1 (sub_left_inj.1 hmap))`.
-/
theorem zzrel_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    X'.map (π1 M g) = L.map (π1 M g) * X.map (π1 M g) * P.map (π1 M g) ∧
    (X'.map (π2 M g))ᵀ = L.map (π2 M g) * (X.map (π2 M g))ᵀ * P.map (π2 M g) := by
  classical
  have hq : (g.q : F) ≠ 0 := q_ne M g
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hZ : ∀ (Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)),
      Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T' a b =
        g.e.symm ((g.e (Y a b)).1 / (g.q : F), -((g.e (Y b a)).2 / (g.q : F))) -
        (if a = Fin.last r ∧ b = Fin.last r then g.e.symm (-T / (g.q : F), T' / (g.q : F)) else 0) := by
    intro Y a b
    simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, Matrix.of_apply]
  let Ec : Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
    Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0
  have hZ1 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π1 M g) =
      (g.q : F)⁻¹ • Y.map (π1 M g) + (T / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.fst_zero, sub_zero, Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul,
        mul_zero, add_zero]
      ring
  have hZ2 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π2 M g) =
      -((g.q : F)⁻¹ • (Y.map (π2 M g))ᵀ) - (T' / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, Ec, Matrix.of_apply,
        smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.snd_zero, sub_zero, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.transpose_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_zero]
      ring
  have hE : ∀ φ : E →+* F, L.map φ * Ec * P.map φ = Ec := by
    intro φ
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Ec, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · simp only [and_self, if_true, mul_one, hL, hP]
        split_ifs <;> simp_all
      · intro k _ hk
        simp [hk]
      · simp
    · intro l _ hl
      simp [hl]
    · simp
  have hinv : (g.q : F)⁻¹ ≠ 0 := inv_ne_zero hq
  constructor
  · have hmap := congrArg (fun Z => Matrix.map Z (π1 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ1, hZ1] at hmap
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hE] at hmap
    exact smul_right_injective _ hinv (add_right_cancel hmap)
  · have hmap := congrArg (fun Z => Matrix.map Z (π2 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ2, hZ2] at hmap
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      hE] at hmap
    exact smul_right_injective _ hinv (neg_inj.1 (sub_left_inj.1 hmap))

/- English proof (translation)
Take `⟨h1, h2⟩` from `zzrel_G M g hs hL hP T T' h`. Establish `hπ1 : ∀ x : E, π1 M g x = (g.e x).1` using `fun x => rfl`. Establish `hπ2 : ∀ x : E, π2 M g x = (g.e x).2` using `fun x => rfl`. Establish `hcj : ∀ x : E, g.e ((M.L.cj : E →+* E) x) = (g.e x).swap` using `fun x => g.e_cj x`. Use extensionality with `i j`.

Apply `g.e.injective` to reduce the goal to its premises. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Establish `h1'` using `congrArg (fun A => A i j) h1`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, hπ1, Finset.sum_mul] at h1'`. Simplify using `only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.fst_sum, Prod.fst_mul, hcj, Prod.fst_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]`.

Rewrite using `[h1']`. Establish `h2'` using `congrArg (fun A => A j i) h2`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, hπ2, Finset.sum_mul] at h2'`. Simplify using `only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.snd_sum, Prod.snd_mul, hcj, Prod.snd_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]`. Rewrite using `[h2', Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem condX_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * X * uuG M g L P = X' := by
  obtain ⟨h1, h2⟩ := zzrel_G M g hs hL hP T T' h
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hcj : ∀ x : E, g.e ((M.L.cj : E →+* E) x) = (g.e x).swap := fun x => g.e_cj x
  ext i j
  apply g.e.injective
  refine Prod.ext ?_ ?_
  · have h1' := congrArg (fun A => A i j) h1
    simp only [Matrix.map_apply, Matrix.mul_apply, hπ1, Finset.sum_mul] at h1'
    simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.fst_sum,
      Prod.fst_mul, hcj, Prod.fst_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h1']
  · have h2' := congrArg (fun A => A j i) h2
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, hπ2, Finset.sum_mul] at h2'
    simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.snd_sum,
      Prod.snd_mul, hcj, Prod.snd_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h2', Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/- English proof (translation)
Establish `hm : ∀ i, mmG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0`. Introduce `i`. Simplify using `only [mmG, Matrix.of_apply, hP, hL]`. Apply the tactic sequence `split_ifs <;> simp`. Use extensionality with `i j`.

Simplify using `only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Apply the tactic sequence `simp only [and_self, if_true, hm] split_ifs <;> simp_all`. Introduce `k _ hk`.

Simplify using `[hk]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Simplify using `[hl]`. Simplify using the standard rewrite rules.
-/
theorem condM_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * cornerM c * mmG M g L P = cornerM c := by
  have hm : ∀ i, mmG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [mmG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

/- English proof (translation)
Establish `hm : ∀ i, uuG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0`. Introduce `i`. Simplify using `only [uuG, Matrix.of_apply, hP, hL]`. Apply the tactic sequence `split_ifs <;> simp`. Use extensionality with `i j`.

Simplify using `only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Apply the tactic sequence `simp only [and_self, if_true, hm] split_ifs <;> simp_all`. Introduce `k _ hk`.

Simplify using `[hk]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Simplify using `[hl]`. Simplify using the standard rewrite rules.
-/
theorem condU_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (uuG M g L P) * cornerM c * uuG M g L P = cornerM c := by
  have hm : ∀ i, uuG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [uuG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
