import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix
import Formalism.YangianSpanCharacter.YangianRelationFirst

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr9

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}

/- English proof (translation)
Establish `h` using `Wd11.ins_sandwich hx M 1`. Rewrite `h` using `[Wd11.d0_one, mul_one, mul_one]`. Conclude with `h.symm`.
-/
theorem ins_left {b : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf b x) (M : M2 (SlopeTestRemainingChoices S A)) :
    x * ins b M = ins b (d0 x * M) := by
  have h := Wd11.ins_sandwich hx M 1
  rw [Wd11.d0_one, mul_one, mul_one] at h
  exact h.symm

/- English proof (translation)
Establish `h` using `Wd11.ins_sandwich (Wd11.free_one b) M y`. Rewrite `h` using `[Wd11.d0_one, one_mul, one_mul]`. Conclude with `h.symm`.
-/
theorem ins_right (b : S) (M : M2 (SlopeTestRemainingChoices S A)) (y : SlopeTestRemainingChoices S A) :
    ins b M * y = ins b (M * d0 y) := by
  have h := Wd11.ins_sandwich (Wd11.free_one b) M y
  rw [Wd11.d0_one, one_mul, one_mul] at h
  exact h.symm

/- English proof (translation)
Establish `h` using `Wd1.sum_eU_diag (A := A) b`. Rewrite `h` using `[Fin.sum_univ_two]`. Establish `e : T 1 j = eU b 0 0 * T 1 j + eU b 1 1 * T 1 j` using `by rw [← add_mul, h, one_mul]`. Establish `l : (Rht0 b d * T : M2 (SlopeTestRemainingChoices S A)) 1 j = (d - 1)⁻¹ • (d • T 1 j - (eU b 1 0 * T 0 j + eU b 1 1 * T 1 j))`. Unfold `Rht0`.

Rewrite using `[Matrix.smul_mul, Matrix.smul_apply, Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `only [Q0, Matrix.of_apply]`. Rewrite using `[l]`. Unfold `ins`. Simplify using `only [Matrix.smul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_smul_comm, mul_zero, smul_zero, add_zero, mul_neg]`.

Rewrite using `[← smul_add, ← smul_add]`. Use `congr 1`. Rewrite using `[sub_smul, one_smul]`. Establish `e' : d • T 1 j = d • (eU b 0 0 * T 1 j) + d • (eU b 1 1 * T 1 j)` using `by rw [← smul_add, ← e]`. Rewrite using `[e']`.

Normalize the expressions using the abelian group laws.
-/
theorem rht_row (b : S) (d : ℂ) (T : M2 (SlopeTestRemainingChoices S A)) (j : Fin 2) :
    (Rht0 b d * T : M2 (SlopeTestRemainingChoices S A)) 1 j =
      ins b ((d - 1)⁻¹ • !![d • T 1 j, 0; -T 0 j, (d - 1) • T 1 j]) := by
  have h := Wd1.sum_eU_diag (A := A) b
  rw [Fin.sum_univ_two] at h
  have e : T 1 j = eU b 0 0 * T 1 j + eU b 1 1 * T 1 j := by rw [← add_mul, h, one_mul]
  have l : (Rht0 b d * T : M2 (SlopeTestRemainingChoices S A)) 1 j =
      (d - 1)⁻¹ • (d • T 1 j - (eU b 1 0 * T 0 j + eU b 1 1 * T 1 j)) := by
    unfold Rht0
    rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul,
      Matrix.one_mul, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Q0, Matrix.of_apply]
  rw [l]
  unfold ins
  simp only [Matrix.smul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_smul_comm, mul_zero, smul_zero, add_zero, mul_neg]
  rw [← smul_add, ← smul_add]
  congr 1
  rw [sub_smul, one_smul]
  have e' : d • T 1 j = d • (eU b 0 0 * T 1 j) + d • (eU b 1 1 * T 1 j) := by rw [← smul_add, ← e]
  rw [e']
  abel

/- English proof (translation)
Use `show xi * y = y * xi`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem comm_inv {B : Type*} [Ring B] {x xi y : B} (h1 : x * xi = 1) (h2 : xi * x = 1) (h : Commute x y) :
    Commute xi y := by
  show xi * y = y * xi
  calc xi * y = xi * (y * x) * xi := by rw [mul_assoc, mul_assoc, h1, mul_one]
    _ = y * xi := by rw [← h.eq, ← mul_assoc, h2, one_mul]

section Level

variable (L : LevelData A r)

/- English proof (translation)
The claim follows from `L.fns_comm x (Or.inr hx) y (Or.inr hy)`.
-/
theorem zc {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : x * y = y * x :=
  L.fns_comm x (Or.inr hx) y (Or.inr hy)

/- English proof (translation)
Simplify using `[zfns]`.
-/
theorem mζ : L.ζ ∈ zfns L := by simp [zfns]
/- English proof (translation)
Simplify using `[zfns]`.
-/
theorem mζi : L.ζi ∈ zfns L := by simp [zfns]
/- English proof (translation)
Simplify using `[zfns]`.
-/
theorem mζb : L.ζb ∈ zfns L := by simp [zfns]
/- English proof (translation)
Simplify using `[zfns]`.
-/
theorem mζbi : L.ζbi ∈ zfns L := by simp [zfns]
/- English proof (translation)
Simplify using `[zfns]`.
-/
theorem mG : L.GG ∈ zfns L := by simp [zfns]
/- English proof (translation)
Simplify using `[zfns]`.
-/
theorem mGi : L.GGi ∈ zfns L := by simp [zfns]

variable {L}

/- English proof (translation)
Rewrite using `[← hS.1, star_star]`.
-/
theorem star_ζb (hS : IsStarLevel L) : star L.ζb = L.ζ := by rw [← hS.1, star_star]

/- English proof (translation)
Rewrite using `[L.GG_def, star_sub, star_mul, star_ζb hS, hS.1, ← algebraMap_star_comm, hS.2.2]`.
-/
theorem star_GG (hS : IsStarLevel L) : star L.GG = L.GG := by
  rw [L.GG_def, star_sub, star_mul, star_ζb hS, hS.1, ← algebraMap_star_comm, hS.2.2]

/- English proof (translation)
Establish `h : star L.GGi * L.GG = 1`. Use `congrArg star L.GG_GGi` as an intermediate fact. Rewrite `this` using `[star_mul, star_GG hS, star_one]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
theorem star_GGi (hS : IsStarLevel L) : star L.GGi = L.GGi := by
  have h : star L.GGi * L.GG = 1 := by
    have := congrArg star L.GG_GGi
    rwa [star_mul, star_GG hS, star_one] at this
  calc star L.GGi = star L.GGi * (L.GG * L.GGi) := by rw [L.GG_GGi, mul_one]
    _ = L.GGi := by rw [← mul_assoc, h, one_mul]

/- English proof (translation)
Unfold `wt`. Rewrite using `[Wd11.io_star, star_mul, star_mul, star_GGi hS, star_ζb hS, hS.1]`. Use `congr 1`. Rewrite using `[← mul_assoc, zc L (mGi L) (mζ L), mul_assoc, zc L (mGi L) (mζb L), ← mul_assoc]`.
-/
theorem star_wt (hS : IsStarLevel L) : star (wt L : SlopeTestRemainingChoices S A) = wt L := by
  unfold wt
  rw [Wd11.io_star, star_mul, star_mul, star_GGi hS, star_ζb hS, hS.1]
  congr 1
  rw [← mul_assoc, zc L (mGi L) (mζ L), mul_assoc, zc L (mGi L) (mζb L), ← mul_assoc]

end Level

section Frame

variable {L : LevelData A r} {f : FrameData S A}

/- English proof (translation)
Use `show io x * io y = io y * io x`. Rewrite using `[← Wd11.io_mul, ← Wd11.io_mul, h]`.
-/
theorem io_comm {x y : A} (h : x * y = y * x) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  show io x * io y = io y * io x
  rw [← Wd11.io_mul, ← Wd11.io_mul, h]

/- English proof (translation)
Unfold `wt`. Rewrite using `[Wd11.io_mul, Wd11.io_mul]`. Conclude with `((h.c_fn _ (mζ L)).mul_right (h.c_fn _ (mζb L))).mul_right (h.c_fn _ (mGi L))`.
-/
theorem c_wt (h : IsFrame L f) : Commute f.c (wt L) := by
  unfold wt
  rw [Wd11.io_mul, Wd11.io_mul]
  exact ((h.c_fn _ (mζ L)).mul_right (h.c_fn _ (mζb L))).mul_right (h.c_fn _ (mGi L))

/- English proof (translation)
Unfold `FrameData.d`. Rewrite using `[star_mul, star_pow, star_wt hS, h.c_star]`. Conclude with `((c_wt h).pow_right _).eq`.
-/
theorem star_d (hS : IsStarLevel L) (h : IsFrame L f) : star (f.d L) = f.d L := by
  unfold FrameData.d
  rw [star_mul, star_pow, star_wt hS, h.c_star]
  exact ((c_wt h).pow_right _).eq

/- English proof (translation)
Unfold `wti wt`. Rewrite using `[← Wd11.io_mul, ← Wd11.io_one]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = L.GG * ((L.ζi * L.ζ) * (L.ζbi * L.ζb)) * L.GGi := by`. Rewrite using `[zc L (mζbi L) (mζ L)]`. Simplify using `only [mul_assoc]`. Use `_ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]`.
-/
theorem wti_wt : (wti L : SlopeTestRemainingChoices S A) * wt L = 1 := by
  unfold wti wt
  rw [← Wd11.io_mul, ← Wd11.io_one]
  congr 1
  calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = L.GG * (L.ζi * (L.ζbi * L.ζ) * L.ζb) * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * ((L.ζi * L.ζ) * (L.ζbi * L.ζb)) * L.GGi := by
        rw [zc L (mζbi L) (mζ L)]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]

/- English proof (translation)
Unfold `wti wt`. Rewrite using `[← Wd11.io_mul, ← Wd11.io_one]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = L.ζ * (L.ζb * L.ζi) * L.ζbi := by rw [L.GGi_GG, mul_one]; simp only [mul_assoc]`. Use `_ = (L.ζ * L.ζi) * (L.ζb * L.ζbi) := by rw [zc L (mζb L) (mζi L)]; simp only [mul_assoc]`. Use `_ = 1 := by rw [L.ζ_ζi, L.ζb_ζbi, mul_one]`.
-/
theorem wt_wti : (wt L : SlopeTestRemainingChoices S A) * wti L = 1 := by
  unfold wti wt
  rw [← Wd11.io_mul, ← Wd11.io_one]
  congr 1
  calc L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = L.ζ * L.ζb * (L.GGi * L.GG) * L.ζi * L.ζbi := by
        simp only [mul_assoc]
    _ = L.ζ * (L.ζb * L.ζi) * L.ζbi := by rw [L.GGi_GG, mul_one]; simp only [mul_assoc]
    _ = (L.ζ * L.ζi) * (L.ζb * L.ζbi) := by rw [zc L (mζb L) (mζi L)]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζ_ζi, L.ζb_ζbi, mul_one]

/- English proof (translation)
Unfold `FrameData.di FrameData.d`. Establish `c : Commute (wti L : SlopeTestRemainingChoices S A) (wt L)` using `by show _ = _`. Rewrite using `[wti_wt, wt_wti]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = 1 := by rw [← c.mul_pow, wti_wt, one_pow, mul_one, h.c_ci.2]`.
-/
theorem di_d (h : IsFrame L f) : f.di L * f.d L = 1 := by
  unfold FrameData.di FrameData.d
  have c : Commute (wti L : SlopeTestRemainingChoices S A) (wt L) := by
    show _ = _
    rw [wti_wt, wt_wti]
  calc f.ci * wti L ^ f.N * (wt L ^ f.N * f.c) = f.ci * (wti L ^ f.N * wt L ^ f.N) * f.c := by
        simp only [mul_assoc]
    _ = 1 := by rw [← c.mul_pow, wti_wt, one_pow, mul_one, h.c_ci.2]

/- English proof (translation)
Simplify using `[FrameData.hatT, hY]`.
-/
theorem hat_reg {Y : ℂ} (hY : Y ∈ f.reg) (i j : Fin 2) : f.hatT Y i j = f.F * f.TT Y i j * f.Fi := by
  simp [FrameData.hatT, hY]

/- English proof (translation)
Rewrite using `[hat_reg hY, mul_assoc, h.Fi_F, mul_one]`.
-/
theorem hat_F (h : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) (i j : Fin 2) :
    f.hatT Y i j * f.F = f.F * f.TT Y i j := by
  rw [hat_reg hY, mul_assoc, h.Fi_F, mul_one]

/- English proof (translation)
Rewrite using `[hat_reg hY, h.frame_τ Y hY, mul_assoc, h.F_Fi, mul_one]`.
-/
theorem hat_τ (h : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) : f.hatT Y 1 1 = io L.GG * f.x Y := by
  rw [hat_reg hY, h.frame_τ Y hY, mul_assoc, h.F_Fi, mul_one]

/- English proof (translation)
Establish `e` using `congrFun (congrFun (h.module.herm Y hY hr) j) i`. Rewrite `e` using `[Matrix.conjTranspose_apply, Wd11.diagScalar_mul_apply, Wd11.diagScalar_mul_apply, h.form]`. Establish `e1 : ∀ i j, star f.F * f.d L * f.F * f.TT Y i j = star f.F * (f.d L * f.hatT Y i j) * f.F`. Introduce `i j`. Rewrite using `[mul_assoc (star f.F * f.d L), ← hat_F h hY]`.

Simplify using `only [mul_assoc]`. Rewrite `e` using `[e1, e1, star_mul, star_mul, star_star, ← mul_assoc]`. Establish `s : star f.Fi * star f.F = 1` using `by rw [← star_mul, h.F_Fi, star_one]`. Establish `cancel : ∀ z, star f.Fi * (star f.F * z * f.F) * f.Fi = z`. Introduce `z`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = z := by rw [s, h.F_Fi, one_mul, mul_one]`. Rewrite using `[← cancel (star (f.d L * f.hatT Y i j)), e, cancel]`.
-/
theorem hat_herm (h : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) (hr : star Y = Y) (i j : Fin 2) :
    star (f.d L * f.hatT Y i j) = f.d L * f.hatT Y j i := by
  have e := congrFun (congrFun (h.module.herm Y hY hr) j) i
  rw [Matrix.conjTranspose_apply, Wd11.diagScalar_mul_apply, Wd11.diagScalar_mul_apply, h.form] at e
  have e1 : ∀ i j, star f.F * f.d L * f.F * f.TT Y i j = star f.F * (f.d L * f.hatT Y i j) * f.F := by
    intro i j
    rw [mul_assoc (star f.F * f.d L), ← hat_F h hY]; simp only [mul_assoc]
  rw [e1, e1, star_mul, star_mul, star_star, ← mul_assoc] at e
  have s : star f.Fi * star f.F = 1 := by rw [← star_mul, h.F_Fi, star_one]
  have cancel : ∀ z, star f.Fi * (star f.F * z * f.F) * f.Fi = z := by
    intro z
    calc star f.Fi * (star f.F * z * f.F) * f.Fi = (star f.Fi * star f.F) * z * (f.F * f.Fi) := by
          simp only [mul_assoc]
      _ = z := by rw [s, h.F_Fi, one_mul, mul_one]
  rw [← cancel (star (f.d L * f.hatT Y i j)), e, cancel]

/- English proof (translation)
Take `⟨H, Hl⟩` from `frame_gives_one_letter_hyps A S r L f h`. Establish `h1' : Y - 1 + 1 ∈ f.inv` using `by rwa [sub_add_cancel]`. Establish `hr' : star (Y - 1) = Y - 1` using `by rw [star_sub, hr, star_one]`. Establish `adj` using `adjoint_l_shift_relation ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv (f.d L) H (star_d hS h) (Y - 1) h2 h1' (hat_herm h (h.inv_reg h2) hr')`. Rewrite `adj` using `[Hl _ h2 h1', sub_add_cancel]`.

Unfold `FrameData.m`. Rewrite using `[mul_assoc, ← adj, ← mul_assoc, di_d h, one_mul]`.
-/
theorem hat_m (hS : IsStarLevel L) (h : IsFrame L f) {Y : ℂ} (hr : star Y = Y) (h1 : Y ∈ f.inv)
    (h2 : Y - 1 ∈ f.inv) : mf f.hatT (fun Y => io L.GGi * f.xi Y) Y = f.m L Y := by
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  have h1' : Y - 1 + 1 ∈ f.inv := by rwa [sub_add_cancel]
  have hr' : star (Y - 1) = Y - 1 := by rw [star_sub, hr, star_one]
  have adj := adjoint_l_shift_relation ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv (f.d L) H (star_d hS h) (Y - 1) h2 h1'
    (hat_herm h (h.inv_reg h2) hr')
  rw [Hl _ h2 h1', sub_add_cancel] at adj
  unfold FrameData.m
  rw [mul_assoc, ← adj, ← mul_assoc, di_d h, one_mul]

/- English proof (translation)
Take `⟨H, -⟩` from `frame_gives_one_letter_hyps A S r L f h`. Take `⟨-, -, -, h3, -, -⟩` from `H`. Rewrite using `[← hat_m hS h hr h1 h2, ← hat_τ h (h.inv_reg h1)]`. Unfold `mf`. Rewrite using `[← mul_assoc, (h3 Y h1).1, one_mul]`.
-/
theorem frameM (hS : IsStarLevel L) (h : IsFrame L f) {Y : ℂ} (hr : star Y = Y) (h1 : Y ∈ f.inv)
    (h2 : Y - 1 ∈ f.inv) : f.hatT Y 0 1 = io L.GG * f.x Y * f.m L Y := by
  obtain ⟨H, -⟩ := frame_gives_one_letter_hyps A S r L f h
  obtain ⟨-, -, -, h3, -, -⟩ := H
  rw [← hat_m hS h hr h1 h2, ← hat_τ h (h.inv_reg h1)]
  unfold mf
  rw [← mul_assoc, (h3 Y h1).1, one_mul]

end Frame

section Free

variable {b : S}

/- English proof (translation)
Introduce `i j` and use `(hx i j).add_right (hy i j)`.
-/
theorem free_add {x y : SlopeTestRemainingChoices S A} (hx : FreeOf b x) (hy : FreeOf b y) : FreeOf b (x + y) :=
  fun i j => (hx i j).add_right (hy i j)

/- English proof (translation)
Introduce `i j` and use `(hx i j).neg_right`.
-/
theorem free_neg {x : SlopeTestRemainingChoices S A} (hx : FreeOf b x) : FreeOf b (-x) :=
  fun i j => (hx i j).neg_right

/- English proof (translation)
Introduce `i j` and use `(hx i j).smul_right c`.
-/
theorem free_smul {x : SlopeTestRemainingChoices S A} (c : ℂ) (hx : FreeOf b x) : FreeOf b (c • x) :=
  fun i j => (hx i j).smul_right c

/- English proof (translation)
Introduce `i j` and use `(hx i j).pow_right n`.
-/
theorem free_pow {x : SlopeTestRemainingChoices S A} (hx : FreeOf b x) (n : ℕ) : FreeOf b (x ^ n) :=
  fun i j => (hx i j).pow_right n

/- English proof (translation)
Introduce `i j`. Establish `h` using `(hx j i).star_star`. Rewrite `h` using `[Wd1.star_eU]`. Then use the resulting hypothesis.
-/
theorem free_star {x : SlopeTestRemainingChoices S A} (hx : FreeOf b x) : FreeOf b (star x) := by
  intro i j
  have h := (hx j i).star_star
  rwa [Wd1.star_eU] at h

/- English proof (translation)
Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `hp`. Conclude with `hq`. Conclude with `hs`.

Conclude with `ht`.
-/
theorem freeOf2_matrix_entries {p q s t : SlopeTestRemainingChoices S A} (hp : FreeOf b p) (hq : FreeOf b q) (hs : FreeOf b s)
    (ht : FreeOf b t) : FreeOf2 b !![p, q; s, t] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact hp
  · exact hq
  · exact hs
  · exact ht

variable {L : LevelData A r} {f : FrameData S A}

/- English proof (translation)
The claim follows from `free_add (Wd11.free_io b _) (Wd11.free_mul (Wd11.free_io b _) (hf.2.2.2.2.2.2.2.2 Y))`.
-/
theorem free_l (hf : f.Free b) (Y : ℂ) : FreeOf b (f.l L Y) :=
  free_add (Wd11.free_io b _) (Wd11.free_mul (Wd11.free_io b _) (hf.2.2.2.2.2.2.2.2 Y))

/- English proof (translation)
The claim follows from `Wd11.free_mul (Wd11.free_mul (Wd11.free_mul hf.2.2.2.2.2.2.2.1 (free_pow (Wd11.free_io b _) _)) (free_star (free_l hf _))) (Wd11.free_mul (free_pow (Wd11.free_io b _) _) hf.2.2.2.2.2.2.1)`.
-/
theorem free_m (hf : f.Free b) (Y : ℂ) : FreeOf b (f.m L Y) :=
  Wd11.free_mul (Wd11.free_mul (Wd11.free_mul hf.2.2.2.2.2.2.2.1 (free_pow (Wd11.free_io b _) _))
    (free_star (free_l hf _))) (Wd11.free_mul (free_pow (Wd11.free_io b _) _) hf.2.2.2.2.2.2.1)

end Free

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [d0]`.
-/
theorem d0_eq (y : SlopeTestRemainingChoices S A) : d0 y = !![y, 0; 0, y] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d0]

/- English proof (translation)
Substitute `hp hq hs ht` using the available equality. Both sides reduce to the same expression.
-/
theorem mk2 {B : Type*} {p q s t p' q' s' t' : B} (hp : p = p') (hq : q = q') (hs : s = s') (ht : t = t') :
    !![p, q; s, t] = !![p', q'; s', t'] := by
  subst hp hq hs ht; rfl

/- English proof (translation)
Establish `e` using `congrArg (fun z => τbi * z) hR`. Simplify using `only [hm, mul_smul_comm, mul_sub] at e`. Establish `a1 : τbi * (τb * m * τ) = m * τ` using `by rw [mul_assoc, ← mul_assoc, h1, one_mul]`. Establish `a2 : τbi * (τ * (τb * m)) = τ * m`. Rewrite using `[← mul_assoc τ, ← hc.eq, mul_assoc, ← mul_assoc, h1, one_mul]`.

Establish `a3 : τbi * (τb * t12) = t12` using `by rw [← mul_assoc, h1, one_mul]`. Rewrite `e` using `[a1, a2, a3]`. Then use the resulting hypothesis.
-/
theorem tau_key {B : Type*} [Ring B] [Algebra ℂ B] {τb τbi τ t12b t12 m : B} {d : ℂ} (h1 : τbi * τb = 1)
    (hc : Commute τb τ) (hm : t12b = τb * m)
    (hR : d • (t12b * τ - τ * t12b) = τb * t12 - τ * t12b) : d • (m * τ - τ * m) = t12 - τ * m := by
  have e := congrArg (fun z => τbi * z) hR
  simp only [hm, mul_smul_comm, mul_sub] at e
  have a1 : τbi * (τb * m * τ) = m * τ := by rw [mul_assoc, ← mul_assoc, h1, one_mul]
  have a2 : τbi * (τ * (τb * m)) = τ * m := by
    rw [← mul_assoc τ, ← hc.eq, mul_assoc, ← mul_assoc, h1, one_mul]
  have a3 : τbi * (τb * t12) = t12 := by rw [← mul_assoc, h1, one_mul]
  rwa [a1, a2, a3] at e

/- English proof (translation)
Rewrite using `[Matrix.mul_fin_two, Matrix.mul_fin_two]`. Use `mk2 ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[zero_mul, zero_mul, add_zero, add_zero, mul_smul_comm, smul_mul_assoc, h1.eq]`. Simplify using the standard rewrite rules. Establish `e : d • (m * τ) - t12 = (d - 1) • (τ * m)`.

Rewrite `hk` using `[smul_sub]`. Rewrite using `[sub_smul, one_smul]`. Rewrite `hk` using `[sub_eq_iff_eq_add]`. Rewrite using `[hk]`. Normalize the expressions using the abelian group laws.

Rewrite using `[zero_mul, zero_add, mul_assoc, mul_smul_comm, mul_neg, ← sub_eq_add_neg, ← mul_sub, e, mul_smul_comm, smul_mul_assoc, ← mul_assoc, ← mul_assoc, h2.eq]`. Rewrite using `[mul_zero, zero_mul, zero_add, zero_add, mul_smul_comm, smul_mul_assoc, h2.eq]`.
-/
theorem tau_mat {B : Type*} [Ring B] [Algebra ℂ B] {zbi zg m τ t12 : B} {d : ℂ}
    (h1 : Commute zbi τ) (h2 : Commute zg τ) (hk : d • (m * τ - τ * m) = t12 - τ * m) :
    !![zbi, 0; zg * m, zg] * !![d • τ, 0; -t12, (d - 1) • τ] =
      !![d • τ, 0; 0, (d - 1) • τ] * !![zbi, 0; zg * m, zg] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine mk2 ?_ ?_ ?_ ?_
  · rw [zero_mul, zero_mul, add_zero, add_zero, mul_smul_comm, smul_mul_assoc, h1.eq]
  · simp
  · have e : d • (m * τ) - t12 = (d - 1) • (τ * m) := by
      rw [smul_sub] at hk
      rw [sub_smul, one_smul]
      rw [sub_eq_iff_eq_add] at hk
      rw [hk]; abel
    rw [zero_mul, zero_add, mul_assoc, mul_smul_comm, mul_neg, ← sub_eq_add_neg, ← mul_sub, e, mul_smul_comm,
      smul_mul_assoc, ← mul_assoc, ← mul_assoc, h2.eq]
  · rw [mul_zero, zero_mul, zero_add, zero_add, mul_smul_comm, smul_mul_assoc, h2.eq]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
theorem smul_matrix2_of {B : Type*} [Ring B] [Algebra ℂ B] (c : ℂ) (p q s t : B) :
    c • !![p, q; s, t] = !![c • p, c • q; c • s, c • t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

section Reduce

variable {b : S}

/- English proof (translation)
Rewrite using `[mul_assoc, ins_left hF, hN, ← Wd1.ins_mul _ _ _ hP, mul_assoc]`.
-/
theorem lhs_red {F : SlopeTestRemainingChoices S A} (hF : FreeOf b F) {P N Nh : M2 (SlopeTestRemainingChoices S A)} (hP : FreeOf2 b P)
    (hN : d0 F * N = Nh * d0 F) : ins b P * F * ins b N = ins b (P * Nh * d0 F) := by
  rw [mul_assoc, ins_left hF, hN, ← Wd1.ins_mul _ _ _ hP, mul_assoc]

/- English proof (translation)
Rewrite using `[← mul_assoc, ← Wd1.ins_mul _ _ _ hW, ins_right]`.
-/
theorem rhs_red {F : SlopeTestRemainingChoices S A} {P W : M2 (SlopeTestRemainingChoices S A)} (hW : FreeOf2 b W) :
    ins b W * (ins b P * F) = ins b (W * P * d0 F) := by
  rw [← mul_assoc, ← Wd1.ins_mul _ _ _ hW, ins_right]

variable {L : LevelData A r} {f : FrameData S A}

/- English proof (translation)
Rewrite using `[d0_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_fin_two, Matrix.mul_fin_two]`. Use `congr 1`. Use `mk2 ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[zero_mul, zero_mul, add_zero, add_zero, mul_smul_comm, smul_mul_assoc, hat_F h hY]`. Simplify using the standard rewrite rules.

Rewrite using `[zero_mul, mul_zero, zero_add, add_zero, mul_neg, neg_mul, hat_F h hY]`. Rewrite using `[zero_mul, mul_zero, zero_add, zero_add, mul_smul_comm, smul_mul_assoc, hat_F h hY]`.
-/
theorem hatN (h : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) (c d : ℂ) (j : Fin 2) :
    d0 f.F * (c • !![d • f.TT Y 1 j, 0; -f.TT Y 0 j, (d - 1) • f.TT Y 1 j]) =
      (c • !![d • f.hatT Y 1 j, 0; -f.hatT Y 0 j, (d - 1) • f.hatT Y 1 j]) * d0 f.F := by
  rw [d0_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  refine mk2 ?_ ?_ ?_ ?_
  · rw [zero_mul, zero_mul, add_zero, add_zero, mul_smul_comm, smul_mul_assoc, hat_F h hY]
  · simp
  · rw [zero_mul, mul_zero, zero_add, add_zero, mul_neg, neg_mul, hat_F h hY]
  · rw [zero_mul, mul_zero, zero_add, zero_add, mul_smul_comm, smul_mul_assoc, hat_F h hY]

/- English proof (translation)
Rewrite using `[Matrix.mul_fin_two]`. Apply the tactic sequence `refine mk2 ?_ ?_ ?_ ?_ <;> simp [mul_assoc]`.
-/
theorem frame_mat (L : LevelData A r) (m : SlopeTestRemainingChoices S A) :
    (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζbi, 0; io L.ζi * io L.GG * m, io L.ζi * io L.GG] := by
  rw [Matrix.mul_fin_two]
  refine mk2 ?_ ?_ ?_ ?_ <;> simp [mul_assoc]

/- English proof (translation)
Rewrite using `[d0_eq, Matrix.mul_fin_two, smul_matrix2_of]`. Use `mk2 ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[zero_mul, add_zero, mul_smul_comm, mul_one, smul_smul, div_eq_inv_mul]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite using `[zero_mul, zero_add, mul_one, smul_smul, inv_mul_cancel₀ hd, one_smul]`.
-/
theorem diag_mat (τ : SlopeTestRemainingChoices S A) {d : ℂ} (hd : d - 1 ≠ 0) :
    d0 τ * !![(d / (d - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] = (d - 1)⁻¹ • !![d • τ, 0; 0, (d - 1) • τ] := by
  rw [d0_eq, Matrix.mul_fin_two, smul_matrix2_of]
  refine mk2 ?_ ?_ ?_ ?_
  · rw [zero_mul, add_zero, mul_smul_comm, mul_one, smul_smul, div_eq_inv_mul]
  · simp
  · simp
  · rw [zero_mul, zero_add, mul_one, smul_smul, inv_mul_cancel₀ hd, one_smul]

end Reduce

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L f b Yb ⟨hS, h, hf, hr, hb, hb1, hbm, hq⟩ Y hY`. Take `⟨hY, hd⟩` from `hY`. Establish `hd : Yb - Y - 1 ≠ 0` using `sub_ne_zero.mpr hd`. Take `⟨H, -⟩` from `frame_gives_one_letter_hyps A S r L f h`. Take `⟨hrtt, -, -, h3, h4, -⟩` from `H`.

Establish `hF` using `hf.2.2.1`. Establish `hk : (Yb - Y) • (f.m L Yb * f.hatT Y 1 1 - f.hatT Y 1 1 * f.m L Yb) = f.hatT Y 0 1 - f.hatT Y 1 1 * f.m L Yb`. Use `tau_key (h3 Yb hb).2 (h4 Yb Y) ?_ (hrtt Yb Y 0 1 1 1)` and prove the remaining obligations. Rewrite using `[frameM hS h hr hb hbm, hat_τ h (h.inv_reg hb)]`. Establish `c1 : Commute (io L.ζbi : SlopeTestRemainingChoices S A) (f.hatT Y 1 1)`.

Rewrite using `[hat_τ h hY]`. Conclude with `(io_comm (zc L (mζbi L) (mG L))).mul_right (h.x_fn Y _ (mζbi L)).symm`. Establish `c2 : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (f.hatT Y 1 1)`. Rewrite using `[hat_τ h hY]`. Conclude with `((io_comm (zc L (mζi L) (mG L))).mul_right (h.x_fn Y _ (mζi L)).symm).mul_left ((Commute.refl _).mul_right (h.x_fn Y _ (mG L)).symm)`.

Establish `hτfree : FreeOf b (f.hatT Y 1 1)`. Rewrite using `[hat_τ h hY]`. Conclude with `Wd11.free_mul (Wd11.free_io b _) (hf.2.2.2.2.1 Y)`. Use `show ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F * (Rht0 b (Yb - Y) * f.TT Y : M2 (SlopeTestRemainingChoices S A)) 1 1 = io L.GG * (f.x Y * ins b !![((Yb - Y) / (Yb - Y - 1)) • 1, 0; 0, 1]) * (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io …`. Establish `hP : FreeOf2 b (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A))` using `freeOf2_matrix_entries (Wd11.free_io b _) (Wd11.free_zero b) (Wd11.free_mul (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _)) (free_m hf _)) (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _))`.

Establish `hW : FreeOf2 b ((Yb - Y - 1)⁻¹ • !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1])` using `fun i j => free_smul _ (freeOf2_matrix_entries (free_smul _ hτfree) (Wd11.free_zero b) (Wd11.free_zero b) (free_smul _ hτfree) i j)`. Rewrite using `[frame_mat, rht_row, lhs_red hF hP (hatN h hY _ _ 1), ← mul_assoc (io L.GG), ← hat_τ h hY, ins_left hτfree, diag_mat _ hd, rhs_red hW, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, tau_mat c1 c2 hk]`.
-/
theorem minusTau : MinusTau := by
  intro A S _ _ _ _ _ _ r L f b Yb ⟨hS, h, hf, hr, hb, hb1, hbm, hq⟩ Y hY
  obtain ⟨hY, hd⟩ := hY
  have hd : Yb - Y - 1 ≠ 0 := sub_ne_zero.mpr hd
  obtain ⟨H, -⟩ := frame_gives_one_letter_hyps A S r L f h
  obtain ⟨hrtt, -, -, h3, h4, -⟩ := H
  have hF := hf.2.2.1
  have hk : (Yb - Y) • (f.m L Yb * f.hatT Y 1 1 - f.hatT Y 1 1 * f.m L Yb) =
      f.hatT Y 0 1 - f.hatT Y 1 1 * f.m L Yb := by
    refine tau_key (h3 Yb hb).2 (h4 Yb Y) ?_ (hrtt Yb Y 0 1 1 1)
    rw [frameM hS h hr hb hbm, hat_τ h (h.inv_reg hb)]
  have c1 : Commute (io L.ζbi : SlopeTestRemainingChoices S A) (f.hatT Y 1 1) := by
    rw [hat_τ h hY]
    exact (io_comm (zc L (mζbi L) (mG L))).mul_right (h.x_fn Y _ (mζbi L)).symm
  have c2 : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (f.hatT Y 1 1) := by
    rw [hat_τ h hY]
    exact ((io_comm (zc L (mζi L) (mG L))).mul_right (h.x_fn Y _ (mζi L)).symm).mul_left
      ((Commute.refl _).mul_right (h.x_fn Y _ (mG L)).symm)
  have hτfree : FreeOf b (f.hatT Y 1 1) := by
    rw [hat_τ h hY]; exact Wd11.free_mul (Wd11.free_io b _) (hf.2.2.2.2.1 Y)
  show ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F *
      (Rht0 b (Yb - Y) * f.TT Y : M2 (SlopeTestRemainingChoices S A)) 1 1 =
    io L.GG * (f.x Y * ins b !![((Yb - Y) / (Yb - Y - 1)) • 1, 0; 0, 1]) *
      (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F)
  have hP : FreeOf2 b (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_matrix_entries (Wd11.free_io b _) (Wd11.free_zero b)
      (Wd11.free_mul (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _)) (free_m hf _))
      (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _))
  have hW : FreeOf2 b ((Yb - Y - 1)⁻¹ • !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1]) :=
    fun i j => free_smul _ (freeOf2_matrix_entries (free_smul _ hτfree) (Wd11.free_zero b) (Wd11.free_zero b)
      (free_smul _ hτfree) i j)
  rw [frame_mat, rht_row, lhs_red hF hP (hatN h hY _ _ 1), ← mul_assoc (io L.GG), ← hat_τ h hY,
    ins_left hτfree, diag_mat _ hd, rhs_red hW, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.smul_mul, tau_mat c1 c2 hk]

section LevelId

variable (L : LevelData A r)

/- English proof (translation)
Unfold `io`. Conclude with `map_add _ x y`.
-/
theorem io_add (x y : A) : (io (x + y) : SlopeTestRemainingChoices S A) = io x + io y := by
  unfold io; exact map_add _ x y

/- English proof (translation)
Unfold `io`. Conclude with `map_sub _ x y`.
-/
theorem io_sub (x y : A) : (io (x - y) : SlopeTestRemainingChoices S A) = io x - io y := by
  unfold io; exact map_sub _ x y

/- English proof (translation)
Unfold `io`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.scalar, hij]`.
-/
theorem io_smul (c : ℂ) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  unfold io
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar, hij]

/- English proof (translation)
Unfold `LevelData.l0`. Rewrite using `[← Algebra.smul_def]`.
-/
theorem l0_eq_neg_nabla_sub (Y : ℂ) : L.l0 Y = -L.nab - (Y + 1 / 2) • (L.ζb * L.GGi) := by
  unfold LevelData.l0
  rw [← Algebra.smul_def]

/- English proof (translation)
Rewrite using `[l0_eq_neg_nabla_sub]`. Establish `e : L.GG * (L.ζb * L.GGi) = L.ζb * L.GGi * L.GG`. Rewrite using `[mul_assoc, L.GGi_GG, zc L (mζb L) (mGi L), ← mul_assoc, L.GG_GGi, one_mul, mul_one]`. Rewrite using `[mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, e, mul_neg, neg_mul, L.nab_GG]`. Normalize the expressions using the abelian group laws.
-/
theorem commutator_GG_l0 (Y : ℂ) : L.GG * L.l0 Y - L.l0 Y * L.GG = L.ζb := by
  rw [l0_eq_neg_nabla_sub]
  have e : L.GG * (L.ζb * L.GGi) = L.ζb * L.GGi * L.GG := by
    rw [mul_assoc, L.GGi_GG, zc L (mζb L) (mGi L), ← mul_assoc, L.GG_GGi, one_mul, mul_one]
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, e, mul_neg, neg_mul, L.nab_GG]
  abel

/- English proof (translation)
Rewrite using `[l0_eq_neg_nabla_sub]`. Establish `e : L.ζbi * (L.ζb * L.GGi) = L.ζb * L.GGi * L.ζbi`. Rewrite using `[← mul_assoc, zc L (mζbi L) (mζb L), mul_assoc, zc L (mζbi L) (mGi L), mul_assoc]`. Rewrite using `[mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, e, mul_neg, neg_mul, L.nab_ζbi]`.
-/
theorem zetaBarInv_commute_l0 (Y : ℂ) : L.ζbi * L.l0 Y = L.l0 Y * L.ζbi := by
  rw [l0_eq_neg_nabla_sub]
  have e : L.ζbi * (L.ζb * L.GGi) = L.ζb * L.GGi * L.ζbi := by
    rw [← mul_assoc, zc L (mζbi L) (mζb L), mul_assoc, zc L (mζbi L) (mGi L), mul_assoc]
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, e, mul_neg, neg_mul, L.nab_ζbi]

/- English proof (translation)
Rewrite using `[l0_eq_neg_nabla_sub]`. Establish `e : L.ζi * L.GG * (L.ζb * L.GGi) = L.ζb * L.GGi * (L.ζi * L.GG)`. Rewrite using `[zc L (mζi L) (mG L), zc L (mζb L) (mGi L)]`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : L.nab * (L.ζi * L.GG) = L.ζi * L.GG * L.nab + L.ζi * L.ζb - L.ζi * L.ζi * L.GG`.

Rewrite using `[← mul_assoc, L.nab_ζi, sub_mul, mul_assoc, L.nab_GG, mul_add, ← mul_assoc]`. Establish `e3 : L.ζi * L.GGi * (L.ζi * L.GG) = L.ζi * L.ζi`. Rewrite using `[mul_assoc, ← mul_assoc L.GGi, zc L (mGi L) (mζi L), mul_assoc, L.GGi_GG, mul_one]`. Establish `e4 : L.ζi * L.ζi * L.GG = L.ζi * L.ζb - L.TT • (L.ζi * L.ζi)`. Rewrite using `[L.GG_def, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, mul_assoc, ← mul_assoc L.ζi L.ζ, L.ζi_ζ, one_mul]`.

Rewrite using `[mul_sub, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, e, mul_neg, neg_mul, e2, e3, e4]`. Normalize the expressions using the abelian group laws.
-/
theorem zetaInv_GG_conj_l0 (Y : ℂ) :
    L.ζi * L.GG * L.l0 Y = (L.l0 Y + L.TT • (L.ζi * L.GGi)) * (L.ζi * L.GG) := by
  rw [l0_eq_neg_nabla_sub]
  have e : L.ζi * L.GG * (L.ζb * L.GGi) = L.ζb * L.GGi * (L.ζi * L.GG) := by
    rw [zc L (mζi L) (mG L), zc L (mζb L) (mGi L)]
    calc L.GG * L.ζi * (L.GGi * L.ζb) = L.GG * (L.ζi * L.GGi) * L.ζb := by simp only [mul_assoc]
      _ = (L.GG * L.GGi) * (L.ζi * L.ζb) := by rw [zc L (mζi L) (mGi L)]; simp only [mul_assoc]
      _ = (L.GGi * L.GG) * (L.ζb * L.ζi) := by rw [L.GG_GGi, L.GGi_GG, zc L (mζi L) (mζb L)]
      _ = L.GGi * (L.GG * L.ζb) * L.ζi := by simp only [mul_assoc]
      _ = L.GGi * L.ζb * (L.GG * L.ζi) := by rw [zc L (mG L) (mζb L)]; simp only [mul_assoc]
  have e2 : L.nab * (L.ζi * L.GG) = L.ζi * L.GG * L.nab + L.ζi * L.ζb - L.ζi * L.ζi * L.GG := by
    rw [← mul_assoc, L.nab_ζi, sub_mul, mul_assoc, L.nab_GG, mul_add, ← mul_assoc]
  have e3 : L.ζi * L.GGi * (L.ζi * L.GG) = L.ζi * L.ζi := by
    rw [mul_assoc, ← mul_assoc L.GGi, zc L (mGi L) (mζi L), mul_assoc, L.GGi_GG, mul_one]
  have e4 : L.ζi * L.ζi * L.GG = L.ζi * L.ζb - L.TT • (L.ζi * L.ζi) := by
    rw [L.GG_def, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, mul_assoc, ← mul_assoc L.ζi L.ζ, L.ζi_ζ,
      one_mul]
  rw [mul_sub, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, e, mul_neg, neg_mul, e2, e3, e4]
  abel

end LevelId

section Ee

variable {L : LevelData A r} {f : FrameData S A}

/- English proof (translation)
Unfold `kapL`. Rewrite using `[Wd11.io_mul, Wd11.io_mul]`. Conclude with `((hy _ (mζb L)).mul_right (hy _ (mζi L))).mul_right (hy _ (mGi L))`.
-/
theorem comm_kapL {y : SlopeTestRemainingChoices S A} (hy : ∀ g ∈ zfns L, Commute y (io g)) : Commute y (kapL L) := by
  unfold kapL
  rw [Wd11.io_mul, Wd11.io_mul]
  exact ((hy _ (mζb L)).mul_right (hy _ (mζi L))).mul_right (hy _ (mGi L))

/- English proof (translation)
Rewrite using `[l0_eq_neg_nabla_sub, io_sub, Wd11.io_neg, io_smul, Wd11.io_mul]`. Conclude with `hn.neg_right.sub_right (((hy _ (mζb L)).mul_right (hy _ (mGi L))).smul_right _)`.
-/
theorem commute_level_zero_element {y : SlopeTestRemainingChoices S A} (hy : ∀ g ∈ zfns L, Commute y (io g)) (hn : Commute y (io L.nab)) (Y : ℂ) :
    Commute y (io (L.l0 Y)) := by
  rw [l0_eq_neg_nabla_sub, io_sub, Wd11.io_neg, io_smul, Wd11.io_mul]
  exact hn.neg_right.sub_right (((hy _ (mζb L)).mul_right (hy _ (mGi L))).smul_right _)

/- English proof (translation)
The claim follows from `io_comm (zc L hg hg')`.
-/
theorem io_fn_comm {g g' : A} (hg : g ∈ zfns L) (hg' : g' ∈ zfns L) : Commute (io g : SlopeTestRemainingChoices S A) (io g') :=
  io_comm (zc L hg hg')

/- English proof (translation)
Unfold `kapL`. Rewrite using `[← Wd11.io_mul, ← Wd11.io_one]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = 1 := by rw [L.ζbi_ζb, mul_one, L.ζ_ζi, mul_one, L.GG_GGi]`.
-/
theorem kapL_inv : (io (L.GG * L.ζ * L.ζbi) : SlopeTestRemainingChoices S A) * kapL L = 1 := by
  unfold kapL
  rw [← Wd11.io_mul, ← Wd11.io_one]
  congr 1
  calc L.GG * L.ζ * L.ζbi * (L.ζb * L.ζi * L.GGi) = L.GG * (L.ζ * (L.ζbi * L.ζb) * L.ζi) * L.GGi := by
        simp only [mul_assoc]
    _ = 1 := by rw [L.ζbi_ζb, mul_one, L.ζ_ζi, mul_one, L.GG_GGi]

/- English proof (translation)
Establish `T : g * k * (x * e - e * x + x * D) = (g * x * (L0 + k * e) - (L0 + k * e) * (g * x) + g * x * (-w + k * D)) - g * (x * k - k * x) * e - g * (x * k - k * x) * D + k * (e * g - g * e) * x + (k * g - g * k) * e * x - g * (x * L0 - L0 * x) - (g * L0 - L0 * g - g * w) * x - g * (w * …` using `by noncomm_ring`. Rewrite `T` using `[hY, xk, eg, kg, xL, gL, wx]`. Simplify using `only [sub_self, mul_zero, zero_mul, add_zero, neg_add_cancel] at T`. Establish `T2 : x * e - e * x + x * D = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc g, ← mul_assoc gi, hg, one_mul, ← mul_assoc ki, hk, one_mul]`. Use `_ = 0 := by rw [T, mul_zero, mul_zero]`. Establish `T3` using `congrArg (fun z => xi * z) T2`. Simplify using `only [mul_add, mul_sub, mul_zero, ← mul_assoc, hx, one_mul] at T3`. Rewrite using `[sub_eq_iff_eq_add, ← sub_eq_zero, ← neg_eq_zero, ← T3]`.

Normalize the expressions using the abelian group laws.
-/
theorem ee_abs {B : Type*} [Ring B] {g gi k ki x xi L0 e D w : B} (hg : gi * g = 1) (hk : ki * k = 1)
    (hx : xi * x = 1) (xk : x * k = k * x) (eg : e * g = g * e) (kg : k * g = g * k) (xL : x * L0 = L0 * x)
    (gL : g * L0 - L0 * g = g * w) (wx : w * x = x * w)
    (hY : g * x * (L0 + k * e) - (L0 + k * e) * (g * x) = -(g * x * (-w + k * D))) :
    xi * e * x - D = e := by
  have T : g * k * (x * e - e * x + x * D) =
      (g * x * (L0 + k * e) - (L0 + k * e) * (g * x) + g * x * (-w + k * D)) - g * (x * k - k * x) * e
        - g * (x * k - k * x) * D + k * (e * g - g * e) * x + (k * g - g * k) * e * x
        - g * (x * L0 - L0 * x) - (g * L0 - L0 * g - g * w) * x - g * (w * x - x * w) := by
    noncomm_ring
  rw [hY, xk, eg, kg, xL, gL, wx] at T
  simp only [sub_self, mul_zero, zero_mul, add_zero, neg_add_cancel] at T
  have T2 : x * e - e * x + x * D = 0 := by
    calc x * e - e * x + x * D = ki * (gi * (g * k * (x * e - e * x + x * D))) := by
          rw [mul_assoc g, ← mul_assoc gi, hg, one_mul, ← mul_assoc ki, hk, one_mul]
      _ = 0 := by rw [T, mul_zero, mul_zero]
  have T3 := congrArg (fun z => xi * z) T2
  simp only [mul_add, mul_sub, mul_zero, ← mul_assoc, hx, one_mul] at T3
  rw [sub_eq_iff_eq_add, ← sub_eq_zero, ← neg_eq_zero, ← T3]
  abel

/- English proof (translation)
Unfold `FrameData.DD`. Rewrite using `[← neg_sub Y Ya, ← neg_sub (f.ee Y) (f.ee Ya), inv_neg, neg_smul, smul_neg, neg_neg]`.
-/
theorem DD_symm (Y Ya : ℂ) : f.DD Ya Y = f.DD Y Ya := by
  unfold FrameData.DD
  rw [← neg_sub Y Ya, ← neg_sub (f.ee Y) (f.ee Ya), inv_neg, neg_smul, smul_neg, neg_neg]

/- English proof (translation)
Take `⟨H, Hl⟩` from `frame_gives_one_letter_hyps A S r L f h`. Establish `y1` using `Formalism.YangianSpanCharacter.P.wedgeMapInLieAlgebra ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv H Ya Y ha hY hne.symm`. Unfold `eta at y1`. Rewrite `y1` using `[Hl Y hY hY1, Hl Ya ha ha1, divided_difference_l A S r L f Ya Y hne.symm, DD_symm, hat_τ h (h.inv_reg ha)]`. Establish `gg2 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1` using `by rw [← Wd11.io_mul, L.GGi_GG, Wd11.io_one]`.

Use `ee_abs (g := io L.GG) (w := io (L.ζb * L.GGi)) gg2 kapL_inv (h.x_xi Ya ha).2 (comm_kapL (h.x_fn Ya)).eq (h.ee_fn Y _ (mG L)).eq (comm_kapL (fun g hg => io_fn_comm (mG L) hg)).eq.symm (commute_level_zero_element (h.x_fn Ya) (h.x_nab Ya) Y).eq ?_ ?_ y1` and prove the remaining obligations. Rewrite using `[← Wd11.io_mul, ← Wd11.io_mul, ← Wd11.io_mul, ← io_sub, commutator_GG_l0, zc L (mζb L) (mGi L), ← mul_assoc, L.GG_GGi, one_mul]`. Rewrite using `[Wd11.io_mul]`. Conclude with `((h.x_fn Ya _ (mζb L)).mul_right (h.x_fn Ya _ (mGi L))).eq.symm`.
-/
theorem eeConj (h : IsFrame L f) {Y Ya : ℂ} (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) (ha : Ya ∈ f.inv)
    (ha1 : Ya + 1 ∈ f.inv) (hne : Y ≠ Ya) : f.xi Ya * f.ee Y * f.x Ya - f.DD Y Ya = f.ee Y := by
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  have y1 := Formalism.YangianSpanCharacter.P.wedgeMapInLieAlgebra ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv H Ya Y ha hY hne.symm
  unfold eta at y1
  rw [Hl Y hY hY1, Hl Ya ha ha1, divided_difference_l A S r L f Ya Y hne.symm, DD_symm,
    hat_τ h (h.inv_reg ha)] at y1
  have gg2 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← Wd11.io_mul, L.GGi_GG, Wd11.io_one]
  refine ee_abs (g := io L.GG) (w := io (L.ζb * L.GGi)) gg2 kapL_inv (h.x_xi Ya ha).2
    (comm_kapL (h.x_fn Ya)).eq (h.ee_fn Y _ (mG L)).eq
    (comm_kapL (fun g hg => io_fn_comm (mG L) hg)).eq.symm
    (commute_level_zero_element (h.x_fn Ya) (h.x_nab Ya) Y).eq ?_ ?_ y1
  · rw [← Wd11.io_mul, ← Wd11.io_mul, ← Wd11.io_mul, ← io_sub, commutator_GG_l0, zc L (mζb L) (mGi L), ← mul_assoc,
      L.GG_GGi, one_mul]
  · rw [Wd11.io_mul]
    exact ((h.x_fn Ya _ (mζb L)).mul_right (h.x_fn Ya _ (mGi L))).eq.symm

end Ee

section LL

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
theorem add_matrix2_of {B : Type*} [Ring B] (p q s t p' q' s' t' : B) :
    !![p, q; s, t] + !![p', q'; s', t'] = !![p + p', q + q'; s + s', t + t'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Unfold `ins`. Simplify using `only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem ins_add (b : S) (M N : M2 (SlopeTestRemainingChoices S A)) : ins b (M + N) = ins b M + ins b N := by
  unfold ins
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem l_mat {B : Type*} [Ring B] {E Gb τn Ln N dg Ln' lm : Matrix (Fin 2) (Fin 2) B} (m3 : τn * Ln = N)
    (m4 : Gb * τn = dg * Gb) (m5 : Gb * Ln = Ln' * Gb) (e1 : E * dg = dg * E) (e2 : E * Ln' = lm * E) :
    E * Gb * N = dg * lm * (E * Gb) := by
  calc E * Gb * N = E * (Gb * τn) * Ln := by rw [← m3]; simp only [Matrix.mul_assoc]
    _ = E * dg * (Gb * Ln) := by rw [m4]; simp only [Matrix.mul_assoc]
    _ = dg * (E * Ln') * Gb := by rw [m5, e1]; simp only [Matrix.mul_assoc]
    _ = dg * lm * (E * Gb) := by rw [e2]; simp only [Matrix.mul_assoc]

variable {L : LevelData A r} {f : FrameData S A}

/- English proof (translation)
Unfold `FrameData.l`. Rewrite using `[mul_add, add_mul, ← Wd11.io_mul, zetaBarInv_commute_l0, Wd11.io_mul, ← mul_assoc, (comm_kapL (fun g hg => io_fn_comm (mζbi L) hg)).eq, mul_assoc, mul_assoc, (h.ee_fn Y _ (mζbi L)).eq]`.
-/
theorem ζbi_l (h : IsFrame L f) (Y : ℂ) : io L.ζbi * f.l L Y = f.l L Y * io L.ζbi := by
  unfold FrameData.l
  rw [mul_add, add_mul, ← Wd11.io_mul, zetaBarInv_commute_l0, Wd11.io_mul, ← mul_assoc,
    (comm_kapL (fun g hg => io_fn_comm (mζbi L) hg)).eq, mul_assoc, mul_assoc, (h.ee_fn Y _ (mζbi L)).eq]

/- English proof (translation)
Unfold `kapL tz`. Rewrite using `[← Wd11.io_mul, mul_smul_comm]`. Use `congr 2`. Rewrite using `[mul_assoc, mul_assoc, zc L (mGi L) (mζbi L), ← mul_assoc L.ζi, zc L (mζi L) (mζbi L), mul_assoc, ← mul_assoc, L.ζb_ζbi, one_mul]`.
-/
theorem kapL_tz : (kapL L : SlopeTestRemainingChoices S A) * tz L = io (L.TT • (L.ζi * L.GGi)) := by
  unfold kapL tz
  rw [← Wd11.io_mul, mul_smul_comm]
  congr 2
  rw [mul_assoc, mul_assoc, zc L (mGi L) (mζbi L), ← mul_assoc L.ζi, zc L (mζi L) (mζbi L), mul_assoc,
    ← mul_assoc, L.ζb_ζbi, one_mul]

/- English proof (translation)
Unfold `FrameData.l`. Establish `c : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (kapL L * f.ee Y)` using `((comm_kapL (fun g hg => io_fn_comm (mζi L) hg)).mul_right (h.ee_fn Y _ (mζi L)).symm).mul_left ((comm_kapL (fun g hg => io_fn_comm (mG L) hg)).mul_right (h.ee_fn Y _ (mG L)).symm)`. Rewrite using `[mul_add, c.eq, kapL_tz, ← Wd11.io_mul, ← Wd11.io_mul, zetaInv_GG_conj_l0, Wd11.io_mul, io_add, add_mul, add_mul, add_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem ζiGG_l (h : IsFrame L f) (Y : ℂ) :
    io L.ζi * io L.GG * f.l L Y = (f.l L Y + kapL L * tz L) * (io L.ζi * io L.GG) := by
  unfold FrameData.l
  have c : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (kapL L * f.ee Y) :=
    ((comm_kapL (fun g hg => io_fn_comm (mζi L) hg)).mul_right (h.ee_fn Y _ (mζi L)).symm).mul_left
      ((comm_kapL (fun g hg => io_fn_comm (mG L) hg)).mul_right (h.ee_fn Y _ (mG L)).symm)
  rw [mul_add, c.eq, kapL_tz, ← Wd11.io_mul, ← Wd11.io_mul, zetaInv_GG_conj_l0, Wd11.io_mul, io_add, add_mul, add_mul,
    add_mul]
  abel

/- English proof (translation)
Unfold `kapL`. Rewrite using `[← Wd11.io_mul, ← Wd11.io_mul]`. Use `congr 1`. Rewrite using `[mul_assoc, mul_assoc, zc L (mGi L) (mζbi L), ← mul_assoc L.ζi, zc L (mζi L) (mζbi L), mul_assoc, ← mul_assoc, L.ζb_ζbi, one_mul]`.
-/
theorem kapL_ζbi : (kapL L : SlopeTestRemainingChoices S A) * io L.ζbi = io L.ζi * io L.GGi := by
  unfold kapL
  rw [← Wd11.io_mul, ← Wd11.io_mul]
  congr 1
  rw [mul_assoc, mul_assoc, zc L (mGi L) (mζbi L), ← mul_assoc L.ζi, zc L (mζi L) (mζbi L), mul_assoc,
    ← mul_assoc, L.ζb_ζbi, one_mul]

/- English proof (translation)
Establish `gg1 : (io L.GG : SlopeTestRemainingChoices S A) * io L.GGi = 1` using `by rw [← Wd11.io_mul, L.GG_GGi, Wd11.io_one]`. Establish `a : io L.ζi * io L.GG * (io L.GGi * X1 * (io L.GGi * X2)) = io L.ζi * io L.GGi * (X2 * X1)`. Combine the equalities or inequalities in the displayed calculation. Establish `b : kapL L * (X2 * X1) * io L.ζbi = io L.ζi * io L.GGi * (X2 * X1)`. Rewrite using `[mul_assoc, ((h2 _ (mζbi L)).mul_left (h1 _ (mζbi L))).eq, ← mul_assoc, kapL_ζbi]`.

Rewrite using `[mul_neg, neg_mul, mul_smul_comm, mul_smul_comm, a, mul_smul_comm, smul_mul_assoc, b, smul_smul, div_eq_inv_mul]`.
-/
theorem h_entry {X1 X2 : SlopeTestRemainingChoices S A} (h1 : ∀ g ∈ zfns L, Commute X1 (io g)) (h2 : ∀ g ∈ zfns L, Commute X2 (io g))
    (h12 : Commute X1 X2) (c q : ℂ) :
    io L.ζi * io L.GG * -(c⁻¹ • q • (io L.GGi * X1 * (io L.GGi * X2))) =
      -(kapL L * ((q / c) • (X2 * X1))) * io L.ζbi := by
  have gg1 : (io L.GG : SlopeTestRemainingChoices S A) * io L.GGi = 1 := by rw [← Wd11.io_mul, L.GG_GGi, Wd11.io_one]
  have a : io L.ζi * io L.GG * (io L.GGi * X1 * (io L.GGi * X2)) = io L.ζi * io L.GGi * (X2 * X1) := by
    calc io L.ζi * io L.GG * (io L.GGi * X1 * (io L.GGi * X2))
        = io L.ζi * (io L.GG * io L.GGi) * (X1 * io L.GGi) * X2 := by simp only [mul_assoc]
      _ = io L.ζi * io L.GGi * (X1 * X2) := by rw [gg1, mul_one, (h1 _ (mGi L)).eq]; simp only [mul_assoc]
      _ = _ := by rw [h12.eq]
  have b : kapL L * (X2 * X1) * io L.ζbi = io L.ζi * io L.GGi * (X2 * X1) := by
    rw [mul_assoc, ((h2 _ (mζbi L)).mul_left (h1 _ (mζbi L))).eq, ← mul_assoc, kapL_ζbi]
  rw [mul_neg, neg_mul, mul_smul_comm, mul_smul_comm, a, mul_smul_comm, smul_mul_assoc, b, smul_smul,
    div_eq_inv_mul]

end LL

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L f b Yb ⟨hS, h, hfr, hr, hb, hb1, hbm, hq⟩ Y hY hY1`. Take `⟨hYi, hd0, hd1⟩` from `hY`. Take `⟨hY1i, -, -⟩` from `hY1`. Establish `hY` using `h.inv_reg hYi`. Establish `hd : Yb - Y - 1 ≠ 0` using `sub_ne_zero.mpr hd1`.

Establish `hne : Y ≠ Yb` using `fun e => hd0 (by rw [e, sub_self])`. Take `⟨H, Hl⟩` from `frame_gives_one_letter_hyps A S r L f h`. Establish `MF` using `Formalism.YangianSpanCharacter.P.minus_frame_identity ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv H Y Yb hYi hY1i hb hb1 hbm hd0 hd`. Take `⟨-, -, m3, m4, m5⟩` from `MF`. Rewrite `m3`, `m5` using `[Hl Y hYi hY1i]`.

Rewrite `m4`, `m5` using `[hat_m hS h hr hb hbm]`. Establish `hF` using `hfr.2.2.1`. Establish `hxi` using `hfr.2.2.2.2.2.1`. Establish `c1 : Commute (io L.ζbi : SlopeTestRemainingChoices S A) (f.hatT Y 1 1)`. Rewrite using `[hat_τ h hY]`.

Conclude with `(io_comm (zc L (mζbi L) (mG L))).mul_right (h.x_fn Y _ (mζbi L)).symm`. Establish `c2 : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (f.hatT Y 1 1)`. Rewrite using `[hat_τ h hY]`. Conclude with `((io_comm (zc L (mζi L) (mG L))).mul_right (h.x_fn Y _ (mζi L)).symm).mul_left ((Commute.refl _).mul_right (h.x_fn Y _ (mG L)).symm)`. Establish `hτfree : FreeOf b (f.hatT Y 1 1)`.

Rewrite using `[hat_τ h hY]`. Conclude with `Wd11.free_mul (Wd11.free_io b _) (hfr.2.2.2.2.1 Y)`. Establish `hQ : f.hatQ (Yb - 1) = f.q (Yb - 1)`. Simplify using `[FrameData.hatQ, h.inv_reg hbm, h.inv_reg hb]`. Establish `xif : ∀ u ∈ f.inv, ∀ g ∈ zfns L, Commute (f.xi u) (io g)` using `fun u hu g hg => comm_inv (h.x_xi u hu).1 (h.x_xi u hu).2 (h.x_fn u g hg)`.

Establish `xixi : Commute (f.xi (Yb - 1)) (f.xi Yb)` using `comm_inv (h.x_xi _ hbm).1 (h.x_xi _ hbm).2 (comm_inv (h.x_xi _ hb).1 (h.x_xi _ hb).2 (h.x_commute Yb (Yb - 1))).symm`. Use `show ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F * (Rht0 b (Yb - Y) * f.TT Y : M2 (SlopeTestRemainingChoices S A)) 1 0 = io L.GG * (f.x Y * ins b !![((Yb - Y) / (Yb - Y - 1)) • 1, 0; 0, 1]) * (io (L.l0 Y) + kapL L * ins b !![f.ee Y, 0; -((f.q …`. Establish `hP : FreeOf2 b (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A))` using `freeOf2_matrix_entries (Wd11.free_io b _) (Wd11.free_zero b) (Wd11.free_mul (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _)) (free_m hfr _)) (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _))`. Establish `hW : FreeOf2 b ((Yb - Y - 1)⁻¹ • !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1])` using `fun i j => free_smul _ (freeOf2_matrix_entries (free_smul _ hτfree) (Wd11.free_zero b) (Wd11.free_zero b) (free_smul _ hτfree) i j)`. Establish `hk : FreeOf b (kapL L : SlopeTestRemainingChoices S A)` using `Wd11.free_io b _`.

Establish `hlm : FreeOf2 b !![f.l L Y, 0; -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1)))), f.l L Y + kapL L * tz L]` using `freeOf2_matrix_entries (free_l hfr _) (Wd11.free_zero b) (free_neg (Wd11.free_mul hk (free_smul _ (Wd11.free_mul (hxi _) (hxi _))))) (free_add (free_l hfr _) (Wd11.free_mul hk (Wd11.free_io b _)))`. Establish `lins : io (L.l0 Y) + kapL L * ins b !![f.ee Y, 0; -((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1))), f.xi Yb * f.ee Y * f.x Yb - f.DD Y Yb + tz L] = ins b !![f.l L Y, 0; -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1)))), f.l L Y + kapL L * tz L]`. Rewrite using `[eeConj h hYi hY1i hb hb1 hne, ins_left hk, ← Wd1.insert_diagonal_extract b (io (L.l0 Y)), ← ins_add, d0_eq, d0_eq, Matrix.mul_fin_two, add_matrix2_of]`. Use `congr 1`. Unfold `FrameData.l`.

Use `mk2 ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[zero_mul, add_zero]`. Simplify using the standard rewrite rules. Rewrite using `[zero_mul, zero_add, zero_add, mul_neg]`. Rewrite using `[zero_mul, zero_add, mul_add, add_assoc]`.

Establish `pf : (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) = !![io L.ζbi, 0; 0, io L.ζi * io L.GG] * !![1, 0; f.m L Yb, 1]`. Rewrite using `[Matrix.mul_fin_two]`. Apply the tactic sequence `refine mk2 ?_ ?_ ?_ ?_ <;> simp`. Establish `e1 : (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) * !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1] = !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1] * !![io L.ζbi, 0; 0, io L.ζi * io L.GG]`. Rewrite using `[Matrix.mul_fin_two, Matrix.mul_fin_two]`.

Use `mk2 ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `only [mul_zero, add_zero]`. Rewrite using `[mul_smul_comm, smul_mul_assoc, c1.eq]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using `only [mul_zero, zero_add]`. Rewrite using `[mul_smul_comm, smul_mul_assoc, c2.eq]`. Establish `e2 : (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) * !![f.l L Y, 0; -((Yb - Y - 1)⁻¹ • Formalism.YangianSpanCharacter.Y.hf (fun Y => io L.GGi * f.xi Y) f.hatQ (Yb - 1)), f.l L Y] = !![f.l L Y, 0; -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb …`. Rewrite using `[Matrix.mul_fin_two, Matrix.mul_fin_two]`. Use `mk2 ?_ ?_ ?_ ?_` and prove the remaining obligations.

Simplify using `only [zero_mul, mul_zero, add_zero]`. Rewrite using `[ζbi_l h]`. Simplify using the standard rewrite rules. Unfold `Formalism.YangianSpanCharacter.Y.hf`. Simplify using `only [zero_mul, mul_zero, add_zero, zero_add]`.

Rewrite using `[hQ, sub_add_cancel]`. Apply the tactic sequence `exact h_entry (xif _ hbm) (xif _ hb) xixi _ _`. Simplify using `only [mul_zero, zero_add]`. Rewrite using `[ζiGG_l h]`. Rewrite using `[lins, frame_mat, rht_row, lhs_red hF hP (hatN h hY _ _ 0), ← mul_assoc (io L.GG), ← hat_τ h hY, ins_left hτfree, diag_mat _ hd, ← Wd1.ins_mul _ _ _ hW, rhs_red (Wd11.freeOf2_mul hW hlm), Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, pf, l_m …`.
-/
theorem minusL : MinusL := by
  intro A S _ _ _ _ _ _ r L f b Yb ⟨hS, h, hfr, hr, hb, hb1, hbm, hq⟩ Y hY hY1
  obtain ⟨hYi, hd0, hd1⟩ := hY
  obtain ⟨hY1i, -, -⟩ := hY1
  have hY := h.inv_reg hYi
  have hd : Yb - Y - 1 ≠ 0 := sub_ne_zero.mpr hd1
  have hne : Y ≠ Yb := fun e => hd0 (by rw [e, sub_self])
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  have MF := Formalism.YangianSpanCharacter.P.minus_frame_identity ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv H Y Yb hYi hY1i hb hb1 hbm hd0 hd
  obtain ⟨-, -, m3, m4, m5⟩ := MF
  rw [Hl Y hYi hY1i] at m3 m5
  rw [hat_m hS h hr hb hbm] at m4 m5
  have hF := hfr.2.2.1
  have hxi := hfr.2.2.2.2.2.1
  have c1 : Commute (io L.ζbi : SlopeTestRemainingChoices S A) (f.hatT Y 1 1) := by
    rw [hat_τ h hY]
    exact (io_comm (zc L (mζbi L) (mG L))).mul_right (h.x_fn Y _ (mζbi L)).symm
  have c2 : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (f.hatT Y 1 1) := by
    rw [hat_τ h hY]
    exact ((io_comm (zc L (mζi L) (mG L))).mul_right (h.x_fn Y _ (mζi L)).symm).mul_left
      ((Commute.refl _).mul_right (h.x_fn Y _ (mG L)).symm)
  have hτfree : FreeOf b (f.hatT Y 1 1) := by
    rw [hat_τ h hY]; exact Wd11.free_mul (Wd11.free_io b _) (hfr.2.2.2.2.1 Y)
  have hQ : f.hatQ (Yb - 1) = f.q (Yb - 1) := by
    simp [FrameData.hatQ, h.inv_reg hbm, h.inv_reg hb]
  have xif : ∀ u ∈ f.inv, ∀ g ∈ zfns L, Commute (f.xi u) (io g) := fun u hu g hg =>
    comm_inv (h.x_xi u hu).1 (h.x_xi u hu).2 (h.x_fn u g hg)
  have xixi : Commute (f.xi (Yb - 1)) (f.xi Yb) :=
    comm_inv (h.x_xi _ hbm).1 (h.x_xi _ hbm).2
      (comm_inv (h.x_xi _ hb).1 (h.x_xi _ hb).2 (h.x_commute Yb (Yb - 1))).symm
  show ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F *
      (Rht0 b (Yb - Y) * f.TT Y : M2 (SlopeTestRemainingChoices S A)) 1 0 =
    io L.GG * (f.x Y * ins b !![((Yb - Y) / (Yb - Y - 1)) • 1, 0; 0, 1]) *
      (io (L.l0 Y) + kapL L * ins b !![f.ee Y, 0;
        -((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1))),
        f.xi Yb * f.ee Y * f.x Yb - f.DD Y Yb + tz L]) *
      (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F)
  have hP : FreeOf2 b (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_matrix_entries (Wd11.free_io b _) (Wd11.free_zero b)
      (Wd11.free_mul (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _)) (free_m hfr _))
      (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _))
  have hW : FreeOf2 b ((Yb - Y - 1)⁻¹ • !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1]) :=
    fun i j => free_smul _ (freeOf2_matrix_entries (free_smul _ hτfree) (Wd11.free_zero b) (Wd11.free_zero b)
      (free_smul _ hτfree) i j)
  have hk : FreeOf b (kapL L : SlopeTestRemainingChoices S A) := Wd11.free_io b _
  have hlm : FreeOf2 b !![f.l L Y, 0;
      -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1)))), f.l L Y + kapL L * tz L] :=
    freeOf2_matrix_entries (free_l hfr _) (Wd11.free_zero b)
      (free_neg (Wd11.free_mul hk (free_smul _ (Wd11.free_mul (hxi _) (hxi _)))))
      (free_add (free_l hfr _) (Wd11.free_mul hk (Wd11.free_io b _)))
  have lins : io (L.l0 Y) + kapL L * ins b !![f.ee Y, 0;
        -((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1))),
        f.xi Yb * f.ee Y * f.x Yb - f.DD Y Yb + tz L] =
      ins b !![f.l L Y, 0;
        -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1)))), f.l L Y + kapL L * tz L] := by
    rw [eeConj h hYi hY1i hb hb1 hne, ins_left hk, ← Wd1.insert_diagonal_extract b (io (L.l0 Y)), ← ins_add, d0_eq, d0_eq,
      Matrix.mul_fin_two, add_matrix2_of]
    congr 1
    unfold FrameData.l
    refine mk2 ?_ ?_ ?_ ?_
    · rw [zero_mul, add_zero]
    · simp
    · rw [zero_mul, zero_add, zero_add, mul_neg]
    · rw [zero_mul, zero_add, mul_add, add_assoc]
  have pf : (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζbi, 0; 0, io L.ζi * io L.GG] * !![1, 0; f.m L Yb, 1] := by
    rw [Matrix.mul_fin_two]
    refine mk2 ?_ ?_ ?_ ?_ <;> simp
  have e1 : (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) *
        !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1] =
      !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1] *
        !![io L.ζbi, 0; 0, io L.ζi * io L.GG] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine mk2 ?_ ?_ ?_ ?_
    · simp only [mul_zero, add_zero]
      rw [mul_smul_comm, smul_mul_assoc, c1.eq]
    · simp
    · simp
    · simp only [mul_zero, zero_add]
      rw [mul_smul_comm, smul_mul_assoc, c2.eq]
  have e2 : (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) *
        !![f.l L Y, 0; -((Yb - Y - 1)⁻¹ • Formalism.YangianSpanCharacter.Y.hf (fun Y => io L.GGi * f.xi Y) f.hatQ (Yb - 1)), f.l L Y] =
      !![f.l L Y, 0;
        -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1)))), f.l L Y + kapL L * tz L] *
        !![io L.ζbi, 0; 0, io L.ζi * io L.GG] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine mk2 ?_ ?_ ?_ ?_
    · simp only [zero_mul, mul_zero, add_zero]
      rw [ζbi_l h]
    · simp
    · unfold Formalism.YangianSpanCharacter.Y.hf
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      rw [hQ, sub_add_cancel]
      exact h_entry (xif _ hbm) (xif _ hb) xixi _ _
    · simp only [mul_zero, zero_add]
      rw [ζiGG_l h]
  rw [lins, frame_mat, rht_row, lhs_red hF hP (hatN h hY _ _ 0), ← mul_assoc (io L.GG), ← hat_τ h hY,
    ins_left hτfree, diag_mat _ hd, ← Wd1.ins_mul _ _ _ hW, rhs_red (Wd11.freeOf2_mul hW hlm), Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, pf, l_mat m3 m4 m5 e1 e2]

end Formalism.FourierDecayAlt.P.Fr9

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `Fr9.minusTau`.
-/
theorem minus_letter_tau : Formalism.FourierDecayAlt.Fr.MinusTau := Fr9.minusTau

/- English proof (translation)
The claim follows from `Fr9.minusL`.
-/
theorem minus_letter_l : Formalism.FourierDecayAlt.Fr.MinusL := Fr9.minusL

end Formalism.FourierDecayAlt.P
