import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfSteps

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

section LeadLemmas

variable {K K' : Type*} [CommRing K] [CommRing K']

/- English proof (translation)
The claim follows from `(RingHom.map_det f A).symm`.
-/
theorem det_map' {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) : (A.map f).det = f A.det :=
  (RingHom.map_det f A).symm

/- English proof (translation)
Unfold `leadM`. Rewrite using `[dif_pos le_rfl]`. Both sides reduce to the same expression.
-/
theorem leadM_top {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : leadM A (r + 1) = A.det := by
  unfold leadM; rw [dif_pos le_rfl]; rfl

/- English proof (translation)
Unfold `leadM`. Use `split_ifs with hl`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem leadM_map {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (A.map f) l = f (leadM A l) := by
  unfold leadM
  split_ifs with hl
  · rw [RingHom.map_det]; rfl
  · simp

/- English proof (translation)
Unfold `leadM`. Use `split_ifs with hl`. Rewrite using `[show (c • A).submatrix (Fin.castLE hl) (Fin.castLE hl) = c • A.submatrix (Fin.castLE hl) (Fin.castLE hl) from rfl, Matrix.det_smul, Fintype.card_fin]`. Simplify using the standard rewrite rules.
-/
theorem leadM_smul {m : ℕ} (c : K) (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (c • A) l = c ^ l * leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [show (c • A).submatrix (Fin.castLE hl) (Fin.castLE hl) = c • A.submatrix (Fin.castLE hl) (Fin.castLE hl)
      from rfl, Matrix.det_smul, Fintype.card_fin]
  · simp

/- English proof (translation)
Unfold `leadM`. Use `split_ifs with hl`. Rewrite using `[← Matrix.det_transpose]`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem leadM_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) K) (l : ℕ) : leadM A.transpose l = leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [← Matrix.det_transpose]; rfl
  · rfl

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Fin.val h`. Establish `h2` using `a.isLt`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem castLE_ne_last {r : ℕ} (a : Fin r) : Fin.castLE (Nat.le_succ r) a ≠ Fin.last r := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := a.isLt
  simp at h1
  omega

/- English proof (translation)
Unfold `leadM`. Rewrite using `[dif_pos (Nat.le_succ r), dif_pos (Nat.le_succ r)]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `[Ecorner, castLE_ne_last a]`.
-/
theorem leadM_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    leadM (A + c • Ecorner r) r = leadM A r := by
  unfold leadM
  rw [dif_pos (Nat.le_succ r), dif_pos (Nat.le_succ r)]
  congr 1
  ext a b
  simp [Ecorner, castLE_ne_last a]

/- English proof (translation)
Establish `hE : A + c • Ecorner r = A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1)`. Use extensionality with `a b`. Distinguish the cases in `ha : a = Fin.last r`. Substitute `ha` using the available equality. Distinguish the cases in `hb : b = Fin.last r`.

Substitute `hb` using the available equality. Simplify using `[Ecorner]`. Simplify using `[Ecorner, hb]`. Simplify using `[Ecorner, ha]`. Rewrite using `[hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]`.

Use `congr 2`. Rewrite using `[Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]`. Establish `h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0`. Introduce `j`. Rewrite using `[Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]`.

Simplify using `only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self, Pi.single_eq_same, mul_one, Fin.succAbove_last]`. Establish `hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc = A.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[Matrix.updateRow_ne (Fin.castSucc_ne_last a)]`.

Both sides reduce to the same expression. Rewrite using `[hs, leadM, dif_pos (Nat.le_succ r)]`. Establish `hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1` using `Even.neg_one_pow ⟨_, rfl⟩`. Rewrite using `[hpow, one_mul]`.
-/
theorem det_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (A + c • Ecorner r).det = A.det + c * leadM A r := by
  have hE : A + c • Ecorner r =
      A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ecorner]
      · simp [Ecorner, hb]
    · simp [Ecorner, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r)) := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
    rfl
  rw [hs, leadM, dif_pos (Nat.le_succ r)]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

end LeadLemmas

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Break down `hs : M.split with _ | g` into its components or cases. Establish `e : Loc.HermSp.ZZplusOf M Zh T T' = Zh` using `by unfold Loc.HermSp.ZZplusOf; rw [hs]`. Rewrite using `[e, ← leadM_top]`. Conclude with `⟨Iff.rfl, Iff.rfl, fun _ h => h⟩`. Use `set q : F := (g.q : F) with hq`.

Establish `hq0 : q ≠ 0` using `fun h => g.q_irr.ne_zero (Subtype.ext h)`. Set `π₁ : E →+* F` to `(RingHom.fst F F).comp g.e.toRingEquiv.toRingHom`. Set `π₂ : E →+* F` to `(RingHom.snd F F).comp g.e.toRingEquiv.toRingHom`. Establish `hzero : ∀ x : E, x = 0 ↔ π₁ x = 0 ∧ π₂ x = 0`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Introduce and unpack `⟨h1, h2⟩`. Establish `: g.e x = 0` using `Prod.ext h1 h2`.

Conclude with `(map_eq_zero_iff g.e g.e.injective).1 this`. Establish `hunit : ∀ x : E, IsUnit x ↔ π₁ x ≠ 0 ∧ π₂ x ≠ 0`. Introduce `x`. Rewrite using `[← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]`. Both sides reduce to the same expression.

Establish `e1 : (Loc.HermSp.ZZplusOf M Zh T T').map π₁ = q⁻¹ • Zh.map π₁ + (T / q) • Ecorner r`. Use extensionality with `a b`. Unfold `Loc.HermSp.ZZplusOf`. Rewrite using `[hs]`. Distinguish the cases in `hab : a = Fin.last r ∧ b = Fin.last r`.

Apply the tactic sequence `simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring`. Apply the tactic sequence `simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring`. Establish `e2 : (Loc.HermSp.ZZplusOf M Zh T T').map π₂ = (-q⁻¹) • (Zh.map π₂).transpose + (-(T' / q)) • Ecorner r`. Use extensionality with `a b`. Unfold `Loc.HermSp.ZZplusOf`.

Rewrite using `[hs]`. Distinguish the cases in `hab : a = Fin.last r ∧ b = Fin.last r`. Apply the tactic sequence `simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring`. Apply the tactic sequence `simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring`. Establish `l1 : π₁ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = q⁻¹ ^ r * π₁ (leadM Zh r)`.

Rewrite using `[← leadM_map, e1, leadM_add_corner, leadM_smul, leadM_map]`. Establish `l2 : π₂ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = (-q⁻¹) ^ r * π₂ (leadM Zh r)`. Rewrite using `[← leadM_map, e2, leadM_add_corner, leadM_smul, leadM_transpose, leadM_map]`. Establish `hq1 : q⁻¹ ^ r ≠ 0` using `pow_ne_zero _ (inv_ne_zero hq0)`. Establish `hq2 : (-q⁻¹) ^ r ≠ 0` using `pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hzero, hzero (leadM _ r), l1, l2, mul_eq_zero, mul_eq_zero]`. Simplify using `[hq0]`. Rewrite using `[hunit, hunit (leadM _ r), l1, l2]`. Simplify using `[hq0]`.

Introduce `h0 hu`. Rewrite `hu` using `[leadM_top]`. Rewrite `hu`, the goal using `[hunit]`. Establish `z` using `(hzero _).1 h0`. Rewrite using `[← det_map', ← det_map', e1, e2, det_add_corner, det_add_corner, leadM_smul, leadM_smul, leadM_transpose, leadM_map, leadM_map, z.1, z.2, Matrix.det_smul, Matrix.det_smul, Matrix.det_transpose, det_map', det_map']`.

Simplify using `only [mul_zero, add_zero, Fintype.card_fin]`. Conclude with `⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hu.1, mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))) hu.2⟩`.
-/
theorem leadZZ_model (M : Loc.Model F E) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (leadM Zh r = 0 ↔ leadM (Loc.HermSp.ZZplusOf M Zh T T') r = 0) ∧
    (IsUnit (leadM Zh r) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf M Zh T T') r)) ∧
    (leadM Zh r = 0 → IsUnit (leadM Zh (r + 1)) → IsUnit (Loc.HermSp.ZZplusOf M Zh T T').det) := by
  rcases hs : M.split with _ | g
  · have e : Loc.HermSp.ZZplusOf M Zh T T' = Zh := by unfold Loc.HermSp.ZZplusOf; rw [hs]
    rw [e, ← leadM_top]
    exact ⟨Iff.rfl, Iff.rfl, fun _ h => h⟩
  · set q : F := (g.q : F) with hq
    have hq0 : q ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
    let π₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
    let π₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
    have hzero : ∀ x : E, x = 0 ↔ π₁ x = 0 ∧ π₂ x = 0 := by
      intro x
      constructor
      · rintro rfl; simp
      · rintro ⟨h1, h2⟩
        have : g.e x = 0 := Prod.ext h1 h2
        exact (map_eq_zero_iff g.e g.e.injective).1 this
    have hunit : ∀ x : E, IsUnit x ↔ π₁ x ≠ 0 ∧ π₂ x ≠ 0 := by
      intro x
      rw [← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
      rfl
    have e1 : (Loc.HermSp.ZZplusOf M Zh T T').map π₁ = q⁻¹ • Zh.map π₁ + (T / q) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have e2 : (Loc.HermSp.ZZplusOf M Zh T T').map π₂ = (-q⁻¹) • (Zh.map π₂).transpose + (-(T' / q)) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have l1 : π₁ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = q⁻¹ ^ r * π₁ (leadM Zh r) := by
      rw [← leadM_map, e1, leadM_add_corner, leadM_smul, leadM_map]
    have l2 : π₂ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = (-q⁻¹) ^ r * π₂ (leadM Zh r) := by
      rw [← leadM_map, e2, leadM_add_corner, leadM_smul, leadM_transpose, leadM_map]
    have hq1 : q⁻¹ ^ r ≠ 0 := pow_ne_zero _ (inv_ne_zero hq0)
    have hq2 : (-q⁻¹) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))
    refine ⟨?_, ?_, ?_⟩
    · rw [hzero, hzero (leadM _ r), l1, l2, mul_eq_zero, mul_eq_zero]
      simp [hq0]
    · rw [hunit, hunit (leadM _ r), l1, l2]
      simp [hq0]
    · intro h0 hu
      rw [leadM_top] at hu
      rw [hunit] at hu ⊢
      have z := (hzero _).1 h0
      rw [← det_map', ← det_map', e1, e2, det_add_corner, det_add_corner, leadM_smul, leadM_smul,
        leadM_transpose, leadM_map, leadM_map, z.1, z.2, Matrix.det_smul, Matrix.det_smul,
        Matrix.det_transpose, det_map', det_map']
      simp only [mul_zero, add_zero, Fintype.card_fin]
      exact ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hu.1,
        mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))) hu.2⟩

end Model

/- English proof (translation)
Introduce `p Zh T T'` and use `leadZZ_model (Zd.M p) Zh T T'`.
-/
theorem leadZZ_holds {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : LeadZZ Zd :=
  fun p Zh T T' => leadZZ_model (Zd.M p) Zh T T'

end Formalism.L2.SG.Pf.PCount
