import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.UnipBLeColFixOne
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.QIterSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Take `⟨v, hv⟩` from `(GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k n u hu : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)`. Establish `hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v` using `hv.symm`. Rewrite using `[hv']`. Use `show (1 + colMat k n v.toAdd) a b = _`. Rewrite using `[Matrix.add_apply, Matrix.one_apply]`.

Establish `hc : colMat k n v.toAdd a b = 0`. Simplify using `only [colMat]`. Use `split_ifs with hb`. Establish `ha0 : ¬ (a : ℕ) < n` using `fun h' => hab ⟨by rw [hb, Fin.val_last], h'⟩`. Establish `ha : a = Fin.last n`.

Use `ext`. Use `a.isLt` as an intermediate fact. Rewrite using `[Fin.val_last]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[ha, Fin.lastCases_last]`.

Both sides reduce to the same expression. Rewrite using `[hc, add_zero]`.
-/
theorem mirU_apply {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin (n + 1))
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b = if a = b then 1 else 0 := by
  obtain ⟨v, hv⟩ := (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k n u hu :
    ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv']
  show (1 + colMat k n v.toAdd) a b = _
  rw [Matrix.add_apply, Matrix.one_apply]
  have hc : colMat k n v.toAdd a b = 0 := by
    simp only [colMat]
    split_ifs with hb
    · have ha0 : ¬ (a : ℕ) < n := fun h' => hab ⟨by rw [hb, Fin.val_last], h'⟩
      have ha : a = Fin.last n := by
        ext
        have := a.isLt
        rw [Fin.val_last]
        omega
      rw [ha, Fin.lastCases_last]
    · rfl
  rw [hc, add_zero]

/- English proof (translation)
Rewrite using `[blkAt_apply]`. Distinguish the cases in `ha : (a : ℕ) < n + 1`. Rewrite using `[dif_pos ha]`. Distinguish the cases in `hb : (b : ℕ) < n + 1`. Rewrite using `[dif_pos hb, mirU_apply u hu _ _ (by simpa using hab)]`.

Distinguish the cases in `e : a = b`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg e, if_neg]`. Introduce `e'`.

Conclude with `e (Fin.ext (by simpa using congrArg Fin.val e'))`. Rewrite using `[dif_neg hb, if_neg]`. Introduce `e`. Substitute `e` using the available equality. Conclude with `hb ha`.

Rewrite using `[dif_neg ha]`.
-/
theorem blkAt_mirU_apply {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin N)
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a b =
      if a = b then 1 else 0 := by
  rw [blkAt_apply]
  by_cases ha : (a : ℕ) < n + 1
  · rw [dif_pos ha]
    by_cases hb : (b : ℕ) < n + 1
    · rw [dif_pos hb, mirU_apply u hu _ _ (by simpa using hab)]
      by_cases e : a = b
      · subst e
        simp
      · rw [if_neg e, if_neg]
        intro e'
        exact e (Fin.ext (by simpa using congrArg Fin.val e'))
    · rw [dif_neg hb, if_neg]
      intro e
      subst e
      exact hb ha
  · rw [dif_neg ha]

/- English proof (translation)
Use `⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => ?_⟩` and prove the remaining obligations. Rewrite `hji` using `[Fin.lt_def]`. Rewrite using `[blkAt_mirU_apply h u hu i j (by omega), if_neg (fun e => by rw [e] at hji; omega)]`. Rewrite using `[blkAt_mirU_apply h u hu i i (by omega), if_pos rfl]`. Rewrite using `[blkAt_mirU_apply h u hu i j (by omega), Matrix.one_apply]`.
-/
theorem blkAt_mirU_mem {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) ∈ derUnip k N n := by
  refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => ?_⟩
  · rw [Fin.lt_def] at hji
    rw [blkAt_mirU_apply h u hu i j (by omega), if_neg (fun e => by rw [e] at hji; omega)]
  · rw [blkAt_mirU_apply h u hu i i (by omega), if_pos rfl]
  · rw [blkAt_mirU_apply h u hu i j (by omega), Matrix.one_apply]

/- English proof (translation)
Rewrite using `[derChar_def]`. Simplify using `only [whitCharFrom, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]`. Rewrite using `[Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]`. Introduce `p hp`. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hp).2`.

Use `show ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0`. Rewrite using `[blkAt_mirU_apply h u hu _ _ (by omega), if_neg (fun e => by rw [e] at h1; omega)]`.
-/
theorem derChar_blkAt_mirU (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n)
    (hu : mirabolicProjection k n u = 1) : derChar k ψ N n ⟨_, blkAt_mirU_mem h u hu⟩ = 1 := by
  rw [derChar_def]
  simp only [whitCharFrom, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  show ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
  rw [blkAt_mirU_apply h u hu _ _ (by omega), if_neg (fun e => by rw [e] at h1; omega)]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[blkAt_apply, blkAt_apply]`. Establish `hl : ∀ (a' b' : Fin (n + 1)), (((levi k n g : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a' b' = glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a' b'` using `fun _ _ => rfl`. Distinguish the cases in `ha : (a : ℕ) < n`. Establish `ha' : (a : ℕ) < n + 1` using `by omega`.

Rewrite using `[dif_pos ha', dif_pos ha]`. Distinguish the cases in `hb : (b : ℕ) < n`. Establish `hb' : (b : ℕ) < n + 1` using `by omega`. Rewrite using `[dif_pos hb', dif_pos hb, hl, glEmbMat_apply']`. Simplify using `only [ha, hb, dif_pos]`.

Rewrite using `[dif_neg hb]`. Distinguish the cases in `hb' : (b : ℕ) < n + 1`. Rewrite using `[dif_pos hb', hl, glEmbMat_apply']`. Simplify using `only [ha, hb, dif_pos, dif_neg, not_false_eq_true]`. Rewrite using `[dif_neg hb']`.

Rewrite using `[dif_neg ha]`. Distinguish the cases in `ha' : (a : ℕ) < n + 1`. Rewrite using `[dif_pos ha']`. Distinguish the cases in `hb' : (b : ℕ) < n + 1`. Rewrite using `[dif_pos hb', hl, glEmbMat_apply']`.

Simplify using `only [ha, dif_neg, not_false_eq_true]`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `rw [dif_neg hb'] split_ifs with e <;> first | rfl | (simp only [Fin.ext_iff] at e; omega)`. Rewrite using `[dif_neg ha']`.
-/
theorem blkAt_levi {n N : ℕ} (h : n + 1 ≤ N) (g : GL (Fin n) k) :
    blkAt k (n + 1) N h ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = blkAt k n N (by omega) g := by
  ext a b
  rw [blkAt_apply, blkAt_apply]
  have hl : ∀ (a' b' : Fin (n + 1)), (((levi k n g : Mir k n) : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) a' b' = glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a' b' :=
    fun _ _ => rfl
  by_cases ha : (a : ℕ) < n
  · have ha' : (a : ℕ) < n + 1 := by omega
    rw [dif_pos ha', dif_pos ha]
    by_cases hb : (b : ℕ) < n
    · have hb' : (b : ℕ) < n + 1 := by omega
      rw [dif_pos hb', dif_pos hb, hl, glEmbMat_apply']
      simp only [ha, hb, dif_pos]
    · rw [dif_neg hb]
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]
      · rw [dif_neg hb']
  · rw [dif_neg ha]
    by_cases ha' : (a : ℕ) < n + 1
    · rw [dif_pos ha']
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, dif_neg, not_false_eq_true]
        simp only [Fin.ext_iff]
      · rw [dif_neg hb']
        split_ifs with e <;> first | rfl | (simp only [Fin.ext_iff] at e; omega)
    · rw [dif_neg ha']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Establish `hl` using `(mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]`. Rewrite using `[hl, Fin.succAbove_last]`. Simplify using `only [eLast, Pi.single_eq_same, mul_one, Fin.val_last]`.

Rewrite using `[Even.neg_one_pow ⟨n, rfl⟩, one_mul]`. Both sides reduce to the same expression. Introduce `j _ hj`. Rewrite using `[hl, eLast, Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem det_mir {n : ℕ} (p : Mir k n) :
    Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hl := (mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · rw [hl, Fin.succAbove_last]
    simp only [eLast, Pi.single_eq_same, mul_one, Fin.val_last]
    rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]
    rfl
  · intro j _ hj
    rw [hl, eLast, Pi.single_eq_of_ne hj]
    simp
  · simp

/- English proof (translation)
Establish `hu1 : mirabolicProjection k n (p * (levi k n (mirabolicProjection k n p))⁻¹) = 1`. Rewrite using `[map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]`. Establish `hp : (p : GL (Fin (n + 1)) k) = ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k) * ((levi k n (mirabolicProjection k n p) : Mir k n) : GL (Fin (n + 1)) k)`. Rewrite using `[← Subgroup.coe_mul, inv_mul_cancel_right]`. Establish `hkill : ∀ w, q (π (blkAt k (n + 1) N h ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k)) w) = q w`.

Introduce `w`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Apply `hq2` to reduce the goal to its premises. Use `Submodule.subset_span ⟨⟨_, blkAt_mirU_mem h _ hu1⟩, w, ?_⟩` and prove the remaining obligations. Rewrite using `[derChar_blkAt_mirU ψ h _ hu1]`.

Simplify using the standard rewrite rules. Use `⟨fun v => ?_, det_mir p⟩` and prove the remaining obligations. Use `conv_lhs => rw [hp]`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, hkill, blkAt_levi, hq1]`.
-/
theorem mir_act (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup D] [Module ℂ D] (π : Representation ℂ (GL (Fin N) k) V) (ρ' : Representation ℂ (GL (Fin n) k) D)
    (q : V →ₗ[ℂ] D) (hq1 : ∀ g v, q (π (blkAt k n N (by omega) g) v) = ρ' g (q v))
    (hq2 : twKer π (derUnip k N n) (derChar k ψ N n) ≤ LinearMap.ker q) (p : Mir k n) :
    (∀ v, q (π (blkAt k (n + 1) N h p) v) = ρ' (mirabolicProjection k n p) (q v)) ∧
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hu1 : mirabolicProjection k n (p * (levi k n (mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]
  have hp : (p : GL (Fin (n + 1)) k) = ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k) *
      ((levi k n (mirabolicProjection k n p) : Mir k n) : GL (Fin (n + 1)) k) := by
    rw [← Subgroup.coe_mul, inv_mul_cancel_right]
  have hkill : ∀ w, q (π (blkAt k (n + 1) N h
      ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k)) w) = q w := by
    intro w
    rw [← sub_eq_zero, ← map_sub]
    apply hq2
    refine Submodule.subset_span ⟨⟨_, blkAt_mirU_mem h _ hu1⟩, w, ?_⟩
    rw [derChar_blkAt_mirU ψ h _ hu1]
    simp
  refine ⟨fun v => ?_, det_mir p⟩
  conv_lhs => rw [hp]
  rw [map_mul, map_mul, Module.End.mul_apply, hkill, blkAt_levi, hq1]

end PositivityTheory.RgUd.Form.U.Asm
