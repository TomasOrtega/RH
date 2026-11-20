import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos

noncomputable section

namespace PositivityTheory.KB.WhittakerCocycle

/- English proof (translation)
Unfold `ev`. Rewrite using `[Finsupp.linearCombination_apply]`. Simplify using `[smul_eq_mul]`.
-/
theorem ev_eq_lc {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F (Fin.partialProd g)) z := by
  unfold ev
  rw [Finsupp.linearCombination_apply]
  simp [smul_eq_mul]

/- English proof (translation)
Proceed by induction on `l using Fin.induction with`. Consider the case `zero`. Rewrite using `[Fin.partialProd_zero, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]`. Simplify using the standard rewrite rules. Consider the case `succ l ih`.

Rewrite using `[Fin.partialProd_succ, ih]`. Break down `lt_trichotomy (l : ℕ) j with h | h | h` into its components or cases. Establish `e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc` using `Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)`. Establish `e2 : j.succ.succAbove l.succ = l.castSucc.succ`. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]`.

Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2, Fin.partialProd_succ g l.castSucc, Fin.contractNth_apply_of_lt _ _ _ _ h]`. Establish `e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc` using `Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)`. Establish `e2 : j.succ.succAbove l.succ = l.succ.succ` using `Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)`.

Establish `e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.partialProd_succ g l.castSucc, Fin.contractNth_apply_of_eq _ _ _ _ h, mul_assoc]`. Establish `e1 : j.succ.succAbove l.castSucc = l.castSucc.succ` using `Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)`.

Establish `e2 : j.succ.succAbove l.succ = l.succ.succ` using `Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)`. Establish `e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.contractNth_apply_of_gt _ _ _ _ h]`.
-/
private theorem partialProd_contractNth_mul_eq_succAbove {G : Type} [Group G] {k : ℕ} (g : Fin (k + 1) → G) (j l : Fin (k + 1)) :
    Fin.partialProd (Fin.contractNth j (· * ·) g) l = Fin.partialProd g (j.succ.succAbove l) := by
  induction l using Fin.induction with
  | zero =>
    rw [Fin.partialProd_zero, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
    simp
  | succ l ih =>
    rw [Fin.partialProd_succ, ih]
    rcases lt_trichotomy (l : ℕ) j with h | h | h
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.castSucc.succ := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.castSucc, Fin.contractNth_apply_of_lt _ _ _ _ h]
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ := by
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.partialProd_succ g l.castSucc,
        Fin.contractNth_apply_of_eq _ _ _ _ h, mul_assoc]
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ := by
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.contractNth_apply_of_gt _ _ _ _ h]

/- English proof (translation)
Unfold `Inv at hb`. Use `Finsupp.lhom_ext (fun g r => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply]`. Establish `hs : Finsupp.single g r = r • Finsupp.single g (1 : ℝ)`. Rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`.

Rewrite using `[hs, map_smul, map_smul, map_smul]`. Use `congr 1`. Rewrite using `[Finsupp.linearCombination_single, one_smul]`. Unfold `bd`. Rewrite using `[Finsupp.linearCombination_single, one_smul, map_add, map_sum]`.

Simplify using `only [map_smul, map_zsmul, Finsupp.linearCombination_single, one_smul, smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]`. Unfold `dC`. Rewrite using `[Fin.sum_univ_succ]`. Use `congr 1`. Simplify using `only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]`.

Establish `h0` using `hb (g 0) (Fin.partialProd fun i => g i.succ)`. Simplify using `only [MonoidHom.id_apply, smul_eq_mul] at h0`. Rewrite using `[← h0]`. Use `congr 1`. Use function extensionality and compare the values at `l`.

Conclude with `Fin.partialProd_succ' g l`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Fin.val_succ]`. Simplify using `only [one_mul]`. Use `congr 2`.

Use function extensionality and compare the values at `l`. Conclude with `(partialProd_contractNth_mul_eq_succAbove g j l).symm`.
-/
theorem lc_dC {G : Type} [Group G] {k : ℕ} (b : (Fin (k + 1) → G) → ℝ)
    (hb : Inv (MonoidHom.id G) b) :
    Finsupp.linearCombination ℝ (fun g : Fin (k + 1) → G => dC b (Fin.partialProd g)) =
      (Finsupp.linearCombination ℝ (fun g : Fin k → G => b (Fin.partialProd g))).comp (bd G k) := by
  unfold Inv at hb
  refine Finsupp.lhom_ext (fun g r => ?_)
  rw [LinearMap.comp_apply]
  have hs : Finsupp.single g r = r • Finsupp.single g (1 : ℝ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, map_smul]
  congr 1
  rw [Finsupp.linearCombination_single, one_smul]
  unfold bd
  rw [Finsupp.linearCombination_single, one_smul, map_add, map_sum]
  simp only [map_smul, map_zsmul, Finsupp.linearCombination_single, one_smul, smul_eq_mul, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  unfold dC
  rw [Fin.sum_univ_succ]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    have h0 := hb (g 0) (Fin.partialProd fun i => g i.succ)
    simp only [MonoidHom.id_apply, smul_eq_mul] at h0
    rw [← h0]
    congr 1
    funext l
    exact Fin.partialProd_succ' g l
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fin.val_succ]
    simp only [one_mul]
    congr 2
    funext l
    exact (partialProd_contractNth_mul_eq_succAbove g j l).symm

/- English proof (translation)
Rewrite using `[ev_eq_lc, lc_dC b hb, LinearMap.comp_apply]`. Unfold `IsCyc at hz`. Rewrite using `[hz, map_zero]`.
-/
theorem pEv {G : Type} [Group G] {k : ℕ} (b : (Fin (k + 1) → G) → ℝ) (hb : Inv (MonoidHom.id G) b)
    (z : Chn G (k + 1)) (hz : IsCyc z) : ev (MonoidHom.id G) (dC b) 1 z = 0 := by
  rw [ev_eq_lc, lc_dC b hb, LinearMap.comp_apply]
  unfold IsCyc at hz
  rw [hz, map_zero]

end PositivityTheory.KB.WhittakerCocycle

end
