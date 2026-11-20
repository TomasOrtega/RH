import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.EvhEqSum

noncomputable section

namespace PositivityTheory.KB

open ChainCochainPairing

/- English proof (translation)
Introduce `G _ k z _ hnb`. Take `⟨φ, hφz, hφp⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hnb inferInstance`. Establish `hφ : ∀ w, φ (bd G (k + 1) w) = 0`. Introduce `w`. Establish `hw : φ (bd G (k + 1) w) ∈ (LinearMap.range (bd G (k + 1))).map φ` using `Submodule.mem_map_of_mem (LinearMap.mem_range_self _ w)`.

Rewrite `hw` using `[hφp]`. Conclude with `(Submodule.mem_bot ℝ).mp hw`. Use `⟨fun y => φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g y`. Simplify using `[smul_eq_mul, mul_assoc]`.

Use function extensionality and compare the values at `y`. Establish `key : dC (fun y : Fin (k + 2) → G => φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1)) y = φ (bd G (k + 1) (Finsupp.single (fun i : Fin (k + 2) => (y i.castSucc)⁻¹ * y i.succ) 1))`. Simplify using `only [dC, bd, Finsupp.linearCombination_single, one_smul, map_add, map_sum, map_smul]`. Rewrite using `[Fin.sum_univ_succ]`. Use `congr 1`.

Simplify using `only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.succ_castSucc]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Fin.val_succ, smul_eq_mul]`. Use `congr 3`. Use function extensionality and compare the values at `l`.

Break down `lt_trichotomy (l : ℕ) (j : ℕ) with h | h | h` into its components or cases. Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ h]`. Establish `e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc` using `Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)`. Establish `e2 : j.succ.succAbove l.succ = l.succ.castSucc` using `Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)`. Rewrite using `[e1, e2, Fin.succ_castSucc]`.

Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ h]`. Establish `e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc` using `Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)`. Establish `e2 : j.succ.succAbove l.succ = l.succ.succ` using `Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)`. Rewrite using `[e1, e2, Fin.succ_castSucc]`. Use `group`.

Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ h]`. Establish `e1 : j.succ.succAbove l.castSucc = l.castSucc.succ` using `Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)`. Establish `e2 : j.succ.succAbove l.succ = l.succ.succ` using `Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)`. Rewrite using `[e1, e2, Fin.succ_castSucc]`. Rewrite using `[key, hφ]`.

Both sides reduce to the same expression. Establish `hev : ev (MonoidHom.id G) (fun y : Fin (k + 2) → G => φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1)) 1 z = φ z`. Unfold `ev`. Simplify using `only [MonoidHom.id_apply, smul_eq_mul, mul_one]`. Use `conv_rhs => rw [← Finsupp.sum_single z]`.

Simplify using `only [Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl (fun g _ => ?_)` and prove the remaining obligations. Establish `hg : (fun i : Fin (k + 1) => (Fin.partialProd g i.castSucc)⁻¹ * Fin.partialProd g i.succ) = g`. Use function extensionality and compare the values at `i`. Simplify using `[Fin.partialProd_succ]`.

Rewrite using `[hg, ← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[hev]`. Conclude with `hφz`.
-/
theorem sSep : SSep := by
  intro G _ k z _ hnb
  classical
  obtain ⟨φ, hφz, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnb inferInstance
  have hφ : ∀ w, φ (bd G (k + 1) w) = 0 := by
    intro w
    have hw : φ (bd G (k + 1) w) ∈ (LinearMap.range (bd G (k + 1))).map φ :=
      Submodule.mem_map_of_mem (LinearMap.mem_range_self _ w)
    rw [hφp] at hw
    exact (Submodule.mem_bot ℝ).mp hw
  refine ⟨fun y => φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1), ?_, ?_, ?_⟩
  · intro g y
    simp [smul_eq_mul, mul_assoc]
  · funext y
    have key : dC (fun y : Fin (k + 2) → G =>
        φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1)) y
        = φ (bd G (k + 1) (Finsupp.single (fun i : Fin (k + 2) => (y i.castSucc)⁻¹ * y i.succ) 1)) := by
      simp only [dC, bd, Finsupp.linearCombination_single, one_smul, map_add, map_sum, map_smul]
      rw [Fin.sum_univ_succ]
      congr 1
      · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.succ_castSucc]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Fin.val_succ, smul_eq_mul]
        congr 3
        funext l
        rcases lt_trichotomy (l : ℕ) (j : ℕ) with h | h | h
        · rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
        · rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
          group
        · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
    rw [key, hφ]
    rfl
  · have hev : ev (MonoidHom.id G) (fun y : Fin (k + 2) → G =>
        φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1)) 1 z = φ z := by
      unfold ev
      simp only [MonoidHom.id_apply, smul_eq_mul, mul_one]
      conv_rhs => rw [← Finsupp.sum_single z]
      simp only [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      have hg : (fun i : Fin (k + 1) => (Fin.partialProd g i.castSucc)⁻¹ * Fin.partialProd g i.succ) = g := by
        funext i
        simp [Fin.partialProd_succ]
      rw [hg, ← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hev]
    exact hφz

/- English proof (translation)
Introduce `_` and use `sSep`.
-/
theorem sSep_of : SChain → SSep := fun _ => sSep

end PositivityTheory.KB
