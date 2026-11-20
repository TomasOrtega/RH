import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SsD

/- English proof (translation)
Establish `h : (mat σ).det ≠ 0` using `by simp [mat]`. Unfold `toGL`. Rewrite using `[dif_neg h]`. Use extensionality with `i j`. Simplify using `[Matrix.GeneralLinearGroup.mkOfDetNeZero, mat]`.
-/
theorem toGL_mat (σ : SL(2, ℤ)) : toGL (mat σ) = (σ : GL (Fin 2) ℝ) := by
  have h : (mat σ).det ≠ 0 := by simp [mat]
  unfold toGL
  rw [dif_neg h]
  ext i j
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, mat]

/- English proof (translation)
Simplify using `[DdF, hkF, toGL_mat, ModularForm.SL_slash]`.
-/
theorem DdF_eq (k : ℤ) (σ : SL(2, ℤ)) (F : ℍ → ℂ) : DdF k σ F = F ∣[k] σ := by
  simp [DdF, hkF, toGL_mat, ModularForm.SL_slash]

/- English proof (translation)
Take `⟨i, j, hij, h⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (QuotientGroup.mk (a ^ n) : G ⧸ H))`. Establish `h' : (a ^ i)⁻¹ * a ^ j ∈ H` using `QuotientGroup.eq.mp h`. Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases. Use `⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩` and prove the remaining obligations. Establish `e : a ^ (j - i) = (a ^ i)⁻¹ * a ^ j`.

Rewrite using `[eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hlt.le]`. Rewrite using `[e]` and apply the resulting hypothesis. Use `⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩` and prove the remaining obligations. Establish `e : a ^ (i - j) = (a ^ j)⁻¹ * a ^ i`. Rewrite using `[eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hlt.le]`.

Rewrite using `[e]`. Simplify `H.inv_mem h'` using `[mul_inv_rev]`.
-/
theorem exists_pow_mem {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] (a : G) :
    ∃ m, 0 < m ∧ a ^ m ∈ H := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (QuotientGroup.mk (a ^ n) : G ⧸ H))
  have h' : (a ^ i)⁻¹ * a ^ j ∈ H := QuotientGroup.eq.mp h
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : a ^ (j - i) = (a ^ i)⁻¹ * a ^ j := by
      rw [eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rwa [e]
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : a ^ (i - j) = (a ^ j)⁻¹ * a ^ i := by
      rw [eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e]
    simpa [mul_inv_rev] using H.inv_mem h'

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `at h2`. Simplify using `[h2]`. Use `set p : ℂ[X] := X ^ m - C 1`. Use `set q : ℂ[X] := (X - C c) ^ n`.

Establish `hp : aeval D p v = 0` using `by simp [p, h1]`. Establish `hq : aeval D q v = 0`. Simplify `h2` using `[q, Module.algebraMap_end_eq_smul_id]`. Establish `hsq : Squarefree p` using `(separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero).squarefree`. Establish `hg : aeval D (EuclideanDomain.gcd p q) v = 0`.

Rewrite using `[EuclideanDomain.gcd_eq_gcd_ab p q, mul_comm p, mul_comm q, map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp, hq, map_zero, map_zero, add_zero]`. Establish `hgd : EuclideanDomain.gcd p q ∣ X - C c`. Conclude with `(hsq.squarefree_of_dvd (EuclideanDomain.gcd_dvd_left p q)).dvd_pow_iff_dvd hn.ne' |>.mp (EuclideanDomain.gcd_dvd_right p q)`. Take `⟨r, hr⟩` from `hgd`. Establish `: aeval D (X - C c) v = 0`.

Rewrite using `[hr, mul_comm, map_mul, Module.End.mul_apply, hg, map_zero]`. Simplify `this` using `[sub_eq_zero, Module.algebraMap_end_eq_smul_id]`.
-/
theorem eigen_of_pow_fix {V : Type*} [AddCommGroup V] [Module ℂ V] (D : Module.End ℂ V) {m : ℕ}
    (hm : 0 < m) (v : V) (c : ℂ) (n : ℕ) (h1 : (D ^ m) v = v)
    (h2 : ((D - c • LinearMap.id : Module.End ℂ V) ^ n) v = 0) : D v = c • v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h2
    simp [h2]
  set p : ℂ[X] := X ^ m - C 1
  set q : ℂ[X] := (X - C c) ^ n
  have hp : aeval D p v = 0 := by simp [p, h1]
  have hq : aeval D q v = 0 := by
    simpa [q, Module.algebraMap_end_eq_smul_id] using h2
  have hsq : Squarefree p :=
    (separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero).squarefree
  have hg : aeval D (EuclideanDomain.gcd p q) v = 0 := by
    rw [EuclideanDomain.gcd_eq_gcd_ab p q, mul_comm p, mul_comm q, map_add, map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp, hq, map_zero, map_zero,
      add_zero]
  have hgd : EuclideanDomain.gcd p q ∣ X - C c := by
    exact (hsq.squarefree_of_dvd (EuclideanDomain.gcd_dvd_left p q)).dvd_pow_iff_dvd hn.ne' |>.mp
      (EuclideanDomain.gcd_dvd_right p q)
  obtain ⟨r, hr⟩ := hgd
  have : aeval D (X - C c) v = 0 := by
    rw [hr, mul_comm, map_mul, Module.End.mul_apply, hg, map_zero]
  simpa [sub_eq_zero, Module.algebraMap_end_eq_smul_id] using this

noncomputable def slashEnd (k : ℤ) (σ : SL(2, ℤ)) : Module.End ℂ (ℍ → ℂ) where
  toFun F := F ∣[k] σ
  map_add' F G := SlashAction.add_slash _ _ _ _
  map_smul' c F := by simp [ModularForm.SL_smul_slash]

/- English proof (translation)
Proceed by induction on `j generalizing F with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ', SlashAction.slash_mul]`. Both sides reduce to the same expression.
-/
theorem slashEnd_pow (k : ℤ) (σ : SL(2, ℤ)) (j : ℕ) (F : ℍ → ℂ) :
    (slashEnd k σ ^ j) F = F ∣[k] (σ ^ j) := by
  induction j generalizing F with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ', SlashAction.slash_mul]
    rfl

end GlobalTheory.HeckeFamilyMatrices.SsD

namespace GlobalTheory.HeckeFamilyMatrices

open GlobalTheory.HeckeFamilyMatrices.SsD in

/- English proof (translation)
Introduce `N l k hN hl _ _ d σ _ f c n hn`. Use `haveI : NeZero N := ⟨by omega⟩`. Use `haveI : NeZero l := ⟨hl.ne_zero⟩`. Use `haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance`. Take `⟨m, hm, hmem⟩` from `exists_pow_mem (Lev N l) σ`.

Establish `hfix : (slashEnd (k : ℤ) σ ^ m) ⇑f = ⇑f`. Rewrite using `[slashEnd_pow]`. Conclude with `SlashInvariantForm.slash_action_eqn f _ ⟨_, hmem, rfl⟩`. Establish `hE : ⇑(slashEnd (k : ℤ) σ - c • LinearMap.id : Module.End ℂ (ℍ → ℂ)) = fun F => DdF (k : ℤ) σ F - c • F`. Use function extensionality and compare the values at `F`.

Simplify using `[slashEnd, DdF_eq]`. Establish `h2 : ((slashEnd (k : ℤ) σ - c • LinearMap.id : Module.End ℂ (ℍ → ℂ)) ^ n) ⇑f = 0`. Rewrite using `[Module.End.pow_apply, hE]`. Conclude with `hn`. Use `eigen_of_pow_fix _ hm _ c n hfix h2` as an intermediate fact.

Simplify `this` using `[slashEnd, DdF_eq]`.
-/
theorem diamond_genEigen_eigen : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
  ∀ (f : ModularForm (Lev N l) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => DdF (k : ℤ) σ F - c • F)^[n] ⇑f = 0 → DdF (k : ℤ) σ ⇑f = c • ⇑f := by
  intro N l k hN hl _ _ d σ _ f c n hn
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance
  obtain ⟨m, hm, hmem⟩ := exists_pow_mem (Lev N l) σ
  have hfix : (slashEnd (k : ℤ) σ ^ m) ⇑f = ⇑f := by
    rw [slashEnd_pow]
    exact SlashInvariantForm.slash_action_eqn f _ ⟨_, hmem, rfl⟩
  have hE : ⇑(slashEnd (k : ℤ) σ - c • LinearMap.id : Module.End ℂ (ℍ → ℂ)) = fun F => DdF (k : ℤ) σ F - c • F := by
    funext F
    simp [slashEnd, DdF_eq]
  have h2 : ((slashEnd (k : ℤ) σ - c • LinearMap.id : Module.End ℂ (ℍ → ℂ)) ^ n) ⇑f = 0 := by
    rw [Module.End.pow_apply, hE]
    exact hn
  have := eigen_of_pow_fix _ hm _ c n hfix h2
  simpa [slashEnd, DdF_eq] using this

end GlobalTheory.HeckeFamilyMatrices
