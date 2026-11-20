import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCyc

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {p q r s : ℕ}

/- English proof (translation)
Unfold `quadT`. Simplify using `only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]`.
-/
theorem quadT_sub {ι E : Type*} [Fintype ι] [Ring E] [Algebra ℂ E] (R L : ι → E) (A B : Matrix ι ι ℂ) :
    quadT R L (A - B) = quadT R L A - quadT R L B := by
  unfold quadT
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

/- English proof (translation)
Establish `h1` using `quadT_mul (raiB (p := p) (q := q) (r := r) (s := s)) lowB low_rai M N`. Establish `h2` using `quadT_mul (raiB (p := p) (q := q) (r := r) (s := s)) lowB low_rai N M`. Establish `h3` using `quartT_comm (raiB (p := p) (q := q) (r := r) (s := s)) lowB rai_rai low_low M N`. Establish `ht : (∑ l, (M * N - N * M) l l * (1 / 2 : ℂ)) = 0`. Rewrite using `[← Finset.sum_mul]`.

Establish `: (∑ l, (M * N - N * M) l l) = (M * N - N * M).trace` using `rfl`. Rewrite using `[this, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, zero_mul]`. Rewrite using `[omAct_eq, omAct_eq, omAct_eq, ht, zero_smul, add_zero, quadT_sub]`. Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1, h2, h3, smul_add, smul_smul]`. Rewrite using `[mul_comm (∑ l, M l l * (1 / 2 : ℂ))]`.

Normalize the expressions using the abelian group laws.
-/
theorem omAct_lie (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M * omAct p q r s N - omAct p q r s N * omAct p q r s M = omAct p q r s (M * N - N * M) := by
  have h1 := quadT_mul (raiB (p := p) (q := q) (r := r) (s := s)) lowB low_rai M N
  have h2 := quadT_mul (raiB (p := p) (q := q) (r := r) (s := s)) lowB low_rai N M
  have h3 := quartT_comm (raiB (p := p) (q := q) (r := r) (s := s)) lowB rai_rai low_low M N
  have ht : (∑ l, (M * N - N * M) l l * (1 / 2 : ℂ)) = 0 := by
    rw [← Finset.sum_mul]
    have : (∑ l, (M * N - N * M) l l) = (M * N - N * M).trace := rfl
    rw [this, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, zero_mul]
  rw [omAct_eq, omAct_eq, omAct_eq, ht, zero_smul, add_zero, quadT_sub]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1, h2, h3, smul_add, smul_smul]
  rw [mul_comm (∑ l, M l l * (1 / 2 : ℂ))]
  abel

/- English proof (translation)
Introduce `X Y`. Establish `h` using `omAct_lie (Matrix.kroneckerMap (· * ·) X (1 : Mat r s)) (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s))`. Rewrite `h` using `[← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, map_sub]`. Rewrite using `[map_sub]`. Conclude with `h`.
-/
theorem lie1 (p q r s : ℕ) : IsLie (fockAct1 p q r s) := by
  intro X Y
  have h := omAct_lie (Matrix.kroneckerMap (· * ·) X (1 : Mat r s)) (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, map_sub] at h
  rw [map_sub]
  exact h

/- English proof (translation)
Introduce `X Y`. Establish `h` using `omAct_lie (Matrix.kroneckerMap (· * ·) (1 : Mat p q) X) (Matrix.kroneckerMap (· * ·) (1 : Mat p q) Y)`. Rewrite `h` using `[← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, map_sub]`. Rewrite using `[map_sub]`. Conclude with `h`.
-/
theorem lie2 (p q r s : ℕ) : IsLie (fockAct2 p q r s) := by
  intro X Y
  have h := omAct_lie (Matrix.kroneckerMap (· * ·) (1 : Mat p q) X) (Matrix.kroneckerMap (· * ·) (1 : Mat p q) Y)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, map_sub] at h
  rw [map_sub]
  exact h

/- English proof (translation)
Introduce `X Y`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Establish `h` using `LinearMap.congr_fun (lie2 p q r s X Y) f`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Establish `ht : (X * Y - Y * X).trace = 0`.

Rewrite using `[Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, twAct_apply]`. Rewrite using `[ht, mul_zero, zero_smul, add_zero, ← h]`. Simplify using `only [map_add, map_smul, smul_add, smul_smul]`. Rewrite using `[mul_comm (τ * X.trace)]`.

Normalize the expressions using the abelian group laws.
-/
theorem lie_tw (p q r s : ℕ) (τ : ℂ) : IsLie (twAct p q r s τ) := by
  intro X Y
  refine LinearMap.ext fun f => ?_
  have h := LinearMap.congr_fun (lie2 p q r s X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have ht : (X * Y - Y * X).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, twAct_apply]
  rw [ht, mul_zero, zero_smul, add_zero, ← h]
  simp only [map_add, map_smul, smul_add, smul_smul]
  rw [mul_comm (τ * X.trace)]
  abel

/- English proof (translation)
Introduce `X Y`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨f, rfl⟩ : ∃ f, thMkC p q r s c f = x` from `Submodule.mkQ_surjective _ x`. Establish `h` using `LinearMap.congr_fun (lie_tw p q r s τ X Y) f`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply]`. Rewrite using `[thAct_mk, thAct_mk, thAct_mk, thAct_mk, thAct_mk, ← h, map_sub]`.
-/
theorem lie_th (p q r s : ℕ) (c τ : ℂ) : IsLie (thAct p q r s c τ) := by
  intro X Y
  refine LinearMap.ext fun x => ?_
  obtain ⟨f, rfl⟩ : ∃ f, thMkC p q r s c f = x := Submodule.mkQ_surjective _ x
  have h := LinearMap.congr_fun (lie_tw p q r s τ X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [thAct_mk, thAct_mk, thAct_mk, thAct_mk, thAct_mk, ← h, map_sub]

def sgnC (l : Ln p q r s) : ℂ := if linePos l = true then 1 else -1

/- English proof (translation)
Unfold `raiB lowB sgnC`. Distinguish the cases in `h : linePos l = true`. Simplify using `only [h, if_true, one_mul]`. Conclude with `PI.FHS.fockInner_X_mul l P Q`. Rewrite using `[if_neg h, if_neg h, if_neg h, LinearMap.neg_apply, PI.FHS.fockInner_neg_left, neg_one_mul]`.

Conclude with `congrArg Neg.neg (PI.FHS.fockInner_pderiv l P Q)`.
-/
theorem rai_adj (l : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (raiB l P) Q = sgnC l * fockInner P (lowB l Q) := by
  unfold raiB lowB sgnC
  by_cases h : linePos l = true
  · simp only [h, if_true, one_mul]
    exact PI.FHS.fockInner_X_mul l P Q
  · rw [if_neg h, if_neg h, if_neg h, LinearMap.neg_apply, PI.FHS.fockInner_neg_left, neg_one_mul]
    exact congrArg Neg.neg (PI.FHS.fockInner_pderiv l P Q)

/- English proof (translation)
Unfold `raiB lowB sgnC`. Distinguish the cases in `h : linePos l = true`. Simplify using `only [h, if_true, one_mul]`. Conclude with `PI.FHS.fockInner_pderiv l P Q`. Rewrite using `[if_neg h, if_neg h, if_neg h, LinearMap.neg_apply, PI.FHS.fockInner_neg_right, neg_one_mul, neg_neg]`.

Conclude with `PI.FHS.fockInner_X_mul l P Q`.
-/
theorem low_adj (l : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (lowB l P) Q = sgnC l * fockInner P (raiB l Q) := by
  unfold raiB lowB sgnC
  by_cases h : linePos l = true
  · simp only [h, if_true, one_mul]
    exact PI.FHS.fockInner_pderiv l P Q
  · rw [if_neg h, if_neg h, if_neg h, LinearMap.neg_apply, PI.FHS.fockInner_neg_right, neg_one_mul, neg_neg]
    exact PI.FHS.fockInner_X_mul l P Q

/- English proof (translation)
Unfold `omE`. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply]`. Rewrite using `[PI.FHS.fockInner_add_left, PI.FHS.fockInner_add_right, rai_adj, low_adj, mul_add, mul_assoc]`. Use `congr 1`. Distinguish the cases in `h : l = l'`.

Substitute `h` using the available equality. Establish `hs : sgnC l * sgnC l = 1`. Apply the tactic sequence `unfold sgnC; split_ifs <;> simp`. Rewrite using `[hs, one_mul, if_pos rfl]`. Simplify using `only [LinearMap.smul_apply, Module.End.one_apply]`.

Rewrite using `[PI.FHS.fockInner_smul_left, PI.FHS.fockInner_smul_right]`. Use `congr 1`. Simplify using `[map_ofNat]`. Rewrite using `[if_neg h, if_neg (Ne.symm h)]`. Simplify using `only [LinearMap.zero_apply]`.

Rewrite using `[PI.FHS.fockInner_zero_left, PI.FHS.fockInner_zero_right, mul_zero]`.
-/
theorem omE_adj_gen (l l' : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (omE l l' P) Q = (sgnC l * sgnC l') * fockInner P (omE l' l Q) := by
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply]
  rw [PI.FHS.fockInner_add_left, PI.FHS.fockInner_add_right, rai_adj, low_adj, mul_add, mul_assoc]
  congr 1
  by_cases h : l = l'
  · subst h
    have hs : sgnC l * sgnC l = 1 := by
      unfold sgnC; split_ifs <;> simp
    rw [hs, one_mul, if_pos rfl]
    simp only [LinearMap.smul_apply, Module.End.one_apply]
    rw [PI.FHS.fockInner_smul_left, PI.FHS.fockInner_smul_right]
    congr 1
    simp [map_ofNat]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.zero_apply]
    rw [PI.FHS.fockInner_zero_left, PI.FHS.fockInner_zero_right, mul_zero]

/- English proof (translation)
Rewrite using `[PI.FHS.fockAct1_eq, PI.FHS.omAct_apply]`. Simplify using `only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single a (by intro x _ hx; simp [Ne.symm hx]) (by simp)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single b (by intro x _ hx; simp [Ne.symm hx]) (by simp)]`.

Simplify using the standard rewrite rules.
-/
theorem fockAct1_unit (a b : Ix p q) (P : Pol p q r s) :
    fockAct1 p q r s (Eab a b) P = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (b, c) P := by
  rw [PI.FHS.fockAct1_eq, PI.FHS.omAct_apply]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single a (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single b (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  simp

/- English proof (translation)
Rewrite using `[PI.FHS.fockAct2_eq, PI.FHS.omAct_apply]`. Simplify using `only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single c (by intro x _ hx; simp [Ne.symm hx]) (by simp)]`. Rewrite using `[Finset.sum_eq_single a (by intro x _ hx; simp [Ne.symm hx]) (by simp)]`.

Rewrite using `[Finset.sum_eq_single d (by intro x _ hx; simp [Ne.symm hx]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem fockAct2_unit (c d : Ix r s) (P : Pol p q r s) :
    fockAct2 p q r s (Eab c d) P = ∑ a : Ix p q, omE ((a, c) : Ln p q r s) (a, d) P := by
  rw [PI.FHS.fockAct2_eq, PI.FHS.omAct_apply]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single c (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single a (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single d (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  simp

/- English proof (translation)
Rewrite using `[fockAct1_unit, fockAct1_unit, PI.FHS.fockInner_sum_left, PI.FHS.fockInner_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[omE_adj_gen]`. Use `congr 1`. Apply the tactic sequence `cases a <;> cases b <;> cases c <;> simp [sgnC, epsB, linePos, sameBlock]`.
-/
theorem fock_inner_adjoint_first (a b : Ix p q) (u v : Pol p q r s) :
    fockInner (fockAct1 p q r s (Eab a b) u) v = epsB a b * fockInner u (fockAct1 p q r s (Eab b a) v) := by
  rw [fockAct1_unit, fockAct1_unit, PI.FHS.fockInner_sum_left, PI.FHS.fockInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [omE_adj_gen]
  congr 1
  cases a <;> cases b <;> cases c <;> simp [sgnC, epsB, linePos, sameBlock]

/- English proof (translation)
Rewrite using `[fockAct2_unit, fockAct2_unit, PI.FHS.fockInner_sum_left, PI.FHS.fockInner_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[omE_adj_gen]`. Use `congr 1`. Apply the tactic sequence `cases a <;> cases b <;> cases c <;> simp [sgnC, epsB, linePos, sameBlock]`.
-/
theorem fock_inner_adjoint_second (a b : Ix r s) (u v : Pol p q r s) :
    fockInner (fockAct2 p q r s (Eab a b) u) v = epsB a b * fockInner u (fockAct2 p q r s (Eab b a) v) := by
  rw [fockAct2_unit, fockAct2_unit, PI.FHS.fockInner_sum_left, PI.FHS.fockInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [omE_adj_gen]
  congr 1
  cases a <;> cases b <;> cases c <;> simp [sgnC, epsB, linePos, sameBlock]

/- English proof (translation)
Introduce `a b u v` and use `fock_inner_adjoint_first a b u v`.
-/
theorem adj1 (p q r s : ℕ) : AdjG (fvAct1 p q r s) := fun a b u v => fock_inner_adjoint_first a b u v

/- English proof (translation)
Introduce `a b u v` and use `fock_inner_adjoint_second a b u v`.
-/
theorem adj2 (p q r s : ℕ) : AdjG (fvAct2 p q r s) := fun a b u v => fock_inner_adjoint_second a b u v

/- English proof (translation)
The claim follows from `PI.FockOneDegW.Swap.mem_hwSub_iff act μ v`.
-/
theorem hwK_of_hwSub {m n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat m n →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix m n → ℚ} {v : V} : v ∈ hwSub act μ ↔ HwK (units act) μ v :=
  PI.FockOneDegW.Swap.mem_hwSub_iff act μ v

/- English proof (translation)
Establish `hL : IsLie (fvAct2 p q r s)` using `lie2 p q r s`. Establish `hw : HwK (units (fvAct2 p q r s)) ν (show FV p q r s from g)` using `hwK_of_hwSub.1 hg.2`. Conclude with `dom_of_hw (adjK_of_adjG (adj2 p q r s)) (glK_of_lie hL) hw hg.1`.
-/
theorem dom2 {ν : Ix r s → ℚ} {g : Pol p q r s} (hg : IsHW (fockAct2 p q r s) ν g) : Dom ν := by
  have hL : IsLie (fvAct2 p q r s) := lie2 p q r s
  have hw : HwK (units (fvAct2 p q r s)) ν (show FV p q r s from g) := hwK_of_hwSub.1 hg.2
  exact dom_of_hw (adjK_of_adjG (adj2 p q r s)) (glK_of_lie hL) hw hg.1

/- English proof (translation)
Establish `hint : ∀ (Y : Mat r s) (w : Pol p q r s), fockAct1 r s p q Y (PI.FockOneDegW.Swap.swL p q r s w) = PI.FockOneDegW.Swap.swL p q r s (fockAct2 p q r s Y w)` using `fun Y w => (PI.FockOneDegW.Swap.rename_fockAct2 Y w).symm`. Establish `hinj : Function.Injective (PI.FockOneDegW.Swap.swL p q r s)` using `PI.FockOneDegW.Swap.rename_sw_injective p q r s`. Take `⟨ν, v, hv, hw⟩` from `PI.FockOneDegW.hwExist r s p q (U.map (PI.FockOneDegW.Swap.swL p q r s)) inferInstance (by`. Introduce `h`. Apply `h0` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: PI.FockOneDegW.Swap.swL p q r s x ∈ (⊥ : Submodule ℂ (Pol r s p q))` using `h ▸ Submodule.mem_map_of_mem hx`. Rewrite `this`, the goal using `[Submodule.mem_bot]`. Conclude with `hinj (by rw [this, map_zero])) (by`.

Introduce and unpack `a b hab _ ⟨w, hw, rfl⟩`. Rewrite using `[hint]`. Conclude with `Submodule.mem_map_of_mem (hU a b hab w hw))`. Take `⟨w, hw', rfl⟩` from `hv`. Conclude with `⟨ν, w, hw', PI.FockOneDegW.Swap.isHW_of_map _ _ _ hinj hint ν w hw⟩`.
-/
theorem hwExist2 (U : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ U] (h0 : U ≠ ⊥)
    (hU : KSt (units (fockAct2 p q r s)) U) : ∃ ν v, v ∈ U ∧ IsHW (fockAct2 p q r s) ν v := by
  have hint : ∀ (Y : Mat r s) (w : Pol p q r s),
      fockAct1 r s p q Y (PI.FockOneDegW.Swap.swL p q r s w) =
        PI.FockOneDegW.Swap.swL p q r s (fockAct2 p q r s Y w) :=
    fun Y w => (PI.FockOneDegW.Swap.rename_fockAct2 Y w).symm
  have hinj : Function.Injective (PI.FockOneDegW.Swap.swL p q r s) :=
    PI.FockOneDegW.Swap.rename_sw_injective p q r s
  obtain ⟨ν, v, hv, hw⟩ := PI.FockOneDegW.hwExist r s p q (U.map (PI.FockOneDegW.Swap.swL p q r s))
    inferInstance (by
      intro h
      apply h0
      rw [eq_bot_iff]
      intro x hx
      have : PI.FockOneDegW.Swap.swL p q r s x ∈ (⊥ : Submodule ℂ (Pol r s p q)) :=
        h ▸ Submodule.mem_map_of_mem hx
      rw [Submodule.mem_bot] at this ⊢
      exact hinj (by rw [this, map_zero])) (by
      rintro a b hab _ ⟨w, hw, rfl⟩
      rw [hint]
      exact Submodule.mem_map_of_mem (hU a b hab w hw))
  obtain ⟨w, hw', rfl⟩ := hv
  exact ⟨ν, w, hw', PI.FockOneDegW.Swap.isHW_of_map _ _ _ hinj hint ν w hw⟩

/- English proof (translation)
Establish `hL : IsLie (fvAct1 p q r s)` using `lie1 p q r s`. Establish `hw : HwK (units (fvAct1 p q r s)) μ (show FV p q r s from x)` using `hwK_of_hwSub.1 hx`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`.

Conclude with `hw.1 a`. Rewrite using `[if_neg h, zero_smul]`. Break down `PI.FockOneDegW.Core.posC_or a b hab h with h1 | h1` into its components or cases. Conclude with `hw.2 a b h1`. Conclude with `low_kill (adjK_of_adjG (adj1 p q r s)) (glK_of_lie hL) hw h1 (hμ a b hab).symm`.
-/
theorem scalar_of_hw {μ : Ix p q → ℚ} (hμ : ∀ a b, sameBlock a b → μ a = μ b) {x : Pol p q r s}
    (hx : x ∈ hwSub (fockAct1 p q r s) μ) (a b : Ix p q) (hab : sameBlock a b) :
    fockAct1 p q r s (Eab a b) x = (if a = b then ((μ a : ℚ) : ℂ) else 0) • x := by
  have hL : IsLie (fvAct1 p q r s) := lie1 p q r s
  have hw : HwK (units (fvAct1 p q r s)) μ (show FV p q r s from x) := hwK_of_hwSub.1 hx
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    exact hw.1 a
  · rw [if_neg h, zero_smul]
    rcases PI.FockOneDegW.Core.posC_or a b hab h with h1 | h1
    · exact hw.2 a b h1
    · exact low_kill (adjK_of_adjG (adj1 p q r s)) (glK_of_lie hL) hw h1 (hμ a b hab).symm

/- English proof (translation)
Unfold `polChi jointEig`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h a b hab`. Establish `h1` using `h ⟨Eab a b, PI.FockOneDegW.isKC_Eab hab⟩`.

Use `h1.trans ?_` and prove the remaining obligations. Use `congr 1`. Distinguish the cases in `e : a = b`. Substitute `e` using the available equality. Simplify using `[chiTr, Eab]`.

Simplify using `[chiTr, Eab, e, Matrix.trace_single_eq_of_ne _ _ _ e]`. Introduce and unpack `h ⟨Z, hZ⟩`. Express the relevant statement in the definitionally equal form `fockAct1 p q r s Z x = chiTr c Z • x`. Rewrite using `[act_eq_sum (fockAct1 p q r s) Z]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply]`.

Establish `key : ∀ a b, Z a b • fockAct1 p q r s (Eab a b) x = (if a = b then c * Z a a else 0) • x`. Introduce `a b`. Distinguish the cases in `hab : sameBlock a b`. Rewrite using `[h a b hab, smul_smul]`. Distinguish the cases in `e : a = b`.

Substitute `e` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, mul_comm]`. Rewrite using `[if_neg e, if_neg e, mul_zero]`. Establish `e : a ≠ b`. Introduce and unpack `rfl`.

Apply the tactic sequence `exact hab (by cases a <;> trivial)`. Rewrite using `[hZ a b hab, if_neg e, zero_smul, zero_smul]`. Simplify using `only [key, ← Finset.sum_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `congr 1`. Simplify using `only [chiTr, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]`.
-/
theorem mem_polChi_iff (c : ℂ) (x : Pol p q r s) : x ∈ polChi p q r s c ↔
    ∀ a b, sameBlock a b → fockAct1 p q r s (Eab a b) x = (if a = b then c else 0) • x := by
  unfold polChi jointEig
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h a b hab
    have h1 := h ⟨Eab a b, PI.FockOneDegW.isKC_Eab hab⟩
    refine h1.trans ?_
    congr 1
    by_cases e : a = b
    · subst e
      simp [chiTr, Eab]
    · simp [chiTr, Eab, e, Matrix.trace_single_eq_of_ne _ _ _ e]
  · rintro h ⟨Z, hZ⟩
    change fockAct1 p q r s Z x = chiTr c Z • x
    rw [act_eq_sum (fockAct1 p q r s) Z]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have key : ∀ a b, Z a b • fockAct1 p q r s (Eab a b) x = (if a = b then c * Z a a else 0) • x := by
      intro a b
      by_cases hab : sameBlock a b
      · rw [h a b hab, smul_smul]
        by_cases e : a = b
        · subst e
          rw [if_pos rfl, if_pos rfl, mul_comm]
        · rw [if_neg e, if_neg e, mul_zero]
      · have e : a ≠ b := by
          rintro rfl
          exact hab (by cases a <;> trivial)
        rw [hZ a b hab, if_neg e, zero_smul, zero_smul]
    simp only [key, ← Finset.sum_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    simp only [chiTr, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]

/- English proof (translation)
Substitute `hc` using the available equality. Rewrite using `[mem_polChi_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(PI.FockOneDegW.Swap.mem_hwSub_iff _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rw [h a a (by cases a <;> trivial), if_pos rfl]`. Rewrite using `[h a b (PI.FockOneDegW.Core.posC_sb a b hab), if_neg (PI.FockOneDegW.Core.posC_ne a b hab), zero_smul]`. Introduce `h a b hab`. Conclude with `scalar_of_hw (μ := fun _ => c0) (fun _ _ _ => rfl) h a b hab`.
-/
theorem mem_polChi_iff_hw (c : ℂ) (c0 : ℚ) (hc : c = c0) (x : Pol p q r s) :
    x ∈ polChi p q r s c ↔ x ∈ hwSub (fockAct1 p q r s) (fun _ => c0) := by
  subst hc
  rw [mem_polChi_iff]
  constructor
  · intro h
    refine (PI.FockOneDegW.Swap.mem_hwSub_iff _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩
    · rw [h a a (by cases a <;> trivial), if_pos rfl]
    · rw [h a b (PI.FockOneDegW.Core.posC_sb a b hab), if_neg (PI.FockOneDegW.Core.posC_ne a b hab), zero_smul]
  · intro h a b hab
    exact scalar_of_hw (μ := fun _ => c0) (fun _ _ _ => rfl) h a b hab

end PositivityTheory.KReal

end
