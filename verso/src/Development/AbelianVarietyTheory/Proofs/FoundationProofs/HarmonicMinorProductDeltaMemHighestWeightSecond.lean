import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor

namespace GlobalTheory.DeltaHighest

def ext0 {l : ℕ} (a : Fin l → ℕ) (i : ℕ) : ℕ := if h : i < l then a ⟨i, h⟩ else 0

/- English proof (translation)
Introduce `i j hij`. Unfold `ext0`. Use `split_ifs with h h'`. Conclude with `ha (by simpa using hij)`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem partitionExtendByZero_antitone {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) : Antitone (ext0 a) := by
  intro i j hij
  unfold ext0
  split_ifs with h h'
  · exact ha (by simpa using hij)
  · omega
  · omega
  · omega

def leadProd {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ) :
    MvPolynomial σ ℂ :=
  ∏ i : Fin l, lead z (n := i.1 + 1) (le_trans i.2 h) i.2 ^ (ext0 a i - ext0 a (i + 1))

/- English proof (translation)
Simplify using `[ext0, nextRow]`.
-/
theorem partition_row_difference_eq_extendByZero_difference {l : ℕ} (a : Fin l → ℕ) (i : Fin l) :
    a i - nextRow a i = ext0 a i - ext0 a (i + 1) := by
  simp [ext0, nextRow]

/- English proof (translation)
Use `what₂ z hz (ext0 a) (partitionExtendByZero_antitone ha) l (fun i hi => dif_neg (by omega)) (fun i => le_trans i.2 h) (fun i => i.2)` as an intermediate fact. Simplify `this` using `only [rowOp_eq_rowDer, leadProd]`.
-/
theorem leadProd_rows {σ : Type} {n l : ℕ} (h : l ≤ n) {a : Fin l → ℕ} (ha : Antitone a)
    (z : Fin n × Fin l → σ) (hz : Function.Injective z) :
    (∀ c d : Fin n, c < d → rowDer z c d (leadProd h a z) = 0) ∧
      ∀ c : Fin n, rowDer z c c (leadProd h a z) = (ext0 a c : ℂ) • leadProd h a z := by
  have := what₂ z hz (ext0 a) (partitionExtendByZero_antitone ha) l (fun i hi => dif_neg (by omega))
    (fun i => le_trans i.2 h) (fun i => i.2)
  simpa only [rowOp_eq_rowDer, leadProd] using this

/- English proof (translation)
Rewrite using `[leadProd, derivation_prod_pow D _ _ _ (fun _ => 0)]`. Simplify using the standard rewrite rules. Introduce `i`. Rewrite using `[zero_smul, lead, derivation_det]`. Use `Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.updateRow_self]`. Conclude with `hD _`.
-/
theorem leadProd_kill {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (hD : ∀ w, D (X (z w)) = 0) :
    D (leadProd h a z) = 0 := by
  rw [leadProd, derivation_prod_pow D _ _ _ (fun _ => 0)]
  · simp
  · intro i
    rw [zero_smul, lead, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self]
    exact hD _

/- English proof (translation)
Rewrite using `[← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_X_of_ne (hv _).symm, mul_zero]`.
-/
theorem rowDer_X_other {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (c d : Fin n) (v : σ)
    (hv : ∀ w, z w ≠ v) : rowDer z c d (X v) = 0 := by
  classical
  rw [← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pderiv_X_of_ne (hv _).symm, mul_zero]

variable (p q n : ℕ)

def vp : Fin n × Fin p → Ln p q n 0 := fun w => (Sum.inl w.2, Sum.inl w.1)

def vm : Fin n × Fin q → Ln p q n 0 := fun w => (Sum.inr w.2, Sum.inl w.1.rev)

/- English proof (translation)
Introduce `u w h` and use `by simpa [vp, Prod.ext_iff, and_comm] using h`.
-/
theorem vp_inj : Function.Injective (vp p q n) := fun u w h => by
  simpa [vp, Prod.ext_iff, and_comm] using h

/- English proof (translation)
Introduce `u w h` and use `by simpa [vm, Prod.ext_iff, and_comm] using h`.
-/
theorem vm_inj : Function.Injective (vm p q n) := fun u w h => by
  simpa [vm, Prod.ext_iff, and_comm] using h

/- English proof (translation)
Unfold `minorProd leadProd`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[partition_row_difference_eq_extendByZero_difference]`. Both sides reduce to the same expression.
-/
theorem top_eq (h : p ≤ n) (a : Fin p → ℕ) :
    minorProd a (zPlus p q n) (topRows h) = leadProd h a (vp p q n) := by
  unfold minorProd leadProd
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference]
  rfl

/- English proof (translation)
Use `⟨∏ i : Fin q, ((Equiv.Perm.sign (Fin.revPerm (n := i.1 + 1)) : ℤ) : ℂ) ^ (ext0 a i - ext0 a (i + 1)), ?_⟩` and prove the remaining obligations. Unfold `minorProd leadProd`. Rewrite using `[Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[partition_row_difference_eq_extendByZero_difference, map_pow, ← mul_pow, map_intCast, lead, ← Matrix.det_permute]`.

Use `congr 2`. Use `ext1 c b`. Simplify using `only [zMinus, vm, Matrix.submatrix_apply, Matrix.of_apply, id]`. Use `congr 3`. Apply `Fin.ext` to reduce the goal to its premises.

Use `i.2` as an intermediate fact. Use `c.2` as an intermediate fact. Simplify using `[botRows, Fin.revPerm, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bot_eq (h : q ≤ n) (a : Fin q → ℕ) :
    ∃ u : ℂ, minorProd a (zMinus p q n) (botRows h) = u • leadProd h a (vm p q n) := by
  refine ⟨∏ i : Fin q, ((Equiv.Perm.sign (Fin.revPerm (n := i.1 + 1)) : ℤ) : ℂ) ^
    (ext0 a i - ext0 a (i + 1)), ?_⟩
  unfold minorProd leadProd
  rw [Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference, map_pow, ← mul_pow, map_intCast, lead, ← Matrix.det_permute]
  congr 2
  ext1 c b
  simp only [zMinus, vm, Matrix.submatrix_apply, Matrix.of_apply, id]
  congr 3
  apply Fin.ext
  have := i.2
  have := c.2
  simp [botRows, Fin.revPerm, Fin.val_rev]
  omega

/- English proof (translation)
Rewrite using `[fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, ← rowOp_eq_rowDer, ← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply]`. Simplify using `only [omE_pos_pos (l := (.inl _, .inl c)) (l' := (.inl _, .inl d)) rfl rfl, omE_neg_neg (l := (.inr _, .inl c)) (l' := (.inr _, .inl d)) rfl rfl, vp, vm, Fin.rev_rev, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]`. Apply the tactic sequence `by_cases h : c = d <;> simp [h] <;> module`.
-/
theorem act_eq (c d : Fin n) (P : Pol p q n 0) :
    fockAct2 p q n 0 (Eab (.inl c) (.inl d)) P =
      rowDer (vp p q n) c d P - rowDer (vm p q n) d.rev c.rev P +
        (if c = d then ((p : ℂ) - q) / 2 else 0) • P := by
  rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, ← rowOp_eq_rowDer,
    ← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply]
  simp only [omE_pos_pos (l := (.inl _, .inl c)) (l' := (.inl _, .inl d)) rfl rfl,
    omE_neg_neg (l := (.inr _, .inl c)) (l' := (.inr _, .inl d)) rfl rfl, vp, vm, Fin.rev_rev,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
  by_cases h : c = d <;> simp [h] <;> module

/- English proof (translation)
Introduce `p q n hn ap am hp hm`. Establish `h1 : p ≤ n` using `by omega`. Establish `h2 : q ≤ n` using `by omega`. Take `⟨u, hu⟩` from `bot_eq p q n h2 am`. Establish `e : delta hn ap am = u • (leadProd h1 ap (vp p q n) * leadProd h2 am (vm p q n))`.

Rewrite using `[delta, top_eq, hu, mul_smul_comm]`. Rewrite using `[e]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `a1` using `leadProd_rows h1 hp _ (vp_inj p q n)`. Establish `a2` using `leadProd_rows h2 hm _ (vm_inj p q n)`.

Establish `k1 : ∀ c d, rowDer (vp p q n) c d (leadProd h2 am (vm p q n)) = 0` using `fun c d => leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]`. Establish `k2 : ∀ c d, rowDer (vm p q n) c d (leadProd h1 ap (vp p q n)) = 0` using `fun c d => leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]`. Simplify using `only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Sum.forall, posC, IsEmpty.forall_iff, implies_true, and_true, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, act_eq, Derivation.leibniz, k1, k2, a1.2, a2.2, if_true]`. Use `⟨fun c => ?_, fun c d hcd => ?_⟩` and prove the remaining obligations. Establish `hw : ((wtH n ap am (.inl c) : ℚ) : ℂ) = (ext0 ap c : ℂ) - (ext0 am c.rev : ℂ) + ((p : ℂ) - q) / 2`.

Use `c.2` as an intermediate fact. Establish `hr` using `c.val_rev`. Simplify using `only [wtH, ext0]`. Use `split_ifs with h h' h'`. Use linear arithmetic over natural numbers and integers.

Apply the tactic sequence `all_goals simp`. Rewrite using `[hw]`. Generalize the expression as in `leadProd h1 ap (vp p q n) = A`. Generalize the expression as in `leadProd h2 am (vm p q n) = B`. Simplify using `only [mul_zero, zero_add, add_zero, smul_eq_mul, mul_smul_comm, mul_comm B A]`.

Use `module`. Rewrite using `[a1.1 c d hcd, a2.1 _ _ (Fin.rev_lt_rev.2 hcd), if_neg hcd.ne]`. Simplify using the standard rewrite rules.
-/
theorem delta_mem_hwSub : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → delta hn ap am ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := by
  intro p q n hn ap am hp hm
  have h1 : p ≤ n := by omega
  have h2 : q ≤ n := by omega
  obtain ⟨u, hu⟩ := bot_eq p q n h2 am
  have e : delta hn ap am = u • (leadProd h1 ap (vp p q n) * leadProd h2 am (vm p q n)) := by
    rw [delta, top_eq, hu, mul_smul_comm]
  rw [e]
  refine Submodule.smul_mem _ _ ?_
  have a1 := leadProd_rows h1 hp _ (vp_inj p q n)
  have a2 := leadProd_rows h2 hm _ (vm_inj p q n)
  have k1 : ∀ c d, rowDer (vp p q n) c d (leadProd h2 am (vm p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  have k2 : ∀ c d, rowDer (vm p q n) c d (leadProd h1 ap (vp p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Sum.forall,
    posC, IsEmpty.forall_iff, implies_true, and_true, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, act_eq, Derivation.leibniz, k1, k2, a1.2, a2.2, if_true]
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · have hw : ((wtH n ap am (.inl c) : ℚ) : ℂ) =
        (ext0 ap c : ℂ) - (ext0 am c.rev : ℂ) + ((p : ℂ) - q) / 2 := by
      have := c.2
      have hr := c.val_rev
      simp only [wtH, ext0]
      split_ifs with h h' h'
      · omega
      all_goals simp
    rw [hw]
    generalize leadProd h1 ap (vp p q n) = A
    generalize leadProd h2 am (vm p q n) = B
    simp only [mul_zero, zero_add, add_zero, smul_eq_mul, mul_smul_comm, mul_comm B A]
    module
  · rw [a1.1 c d hcd, a2.1 _ _ (Fin.rev_lt_rev.2 hcd), if_neg hcd.ne]
    simp

end GlobalTheory.DeltaHighest

end
