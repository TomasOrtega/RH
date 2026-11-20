import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AlgebraMapInvFf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HasDerivAtInvExpCurveEntry

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

def IsDer (O : Module.End ℂ (Fock n)) (L : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)) : Prop :=
  ∀ (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)),
    O (ExteriorAlgebra.ιMulti ℂ p v) = ∑ i, ExteriorAlgebra.ιMulti ℂ p (Function.update v i (L (v i)))

/- English proof (translation)
Introduce `p v`. Simplify using `only [LinearMap.zero_apply]`. Use `(Finset.sum_eq_zero fun i _ => ?_).symm` and prove the remaining obligations. Conclude with `(ExteriorAlgebra.ιMulti ℂ p).map_update_zero v i`.
-/
theorem isDer_zero : IsDer (0 : Module.End ℂ (Fock n)) 0 := by
  intro p v
  simp only [LinearMap.zero_apply]
  refine (Finset.sum_eq_zero fun i _ => ?_).symm
  exact (ExteriorAlgebra.ιMulti ℂ p).map_update_zero v i

/- English proof (translation)
Introduce `p v`. Rewrite using `[LinearMap.add_apply, h, h', ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_add]`.
-/
theorem isDer_add {O O' : Module.End ℂ (Fock n)} {L L' : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)}
    (h : IsDer O L) (h' : IsDer O' L') : IsDer (O + O') (L + L') := by
  intro p v
  rw [LinearMap.add_apply, h, h', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_add]

/- English proof (translation)
Introduce `p v`. Rewrite using `[LinearMap.smul_apply, h, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_smul]`.
-/
theorem isDer_smul (c : ℂ) {O : Module.End ℂ (Fock n)} {L : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)}
    (h : IsDer O L) : IsDer (c • O) (c • L) := by
  intro p v
  rw [LinearMap.smul_apply, h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_smul]

/- English proof (translation)
Use `isDer_smul (-1) h` as an intermediate fact. Simplify `this` using `only [neg_one_smul]`.
-/
theorem isDer_neg {O : Module.End ℂ (Fock n)} {L : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)}
    (h : IsDer O L) : IsDer (-O) (-L) := by
  have := isDer_smul (-1) h
  simpa only [neg_one_smul] using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (isDer_zero (n := n))`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj]`. Conclude with `isDer_add (h j (Finset.mem_insert_self j s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem isDer_sum {ι : Type*} (s : Finset ι) {O : ι → Module.End ℂ (Fock n)}
    {L : ι → (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)} (h : ∀ j ∈ s, IsDer (O j) (L j)) :
    IsDer (∑ j ∈ s, O j) (∑ j ∈ s, L j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isDer_zero (n := n))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact isDer_add (h j (Finset.mem_insert_self j s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
The claim follows from `| 0, v => by simp only [cmV, ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one, map_zero] rw [Fin.sum_univ_zero] | p + 1, v => by have ih := cpV_cmV_ιMulti u w p (Matrix.vecTail v) simp only [cmV, cpV, LinearMap.mulLeft_apply] at ih ⊢ have hanti : ExteriorAlgebr …`.
-/
theorem cpV_cmV_ιMulti (u w : Fin n × Fin n → ℂ) : ∀ (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)),
    cpV u (cmV w (ExteriorAlgebra.ιMulti ℂ p v)) =
      ∑ i, dualV w (v i) • ExteriorAlgebra.ιMulti ℂ p (Function.update v i u)
  | 0, v => by
    simp only [cmV, ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one, map_zero]
    rw [Fin.sum_univ_zero]
  | p + 1, v => by
    have ih := cpV_cmV_ιMulti u w p (Matrix.vecTail v)
    simp only [cmV, cpV, LinearMap.mulLeft_apply] at ih ⊢
    have hanti : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (v 0) =
        -(ExteriorAlgebra.ι ℂ (v 0) * ExteriorAlgebra.ι ℂ u) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u (v 0))
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul, mul_sub, mul_smul_comm,
      ← mul_assoc (ExteriorAlgebra.ι ℂ u), hanti, neg_mul, sub_neg_eq_add, mul_assoc, ih,
      Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    · rw [ExteriorAlgebra.ιMulti_succ_apply, Function.update_self]
      congr 3
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, ExteriorAlgebra.ιMulti_succ_apply,
        Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 3
      funext j
      simp only [Matrix.vecTail, Function.comp_apply, Function.update_apply, Fin.succ_inj]

/- English proof (translation)
Introduce `p v`. Rewrite using `[Module.End.mul_apply, cpV_cmV_ιMulti]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smulRight_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_smul]`.
-/
theorem isDer_cpV_cmV (u w : Fin n × Fin n → ℂ) :
    IsDer (cpV u * cmV w) (LinearMap.smulRight (dualV w) u) := by
  intro p v
  rw [Module.End.mul_apply, cpV_cmV_ιMulti]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smulRight_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_smul]

def Lab (ε : Fin n → Bool) (a b : Fin n) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  if ε a = true ∧ ε b = true then
    ∑ x ∈ minusIdx ε, LinearMap.smulRight (dualV (Pi.single (b, x) (1 : ℂ))) (Pi.single (a, x) 1)
  else if ε a = false ∧ ε b = false then
    -∑ i ∈ plusIdx ε, LinearMap.smulRight (dualV (Pi.single (i, a) (1 : ℂ))) (Pi.single (i, b) 1)
  else 0

/- English proof (translation)
Unfold `sgE Lab`. Use `split_ifs`. Conclude with `isDer_sum _ fun x _ => by rw [cpFock_eq_cpV, cmFock_eq_cmV]; exact isDer_cpV_cmV _ _`. Conclude with `isDer_neg (isDer_sum _ fun i _ => by rw [cpFock_eq_cpV, cmFock_eq_cmV]; exact isDer_cpV_cmV _ _)`. Conclude with `isDer_zero`.
-/
theorem isDer_sgE (a b : Fin n) : IsDer (sgE ε (cpFock (n := n)) cmFock a b) (Lab ε a b) := by
  unfold sgE Lab
  split_ifs
  · exact isDer_sum _ fun x _ => by rw [cpFock_eq_cpV, cmFock_eq_cmV]; exact isDer_cpV_cmV _ _
  · exact isDer_neg (isDer_sum _ fun i _ => by rw [cpFock_eq_cpV, cmFock_eq_cmV]; exact isDer_cpV_cmV _ _)
  · exact isDer_zero

def sgX (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Fock n) :=
  ∑ a, ∑ b, X a b • sgE ε (cpFock (n := n)) cmFock a b

def LX (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  ∑ a, ∑ b, X a b • Lab ε a b

/- English proof (translation)
The claim follows from `isDer_sum _ fun a _ => isDer_sum _ fun b _ => isDer_smul _ (isDer_sgE a b)`.
-/
theorem isDer_sgX (X : Matrix (Fin n) (Fin n) ℂ) : IsDer (sgX ε X) (LX ε X) :=
  isDer_sum _ fun a _ => isDer_sum _ fun b _ => isDer_smul _ (isDer_sgE a b)

/- English proof (translation)
Take `⟨y1, y2⟩` from `y`. Unfold `Lab`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;>`. Apply the tactic sequence `simp [LinearMap.sum_apply, Finset.sum_apply, dualV_single, Pi.single_apply, minusIdx, plusIdx, Prod.ext_iff, ite_and, Finset.sum_ite_eq] <;>`. Apply the tactic sequence `by_cases h1 : ε y1 = true <;> simp [h1]`.
-/
theorem Lab_apply (a b : Fin n) (w : Fin n × Fin n → ℂ) (y : Fin n × Fin n) :
    Lab ε a b w y =
      (if ε a = true ∧ ε b = true ∧ y.1 = a ∧ ε y.2 = false then w (b, y.2) else 0) -
        (if ε a = false ∧ ε b = false ∧ y.2 = b ∧ ε y.1 = true then w (y.1, a) else 0) := by
  obtain ⟨y1, y2⟩ := y
  unfold Lab
  cases ha : ε a <;> cases hb : ε b <;>
    simp [LinearMap.sum_apply, Finset.sum_apply, dualV_single, Pi.single_apply, minusIdx, plusIdx,
      Prod.ext_iff, ite_and, Finset.sum_ite_eq] <;>
    by_cases h1 : ε y1 = true <;> simp [h1]

/- English proof (translation)
Take `⟨y1, y2⟩` from `y`. Simplify using `only [LX, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Lab_apply, mul_sub, Finset.sum_sub_distrib]`. Establish `h1 : ∑ a, ∑ b, X a b * (if ε a = true ∧ ε b = true ∧ y1 = a ∧ ε y2 = false then w (b, y2) else 0) = if IsPhys ε (y1, y2) then ∑ b ∈ plusIdx ε, X y1 b * w (b, y2) else 0`. Rewrite using `[Finset.sum_eq_single y1 (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [Ne.symm ha]) (by simp)]`. Unfold `IsPhys`.

Apply the tactic sequence `by_cases hy1 : ε y1 = true <;> by_cases hy2 : ε y2 = false <;>`. Simplify using `[hy1, hy2, plusIdx, Finset.sum_filter]`. Establish `h2 : ∑ a, ∑ b, X a b * (if ε a = false ∧ ε b = false ∧ y2 = b ∧ ε y1 = true then w (y1, a) else 0) = if IsPhys ε (y1, y2) then ∑ a ∈ minusIdx ε, X a y2 * w (y1, a) else 0`. Rewrite using `[Finset.sum_congr rfl fun a _ => Finset.sum_eq_single y2 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`. Unfold `IsPhys`.

Apply the tactic sequence `by_cases hy1 : ε y1 = true <;> by_cases hy2 : ε y2 = false <;>`. Simplify using `[hy1, hy2, minusIdx, Finset.sum_filter]`. Rewrite using `[h1, h2]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem LX_apply (X : Matrix (Fin n) (Fin n) ℂ) (w : Fin n × Fin n → ℂ) (y : Fin n × Fin n) :
    LX ε X w y = if IsPhys ε y then
      (∑ b ∈ plusIdx ε, X y.1 b * w (b, y.2)) - ∑ a ∈ minusIdx ε, X a y.2 * w (y.1, a) else 0 := by
  obtain ⟨y1, y2⟩ := y
  simp only [LX, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Lab_apply, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ a, ∑ b, X a b * (if ε a = true ∧ ε b = true ∧ y1 = a ∧ ε y2 = false then w (b, y2) else 0) =
      if IsPhys ε (y1, y2) then ∑ b ∈ plusIdx ε, X y1 b * w (b, y2) else 0 := by
    rw [Finset.sum_eq_single y1 (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [Ne.symm ha])
      (by simp)]
    unfold IsPhys
    by_cases hy1 : ε y1 = true <;> by_cases hy2 : ε y2 = false <;>
      simp [hy1, hy2, plusIdx, Finset.sum_filter]
  have h2 : ∑ a, ∑ b, X a b * (if ε a = false ∧ ε b = false ∧ y2 = b ∧ ε y1 = true then w (y1, a) else 0) =
      if IsPhys ε (y1, y2) then ∑ a ∈ minusIdx ε, X a y2 * w (y1, a) else 0 := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_eq_single y2
      (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    unfold IsPhys
    by_cases hy1 : ε y1 = true <;> by_cases hy2 : ε y2 = false <;>
      simp [hy1, hy2, minusIdx, Finset.sum_filter]
  rw [h1, h2]
  split_ifs <;> simp

def adD (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) : ℂ :=
  if IsPhys ε x ∧ IsPhys ε y then
    X x.1 y.1 * star ((1 : Matrix (Fin n) (Fin n) ℂ) x.2 y.2) + (1 : Matrix (Fin n) (Fin n) ℂ) x.1 y.1 * star (X x.2 y.2)
  else 0

/- English proof (translation)
Establish `he : ∀ c d, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) c d) (X c d) 0`. Introduce `c d`. Apply the tactic sequence `have := hasDerivAt_exp_curve_entry (1 : Matrix (Fin n) (Fin n) ℂ) X c d`. Simplify `this` using `only [Matrix.one_mul]`. Establish `h0 : ∀ c d, NormedSpace.exp (((0 : ℝ) : ℂ) • X) c d = (1 : Matrix (Fin n) (Fin n) ℂ) c d`.

Introduce `c d`. Simplify using the standard rewrite rules. Unfold `adMat adD`. Apply the tactic sequence `by_cases hx : IsPhys ε x <;> by_cases hy : IsPhys ε y`. Simplify using `only [hx, hy, if_true, and_self]`.

Establish `h` using `(he x.1 y.1).fun_mul (he x.2 y.2).star`. Rewrite `h` using `[h0, h0]`. Conclude with `h`. Simplify using `only [hx, hy, if_true, if_false, and_false]`. Conclude with `hasDerivAt_const _ _`.

Simplify using `only [hx, if_false, false_and]`. Conclude with `hasDerivAt_const _ _`. Simplify using `only [hx, if_false, false_and]`. Conclude with `hasDerivAt_const _ _`.
-/
theorem adMat_exp_hasDeriv (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) :
    HasDerivAt (fun t : ℝ => adMat ε (NormedSpace.exp ((t : ℂ) • X)) x y) (adD ε X x y) 0 := by
  have he : ∀ c d, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) c d) (X c d) 0 := by
    intro c d
    have := hasDerivAt_exp_curve_entry (1 : Matrix (Fin n) (Fin n) ℂ) X c d
    simpa only [Matrix.one_mul] using this
  have h0 : ∀ c d, NormedSpace.exp (((0 : ℝ) : ℂ) • X) c d = (1 : Matrix (Fin n) (Fin n) ℂ) c d := by
    intro c d
    simp
  unfold adMat adD
  by_cases hx : IsPhys ε x <;> by_cases hy : IsPhys ε y
  · simp only [hx, hy, if_true, and_self]
    have h := (he x.1 y.1).fun_mul (he x.2 y.2).star
    rw [h0, h0] at h
    exact h
  · simp only [hx, hy, if_true, if_false, and_false]
    exact hasDerivAt_const _ _
  · simp only [hx, if_false, false_and]
    exact hasDerivAt_const _ _
  · simp only [hx, if_false, false_and]
    exact hasDerivAt_const _ _

/- English proof (translation)
Simplify using `only [adPhys, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]`. Conclude with `HasDerivAt.fun_sum fun y _ => (adMat_exp_hasDeriv X x y).mul_const (w y)`.
-/
theorem adPhys_exp_hasDeriv (X : Matrix (Fin n) (Fin n) ℂ) (w : Fin n × Fin n → ℂ) (x : Fin n × Fin n) :
    HasDerivAt (fun t : ℝ => adPhys ε (NormedSpace.exp ((t : ℂ) • X)) w x) (∑ y, adD ε X x y * w y) 0 := by
  simp only [adPhys, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun y _ => (adMat_exp_hasDeriv X x y).mul_const (w y)

/- English proof (translation)
Establish `hs : ∀ c d, star (X c d) = -X d c`. Introduce `c d`. Use `congrFun (congrFun hX d) c` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`. Rewrite using `[LX_apply]`.

Take `⟨x1, x2⟩` from `x`. Unfold `adD IsPhys`. Establish `hst : ∀ c d : Fin n, star ((1 : Matrix (Fin n) (Fin n) ℂ) c d) = (1 : Matrix (Fin n) (Fin n) ℂ) c d`. Introduce `c d`. Rewrite using `[Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Distinguish the cases in `hx : ε x1 = true ∧ ε x2 = false`. Simplify using `only [hx, true_and, if_true]`. Rewrite using `[Fintype.sum_prod_type]`. Use `trans ∑ b, ∑ c, ((if ε b = true ∧ c = x2 then X x1 b * w (b, c) else 0) + (if b = x1 ∧ ε c = false then -X c x2 * w (b, c) else 0))`.

Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hb : ε b = true <;> by_cases hc : c = x2 <;> by_cases hb1 : b = x1 <;>`. Apply the tactic sequence `simp_all [Matrix.one_apply, Ne.symm] <;> ring`. Simplify using `only [Finset.sum_add_distrib]`. Simplify using `[ite_and, plusIdx, minusIdx, Finset.sum_filter, sub_eq_add_neg]`.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [hx, false_and, if_false, zero_mul, Finset.sum_const_zero]`.
-/
theorem sum_adD_eq_LX {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) (w : Fin n × Fin n → ℂ)
    (x : Fin n × Fin n) : ∑ y, adD ε X x y * w y = LX ε X w x := by
  have hs : ∀ c d, star (X c d) = -X d c := by
    intro c d
    have := congrFun (congrFun hX d) c
    simpa [Matrix.conjTranspose_apply] using this
  rw [LX_apply]
  obtain ⟨x1, x2⟩ := x
  unfold adD IsPhys
  have hst : ∀ c d : Fin n, star ((1 : Matrix (Fin n) (Fin n) ℂ) c d) = (1 : Matrix (Fin n) (Fin n) ℂ) c d := by
    intro c d
    rw [Matrix.one_apply]
    split_ifs <;> simp
  by_cases hx : ε x1 = true ∧ ε x2 = false
  · simp only [hx, true_and, if_true]
    rw [Fintype.sum_prod_type]
    trans ∑ b, ∑ c, ((if ε b = true ∧ c = x2 then X x1 b * w (b, c) else 0) +
      (if b = x1 ∧ ε c = false then -X c x2 * w (b, c) else 0))
    · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      by_cases hb : ε b = true <;> by_cases hc : c = x2 <;> by_cases hb1 : b = x1 <;>
        simp_all [Matrix.one_apply, Ne.symm] <;> ring
    · simp only [Finset.sum_add_distrib]
      simp [ite_and, plusIdx, minusIdx, Finset.sum_filter, sub_eq_add_neg]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
  · simp only [hx, false_and, if_false, zero_mul, Finset.sum_const_zero]

/- English proof (translation)
Simplify using `[adPhys, adMat_one]`.
-/
theorem adPhys_one' (w : Fin n × Fin n → ℂ) : adPhys ε 1 w = w := by
  simp [adPhys, adMat_one]

def wedgeCoord (p : ℕ) :
    MultilinearMap ℂ (fun _ : Fin p => Fin n × Fin n → ℂ) (Finset (Fin (n * n)) → ℂ) :=
  (fockBasis n).equivFun.toLinearMap.compMultilinearMap (ExteriorAlgebra.ιMulti ℂ p).toMultilinearMap

/- English proof (translation)
Establish `hv : v = fun i => ∑ x, v i x • Pi.single x (1 : ℂ)`. Use function extensionality and compare the values at `i y`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hv]`. Rewrite using `[MultilinearMap.map_sum]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ]`.
-/
theorem wedgeCoord_eq_sum (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) :
    wedgeCoord p v = ∑ r : Fin p → Fin n × Fin n,
      (∏ i, v i (r i)) • wedgeCoord p (fun i => Pi.single (r i) (1 : ℂ)) := by
  classical
  have hv : v = fun i => ∑ x, v i x • Pi.single x (1 : ℂ) := by
    funext i y
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ]

/- English proof (translation)
Establish `h : (wedgeCoord (n` using `n) p : (Fin p → (Fin n × Fin n → ℂ)) → (Finset (Fin (n * n)) → ℂ)) = fun v => ∑ r : Fin p → Fin n × Fin n, (∏ i, v i (r i)) • wedgeCoord p (fun i => Pi.single (r i) (1 : ℂ)) :=`. Use function extensionality and compare the values at `(wedgeCoord_eq_sum p)`. Rewrite using `[h]`. Use `fun_prop`.
-/
theorem wedgeCoord_continuous (p : ℕ) : Continuous (wedgeCoord (n := n) p) := by
  have h : (wedgeCoord (n := n) p : (Fin p → (Fin n × Fin n → ℂ)) → (Finset (Fin (n * n)) → ℂ)) =
      fun v => ∑ r : Fin p → Fin n × Fin n,
        (∏ i, v i (r i)) • wedgeCoord p (fun i => Pi.single (r i) (1 : ℂ)) :=
    funext (wedgeCoord_eq_sum p)
  rw [h]
  fun_prop

def wedgeCoordC (p : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin p => Fin n × Fin n → ℂ) (Finset (Fin (n * n)) → ℂ) :=
  { toMultilinearMap := wedgeCoord p, cont := wedgeCoord_continuous p }

/- English proof (translation)
Use `set c : ℝ → (Fin p → (Fin n × Fin n → ℂ)) := fun t i => adPhys ε (NormedSpace.exp ((t : ℂ) • X)) (v i) with hcdef`. Establish `hc : HasDerivAt c (fun i => LX ε X (v i)) 0`. Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun x => ?_` and prove the remaining obligations. Rewrite using `[← sum_adD_eq_LX hX]`. Conclude with `adPhys_exp_hasDeriv X (v i) x`.

Establish `hc0 : c 0 = v`. Use function extensionality and compare the values at `i`. Simplify using `[c, adPhys_one']`. Establish `hF` using `(wedgeCoordC (n := n) p).hasFDerivAt (c 0)`. Establish `h` using `(hF.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hc`.

Establish `hfun : (fun t : ℝ => (fockBasis n).equivFun (ff ε (NormedSpace.exp ((t : ℂ) • X)) (ExteriorAlgebra.ιMulti ℂ p v))) = (wedgeCoordC (n` using `n) p) ∘ c := by`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp_apply, ff, ExteriorAlgebra.map_apply_ιMulti]`. Both sides reduce to the same expression. Rewrite using `[hfun]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals try rfl`. Rewrite using `[ContinuousLinearMap.coe_restrictScalars', ContinuousMultilinearMap.linearDeriv_apply, hc0, isDer_sgX, map_sum]`. Both sides reduce to the same expression.
-/
theorem ff_exp_wedge_hasDeriv {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) (p : ℕ)
    (v : Fin p → (Fin n × Fin n → ℂ)) :
    HasDerivAt (fun t : ℝ => (fockBasis n).equivFun
        (ff ε (NormedSpace.exp ((t : ℂ) • X)) (ExteriorAlgebra.ιMulti ℂ p v)))
      ((fockBasis n).equivFun (sgX ε X (ExteriorAlgebra.ιMulti ℂ p v))) 0 := by
  classical
  set c : ℝ → (Fin p → (Fin n × Fin n → ℂ)) :=
    fun t i => adPhys ε (NormedSpace.exp ((t : ℂ) • X)) (v i) with hcdef
  have hc : HasDerivAt c (fun i => LX ε X (v i)) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun x => ?_
    rw [← sum_adD_eq_LX hX]
    exact adPhys_exp_hasDeriv X (v i) x
  have hc0 : c 0 = v := by
    funext i
    simp [c, adPhys_one']
  have hF := (wedgeCoordC (n := n) p).hasFDerivAt (c 0)
  have h := (hF.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hc
  have hfun : (fun t : ℝ => (fockBasis n).equivFun
      (ff ε (NormedSpace.exp ((t : ℂ) • X)) (ExteriorAlgebra.ιMulti ℂ p v))) = (wedgeCoordC (n := n) p) ∘ c := by
    funext t
    simp only [Function.comp_apply, ff, ExteriorAlgebra.map_apply_ιMulti]
    rfl
  rw [hfun]
  convert h using 1
  all_goals try rfl
  rw [ContinuousLinearMap.coe_restrictScalars', ContinuousMultilinearMap.linearDeriv_apply, hc0, isDer_sgX,
    map_sum]
  rfl

/- English proof (translation)
Establish `hf : f = ∑ S, (fockBasis n).repr f S • fockBasis n S` using `((fockBasis n).sum_repr f).symm`. Rewrite using `[hf]`. Simplify using `only [map_sum, map_smul]`. Use `HasDerivAt.fun_sum fun S _ => ?_` and prove the remaining obligations. Use `HasDerivAt.const_smul ((fockBasis n).repr f S) ?_` and prove the remaining obligations.

Rewrite using `[fockBasis_eq]`. Conclude with `ff_exp_wedge_hasDeriv hX _ _`.
-/
theorem ff_exp_hasDeriv {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) (f : Fock n) :
    HasDerivAt (fun t : ℝ => (fockBasis n).equivFun (ff ε (NormedSpace.exp ((t : ℂ) • X)) f))
      ((fockBasis n).equivFun (sgX ε X f)) 0 := by
  have hf : f = ∑ S, (fockBasis n).repr f S • fockBasis n S := ((fockBasis n).sum_repr f).symm
  rw [hf]
  simp only [map_sum, map_smul]
  refine HasDerivAt.fun_sum fun S _ => ?_
  refine HasDerivAt.const_smul ((fockBasis n).repr f S) ?_
  rw [fockBasis_eq]
  exact ff_exp_wedge_hasDeriv hX _ _

end ReciprocityTheory.ChartRestriction.DS.TRGap
