import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

/- English proof (translation)
Simplify using `only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]`. Rewrite using `[sub_eq_zero, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`.
-/
private theorem sum_card_mul_modExp {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] :
    ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[val_deltaHalf]`. Establish `hx : nabs k t ≠ 0` using `(nabs_pos' k t).ne'`. Establish `hn : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (m a) t)) = nabs k t ^ ((Fintype.card (m a) : ℤ))`. Introduce `a`. Rewrite using `[Matrix.GeneralLinearGroup.det_scalar, zpow_natCast]`.

Simplify using `[nabs, map_pow]`. Establish `key : ∀ (s : Finset α) (f : α → ℤ), ∏ a ∈ s, nabs k t ^ f a = nabs k t ^ (∑ a ∈ s, f a)`. Introduce `s f`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]`. Establish `hmod : modulus k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1`. Simplify using `only [modulus, hn, ← zpow_mul]`. Rewrite using `[key, sum_card_mul_modExp, zpow_zero]`. Rewrite using `[hmod]`.

Simplify using the standard rewrite rules.
-/
private theorem deltaHalf_scalar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (t : kˣ) :
    (deltaHalf k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) : ℂ) = 1 := by
  rw [val_deltaHalf]
  have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
  have hn : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (m a) t)) =
      nabs k t ^ ((Fintype.card (m a) : ℤ)) := by
    intro a
    rw [Matrix.GeneralLinearGroup.det_scalar, zpow_natCast]
    simp [nabs, map_pow]
  have key : ∀ (s : Finset α) (f : α → ℤ), ∏ a ∈ s, nabs k t ^ f a = nabs k t ^ (∑ a ∈ s, f a) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]
  have hmod : modulus k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
    simp only [modulus, hn, ← zpow_mul]
    rw [key, sum_card_mul_modExp, zpow_zero]
  rw [hmod]
  simp

/- English proof (translation)
Establish `hmem : Matrix.GeneralLinearGroup.scalar n t ∈ parab k e`. Rewrite using `[mem_parab]`. Introduce `i j hij`. Establish `hne : i ≠ j`. Introduce and unpack `rfl`.

Conclude with `lt_irrefl _ hij`. Simplify using `[Matrix.GeneralLinearGroup.scalar, hne]`. Establish `hproj : leviProj k e ⟨_, hmem⟩ = fun a => Matrix.GeneralLinearGroup.scalar (m a) t`. Use function extensionality and compare the values at `a`. Use extensionality with `i j`.

Simplify using `[leviProj, diagBlock, Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, e.injective.eq_iff, Matrix.diagonal_apply, Sigma.mk.inj_iff]`. Establish `hcomm : ∀ x : GL n k, x * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * x`. Introduce `x`. Use extensionality with `i j`. Simplify using `[Matrix.GeneralLinearGroup.scalar, mul_comm]`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show v.1.1 (x * Matrix.GeneralLinearGroup.scalar n t) = (c • v).1.1 x`. Rewrite using `[hcomm x]`.

Establish `hlaw` using `parInd_law e ρ v ⟨_, hmem⟩ x`. Simplify using `only at hlaw`. Rewrite using `[hlaw, hproj, deltaHalf_scalar, hρ, one_smul]`. Both sides reduce to the same expression.
-/
private theorem parInd_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α n W : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (t : kˣ) (c : ℂ)
    (hρ : ∀ w, ρ (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) w = c • w) (v : IndSp e ρ) :
    parInd e ρ (Matrix.GeneralLinearGroup.scalar n t) v = c • v := by
  have hmem : Matrix.GeneralLinearGroup.scalar n t ∈ parab k e := by
    rw [mem_parab]
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    simp [Matrix.GeneralLinearGroup.scalar, hne]
  have hproj : leviProj k e ⟨_, hmem⟩ = fun a => Matrix.GeneralLinearGroup.scalar (m a) t := by
    funext a
    ext i j
    simp [leviProj, diagBlock, Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, e.injective.eq_iff,
      Matrix.diagonal_apply, Sigma.mk.inj_iff]
  have hcomm : ∀ x : GL n k, x * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * x := by
    intro x
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, mul_comm]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  show v.1.1 (x * Matrix.GeneralLinearGroup.scalar n t) = (c • v).1.1 x
  rw [hcomm x]
  have hlaw := parInd_law e ρ v ⟨_, hmem⟩ x
  simp only at hlaw
  rw [hlaw, hproj, deltaHalf_scalar, hρ, one_smul]
  rfl

/- English proof (translation)
Introduce `w`. Proceed by induction on `w using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r x`. Rewrite using `[LinearMap.map_smul, piTensor_tprod]`. Simplify using `only [hc]`.

Rewrite using `[MultilinearMap.map_smul_univ, smul_comm]`. Consider the case `add x y hx hy`. Rewrite using `[map_add, hx, hy, smul_add]`.
-/
private theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (hc : ∀ a v, ρ a (g a) v = c a • v) : ∀ w, piTensor ρ g w = (∏ i, c i) • w := by
  intro w
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [LinearMap.map_smul, piTensor_tprod]
    simp only [hc]
    rw [MultilinearMap.map_smul_univ, smul_comm]
  | add x y hx hy =>
    rw [map_add, hx, hy, smul_add]

/- English proof (translation)
Introduce `k _ _ _ _ h N y hc t c hy v`. Conclude with `parInd_scalar (stdBlocks (fun a => (y a).1) hc) (piTensor fun a => (y a).rep) t (∏ i, c i) (piTensor_scalar (fun a => (y a).rep) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (y a).1) t) c (fun a w => hy a w)) v`.
-/
theorem UpperTheory.Lit.Cas.scalarFull :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (y : Fin h → IrrGL k) (hc : ∑ i, (y i).1 = N) (t : kˣ) (c : Fin h → ℂ), (∀ i, ScalarBy (y i) t (c i)) → ∀ v, prodIrr y hc (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = (∏ i, c i) • v := by
  intro k _ _ _ _ h N y hc t c hy v
  exact parInd_scalar (stdBlocks (fun a => (y a).1) hc) (piTensor fun a => (y a).rep) t (∏ i, c i)
    (piTensor_scalar (fun a => (y a).rep) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (y a).1) t) c
      (fun a w => hy a w)) v
