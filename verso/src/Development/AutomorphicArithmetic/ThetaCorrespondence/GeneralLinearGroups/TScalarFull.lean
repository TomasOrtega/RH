import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem sum_card_mul_modExp {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] :
    ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.Lit.Cas.scalarFull :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (y : Fin h → IrrGL k) (hc : ∑ i, (y i).1 = N) (t : kˣ) (c : Fin h → ℂ), (∀ i, ScalarBy (y i) t (c i)) → ∀ v, prodIrr y hc (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = (∏ i, c i) • v := by
  intro k _ _ _ _ h N y hc t c hy v
  exact parInd_scalar (stdBlocks (fun a => (y a).1) hc) (piTensor fun a => (y a).rep) t (∏ i, c i)
    (piTensor_scalar (fun a => (y a).rep) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (y a).1) t) c
      (fun a w => hy a w)) v
