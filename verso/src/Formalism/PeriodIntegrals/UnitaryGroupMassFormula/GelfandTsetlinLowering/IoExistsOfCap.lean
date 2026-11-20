import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.HwIrred
import Formalism.PeriodIntegrals.GTBranch
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

def capP {n : ℕ} (mu : DomWeight n) (u : ℂ) : ℂ :=
  ∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ((mu.w k : ℤ) : ℂ))

def CapFacts : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∃ C : ℂ → Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ),
      (∀ mu : DomWeight n, Interlace h lam mu →
        ∀ φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ, IsEqv h mu lam φ →
          ∀ s ∈ nablaSq ℂ n mu, ∀ u, C u (φ s) = capP mu u • φ s) ∧
      ∀ u, C u (xi ℂ h lam sg) = capP sg u • xi ℂ h lam sg

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem io_dw_ext {n : ℕ} {mu sg : DomWeight n} (hw : mu.w = sg.w) : mu = sg := by
  obtain ⟨w, hwa⟩ := mu
  obtain ⟨w', hwa'⟩ := sg
  simp only at hw
  subst hw
  rfl

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Reduce the claim to the hypotheses of an applicable result. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem exists_capelliPolynomial_ne {n : ℕ} (mu sg : DomWeight n) (hne : mu.w ≠ sg.w) : ∃ u, capP mu u ≠ capP sg u := by
  by_contra hall
  push_neg at hall
  apply hne
  have hzero : ∀ (nu : DomWeight n) (i : Fin n), capP nu (((i : ℕ) : ℂ) - ((nu.w i : ℤ) : ℂ)) = 0 := by
    intro nu i
    unfold capP
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    ring
  have hmem : ∀ (nu nu' : DomWeight n), (∀ u, capP nu u = capP nu' u) →
      ∀ i : Fin n, ∃ k : Fin n, ((k : ℕ) : ℤ) - nu'.w k = ((i : ℕ) : ℤ) - nu.w i := by
    intro nu nu' heq i
    have h0 := hzero nu i
    rw [heq] at h0
    unfold capP at h0
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h0
    refine ⟨k, ?_⟩
    have : ((((k : ℕ) : ℤ) - nu'.w k : ℤ) : ℂ) = ((((i : ℕ) : ℤ) - nu.w i : ℤ) : ℂ) := by
      push_cast
      linear_combination -hk
    exact_mod_cast this
  have hmono : ∀ nu : DomWeight n, StrictMono (fun k : Fin n => ((k : ℕ) : ℤ) - nu.w k) := by
    intro nu i j hij
    have h1 := nu.anti hij.le
    have h2 : (i : ℕ) < j := hij
    simp only
    omega
  have hrange : Set.range (fun k : Fin n => ((k : ℕ) : ℤ) - mu.w k) =
      Set.range (fun k : Fin n => ((k : ℕ) : ℤ) - sg.w k) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := hmem mu sg hall i
      exact ⟨k, hk⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := hmem sg mu (fun u => (hall u).symm) i
      exact ⟨k, hk⟩
  have hab := ((hmono mu).range_inj (hmono sg)).mp hrange
  funext k
  have := congrFun hab k
  omega

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
private theorem sum_eq_zero_of_eigen_separated {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : ℂ → Module.End ℂ V) (p : ι → ℂ → ℂ) (i0 : ι) (hp : ∀ i, i ≠ i0 → ∃ u, p i u ≠ p i0 u)
    (G : Finset ι) (hG : i0 ∉ G) : ∀ (y : ι → V), (∀ i ∈ G, ∀ u, C u (y i) = p i u • y i) →
      (∀ u, C u (∑ i ∈ G, y i) = p i0 u • ∑ i ∈ G, y i) → ∑ i ∈ G, y i = 0 := by
  revert hG
  refine Finset.induction_on G ?_ ?_
  · intro _ y _ _
    simp
  · intro j G hj ih hjG y hy hS
    have hi0j : j ≠ i0 := fun h => hjG (h ▸ Finset.mem_insert_self j G)
    have hi0G : i0 ∉ G := fun h => hjG (Finset.mem_insert_of_mem h)
    obtain ⟨u, hu⟩ := hp j hi0j
    have hsum : (p i0 u - p j u) • ∑ i ∈ insert j G, y i = ∑ i ∈ G, (p i u - p j u) • y i := by
      have h1 : C u (∑ i ∈ insert j G, y i) - p j u • ∑ i ∈ insert j G, y i =
          (p i0 u - p j u) • ∑ i ∈ insert j G, y i := by
        rw [hS u, sub_smul]
      have h2 : C u (∑ i ∈ insert j G, y i) - p j u • ∑ i ∈ insert j G, y i =
          ∑ i ∈ G, (p i u - p j u) • y i := by
        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_insert hj,
          hy j (Finset.mem_insert_self j G) u, sub_self, zero_add]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [hy i (Finset.mem_insert_of_mem hi) u, sub_smul]
      rw [← h1, h2]
    have hzero : ∑ i ∈ G, (p i u - p j u) • y i = 0 := by
      refine ih hi0G (fun i => (p i u - p j u) • y i) ?_ ?_
      · intro i hi v
        show C v ((p i u - p j u) • y i) = p i v • ((p i u - p j u) • y i)
        rw [map_smul, hy i (Finset.mem_insert_of_mem hi) v, smul_comm]
      · intro v
        show C v (∑ i ∈ G, (p i u - p j u) • y i) = p i0 v • ∑ i ∈ G, (p i u - p j u) • y i
        rw [← hsum, map_smul, hS v, smul_comm]
    have hfin : (p i0 u - p j u) • ∑ i ∈ insert j G, y i = 0 := by
      rw [hsum, hzero]
    rcases smul_eq_zero.mp hfin with h | h
    · exact absurd (sub_eq_zero.mp h).symm hu
    · exact h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem io_eig_sep {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : ℂ → Module.End ℂ V) (p : ι → ℂ → ℂ) (i0 : ι) (hp : ∀ i, i ≠ i0 → ∃ u, p i u ≠ p i0 u) :
    ∀ (F : Finset ι) (y : ι → V), (∀ i ∈ F, ∀ u, C u (y i) = p i u • y i) →
      (∀ u, C u (∑ i ∈ F, y i) = p i0 u • ∑ i ∈ F, y i) →
      ∑ i ∈ F, y i = ∑ i ∈ F.filter (fun i => i = i0), y i := by
  intro F y hy hS
  have hF := Finset.sum_filter_add_sum_filter_not F (fun i => i = i0) y
  have hz : ∑ i ∈ F.filter (fun i => ¬ i = i0), y i = 0 := by
    apply sum_eq_zero_of_eigen_separated C p i0 hp _ (by simp)
    · intro i hi u
      exact hy i (Finset.mem_filter.mp hi).1 u
    · intro u
      have h2 : ∑ i ∈ F.filter (fun i => ¬ i = i0), y i =
          ∑ i ∈ F, y i - ∑ i ∈ F.filter (fun i => i = i0), y i := by
        rw [← hF]
        abel
      have h3 : ∀ v, C v (∑ i ∈ F.filter (fun i => i = i0), y i) =
          p i0 v • ∑ i ∈ F.filter (fun i => i = i0), y i := by
        intro v
        rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_filter.mp hi
        rw [hy i hi'.1 v, hi'.2]
      rw [h2, map_sub, hS u, h3 u, smul_sub]
  rw [← hF, hz, add_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem io_sqAct_smul {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by
  unfold sqAct
  rw [map_smul, smul_comm]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem io_sqAct_zero {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) : sqAct ℂ k mu g 0 = 0 := by
  unfold sqAct
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem io_sqAct_mem {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) {f : MvPolynomial (Fin k × Fin k) ℂ}
    (hf : f ∈ nablaSq ℂ k mu) : sqAct ℂ k mu g f ∈ nablaSq ℂ k mu := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ k k mu.natW _ f hf)

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem io_sqAct_mul {k : ℕ} (mu : DomWeight k) (g g' : GL (Fin k) ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    sqAct ℂ k mu (g * g') f = sqAct ℂ k mu g (sqAct ℂ k mu g' f) := by
  have hrow : Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) ((g * g' : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ).transpose =
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) (g : Matrix (Fin k) (Fin k) ℂ).transpose).comp
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) (g' : Matrix (Fin k) (Fin k) ℂ).transpose) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.transpose_apply, Units.val_mul,
      Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
    ring
  have hdet : detPow ℂ k (g * g') mu.detShift = detPow ℂ k g mu.detShift * detPow ℂ k g' mu.detShift := by
    unfold detPow
    rw [map_mul, mul_zpow, Units.val_mul]
  unfold sqAct
  rw [hrow, AlgHom.comp_apply, map_smul, smul_smul, hdet]

def ioSqActL (k : ℕ) (mu : DomWeight k) (g : GL (Fin k) ℂ) :
    MvPolynomial (Fin k × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin k × Fin k) ℂ :=
  detPow ℂ k g mu.detShift • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) (g : Matrix (Fin k) (Fin k) ℂ).transpose).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ioSqActL_apply (k : ℕ) (mu : DomWeight k) (g : GL (Fin k) ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    ioSqActL k mu g f = sqAct ℂ k mu g f := rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem io_last_emb {n N : ℕ} (h : n + 1 = N) (a : ℂˣ) (g : GL (Fin n) ℂ) :
    lastGL ℂ N a * embGL ℂ n N h g = embGL ℂ n N h g * lastGL ℂ N a := by
  have hL : ((lastGL ℂ N a : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (fun x : Fin N => ((if x.1 + 1 = N then a else 1 : ℂˣ) : ℂ)) := rfl
  have hE : ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 1).submatrix
        (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm := rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hL, hE]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective i
  obtain ⟨t, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective j
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases s with k | k <;> rcases t with l | l
  · have hk : ¬ ((((finSumFinEquiv.trans (finCongr h)) (Sum.inl k) : Fin N) : ℕ) + 1 = N) := by
      have := k.isLt
      simp only [Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, Fin.coe_cast,
        Fin.coe_castAdd]
      omega
    have hl : ¬ ((((finSumFinEquiv.trans (finCongr h)) (Sum.inl l) : Fin N) : ℕ) + 1 = N) := by
      have := l.isLt
      simp only [Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, Fin.coe_cast,
        Fin.coe_castAdd]
      omega
    rw [if_neg hk, if_neg hl]
    simp
  · simp
  · simp
  · obtain rfl : k = l := Subsingleton.elim _ _
    exact mul_comm _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem io_extremal_mem (h3 : PI.HwIrred) (k : ℕ) (mu : DomWeight k) :
    extremal ℂ k mu ∈ nablaSq ℂ k mu := by
  rw [(h3 k mu).1]
  exact Submodule.subset_span ⟨[], rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ioExists_of_cap (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) (hC : CapFacts) :
    IoExists := by
  classical
  intro n N h lam sg hI
  obtain ⟨hxi0, hxiM, hxiU, -, hxiL, -⟩ := hx n N h lam sg hI
  obtain ⟨C, hCφ, hCxi⟩ := hC n N h lam sg hI
  obtain ⟨hB1, hB2⟩ := h4 n N h lam
  let T : DomWeight n → Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := fun mu =>
    ⨆ (_ : Interlace h lam mu) (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
      (_ : IsEqv h mu lam φ), (nablaSq ℂ n mu).map φ
  have hT : ∀ mu, ∀ y ∈ T mu, ∀ u, C u y = capP mu u • y := by
    intro mu
    let Eig : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
      ⨅ u, LinearMap.ker (C u - capP mu u • LinearMap.id)
    have hle : T mu ≤ Eig := by
      refine iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨s, hs, rfl⟩
      simp only [Eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
      exact fun u => hCφ mu hmu φ hφ s hs u
    intro y hy u
    have hy' := hle hy
    simp only [Eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hy'
    exact hy' u
  have hxiT : xi ℂ h lam sg ∈ ⨆ mu, T mu := by
    have hm := hxiM
    rw [hB2] at hm
    exact hm
  obtain ⟨f, hfT, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp T _).mp hxiT
  have hs : ∑ i ∈ f.support, f i = xi ℂ h lam sg := hfsum
  have hsep := io_eig_sep C (fun mu u => capP mu u) sg
    (fun mu hne => exists_capelliPolynomial_ne mu sg (fun hw => hne (io_dw_ext hw))) f.support f
    (fun mu _ => hT mu (f mu) (hfT mu)) (by rw [hs]; exact hCxi)
  have hxiTsg : xi ℂ h lam sg ∈ T sg := by
    rw [← hs, hsep]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    have hi0 : i = sg := (Finset.mem_filter.mp hi).2
    rw [hi0]
    exact hfT sg
  by_cases hex : ∃ φ0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam φ0 ∧ ∃ s0 ∈ nablaSq ℂ n sg, φ0 s0 ≠ 0
  swap
  · exfalso
    apply hxi0
    have hbot : T sg = ⊥ := by
      refine eq_bot_iff.mpr (iSup_le fun _ => iSup_le fun φ => iSup_le fun hφ => ?_)
      rintro _ ⟨s, hs, rfl⟩
      rw [Submodule.mem_bot]
      by_contra hne
      exact hex ⟨φ, hφ, s, hs, hne⟩
    rw [hbot] at hxiTsg
    exact (Submodule.mem_bot ℂ).mp hxiTsg
  obtain ⟨φ0, hφ0, s0, hs0, hs0ne⟩ := hex
  have hprop : ∀ φ, IsEqv h sg lam φ → ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n sg, φ s = c • φ0 s := by
    intro φ hφ
    refine (hB1 sg φ φ0 ?_ ⟨s0, hs0, hs0ne⟩).2
    intro ψ hψ
    rcases hψ with rfl | rfl
    · exact hφ
    · exact hφ0
  have hTle : T sg ≤ (nablaSq ℂ n sg).map φ0 := by
    refine iSup_le fun _ => iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨c, hc⟩ := hprop φ hφ
    exact ⟨c • s, Submodule.smul_mem _ _ hs, by rw [map_smul, hc s hs]⟩
  obtain ⟨t, ht, hφt⟩ := hTle hxiTsg
  let K : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := nablaSq ℂ n sg ⊓ LinearMap.ker φ0
  have hKst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ K, sqAct ℂ n sg g v ∈ K := by
    intro g v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    rw [LinearMap.mem_ker] at hv2
    refine Submodule.mem_inf.mpr ⟨io_sqAct_mem sg g hv1, ?_⟩
    rw [LinearMap.mem_ker, hφ0.2 g v hv1, hv2, io_sqAct_zero]
  have hK : K = ⊥ := by
    rcases (h3 n sg).2.1 K inf_le_left hKst with hK | hK
    · exact hK
    · exfalso
      have hs0K : s0 ∈ K := by rw [hK]; exact hs0
      exact hs0ne (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hs0K).2)
  have hfix : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ n sg g t = t := by
    intro g hg1 hg2
    have hv : sqAct ℂ n sg g t - t ∈ K := by
      refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ (io_sqAct_mem sg g ht) ht, ?_⟩
      rw [LinearMap.mem_ker, map_sub, hφ0.2 g t ht, hφt, hxiU g hg1 hg2, sub_self]
    rw [hK, Submodule.mem_bot, sub_eq_zero] at hv
    exact hv
  obtain ⟨c, hc⟩ := (h3 n sg).2.2 t ht hfix
  have hext := io_extremal_mem h3 n sg
  let io0 := c • φ0
  have hE : IsEqv h sg lam io0 := by
    refine ⟨fun s hs => Submodule.smul_mem _ _ (hφ0.1 s hs), fun g s hs => ?_⟩
    simp only [io0, LinearMap.smul_apply]
    rw [hφ0.2 g s hs, io_sqAct_smul]
  have hext0 : io0 (extremal ℂ n sg) = xi ℂ h lam sg := by
    simp only [io0, LinearMap.smul_apply]
    rw [← map_smul, ← hc, hφt]
  refine ⟨io0, hE, hext0, ?_⟩
  intro a s hs
  let ψ := (ioSqActL N lam (lastGL ℂ N a)).comp io0
  have hψ : IsEqv h sg lam ψ := by
    refine ⟨fun s hs => io_sqAct_mem lam _ (hE.1 s hs), fun g s hs => ?_⟩
    simp only [ψ, LinearMap.comp_apply, ioSqActL_apply]
    rw [hE.2 g s hs, ← io_sqAct_mul, ← io_sqAct_mul, io_last_emb]
  obtain ⟨-, d, hd⟩ := hB1 sg ψ io0 (by
      intro χ hχ
      rcases hχ with rfl | rfl
      · exact hψ
      · exact hE)
    ⟨extremal ℂ n sg, hext, by rw [hext0]; exact hxi0⟩
  have h1 := hd _ hext
  simp only [ψ, LinearMap.comp_apply, ioSqActL_apply] at h1
  rw [hext0, hxiL a] at h1
  have hd' : d = ((a ^ degZ lam sg : ℂˣ) : ℂ) := by
    have h0 : (((a ^ degZ lam sg : ℂˣ) : ℂ) - d) • xi ℂ h lam sg = 0 := by rw [sub_smul, h1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hxi0)).symm
  have h2 := hd s hs
  simp only [ψ, LinearMap.comp_apply, ioSqActL_apply] at h2
  rw [h2, hd']

end PI.WGL
