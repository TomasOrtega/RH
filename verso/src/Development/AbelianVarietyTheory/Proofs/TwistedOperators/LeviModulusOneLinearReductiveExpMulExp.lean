import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceConjTransposeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceExpSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefConjTransposeMulSelfEqExpPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryExistsSkewLogStatement

open Matrix

noncomputable section

namespace GlobalTheory.LeviPolar

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.FlagLeviGroup

/- English proof (translation)
The claim follows from `GlobalTheory.T.absDetOnStableSubspace_conjTranspose n g V`.
-/
theorem detOn_conjTranspose (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)) :
    (∀ y ∈ V, g *ᵥ y ∈ V) → (∀ y ∈ V, gᴴ *ᵥ y ∈ V) → GlobalTheory.FlagMeas.detOn gᴴ V = GlobalTheory.FlagMeas.detOn g V :=
  GlobalTheory.T.absDetOnStableSubspace_conjTranspose n g V

/- English proof (translation)
The claim follows from `GlobalTheory.T.absDetOnStableSubspace_exp_smul n A V`.
-/
theorem detOn_exp_smul (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)) :
    (∀ y ∈ V, A *ᵥ y ∈ V) →
      ∃ c : ℝ, ∀ t : ℝ, GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) :=
  GlobalTheory.T.absDetOnStableSubspace_exp_smul n A V

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_hermitian_exp_eq_conjTranspose_mul_poly n g`.
-/
theorem exists_herm_log (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : IsUnit g →
    ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧
      L = Polynomial.aeval (gᴴ * g) p :=
  GlobalTheory.T.exists_hermitian_exp_eq_conjTranspose_mul_poly n g

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_skewHermitian_log_of_unitary n k`.
-/
theorem exists_unitary_log (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ) : kᴴ * k = 1 →
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Xᴴ = -X ∧ NormedSpace.exp X = k ∧
      X = Polynomial.aeval k p :=
  GlobalTheory.T.exists_skewHermitian_log_of_unitary n k

open scoped Matrix.Norms.L2Operator in

/- English proof (translation)
Rewrite using `[← CFC.log_exp A hA, ← CFC.log_exp B hB, h]`.
-/
theorem herm_exp_inj (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  rw [← CFC.log_exp A hA, ← CFC.log_exp B hB, h]

variable {n a : ℕ} {ε : Fin n → Bool}

def keepAlg (V : Submodule ℂ (Fin n → ℂ)) : Subalgebra ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | ∀ y ∈ V, A *ᵥ y ∈ V}
  mul_mem' := fun {A B} hA hB y hy => by
    rw [Set.mem_setOf_eq] at hA hB
    rw [← Matrix.mulVec_mulVec]; exact hA _ (hB y hy)
  add_mem' := fun {A B} hA hB y hy => by
    rw [Matrix.add_mulVec]; exact V.add_mem (hA y hy) (hB y hy)
  algebraMap_mem' := fun c y hy => by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]; exact V.smul_mem c hy

/- English proof (translation)
Establish `e : Polynomial.aeval A p = ((Polynomial.aeval (⟨A, hA⟩ : keepAlg V) p : keepAlg V) : Matrix (Fin n) (Fin n) ℂ)` using `Polynomial.aeval_algHom_apply (keepAlg V).val (⟨A, hA⟩ : keepAlg V) p`. Rewrite using `[e]`. Conclude with `(Polynomial.aeval (⟨A, hA⟩ : keepAlg V) p).2`.
-/
theorem aeval_keeps {A : Matrix (Fin n) (Fin n) ℂ} {V : Submodule ℂ (Fin n → ℂ)} (hA : ∀ y ∈ V, A *ᵥ y ∈ V)
    (p : Polynomial ℂ) : ∀ y ∈ V, Polynomial.aeval A p *ᵥ y ∈ V := by
  have e : Polynomial.aeval A p = ((Polynomial.aeval (⟨A, hA⟩ : keepAlg V) p : keepAlg V) : Matrix (Fin n) (Fin n) ℂ) :=
    Polynomial.aeval_algHom_apply (keepAlg V).val (⟨A, hA⟩ : keepAlg V) p
  rw [e]
  exact (Polynomial.aeval (⟨A, hA⟩ : keepAlg V) p).2

/- English proof (translation)
Establish `hA : A ∈ Subalgebra.centralizer ℂ {B}`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce `x hx`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `h.eq.symm`.

Establish `e : Polynomial.aeval A p = ((Polynomial.aeval (⟨A, hA⟩ : Subalgebra.centralizer ℂ {B}) p : Subalgebra.centralizer ℂ {B}) : Matrix (Fin n) (Fin n) ℂ)` using `Polynomial.aeval_algHom_apply (Subalgebra.centralizer ℂ {B}).val (⟨A, hA⟩ : Subalgebra.centralizer ℂ {B}) p`. Establish `hm` using `(Polynomial.aeval (⟨A, hA⟩ : Subalgebra.centralizer ℂ {B}) p).2`. Rewrite `hm` using `[Subalgebra.mem_centralizer_iff]`. Rewrite using `[Commute, SemiconjBy, e]`. Conclude with `(hm B rfl).symm`.
-/
theorem aeval_commute {A B : Matrix (Fin n) (Fin n) ℂ} (h : Commute A B) (p : Polynomial ℂ) :
    Commute (Polynomial.aeval A p) B := by
  have hA : A ∈ Subalgebra.centralizer ℂ {B} := by
    rw [Subalgebra.mem_centralizer_iff]; intro x hx; rw [Set.mem_singleton_iff.1 hx]; exact h.eq.symm
  have e : Polynomial.aeval A p = ((Polynomial.aeval (⟨A, hA⟩ : Subalgebra.centralizer ℂ {B}) p :
      Subalgebra.centralizer ℂ {B}) : Matrix (Fin n) (Fin n) ℂ) :=
    Polynomial.aeval_algHom_apply (Subalgebra.centralizer ℂ {B}).val (⟨A, hA⟩ : Subalgebra.centralizer ℂ {B}) p
  have hm := (Polynomial.aeval (⟨A, hA⟩ : Subalgebra.centralizer ℂ {B}) p).2
  rw [Subalgebra.mem_centralizer_iff] at hm
  rw [Commute, SemiconjBy, e]
  exact (hm B rfl).symm

/- English proof (translation)
Introduce `y hy` and use `by rw [Matrix.smul_mulVec]; exact V.smul_of_tower_mem t (hA y hy)`.
-/
theorem smul_keeps {A : Matrix (Fin n) (Fin n) ℂ} {V : Submodule ℂ (Fin n → ℂ)} (hA : ∀ y ∈ V, A *ᵥ y ∈ V)
    (t : ℝ) : ∀ y ∈ V, (t • A) *ᵥ y ∈ V := fun y hy => by
  rw [Matrix.smul_mulVec]; exact V.smul_of_tower_mem t (hA y hy)

/- English proof (translation)
Take `⟨u, rfl⟩ : g ∈ Set.range (coeMatrixAlt ε)` from `by rw [range_coeMatrix]; exact hg`. Conclude with `(u : (Matrix (Fin n) (Fin n) ℂ)ˣ).isUnit`.
-/
theorem isUnit_of_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : IsUnit g := by
  obtain ⟨u, rfl⟩ : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hg
  exact (u : (Matrix (Fin n) (Fin n) ℂ)ˣ).isUnit

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, ⟨hM, hD⟩, rfl⟩`. Conclude with `⟨u.2, hM, hD⟩`. Introduce and unpack `⟨hU, hM, hD⟩`. Take `⟨u, rfl⟩ : g ∈ Set.range (coeMatrixAlt ε)` from `by rw [range_coeMatrix]; exact hU`.

Conclude with `⟨u, ⟨hM, hD⟩, rfl⟩`.
-/
theorem mem_mats_leviOne {W : Flag n a} {g : Matrix (Fin n) (Fin n) ℂ} :
    g ∈ mats (leviOne ε W) ↔ inUJ ε g ∧ (∀ i, ∀ y ∈ W i, g *ᵥ y ∈ W i ∧ gᴴ *ᵥ y ∈ W i) ∧
      ∀ i, detOn g (W i) = 1 := by
  constructor
  · rintro ⟨u, ⟨hM, hD⟩, rfl⟩
    exact ⟨u.2, hM, hD⟩
  · rintro ⟨hU, hM, hD⟩
    obtain ⟨u, rfl⟩ : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hU
    exact ⟨u, ⟨hM, hD⟩, rfl⟩

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `hg`. Take `⟨v, hv, rfl⟩` from `hh`. Conclude with `⟨u * v, (leviOne ε W).mul_mem hu hv, rfl⟩`.
-/
theorem mats_mul {W : Flag n a} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ mats (leviOne ε W))
    (hh : h ∈ mats (leviOne ε W)) : g * h ∈ mats (leviOne ε W) := by
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨v, hv, rfl⟩ := hh
  exact ⟨u * v, (leviOne ε W).mul_mem hu hv, rfl⟩

/- English proof (translation)
Apply the tactic sequence `unfold detOn; split_ifs <;> positivity`.
-/
theorem detOn_nonneg (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)) : 0 ≤ detOn g V := by
  unfold detOn; split_ifs <;> positivity

def jUnit (ε : Fin n → Bool) : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩

/- English proof (translation)
Conclude with `Matrix.exp_units_conj' (jUnit ε) A`.
-/
theorem exp_conj_J (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Jm ε * A * Jm ε) = Jm ε * NormedSpace.exp A * Jm ε := by
  exact Matrix.exp_units_conj' (jUnit ε) A

/- English proof (translation)
Establish `: (keepAlg V : Set (Matrix (Fin n) (Fin n) ℂ)) = ⋂ z ∈ V, {M | M *ᵥ z ∈ V}`. Use extensionality with `M`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `isClosed_biInter fun z _ => V.closed_of_finiteDimensional.preimage (continuous_id.matrix_mulVec continuous_const)`.
-/
theorem isClosed_keepAlg (V : Submodule ℂ (Fin n → ℂ)) : IsClosed (keepAlg V : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have : (keepAlg V : Set (Matrix (Fin n) (Fin n) ℂ)) = ⋂ z ∈ V, {M | M *ᵥ z ∈ V} := by
    ext M; simp only [Set.mem_iInter, Set.mem_setOf_eq]; rfl
  rw [this]
  exact isClosed_biInter fun z _ =>
    V.closed_of_finiteDimensional.preimage (continuous_id.matrix_mulVec continuous_const)

/- English proof (translation)
Distinguish the cases in `hs : Summable f`. Conclude with `(isClosed_keepAlg V).mem_of_tendsto hs.hasSum (Filter.Eventually.of_forall fun s => Subalgebra.sum_mem _ fun k _ => hf k)`. Rewrite using `[tsum_eq_zero_of_not_summable hs]`. Conclude with `Subalgebra.zero_mem _`.
-/
theorem tsum_mem_keepAlg {V : Submodule ℂ (Fin n → ℂ)} (f : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ k, f k ∈ keepAlg V) : ∑' k, f k ∈ keepAlg V := by
  by_cases hs : Summable f
  · exact (isClosed_keepAlg V).mem_of_tendsto hs.hasSum
      (Filter.Eventually.of_forall fun s => Subalgebra.sum_mem _ fun k _ => hf k)
  · rw [tsum_eq_zero_of_not_summable hs]; exact Subalgebra.zero_mem _

/- English proof (translation)
Introduce `hA`. Use `show NormedSpace.exp A ∈ keepAlg V`. Rewrite using `[NormedSpace.exp_eq_tsum ℂ]`. Conclude with `tsum_mem_keepAlg _ fun k => Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (show A ∈ keepAlg V from hA) k) _`.
-/
theorem exp_keeps (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)) :
    (∀ y ∈ V, A *ᵥ y ∈ V) → ∀ y ∈ V, NormedSpace.exp A *ᵥ y ∈ V := by
  intro hA
  show NormedSpace.exp A ∈ keepAlg V
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact tsum_mem_keepAlg _ fun k => Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (show A ∈ keepAlg V from hA) k) _

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]`.
-/
theorem J_J_mul (x : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * x) = x := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

/- English proof (translation)
The claim follows from `mul_eq_one_comm.mp (coeMatrix_left_inv ε g hg)`.
-/
theorem mul_conj_J {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * (Jm ε * gᴴ * Jm ε) = 1 :=
  mul_eq_one_comm.mp (coeMatrix_left_inv ε g hg)

/- English proof (translation)
Unfold `inUJ`. Rewrite using `[conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]`. Use `_ = Jm ε := by rw [mul_conj_J hg, Matrix.one_mul]`.
-/
theorem inUJ_conjTranspose {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : inUJ ε gᴴ := by
  unfold inUJ
  rw [conjTranspose_conjTranspose]
  calc g * Jm ε * gᴴ = (g * (Jm ε * gᴴ * Jm ε)) * Jm ε := by
        simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = Jm ε := by rw [mul_conj_J hg, Matrix.one_mul]

/- English proof (translation)
Introduce `y hy` and use `by rw [Matrix.neg_mulVec]; exact V.neg_mem (hA y hy)`.
-/
theorem neg_keeps {A : Matrix (Fin n) (Fin n) ℂ} {V : Submodule ℂ (Fin n → ℂ)} (hA : ∀ y ∈ V, A *ᵥ y ∈ V) :
    ∀ y ∈ V, (-A) *ᵥ y ∈ V := fun y hy => by
  rw [Matrix.neg_mulVec]; exact V.neg_mem (hA y hy)

open scoped Matrix.Norms.L2Operator in
/- English proof (translation)
Use `letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _`. Conclude with `NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)`.
-/
theorem continuous_exp_smul (X : Matrix (Fin n) (Fin n) ℂ) : Continuous (fun s : ℝ => NormedSpace.exp (s • X)) := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

/- English proof (translation)
Take `⟨hU, hM, hD⟩` from `mem_mats_leviOne.1 hg`. Take `⟨L, p, hLs, hLe, hLp⟩` from `exists_herm_log n g (isUnit_of_inUJ hU)`. Establish `hhk : ∀ i, ∀ y ∈ W i, (gᴴ * g) *ᵥ y ∈ W i` using `fun i y hy => by`. Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `(hM i _ (hM i y hy).1).2`.

Establish `hLk : ∀ i, ∀ y ∈ W i, L *ᵥ y ∈ W i` using `fun i => hLp ▸ aeval_keeps (hhk i) p`. Establish `hJL : Jm ε * L * Jm ε = -L`. Use `herm_exp_inj n _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose, hLs, Matrix.mul_assoc]`. Rewrite using `[conjTranspose_neg, hLs]`.

Rewrite using `[exp_conj_J, hLe, Matrix.exp_neg, hLe]`. Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, J_J_mul]`. Use `_ = 1 := by rw [mul_conj_J hU, Matrix.mul_one, ← Matrix.mul_assoc]; exact coeMatrix_left_inv ε g hU`.

Establish `hadd : ∀ s r : ℝ, NormedSpace.exp (s • L) * NormedSpace.exp (r • L) = NormedSpace.exp ((s + r) • L)` using `fun s r => by rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left s).smul_right r)]`. Establish `hEs : ∀ s : ℝ, (NormedSpace.exp (s • L))ᴴ = NormedSpace.exp (s • L)` using `fun s => by`. Rewrite using `[← Matrix.exp_conjTranspose, conjTranspose_smul, hLs, star_trivial]`. Establish `hdet : ∀ i s, detOn (NormedSpace.exp (s • L)) (W i) = 1` using `fun i s => by`. Take `⟨c, hc⟩` from `detOn_exp_smul n L (W i) (hLk i)`.

Establish `h1` using `hc 1`. Rewrite `h1` using `[one_smul, hLe, detOn_mul (fun y hy => (hM i y hy).2) (fun y hy => (hM i y hy).1), detOn_conjTranspose n g (W i) (fun y hy => (hM i y hy).1) (fun y hy => (hM i y hy).2), hD i, one_mul, one_mul, eq_comm, Real.exp_eq_one_iff]`. Rewrite using `[hc s, h1, mul_zero, Real.exp_zero]`. Establish `hmem : ∀ s : ℝ, NormedSpace.exp (s • L) ∈ mats (leviOne ε W)` using `fun s => by`. Establish `hk : ∀ i, ∀ y ∈ W i, NormedSpace.exp (s • L) *ᵥ y ∈ W i` using `fun i => exp_keeps n (s • L) (W i) (smul_keeps (hLk i) s)`.

Use `mem_mats_leviOne.2 ⟨?_, fun i y hy => ⟨hk i y hy, by rw [hEs]; exact hk i y hy⟩, fun i => hdet i s⟩` and prove the remaining obligations. Unfold `inUJ`. Establish `hJE : Jm ε * NormedSpace.exp (s • L) * Jm ε = NormedSpace.exp ((-s) • L)`. Rewrite using `[← exp_conj_J, Matrix.mul_smul, Matrix.smul_mul, hJL, smul_neg, neg_smul]`. Rewrite using `[hEs]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, J_J_mul]`. Use `_ = Jm ε := by rw [hJE, Matrix.mul_assoc, hadd, neg_add_cancel, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]`. Use `⟨(1 / 2 : ℝ) • L, fun t => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Conclude with `hmem _`. Rewrite using `[← neg_smul, conjTranspose_mul, hEs, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, ← hLe]`. Establish `: NormedSpace.exp L = NormedSpace.exp ((1 : ℝ) • L)` using `by rw [one_smul]`. Rewrite using `[this, hadd, hadd, show (-(1 / 2 : ℝ) + (1 + -(1 / 2))) = 0 by norm_num, zero_smul, NormedSpace.exp_zero]`.
-/
theorem exists_pos_part {W : Flag n a} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ mats (leviOne ε W)) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ mats (leviOne ε W)) ∧
      (g * NormedSpace.exp (-Y))ᴴ * (g * NormedSpace.exp (-Y)) = 1 := by
  obtain ⟨hU, hM, hD⟩ := mem_mats_leviOne.1 hg
  obtain ⟨L, p, hLs, hLe, hLp⟩ := exists_herm_log n g (isUnit_of_inUJ hU)
  have hhk : ∀ i, ∀ y ∈ W i, (gᴴ * g) *ᵥ y ∈ W i := fun i y hy => by
    rw [← Matrix.mulVec_mulVec]; exact (hM i _ (hM i y hy).1).2
  have hLk : ∀ i, ∀ y ∈ W i, L *ᵥ y ∈ W i := fun i => hLp ▸ aeval_keeps (hhk i) p
  have hJL : Jm ε * L * Jm ε = -L := by
    refine herm_exp_inj n _ _ ?_ ?_ ?_
    · rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose, hLs, Matrix.mul_assoc]
    · rw [conjTranspose_neg, hLs]
    · rw [exp_conj_J, hLe, Matrix.exp_neg, hLe]
      refine (Matrix.inv_eq_left_inv ?_).symm
      calc Jm ε * (gᴴ * g) * Jm ε * (gᴴ * g) = (Jm ε * gᴴ) * (g * (Jm ε * gᴴ * Jm ε)) * (Jm ε * g) := by
            simp only [Matrix.mul_assoc, J_J_mul]
        _ = 1 := by rw [mul_conj_J hU, Matrix.mul_one, ← Matrix.mul_assoc]; exact coeMatrix_left_inv ε g hU
  have hadd : ∀ s r : ℝ, NormedSpace.exp (s • L) * NormedSpace.exp (r • L) = NormedSpace.exp ((s + r) • L) :=
    fun s r => by rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left s).smul_right r)]
  have hEs : ∀ s : ℝ, (NormedSpace.exp (s • L))ᴴ = NormedSpace.exp (s • L) := fun s => by
    rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hLs, star_trivial]
  have hdet : ∀ i s, detOn (NormedSpace.exp (s • L)) (W i) = 1 := fun i s => by
    obtain ⟨c, hc⟩ := detOn_exp_smul n L (W i) (hLk i)
    have h1 := hc 1
    rw [one_smul, hLe, detOn_mul (fun y hy => (hM i y hy).2) (fun y hy => (hM i y hy).1),
      detOn_conjTranspose n g (W i) (fun y hy => (hM i y hy).1) (fun y hy => (hM i y hy).2), hD i, one_mul,
      one_mul, eq_comm, Real.exp_eq_one_iff] at h1
    rw [hc s, h1, mul_zero, Real.exp_zero]
  have hmem : ∀ s : ℝ, NormedSpace.exp (s • L) ∈ mats (leviOne ε W) := fun s => by
    have hk : ∀ i, ∀ y ∈ W i, NormedSpace.exp (s • L) *ᵥ y ∈ W i := fun i =>
      exp_keeps n (s • L) (W i) (smul_keeps (hLk i) s)
    refine mem_mats_leviOne.2 ⟨?_, fun i y hy => ⟨hk i y hy, by rw [hEs]; exact hk i y hy⟩, fun i => hdet i s⟩
    unfold inUJ
    have hJE : Jm ε * NormedSpace.exp (s • L) * Jm ε = NormedSpace.exp ((-s) • L) := by
      rw [← exp_conj_J, Matrix.mul_smul, Matrix.smul_mul, hJL, smul_neg, neg_smul]
    rw [hEs]
    calc NormedSpace.exp (s • L) * Jm ε * NormedSpace.exp (s • L)
        = Jm ε * (Jm ε * NormedSpace.exp (s • L) * Jm ε) * NormedSpace.exp (s • L) := by
          simp only [Matrix.mul_assoc, J_J_mul]
      _ = Jm ε := by rw [hJE, Matrix.mul_assoc, hadd, neg_add_cancel, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
  refine ⟨(1 / 2 : ℝ) • L, fun t => ?_, ?_⟩
  · rw [smul_smul]; exact hmem _
  · rw [← neg_smul, conjTranspose_mul, hEs, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, ← hLe]
    have : NormedSpace.exp L = NormedSpace.exp ((1 : ℝ) • L) := by rw [one_smul]
    rw [this, hadd, hadd, show (-(1 / 2 : ℝ) + (1 + -(1 / 2))) = 0 by norm_num, zero_smul, NormedSpace.exp_zero]

/- English proof (translation)
Take `⟨hU, hM, hD⟩` from `mem_mats_leviOne.1 hk`. Take `⟨X, q, hXs, hXe, hXq⟩` from `exists_unitary_log n k hu`. Establish `hkJ : Commute k (Jm ε)`. Establish `h1 : k * kᴴ = 1` using `mul_eq_one_comm.mp hu`. Use `show k * Jm ε = Jm ε * k`.

Combine the equalities or inequalities in the displayed calculation. Establish `hXJ : Commute X (Jm ε)` using `hXq ▸ aeval_commute hkJ q`. Establish `hXk : ∀ i, ∀ y ∈ W i, X *ᵥ y ∈ W i` using `fun i => hXq ▸ aeval_keeps (fun y hy => (hM i y hy).1) q`. Use `⟨X, fun t => ?_, hXe⟩` and prove the remaining obligations. Establish `hEs : (NormedSpace.exp (t • X))ᴴ = NormedSpace.exp (-(t • X))`.

Rewrite using `[← Matrix.exp_conjTranspose, conjTranspose_smul, hXs, star_trivial, smul_neg]`. Establish `hEE : (NormedSpace.exp (t • X))ᴴ * NormedSpace.exp (t • X) = 1`. Rewrite using `[hEs, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero]`. Establish `hJE : Jm ε * NormedSpace.exp (t • X) * Jm ε = NormedSpace.exp (t • X)`. Rewrite using `[← exp_conj_J, Matrix.mul_smul, Matrix.smul_mul, ← hXJ.eq, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]`.

Establish `hk1 : ∀ i, ∀ y ∈ W i, NormedSpace.exp (t • X) *ᵥ y ∈ W i` using `fun i => exp_keeps n (t • X) (W i) (smul_keeps (hXk i) t)`. Establish `hk2 : ∀ i, ∀ y ∈ W i, (NormedSpace.exp (t • X))ᴴ *ᵥ y ∈ W i` using `fun i => by`. Rewrite using `[hEs]`. Conclude with `exp_keeps n _ (W i) (neg_keeps (smul_keeps (hXk i) t))`. Use `mem_mats_leviOne.2 ⟨?_, fun i y hy => ⟨hk1 i y hy, hk2 i y hy⟩, fun i => ?_⟩` and prove the remaining obligations.

Unfold `inUJ`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]`. Use `_ = Jm ε := by rw [hJE, hEE, Matrix.one_mul]`. Establish `h` using `detOn_mul (hk2 i) (hk1 i)`.

Rewrite `h` using `[hEE, detOn_one, detOn_conjTranspose n _ (W i) (hk1 i) (hk2 i)]`. Use polynomial arithmetic with `[detOn_nonneg (NormedSpace.exp (t • X)) (W i)]`.
-/
theorem exists_unit_part {W : Flag n a} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ mats (leviOne ε W))
    (hu : kᴴ * k = 1) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) ∧
      NormedSpace.exp X = k := by
  obtain ⟨hU, hM, hD⟩ := mem_mats_leviOne.1 hk
  obtain ⟨X, q, hXs, hXe, hXq⟩ := exists_unitary_log n k hu
  have hkJ : Commute k (Jm ε) := by
    have h1 : k * kᴴ = 1 := mul_eq_one_comm.mp hu
    show k * Jm ε = Jm ε * k
    calc k * Jm ε = k * (kᴴ * Jm ε * k) := by rw [hU]
      _ = (k * kᴴ) * Jm ε * k := by simp only [Matrix.mul_assoc]
      _ = Jm ε * k := by rw [h1, Matrix.one_mul]
  have hXJ : Commute X (Jm ε) := hXq ▸ aeval_commute hkJ q
  have hXk : ∀ i, ∀ y ∈ W i, X *ᵥ y ∈ W i := fun i => hXq ▸ aeval_keeps (fun y hy => (hM i y hy).1) q
  refine ⟨X, fun t => ?_, hXe⟩
  have hEs : (NormedSpace.exp (t • X))ᴴ = NormedSpace.exp (-(t • X)) := by
    rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hXs, star_trivial, smul_neg]
  have hEE : (NormedSpace.exp (t • X))ᴴ * NormedSpace.exp (t • X) = 1 := by
    rw [hEs, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  have hJE : Jm ε * NormedSpace.exp (t • X) * Jm ε = NormedSpace.exp (t • X) := by
    rw [← exp_conj_J, Matrix.mul_smul, Matrix.smul_mul, ← hXJ.eq, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
  have hk1 : ∀ i, ∀ y ∈ W i, NormedSpace.exp (t • X) *ᵥ y ∈ W i := fun i =>
    exp_keeps n (t • X) (W i) (smul_keeps (hXk i) t)
  have hk2 : ∀ i, ∀ y ∈ W i, (NormedSpace.exp (t • X))ᴴ *ᵥ y ∈ W i := fun i => by
    rw [hEs]; exact exp_keeps n _ (W i) (neg_keeps (smul_keeps (hXk i) t))
  refine mem_mats_leviOne.2 ⟨?_, fun i y hy => ⟨hk1 i y hy, hk2 i y hy⟩, fun i => ?_⟩
  · unfold inUJ
    calc (NormedSpace.exp (t • X))ᴴ * Jm ε * NormedSpace.exp (t • X)
        = (NormedSpace.exp (t • X))ᴴ * (Jm ε * NormedSpace.exp (t • X) * Jm ε) * Jm ε := by
          simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
      _ = Jm ε := by rw [hJE, hEE, Matrix.one_mul]
  · have h := detOn_mul (hk2 i) (hk1 i)
    rw [hEE, detOn_one, detOn_conjTranspose n _ (W i) (hk1 i) (hk2 i)] at h
    nlinarith [detOn_nonneg (NormedSpace.exp (t • X)) (W i)]

/- English proof (translation)
Take `⟨Y, hY, hu⟩` from `exists_pos_part hg`. Establish `hY1` using `hY (-1)`. Rewrite `hY1` using `[neg_one_smul]`. Take `⟨X, hX, hXe⟩` from `exists_unit_part (mats_mul hg hY1) hu`. Use `⟨X, Y, hX, hY, ?_⟩` and prove the remaining obligations.

Rewrite using `[hXe, Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]`.
-/
theorem exists_exp_mul_exp {W : Flag n a} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ mats (leviOne ε W)) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) ∧
      (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ mats (leviOne ε W)) ∧ g = NormedSpace.exp X * NormedSpace.exp Y := by
  obtain ⟨Y, hY, hu⟩ := exists_pos_part hg
  have hY1 := hY (-1)
  rw [neg_one_smul] at hY1
  obtain ⟨X, hX, hXe⟩ := exists_unit_part (mats_mul hg hY1) hu
  refine ⟨X, Y, hX, hY, ?_⟩
  rw [hXe, Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

/- English proof (translation)
Introduce `n ε a j W hW hj`. Use `⟨⟨⟨1, (leviOne ε W).one_mem, rfl⟩, fun g hg h hh => mats_mul hg hh, fun g hg => isUnit_of_inUJ (mem_mats_leviOne.1 hg).1, ?_, ?_, ?_, ?_⟩, fun g hg => exists_exp_mul_exp hg⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `⟨u⁻¹, (leviOne ε W).inv_mem hu, (Matrix.inv_eq_right_inv (uMat_mul_inv u)).symm⟩`. Introduce `g _ hg`.

Establish `hc : IsClosed (mats (leviOne ε W))` using `(isClosedEmbeddingMatrix n ε).1.isClosedMap _ (isClosed_leviOne hW hj)`. Rewrite `hg` using `[hc.closure_eq]`. Then use the resulting hypothesis. Use `isPreconnected_of_forall 1 fun g hg => ?_` and prove the remaining obligations. Take `⟨X, Y, hX, hY, rfl⟩` from `exists_exp_mul_exp hg`. Use `⟨(fun s : ℝ => NormedSpace.exp (s • X) * NormedSpace.exp (s • Y)) '' Set.Icc 0 1, ?_, ⟨0, ⟨le_refl _, zero_le_one⟩, by simp⟩, ⟨1, ⟨zero_le_one, le_refl _⟩, by simp⟩, isPreconnected_Icc.image _ ((continuous_exp_smul X).mul (continuous_exp_smul Y)).continuousOn⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨s, -, rfl⟩`. Conclude with `mats_mul (hX s) (hY s)`. Introduce `g hg`. Take `⟨hU, hM, hD⟩` from `mem_mats_leviOne.1 hg`. Use `mem_mats_leviOne.2 ⟨inUJ_conjTranspose hU, fun i y hy => ⟨(hM i y hy).2, by` and prove the remaining obligations.

Rewrite using `[conjTranspose_conjTranspose]`. Conclude with `(hM i y hy).1⟩, fun i => ?_⟩`. Rewrite using `[detOn_conjTranspose n g (W i) (fun y hy => (hM i y hy).1) (fun y hy => (hM i y hy).2)]`. Conclude with `hD i`.
-/
theorem isLinRed_leviOne : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W →
    (∀ i, 1 ≤ j i) → GlobalTheory.LinRed.IsLinRed (mats (leviOne ε W)) ∧ ∀ g ∈ mats (leviOne ε W),
      ∃ X Y : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) ∧
        (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ mats (leviOne ε W)) ∧ g = NormedSpace.exp X * NormedSpace.exp Y := by
  intro n ε a j W hW hj
  refine ⟨⟨⟨1, (leviOne ε W).one_mem, rfl⟩, fun g hg h hh => mats_mul hg hh,
    fun g hg => isUnit_of_inUJ (mem_mats_leviOne.1 hg).1, ?_, ?_, ?_, ?_⟩, fun g hg => exists_exp_mul_exp hg⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, (leviOne ε W).inv_mem hu, (Matrix.inv_eq_right_inv (uMat_mul_inv u)).symm⟩
  · intro g _ hg
    have hc : IsClosed (mats (leviOne ε W)) :=
      (isClosedEmbeddingMatrix n ε).1.isClosedMap _ (isClosed_leviOne hW hj)
    rwa [hc.closure_eq] at hg
  · refine isPreconnected_of_forall 1 fun g hg => ?_
    obtain ⟨X, Y, hX, hY, rfl⟩ := exists_exp_mul_exp hg
    refine ⟨(fun s : ℝ => NormedSpace.exp (s • X) * NormedSpace.exp (s • Y)) '' Set.Icc 0 1, ?_,
      ⟨0, ⟨le_refl _, zero_le_one⟩, by simp⟩, ⟨1, ⟨zero_le_one, le_refl _⟩, by simp⟩,
      isPreconnected_Icc.image _ ((continuous_exp_smul X).mul (continuous_exp_smul Y)).continuousOn⟩
    rintro _ ⟨s, -, rfl⟩
    exact mats_mul (hX s) (hY s)
  · intro g hg
    obtain ⟨hU, hM, hD⟩ := mem_mats_leviOne.1 hg
    refine mem_mats_leviOne.2 ⟨inUJ_conjTranspose hU, fun i y hy => ⟨(hM i y hy).2, by
      rw [conjTranspose_conjTranspose]; exact (hM i y hy).1⟩, fun i => ?_⟩
    rw [detOn_conjTranspose n g (W i) (fun y hy => (hM i y hy).1) (fun y hy => (hM i y hy).2)]
    exact hD i

end GlobalTheory.LeviPolar
