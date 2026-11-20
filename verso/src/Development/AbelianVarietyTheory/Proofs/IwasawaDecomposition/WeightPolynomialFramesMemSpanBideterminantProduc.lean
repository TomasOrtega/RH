import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BideterminantFunctionsOfShape

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

noncomputable section

namespace GlobalTheory.Mem.WeightBideterminants

open MvPolynomial

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem prod_eval_mem_span_prod_of_mem_span {L : Type} [Field L] {ι : Type} [Fintype ι] {X : Type}
    (A : ι → Set (X → L)) (s : Finset ι) :
    ∀ h : ι → X → L, (∀ τ ∈ s, h τ ∈ Submodule.span L (A τ)) → (∀ τ ∉ s, h τ ∈ A τ) →
      (fun y : ι → X => ∏ τ, h τ (y τ)) ∈
        Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h _ h2
    exact Submodule.subset_span ⟨h, fun τ => h2 τ (by simp), rfl⟩
  | insert a s ha ih =>
    intro h h1 h2

    have hsplit : ∀ x : X → L, (fun y : ι → X => ∏ τ, Function.update h a x τ (y τ)) =
        fun y => x (y a) * ∏ τ ∈ Finset.univ.erase a, h τ (y τ) := by
      intro x
      funext y
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro τ hτ
        rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hτ)]

    have key : ∀ x ∈ Submodule.span L (A a), (fun y : ι → X => ∏ τ, Function.update h a x τ (y τ)) ∈
        Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        apply ih
        · intro τ hτ
          have hne : τ ≠ a := fun e => ha (e ▸ hτ)
          rw [Function.update_apply, if_neg hne]
          exact h1 τ (Finset.mem_insert_of_mem hτ)
        · intro τ hτ
          by_cases e : τ = a
          · subst e
            simpa using hx
          · rw [Function.update_apply, if_neg e]
            exact h2 τ (by simp [e, hτ])
      | zero =>
        rw [hsplit]
        convert Submodule.zero_mem _ using 1
        funext y
        simp
      | add x x' _ _ hx hx' =>
        rw [hsplit] at hx hx' ⊢
        convert Submodule.add_mem _ hx hx' using 1
        funext y
        simp [add_mul]
      | smul c x _ hx =>
        rw [hsplit] at hx ⊢
        convert Submodule.smul_mem _ c hx using 1
        funext y
        simp [mul_assoc]
    simpa using key (h a) (h1 a (Finset.mem_insert_self a s))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem prod_mem_span_prod {L : Type} [Field L] {ι : Type} [Fintype ι] {X : Type} (A : ι → Set (X → L))
    (h : ι → X → L) (hh : ∀ τ, h τ ∈ Submodule.span L (A τ)) :
    (fun y : ι → X => ∏ τ, h τ (y τ)) ∈
      Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} :=
  prod_eval_mem_span_prod_of_mem_span A Finset.univ h (fun τ _ => hh τ) (fun τ hτ => absurd (Finset.mem_univ τ) hτ)

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem eval_rowAct {L : Type} [Field L] {N : ℕ} (g Y : Matrix (Fin N) (Fin N) L)
    (f : MvPolynomial (Fin N × Fin N) L) :
    eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct L g f) =
      eval (fun v : Fin N × Fin N => (g * Y) v.1 v.2) f := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    simp [Matrix.mul_apply]

def evFn (L : Type) [Field L] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) L →ₗ[L] (Matrix (Fin N) (Fin N) L → L) :=
  LinearMap.pi fun Y => (aeval fun v : Fin N × Fin N => Y v.1 v.2).toLinearMap

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem evFn_apply (L : Type) [Field L] (N : ℕ) (P : MvPolynomial (Fin N × Fin N) L) (Y : Matrix (Fin N) (Fin N) L) :
    evFn L N P Y = eval (fun v : Fin N × Fin N => Y v.1 v.2) P := by
  simp [evFn]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem evFn_mem_span (L : Type) [Field L] (N : ℕ) (ν : Fin N → ℕ) (P : MvPolynomial (Fin N × Fin N) L)
    (hP : P ∈ Formalism.GradedWeylDivisibility.dualWeyl L N N ν) : evFn L N P ∈ Submodule.span L (bideterminantFunctionsOfShape L N ν) := by

  obtain ⟨b, hb, hbm⟩ := Formalism.GradedWeylDivisibility.sSBasis L N N ν
  have hP' : P ∈ Submodule.span L (Set.range b) := by
    rw [hb.2.1]
    exact hP
  have h1 : evFn L N P ∈ (Submodule.span L (Set.range b)).map (evFn L N) := Submodule.mem_map_of_mem hP'
  rw [Submodule.map_span] at h1
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  obtain ⟨-, -, Kc, sz, hsz, I, hs, hI, hbI⟩ := hbm m
  refine ⟨Kc, sz, hsz, I, hs, hI, ?_⟩
  funext Y
  rw [evFn_apply, hbI]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem weightPolynomial_mem_span_bideterminantProducts : ∀ (K L : Type) [Field K] [Field L] [Infinite K] (φ : K →+* L) (ι : Type) [Fintype ι] (N : ℕ)
    (ν : ι → Fin N → ℕ) (M : ι → Matrix (Fin N) (Fin N) L), ∀ Q ∈ WtPol K ν,
    (fun y : ι → Matrix (Fin N) (Fin N) L =>
      MvPolynomial.eval (fun k : ι × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ Q)) ∈
    Submodule.span L {F | ∃ g : ι → Matrix (Fin N) (Fin N) L → L, (∀ τ, g τ ∈ bideterminantFunctionsOfShape L N (ν τ)) ∧
      F = fun y => ∏ τ, g τ (y τ)} := by
  intro K L _ _ _ φ ι _ N ν M Q hQ

  have hT := Formalism.L2.Ker.wtPol_le_tensor (K := K) ν hQ
  clear hQ
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx

    have hfun : (fun y : ι → Matrix (Fin N) (Fin N) L =>
        MvPolynomial.eval (fun k : ι × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2)
          (MvPolynomial.map φ (∏ s, Formalism.GradedWeylDivisibility.blockEmb K s (F s)))) =
        fun y => ∏ τ, evFn L N (Formalism.GradedWeylDivisibility.rowAct L (M τ) (MvPolynomial.map φ (F τ))) (y τ) := by
      funext y
      simp only [map_prod, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename, MvPolynomial.eval_rename, evFn_apply,
        eval_rowAct, Function.comp_def]
    rw [hfun]
    apply prod_mem_span_prod
    intro τ
    apply evFn_mem_span
    exact Formalism.GradedWeylDivisibility.dualWeylRowStable L N N (ν τ) (M τ) _ (Formalism.GradedWeylDivisibility.dualWeylMap K L φ N N (ν τ) (F τ) (hF τ))
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext y
    simp
  | add x x' _ _ hx hx' =>
    convert Submodule.add_mem _ hx hx' using 1
    funext y
    simp
  | smul c x _ hx =>
    convert Submodule.smul_mem _ (φ c) hx using 1
    funext y
    simp [MvPolynomial.smul_eq_C_mul]

end GlobalTheory.Mem.WeightBideterminants
