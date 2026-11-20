import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DetHom

section MH

variable {R : Type} [CommSemiring R] {B n : ℕ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem mh_zero (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Substitute using the available equality.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mh_C (r : R) : IsMultiHomogeneous (0 : Fin B → ℕ) (C r : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_C] at hs
  have : (0 : Fin B × Fin n →₀ ℕ) = s := by
    by_contra h; exact hs (if_neg h)
  subst this; simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Substitute using the available equality.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mh_X (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (Pi.single i 1) (X (i, j) : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_X'] at hs
  have : Finsupp.single (i, j) 1 = s := by
    by_contra h; exact hs (if_neg h)
  subst this
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, hb, Pi.single_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem mh_add {a : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous a g) : IsMultiHomogeneous a (f + g) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (support_add hs) with h | h
  exacts [hf s h, hg s h]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mh_sum {ι : Type} (t : Finset ι) {a : Fin B → ℕ} (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous a (f i)) : IsMultiHomogeneous a (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_zero (R := R) (n := n) a
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact mh_add (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem mh_smul {S : Type} [SMulZeroClass S R] {a : Fin B → ℕ} (c : S) {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) : IsMultiHomogeneous a (c • f) :=
  fun s hs => hf s (support_smul hs)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
theorem mh_mul {a b : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous b g) : IsMultiHomogeneous (a + b) (f * g) := by
  classical
  intro s hs i
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 (support_mul f g hs)
  simp [Finset.sum_add_distrib, hf u hu i, hg v hv i]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mh_prod {ι : Type} (t : Finset ι) (a : ι → Fin B → ℕ) (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous (a i) (f i)) : IsMultiHomogeneous (∑ i ∈ t, a i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_C (R := R) (B := B) (n := n) 1
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    exact mh_mul (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end MH

def cnt {B t : ℕ} (β : Fin t → Fin B) (b : Fin B) : ℕ := (Finset.univ.filter fun q => β q = b).card

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_cnt {B t : ℕ} (β : Fin t → Fin B) : ∑ b, cnt β b = t := by
  classical
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (β x))]
  simp

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem sum_single_eq_cnt {B t : ℕ} (β : Fin t → Fin B) :
    (∑ i, (Pi.single (β i) 1 : Fin B → ℕ)) = cnt β := by
  classical
  funext b
  simp only [Finset.sum_apply, Pi.single_apply, cnt]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : β i = b
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem mh_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (c : A →ₗ[K] K) (β : Fin t → Fin B) (m : A) :
    IsMultiHomogeneous (cnt β) (coordP mul c β m) := by
  classical
  unfold coordP
  refine mh_sum _ _ fun e _ => ?_
  have h := mh_mul (mh_C (R := K) (B := B) (n := N) (c (word mul (fun i => Pi.single (e i) 1) m)))
    (mh_prod Finset.univ (fun i => (Pi.single (β i) 1 : Fin B → ℕ)) (fun i => (X (β i, e i) : MvPolynomial (Fin B × Fin N) K))
      fun i _ => mh_X (β i) (e i))
  rwa [zero_add, sum_single_eq_cnt] at h

end GlobalTheory.HSShort.DetHom

open GlobalTheory.HSShort.DetHom in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.HSShort.det_isMultiHomogeneous : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A) (d : ℕ) (c : Fin d → A →ₗ[F] F) (col : Fin d → S.Col), ∃ a : Fin (S.D + 1) → ℕ, IsMultiHomogeneous a (S.det c col) ∧ ∑ i, a i = ∑ k, (col k).t := by
  intro F A _ _ _ _ _ _ S d c col
  classical
  refine ⟨∑ k, cnt (col k).β, ?_, ?_⟩
  · unfold Sys.det
    rw [Matrix.det_apply]
    refine mh_sum _ _ fun σ _ => mh_smul _ ?_
    have h := mh_prod Finset.univ (fun k => cnt (col k).β)
      (fun k => (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)) (σ k) k)
      fun k _ => by simpa using mh_coordP S.mul (c (σ k)) (col k).β ((col k).x : A)
    exact h
  · simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => sum_cnt (col k).β
