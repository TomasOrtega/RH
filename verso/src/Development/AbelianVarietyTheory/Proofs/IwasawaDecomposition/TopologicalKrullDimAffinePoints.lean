import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
open Module TopologicalSpace GlobalTheory.FlagPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPts

open MvPolynomial

variable {k : Type} [Field k] {J : Type}

def affPtsVanIdeal (x : AffPts k J) : PrimeSpectrum (MvPolynomial J k) :=
  ⟨RingHom.ker (MvPolynomial.eval (show J → k from x)), RingHom.ker_isPrime _⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_affPtsVanIdeal_preimage_basicOpen (p : MvPolynomial J k) (x : AffPts k J) :
    x ∈ affPtsVanIdeal ⁻¹' (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial J k))) ↔
      MvPolynomial.eval x p ≠ 0 := by
  simp [affPtsVanIdeal, PrimeSpectrum.mem_basicOpen]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem isInducing_affPtsVanIdeal : Topology.IsInducing (affPtsVanIdeal (k := k) (J := J)) := by
  rw [Topology.isInducing_iff, PrimeSpectrum.isTopologicalBasis_basic_opens.eq_generateFrom,
    induced_generateFrom_eq]
  show TopologicalSpace.generateFrom _ = _
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, ⟨p, rfl⟩, by ext x; exact mem_affPtsVanIdeal_preimage_basicOpen p x⟩
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, by ext x; exact mem_affPtsVanIdeal_preimage_basicOpen p x⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem topologicalKrullDim_affPts_le [Fintype J] :
    topologicalKrullDim (AffPts k J) ≤ (Fintype.card J : ℕ) := by
  refine isInducing_affPtsVanIdeal.topologicalKrullDim_le.trans ?_
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card]
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isTopologicalBasis_affPts :
    IsTopologicalBasis (Set.preimage (affPtsVanIdeal (k := k) (J := J)) ''
      Set.range fun p : MvPolynomial J k ↦ (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial J k)))) :=
  PrimeSpectrum.isTopologicalBasis_basic_opens.isInducing isInducing_affPtsVanIdeal

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isIrreducible_univ_affPts [Infinite k] : IsIrreducible (Set.univ : Set (AffPts k J)) := by
  refine ⟨⟨fun _ ↦ 0, trivial⟩, ?_⟩
  rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
  obtain ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, hxp, hpu⟩ := isTopologicalBasis_affPts.exists_subset_of_mem_open hx hu
  obtain ⟨_, ⟨_, ⟨q, rfl⟩, rfl⟩, hyq, hqv⟩ := isTopologicalBasis_affPts.exists_subset_of_mem_open hy hv
  rw [mem_affPtsVanIdeal_preimage_basicOpen] at hxp hyq
  have hp : p ≠ 0 := by rintro rfl; simp at hxp
  have hq : q ≠ 0 := by rintro rfl; simp at hyq
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  obtain ⟨z, hz⟩ : ∃ z : AffPts k J, MvPolynomial.eval z (p * q) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hpq (MvPolynomial.funext fun z ↦ by simpa using h z)
  rw [map_mul] at hz
  refine ⟨z, trivial, hpu ?_, hqv ?_⟩
  · exact (mem_affPtsVanIdeal_preimage_basicOpen p z).2 (left_ne_zero_of_mul hz)
  · exact (mem_affPtsVanIdeal_preimage_basicOpen q z).2 (right_ne_zero_of_mul hz)

open Classical in

def affPtsProj (S : Set J) (x : AffPts k J) : AffPts k J := fun j ↦ if j ∈ S then x j else 0

open Classical in
/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eval_affPtsProj (S : Set J) (x : AffPts k J) (p : MvPolynomial J k) :
    MvPolynomial.eval (affPtsProj S x) p =
      MvPolynomial.eval x (MvPolynomial.bind₁ (fun j ↦ if j ∈ S then (X j : MvPolynomial J k) else 0) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.bind₁_C_right]
    exact (MvPolynomial.eval_C (f := affPtsProj S x) a).trans (MvPolynomial.eval_C (f := x) a).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.bind₁_X_right]
    congr 1
    rw [MvPolynomial.eval_X (f := affPtsProj S x)]
    by_cases hj : j ∈ S
    · rw [if_pos hj, MvPolynomial.eval_X (f := x)]
      show (if j ∈ S then x j else 0) = x j
      rw [if_pos hj]
    · rw [if_neg hj, map_zero]
      show (if j ∈ S then x j else 0) = 0
      rw [if_neg hj]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem continuous_affPtsProj (S : Set J) : Continuous (affPtsProj (k := k) S) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨p, rfl⟩
  classical
  convert isOpen_affPts_ne_zero (k := k)
    (MvPolynomial.bind₁ (fun j ↦ if j ∈ S then (X j : MvPolynomial J k) else 0) p) using 1
  ext x
  show MvPolynomial.eval (affPtsProj S x) p ≠ 0 ↔ _
  rw [eval_affPtsProj]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem range_affPtsProj (S : Set J) :
    Set.range (affPtsProj (k := k) S) = {x : AffPts k J | ∀ j, j ∉ S → x j = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ j hj
    simp [affPtsProj, hj]
  · intro hx
    refine ⟨x, funext fun j ↦ ?_⟩
    by_cases hj : j ∈ S
    · simp [affPtsProj, hj]
    · simp [affPtsProj, hj, hx j hj]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isClosed_coordSubspace (S : Set J) : IsClosed {x : AffPts k J | ∀ j, j ∉ S → x j = 0} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦ ?_
  rw [← isOpen_compl_iff]
  have : ({x : AffPts k J | x j = 0}ᶜ : Set (AffPts k J)) =
      {x : AffPts k J | MvPolynomial.eval x (X j : MvPolynomial J k) ≠ 0} := by
    ext x
    exact Iff.not (Eq.to_iff (congrArg (· = (0 : k)) (MvPolynomial.eval_X (f := x) j).symm))
  rw [this]
  exact isOpen_affPts_ne_zero _

def coordSubspace [Infinite k] (S : Set J) : IrreducibleCloseds (AffPts k J) :=
  ⟨{x : AffPts k J | ∀ j, j ∉ S → x j = 0},
    by
      rw [← range_affPtsProj, ← Set.image_univ]
      exact isIrreducible_univ_affPts.image _ (continuous_affPtsProj S).continuousOn,
    isClosed_coordSubspace S⟩

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem le_topologicalKrullDim_affPts [Infinite k] [Fintype J] :
    ((Fintype.card J : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (AffPts k J) := by
  classical
  set e := Fintype.equivFin J
  set n := Fintype.card J
  let f : Fin (n + 1) → IrreducibleCloseds (AffPts k J) :=
    fun m ↦ coordSubspace {j | (e j : ℕ) < m}
  have hf : StrictMono f := by
    intro a b hab
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun x hx j hj ↦ hx j fun h ↦ hj ?_, ?_⟩
    · exact lt_trans (Set.mem_setOf.1 h) hab
    have ha : (a : ℕ) < n := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 b.2)
    refine ⟨fun j ↦ if (e j : ℕ) = a then 1 else 0, ?_, ?_⟩
    · intro j hj
      have : (e j : ℕ) ≠ a := fun h ↦ hj (by simp only [Set.mem_setOf_eq, h]; exact hab)
      simp [this]
    · intro hx
      have := hx (e.symm ⟨a, ha⟩) (by simp)
      simp at this
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk n f hf)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem topologicalKrullDim_affPts_eq_card :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J],
      topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by
  intro k _ _ J _
  haveI : Infinite k := inferInstance
  exact le_antisymm topologicalKrullDim_affPts_le le_topologicalKrullDim_affPts

end GlobalTheory.FlagPts
