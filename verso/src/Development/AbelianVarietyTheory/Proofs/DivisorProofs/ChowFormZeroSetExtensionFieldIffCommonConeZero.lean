import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSolvabilityTransferAlgClosedFieldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosureStatement

set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.HSChoice

namespace GlobalTheory.ChowZeroExt

def incIdeal {F : Type} [Field F] (B : ℕ) {N : ℕ} (I : Ideal (MvPolynomial (Fin N) F)) :
    Ideal (MvPolynomial ((Fin B × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
  Ideal.span ((rename (fun j => Sum.inr (Sum.inl j)) '' (I : Set (MvPolynomial (Fin N) F))) ∪
    (Set.range (fun i : Fin B => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr (Sum.inl j))) ∪
      {∑ j, X (Sum.inr (Sum.inr j)) * X (Sum.inr (Sum.inl j)) - 1}))

/- English proof (translation)
Use `⟨fun h g hg => h g (Ideal.subset_span hg), fun h g hg => ?_⟩` and prove the remaining obligations. Establish `: Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial ι F →ₐ[F] Ω)` using `Ideal.span_le.2 fun g hg => h g hg`. Conclude with `this hg`.
-/
theorem forall_span_iff {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] (S : Set (MvPolynomial ι F))
    (x : ι → Ω) : (∀ g ∈ Ideal.span S, aeval x g = 0) ↔ ∀ g ∈ S, aeval x g = 0 := by
  refine ⟨fun h g hg => h g (Ideal.subset_span hg), fun h g hg => ?_⟩
  have : Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial ι F →ₐ[F] Ω) :=
    Ideal.span_le.2 fun g hg => h g hg
  exact this hg

/- English proof (translation)
Rewrite using `[incIdeal, forall_span_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun g hg => ?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `h _ (Or.inl ⟨g, hg, rfl⟩)` as an intermediate fact.

Rewrite `this` using `[aeval_rename]`. Then use the resulting hypothesis. Simplify using `using h _ (Or.inr (Or.inl ⟨i, rfl⟩))`. Simplify `h _ (Or.inr (Or.inr rfl))` using `[sub_eq_zero]`. Introduce and unpack `⟨h1, h2, h3⟩ g (⟨g, hg, rfl⟩ | ⟨i, rfl⟩ | rfl)`. Rewrite using `[aeval_rename]`.

Conclude with `h1 g hg`. Simplify using `using h2 i`. Simplify `h3` using `[sub_eq_zero]`.
-/
theorem forall_incIdeal_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {B N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) F)) (x : (Fin B × Fin N) ⊕ (Fin N ⊕ Fin N) → Ω) :
    (∀ g ∈ incIdeal B I, aeval x g = 0) ↔
      (∀ g ∈ I, aeval (fun j => x (Sum.inr (Sum.inl j))) g = 0) ∧
      (∀ i, ∑ j, x (Sum.inl (i, j)) * x (Sum.inr (Sum.inl j)) = 0) ∧
      ∑ j, x (Sum.inr (Sum.inr j)) * x (Sum.inr (Sum.inl j)) = 1 := by
  rw [incIdeal, forall_span_iff]
  constructor
  · intro h
    refine ⟨fun g hg => ?_, fun i => ?_, ?_⟩
    · have := h _ (Or.inl ⟨g, hg, rfl⟩)
      rwa [aeval_rename] at this
    · simpa using h _ (Or.inr (Or.inl ⟨i, rfl⟩))
    · simpa [sub_eq_zero] using h _ (Or.inr (Or.inr rfl))
  · rintro ⟨h1, h2, h3⟩ g (⟨g, hg, rfl⟩ | ⟨i, rfl⟩ | rfl)
    · rw [aeval_rename]
      exact h1 g hg
    · simpa using h2 i
    · simpa [sub_eq_zero] using h3

/- English proof (translation)
Take `⟨j, hj⟩` from `Function.ne_iff.1 hy`. Use `⟨Pi.single j (y j)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[Pi.single_eq_same]`. Conclude with `inv_mul_cancel₀ hj`.

Introduce `k _ hk`. Rewrite using `[Pi.single_eq_of_ne hk, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem exists_dual {Ω : Type} [Field Ω] {N : ℕ} {y : Fin N → Ω} (hy : y ≠ 0) :
    ∃ z : Fin N → Ω, ∑ j, z j * y j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  refine ⟨Pi.single j (y j)⁻¹, ?_⟩
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
    exact inv_mul_cancel₀ hj
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `at h`.
-/
theorem ne_zero_of_dual {Ω : Type} [Field Ω] {N : ℕ} {y z : Fin N → Ω} (h : ∑ j, z j * y j = 1) :
    y ≠ 0 := by
  rintro rfl
  simp at h

variable {F : Type} [Field F] {D N d : ℕ} {I : Ideal (MvPolynomial (Fin N) F)}
  {f : MvPolynomial (Fin (D + 1) × Fin N) F}

/- English proof (translation)
Take `⟨z, hz⟩` from `exists_dual hy`. Establish `key` using `GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure F _ (incIdeal (D + 1) I) (rename Sum.inl f) (fun x hx => by`. Take `⟨h1, h2, h3⟩` from `(forall_incIdeal_iff I x).1 hx`. Rewrite using `[aeval_rename]`. Conclude with `(hf.zero_iff _).2 ⟨_, ne_zero_of_dual h3, h1, h2⟩) Ω (Sum.elim u (Sum.elim y z))`.

Use the proof step `((forall_incIdeal_iff I _).2 ⟨hI, hu, hz⟩)`. Rewrite `key` using `[aeval_rename]`. Then use the resulting hypothesis.
-/
theorem aeval_eq_zero_of_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω]
    (u : Fin (D + 1) × Fin N → Ω) (y : Fin N → Ω) (hy : y ≠ 0) (hI : ∀ g ∈ I, aeval y g = 0)
    (hu : ∀ i, ∑ j, u (i, j) * y j = 0) : aeval u f = 0 := by
  obtain ⟨z, hz⟩ := exists_dual hy
  have key := GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure F _ (incIdeal (D + 1) I) (rename Sum.inl f) (fun x hx => by
    obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I x).1 hx
    rw [aeval_rename]
    exact (hf.zero_iff _).2 ⟨_, ne_zero_of_dual h3, h1, h2⟩) Ω (Sum.elim u (Sum.elim y z))
    ((forall_incIdeal_iff I _).2 ⟨hI, hu, hz⟩)
  rwa [aeval_rename] at key

/- English proof (translation)
Take `⟨w, hw⟩` from `GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields F _ _ (Ideal.span {f}) (incIdeal (D + 1) I) (fun v hv => by`. Take `⟨y, hy, h1, h2⟩` from `(hf.zero_iff v).1 (hv f (Ideal.subset_span rfl))`. Take `⟨z, hz⟩` from `exists_dual hy`. Conclude with `⟨Sum.elim y z, (forall_incIdeal_iff I _).2 ⟨h1, h2, hz⟩⟩) Ω u`. Use the proof step `((forall_span_iff _ _).2 (by rintro g rfl; exact hu))`.

Take `⟨h1, h2, h3⟩` from `(forall_incIdeal_iff I _).1 hw`. Conclude with `⟨_, ne_zero_of_dual h3, h1, h2⟩`.
-/
theorem exists_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (u : Fin (D + 1) × Fin N → Ω) (hu : aeval u f = 0) :
    ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧ ∀ i, ∑ j, u (i, j) * y j = 0 := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields F _ _ (Ideal.span {f}) (incIdeal (D + 1) I) (fun v hv => by
    obtain ⟨y, hy, h1, h2⟩ := (hf.zero_iff v).1 (hv f (Ideal.subset_span rfl))
    obtain ⟨z, hz⟩ := exists_dual hy
    exact ⟨Sum.elim y z, (forall_incIdeal_iff I _).2 ⟨h1, h2, hz⟩⟩) Ω u
    ((forall_span_iff _ _).2 (by rintro g rfl; exact hu))
  obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I _).1 hw
  exact ⟨_, ne_zero_of_dual h3, h1, h2⟩

/- English proof (translation)
Rewrite using `[Fin.forall_fin_succ']`. Simplify using `[join]`.
-/
theorem forall_join_iff {Ω : Type} [Field Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω) :
    (∀ i, ∑ j, join s ξ (i, j) * y j = 0) ↔ (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0 := by
  rw [Fin.forall_fin_succ']
  simp [join]

/- English proof (translation)
Introduce `F _ _ D N d I f hf`. Use `⟨fun Ω _ _ s ξ y hy hI hs hξ => ?_, fun Ω _ _ _ s ξ h => ?_⟩` and prove the remaining obligations. Conclude with `aeval_eq_zero_of_common_zero hf _ y hy hI ((forall_join_iff s ξ y).2 ⟨hs, hξ⟩)`. Take `⟨y, hy, h1, h2⟩` from `exists_common_zero hf _ h`. Conclude with `⟨y, hy, h1, (forall_join_iff s ξ y).1 h2⟩`.
-/
theorem zero_set_ext : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F))
    (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f →
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω), y ≠ 0 →
      (∀ g ∈ I, aeval y g = 0) → (∀ i, ∑ j, s i j * y j = 0) → ∑ j, ξ j * y j = 0 →
      aeval (join s ξ) f = 0) ∧
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (s : Fin D → Fin N → Ω) (ξ : Fin N → Ω),
      aeval (join s ξ) f = 0 → ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧
        (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0) := by
  intro F _ _ D N d I f hf
  refine ⟨fun Ω _ _ s ξ y hy hI hs hξ => ?_, fun Ω _ _ _ s ξ h => ?_⟩
  · exact aeval_eq_zero_of_common_zero hf _ y hy hI ((forall_join_iff s ξ y).2 ⟨hs, hξ⟩)
  · obtain ⟨y, hy, h1, h2⟩ := exists_common_zero hf _ h
    exact ⟨y, hy, h1, (forall_join_iff s ξ y).1 h2⟩

end GlobalTheory.ChowZeroExt
