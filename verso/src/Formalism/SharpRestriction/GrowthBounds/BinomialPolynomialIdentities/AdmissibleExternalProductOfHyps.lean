import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsIsotypicDecomposition

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem externalProduct_index_finite (H : ExternalProductHyps) {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    Finite (PIdx r K LL B) := by
  have := standardPath_index_finite N (r + K) LL B
  refine LinearIndependent.finite_of_le_span_finite _ (H.p16 ℚ N r K LL B).1 (Set.range (wd LL B ℚ)) ?_
  rw [span_words_eq_polynomials, ← (H.p16 ℚ N r K LL B).2]
  exact Submodule.subset_span

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem span_inf_iSup_externalProduct (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) (F : Type) [Field F] [CharZero F] {N : ℕ} (r K : ℕ)
    (LL : Letters (Fin N)) (B : Fin N → ℕ) (pi' : Fin (N + 1) → Set (Fin r → ℤ))
    (pi'' : Fin (N + 1) → Set (Fin K → ℤ)) (h' : ∀ i, DomLowerSet (pi' i)) (h'' : ∀ i, DomLowerSet (pi'' i)) :
    Submodule.span F (Set.range (pvec F r K LL B)) ⊓
        (⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) | ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i},
          jointType F LL q.1 q.2) =
      Submodule.span F (pvec F r K LL B '' {x | ∀ i, x.1.1.1 i ∈ pi' i ∧ x.1.2.1 i ∈ pi'' i}) := by
  have := externalProduct_index_finite H r K LL B
  let pi : ∀ s, Set (GLWeightLabels N r K s) := fun s => match s with
    | .inl i => pi' i
    | .inr i => pi'' i
  have key := H.sum F _ (Fin (N + 1) ⊕ Fin (N + 1)) (GLWeightLabels N r K) (PIdx r K LL B) (externalProductJointData D H r K LL B) pi
    (fun s => match s with
      | .inl i => (h' i).1
      | .inr i => (h'' i).1)
    (fun s => match s with
      | .inl i => (h' i).2
      | .inr i => (h'' i).2)
  have hsup : (⨆ q ∈ {q : ∀ s, GLWeightLabels N r K s | ∀ s, q s ∈ pi s}, ⨅ s, (externalProductJointData (F := F) D H r K LL B).W s (q s)) =
      ⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) | ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i},
          jointType F LL q.1 q.2 := by
    apply le_antisymm
    · refine iSup₂_le fun q hq => ?_
      refine le_iSup₂_of_le (f := fun (q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ))
          (_ : q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
            ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i}) => jointType F LL q.1 q.2)
        (fun i => q (.inl i), fun i => q (.inr i)) (fun i => ⟨hq (.inl i), hq (.inr i)⟩) ?_
      exact le_iInf fun i => le_inf (iInf_le (fun s => (externalProductJointData (F := F) D H r K LL B).W s (q s)) (Sum.inl i))
        (iInf_le (fun s => (externalProductJointData (F := F) D H r K LL B).W s (q s)) (Sum.inr i))
    · refine iSup₂_le fun q hq => ?_
      refine le_iSup₂_of_le (f := fun (q : ∀ s, GLWeightLabels N r K s) (_ : q ∈ {q : ∀ s, GLWeightLabels N r K s | ∀ s, q s ∈ pi s}) =>
          ⨅ s, (externalProductJointData (F := F) D H r K LL B).W s (q s))
        (fun s => match s with
          | .inl i => q.1 i
          | .inr i => q.2 i)
        (fun s => match s with
          | .inl i => (hq i).1
          | .inr i => (hq i).2) ?_
      exact le_iInf fun s => match s with
        | .inl i => (iInf_le _ i).trans inf_le_left
        | .inr i => (iInf_le _ i).trans inf_le_right
  have hset : {x | ∀ s, (externalProductJointData (F := F) D H r K LL B).P x s ∈ pi s} =
      {x : PIdx r K LL B | ∀ i, x.1.1.1 i ∈ pi' i ∧ x.1.2.1 i ∈ pi'' i} := by
    ext x
    constructor
    · intro h i
      exact ⟨h (.inl i), h (.inr i)⟩
    · intro h s
      match s with
      | .inl i => exact (h i).1
      | .inr i => exact (h i).2
  rw [(H.p16 F N r K LL B).2, ← hsup, ← hset]
  exact key

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem map_externalProduct_vector {O Kf : Type} [CommRing O] [CommRing Kf] (φ : O →+* Kf) {N : ℕ} (r K : ℕ) (LL : Letters (Fin N))
    (B : Fin N → ℕ) (x : PIdx r K LL B) : MvPolynomial.map φ (pvec O r K LL B x) = pvec Kf r K LL B x := by
  unfold pvec PsiPl PsiTan
  rw [map_mul, MvPolynomial.map_rename, MvPolynomial.map_rename, map_Psi', map_Psi']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem admissible_externalProduct_of_hyps (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) : PairedPathIndependence D := by
  intro O _ _ _ _ N r K _ _ LL B
  have hP := H.p16 O N r K LL B
  refine ⟨⟨hP.1, ?_⟩, ?_⟩
  · rw [← hP.2]
    congr 1
    ext G
    constructor
    · rintro ⟨nu, ka, I', I'', h1, h2, h3, rfl⟩
      exact ⟨⟨((nu, I'), (ka, I'')), h1, h2, h3⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1.1.1, x.1.2.1, x.1.1.2, x.1.2.2, x.2.1, x.2.2.1, x.2.2.2, rfl⟩
  · intro pi' pi'' h' h''
    have hint := span_inter_eq_span_image (IsFractionRing.injective O (KK O)) (pvec O r K LL B) (pvec (KK O) r K LL B)
      (map_externalProduct_vector (algebraMap O (KK O)) r K LL B) (H.p16 (KK O) N r K LL B).1 _ _
      (span_inf_iSup_externalProduct D H (KK O) r K LL B pi' pi'' h' h'')
    rw [hP.2] at hint
    rw [hint]
    congr 2
    ext G
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1.1.1, x.1.2.1, x.1.1.2, x.1.2.2, x.2.1, hx, x.2.2.1, x.2.2.2, rfl⟩
    · rintro ⟨nu, ka, I', I'', h1, hx, h2, h3, rfl⟩
      exact ⟨⟨((nu, I'), (ka, I'')), h1, h2, h3⟩, hx, rfl⟩

end Formalism.MainNotions.G.ColumnFamilies
