import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AddIff
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EvalExact

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
private theorem sum_sec_eq_zero (Pa : Parts C) (F : Coef C) (hF : Pa.Add F) {Q P : C ⥤ Type}
    {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) (h : Pa.LocZero a u)
    (c : ∀ A : C, P.obj A → F.obj A) (hc : c ∈ Sec P F) (A : C) (y : Q.obj A) :
    ∑ i, a i • c A ((u i).app A y) = 0 := by
  have hc' : ∀ {A B : C} (φ : A ⟶ B) (y : P.obj A), (F.map φ).hom (c A y) = c B (P.map φ y) := hc
  obtain ⟨S, hS, hs⟩ := h A y
  apply (hF A S hS).1
  funext s
  show (F.map (S.f s)).hom (∑ i, a i • c A ((u i).app A y)) = (F.map (S.f s)).hom 0
  have hnat : ∀ i, (F.map (S.f s)).hom (a i • c A ((u i).app A y)) =
      a i • c (S.B s) ((u i).app _ (Q.map (S.f s) y)) := by
    intro i
    rw [map_zsmul, hc' (S.f s) _, FunctorToTypes.naturality]
  rw [map_zero, map_sum]
  simp only [hnat]
  rcases hs s with h0 | h0
  · have hL := congrArg
      (Finsupp.liftAddHom fun p : P.obj (S.B s) => zmultiplesHom (F.obj (S.B s)) (c (S.B s) p)) h0
    simpa [map_sum] using hL
  · apply (hF _ _ h0).1
    funext e
    exact e.elim

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Introduce a local definition for the expression.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem locSum_zero (Pa : Parts C) (T : Theory C) (F : Coef C) (hF : Pa.Add F)
    {Q P : C ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) (h : Pa.LocZero a u)
    (x : T.H P F 0) : ∑ i, a i • T.pull (u i) F 0 x = 0 := by
  apply (T.zero Q F).injective
  rw [map_zero]
  apply Subtype.ext
  funext A y
  let E : T.H Q F 0 →+ F.obj A := AddMonoidHom.mk' (fun z => (T.zero Q F z).1 A y) (by
    intro z w
    simp [map_add])
  show E (∑ i, a i • T.pull (u i) F 0 x) = 0
  rw [map_sum]
  have hE : ∀ i, E (a i • T.pull (u i) F 0 x) = a i • (T.zero P F x).1 A ((u i).app A y) := by
    intro i
    rw [map_zsmul]
    congr 1
    exact T.zero_pull (u i) F x A y
  simp only [hE]
  exact sum_sec_eq_zero Pa F hF a u h _ (T.zero P F x).2 A y

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
private theorem locSum_shift (T : Theory C) {Q P : C ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ)
    (u : I → (Q ⟶ P)) (S : ShortComplex (Coef C)) (hS : S.ShortExact) (j : ℕ)
    (hsub : Subsingleton (T.H P S.X₂ (j + 1)))
    (ih : ∀ w : T.H P S.X₃ j, ∑ i, a i • T.pull (u i) S.X₃ j w = 0)
    (x : T.H P S.X₁ (j + 1)) : ∑ i, a i • T.pull (u i) S.X₁ (j + 1) x = 0 := by
  obtain ⟨w, rfl⟩ := (T.ex₁ P S hS j x).1 (hsub.elim _ _)
  have hδ : ∑ i, a i • T.δ Q S hS j (T.pull (u i) S.X₃ j w) =
      T.δ Q S hS j (∑ i, a i • T.pull (u i) S.X₃ j w) := by
    rw [map_sum]
    simp only [map_zsmul]
  simp only [T.pull_δ]
  rw [hδ, ih w, map_zero]

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.Ru.crystallineComparison.locSum :
    UpperTheory.Ru.crystallineComparison.LocSum := by
  intro C _ Pa T F hF Q P I _ a u h j x
  induction j generalizing F with
  | zero => exact locSum_zero Pa T F hF a u h x
  | succ j ih =>
    obtain ⟨K, ι, hm, hK, hKa⟩ := emb C Pa F hF
    let S : ShortComplex (Coef C) := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel ι, mono_f := hm, epi_g := inferInstanceAs (Epi (cokernel.π ι)) }
    have h3 : Pa.Add S.X₃ := quotAdd C Pa S hS hF hKa
    exact locSum_shift T a u S hS j (T.inj P K hK j) (fun w => ih S.X₃ h3 w) x
