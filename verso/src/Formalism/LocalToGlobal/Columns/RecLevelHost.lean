import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP)

section CM

variable {X : Fields}

def fixedIntermediateField (hX : X.Ok) : IntermediateField X.F X.E where
  carrier := {x | star x = x}
  mul_mem' := by
    intro a b ha hb
    show star (a * b) = a * b
    rw [star_mul', ha, hb]
  add_mem' := by
    intro a b ha hb
    show star (a + b) = a + b
    rw [star_add, ha, hb]
  algebraMap_mem' := hX.star_F
  inv_mem' := by
    intro a ha
    show star a⁻¹ = a⁻¹
    rw [star_inv₀, ha]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. It suffices to derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem rlh_fixed (hX : X.Ok) (a : X.E) : star a = a ↔ a ∈ (algebraMap X.F X.E).range := by
  constructor
  · intro ha
    have hp : (Module.finrank X.F X.E).Prime := by rw [hX.rankE]; exact Nat.prime_two
    have := IntermediateField.isSimpleOrder_of_finrank_prime X.F X.E hp
    rcases eq_bot_or_eq_top (fixedIntermediateField hX) with h | h
    · have h1 : a ∈ fixedIntermediateField hX := ha
      rw [h, IntermediateField.mem_bot] at h1
      exact h1
    · exfalso
      have hall : ∀ x : X.E, star x = x := fun x => by
        have : x ∈ fixedIntermediateField hX := by rw [h]; exact IntermediateField.mem_top
        exact this
      obtain ⟨φ⟩ : Nonempty (X.E →+* ℂ) := inferInstance
      have hreal : NumberField.ComplexEmbedding.IsReal φ := by
        rw [NumberField.ComplexEmbedding.isReal_iff]
        ext x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, hall]
      have hc := hX.cplxE.isComplex (NumberField.InfinitePlace.mk φ)
      rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
      exact hc hreal
  · rintro ⟨x, rfl⟩
    exact hX.star_F x

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmData_of_totallyRealFieldsConditions (hX : X.AbelianUnramifiedExtensionConditions) : Formalism.BasicNotions.CMData X.F X.E where
  cmUnram := cm_unramified_of_field_conditions hX
  totReal := hX.ok.realF
  deg2 := hX.ok.rankE
  fixed := rlh_fixed hX.ok

end CM

section Split

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem rlh_conjPl_eq {PP PP' : Pl E} (h : Formalism.L2.DIV.IsConjPl PP PP') : PP' = conjPrime₂ PP := by
  apply HeightOneSpectrum.ext
  ext x
  show x ∈ PP'.asIdeal ↔ cO E x ∈ PP.asIdeal
  exact (h (cO E x) x (by rw [show ((cO E x : 𝓞 E) : E) = star (x : E) from rfl, star_star])).symm

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rlh_conjP_conjP (P : Pl E) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  show cO E (cO E x) ∈ P.asIdeal ↔ x ∈ P.asIdeal
  rw [cO_cO]

end Split

section Primes

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem rlh_vGs_cases (w : Pl X.E) (hw : w ∈ Pr.vGs) : ∃ i, X.conjO (Pr.piG i) ∈ w.asIdeal := by
  classical
  unfold Primes.vGs at hw
  rcases Finset.mem_union.mp hw with h | h
  · exact ⟨0, decoFin_mem_of_mem_divs h⟩
  · exact ⟨1, decoFin_mem_of_mem_divs h⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem rlh_vGs_not_conj (hPr : Pr.Ok) {w w' : Pl X.E} (hw : w ∈ Pr.vGs) (hw' : w' ∈ Pr.vGs) : w' ≠ conjPrime₂ w := by
  intro h
  obtain ⟨i, hi⟩ := rlh_vGs_cases w hw
  obtain ⟨j, hj⟩ := rlh_vGs_cases w' hw'
  have hi' : Pr.piG i ∈ w'.asIdeal := by
    rw [h, mem_conjP]; exact hi
  by_cases hij : i = j
  · subst hij
    obtain ⟨a, b, e⟩ := hPr.piG_cop i
    apply one_notMem w'
    rw [← e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hi') (Ideal.mul_mem_left _ _ hj)
  · have h1 : (Pr.g i : 𝓞 X.E) ∈ w'.asIdeal := by rw [← hPr.piG_norm i]; exact Ideal.mul_mem_right _ _ hi'
    have h2 : (Pr.g j : 𝓞 X.E) ∈ w'.asIdeal := by rw [← hPr.piG_norm j]; exact Ideal.mul_mem_left _ _ hj
    have hne : Pr.g i ≠ Pr.g j := by
      intro he
      apply hij
      have h01 := hPr.g_ne
      fin_cases i <;> fin_cases j <;> simp_all
    have hcop : Nat.Coprime (Pr.g i) (Pr.g j) := (Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne
    have hZ : IsCoprime ((Pr.g i : ℤ)) ((Pr.g j : ℤ)) := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨a, b, e⟩ := hZ.map (Int.castRingHom (𝓞 X.E))
    apply one_notMem w'
    rw [← e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · simpa using h1
    · simpa using h2

open Classical in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isSplitSet_of_ok (hPr : Pr.Ok) (u : Pr.Word) : Formalism.L2.DIV.IsSplitSet (Pr.vT u ∪ Pr.vGs) := by
  intro PP hP PP' hP' hc
  have e := rlh_conjPl_eq hc
  rcases Finset.mem_union.mp hP with h | h <;> rcases Finset.mem_union.mp hP' with h' | h'
  · exact (moveHyp_of_ok hPr u ⟨PP, h⟩).st ⟨PP', h'⟩ e
  · exact ((moveHyp_of_ok hPr u ⟨PP, h⟩).sg ⟨PP', h'⟩).2 e
  · refine ((moveHyp_of_ok hPr u ⟨PP', h'⟩).sg ⟨PP, h⟩).2 ?_
    show PP = conjPrime₂ PP'
    rw [e, rlh_conjP_conjP]
  · exact rlh_vGs_not_conj hPr h h' e

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem disjoint_of_ok (hPr : Pr.Ok) (u : Pr.Word) : Disjoint (Pr.vT u) Pr.vGs := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  exact ((moveHyp_of_ok hPr u ⟨P, hP⟩).sg ⟨P, hP'⟩).1 rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem colDecoPtSurj (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) (u : Pr.Word) (n : ℕ) [NeZero n] (hG : UnimodGenus hc n) :
    DecoPtSurj hc n (Pr.vT u) Pr.vGs :=
  decoPtSurj_of hc n (Pr.vT u) Pr.vGs hG Formalism.L2.DIV.reduction_surjective_bis (isSplitSet_of_ok hPr u) (disjoint_of_ok hPr u)

end Primes

end Formalism.L2.Col
