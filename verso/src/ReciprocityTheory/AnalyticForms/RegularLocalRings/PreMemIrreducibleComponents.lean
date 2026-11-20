import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

section Top

variable {α : Type*} [TopologicalSpace α]

def compsH (T : Set α) : Set (Set α) :=
  {C | Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C}

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.
-/
theorem compsH_pre_isPreirreducible {T C : Set α} (hCT : C ⊆ T) (hC : IsPreirreducible C) :
    IsPreirreducible ((Subtype.val ⁻¹' C : Set T)) := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hC ⊢
  intro z₁ z₂ h₁ h₂ hsub
  obtain ⟨Z₁, hZ₁, rfl⟩ := isClosed_induced_iff.mp h₁
  obtain ⟨Z₂, hZ₂, rfl⟩ := isClosed_induced_iff.mp h₂
  have hC' : C ⊆ Z₁ ∪ Z₂ := fun c hc => hsub (show (⟨c, hCT hc⟩ : T) ∈ Subtype.val ⁻¹' C from hc)
  rcases hC Z₁ Z₂ hZ₁ hZ₂ hC' with h | h
  · exact Or.inl (fun x hx => h hx)
  · exact Or.inr (fun x hx => h hx)

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem compsH_pre_isIrreducible {T C : Set α} (hCT : C ⊆ T) (hC : IsIrreducible C) :
    IsIrreducible ((Subtype.val ⁻¹' C : Set T)) := by
  obtain ⟨c, hc⟩ := hC.nonempty
  exact ⟨⟨⟨c, hCT hc⟩, hc⟩, compsH_pre_isPreirreducible hCT hC.isPreirreducible⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components.
-/
theorem image_mem_compsH {T : Set α} {A : Set T} (hA : A ∈ irreducibleComponents T) :
    Subtype.val '' A ∈ compsH T := by
  refine ⟨⟨hA.1.image _ continuous_subtype_val.continuousOn, by rintro _ ⟨x, _, rfl⟩; exact x.2⟩, ?_⟩
  intro C' hC' hle
  have h1 : A ⊆ Subtype.val ⁻¹' C' := fun x hx => hle ⟨x, hx, rfl⟩
  have h2 := hA.2 (compsH_pre_isIrreducible hC'.2 hC'.1) h1
  intro c hc
  exact ⟨⟨c, hC'.2 hc⟩, h2 hc, rfl⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem pre_mem_irreducibleComponents {T C : Set α} (hC : C ∈ compsH T) :
    (Subtype.val ⁻¹' C : Set T) ∈ irreducibleComponents T := by
  refine ⟨compsH_pre_isIrreducible hC.1.2 hC.1.1, ?_⟩
  intro B hB hle
  have h1 : C ⊆ Subtype.val '' B := fun c hc => ⟨⟨c, hC.1.2 hc⟩, hle hc, rfl⟩
  have h2 := hC.2 ⟨hB.image _ continuous_subtype_val.continuousOn, by rintro _ ⟨x, _, rfl⟩; exact x.2⟩ h1
  intro x hx
  exact h2 ⟨x, hx, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem compsH_finite [NoetherianSpace α] (T : Set α) : (compsH T).Finite := by
  have hfin : (irreducibleComponents T).Finite := NoetherianSpace.finite_irreducibleComponents
  refine (hfin.image (Set.image Subtype.val)).subset fun C hC =>
    ⟨Subtype.val ⁻¹' C, pre_mem_irreducibleComponents hC, ?_⟩
  exact Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hC.1.2)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isClosed_of_mem_compsH {T : Set α} (hT : IsClosed T) {C : Set α} (hC : C ∈ compsH T) :
    IsClosed C := by
  have h2 : closure C ⊆ C := hC.2 ⟨hC.1.1.closure, closure_minimal hC.1.2 hT⟩ subset_closure
  exact closure_subset_iff_isClosed.mp h2

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem sUnion_compsH (T : Set α) : ⋃₀ compsH T = T := by
  apply Set.Subset.antisymm
  · rintro x ⟨C, hC, hx⟩
    exact hC.1.2 hx
  · intro x hx
    exact ⟨Subtype.val '' irreducibleComponent (⟨x, hx⟩ : T),
      image_mem_compsH (irreducibleComponent_mem_irreducibleComponents _),
      ⟨⟨x, hx⟩, mem_irreducibleComponent, rfl⟩⟩

end Top

section Alg

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] {p : Ideal A} [p.IsPrime]
  [IsLocalization.AtPrime S p] [IsRegularLocalRing S] {n : ℕ} {f : Fin n → A}

def parPrime (f : Fin n → A) (i : Fin n) : Ideal A :=
  (Ideal.span {algebraMap A S (f i)}).comap (algebraMap A S)

variable (S) in
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem parPrime_spec (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) (i : Fin n) :
    (parPrime (S := S) f i).IsPrime ∧ parPrime (S := S) f i ≤ p ∧ f i ∈ parPrime (S := S) f i := by
  have hp := prime_of_regular_params _ hrsp.1 hrsp.2 i
  have hP : (Ideal.span {algebraMap A S (f i)}).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  refine ⟨Ideal.comap_isPrime _ _, ?_, Ideal.mem_comap.mpr (Ideal.subset_span rfl)⟩
  intro a ha
  have hle : Ideal.span {algebraMap A S (f i)} ≤ maximalIdeal S := by
    rw [Ideal.span_le, Set.singleton_subset_iff, ← hrsp.1]
    exact Ideal.subset_span ⟨i, rfl⟩
  have := hle (Ideal.mem_comap.mp ha)
  have h2 : (maximalIdeal S).comap (algebraMap A S) = p :=
    IsLocalization.AtPrime.under_maximalIdeal S p
  rw [← Ideal.mem_comap, h2] at this
  exact this

variable (S) in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_iff_parPrime_le (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) (i : Fin n)
    {Q : Ideal A} [Q.IsPrime] (hQ : Q ≤ p) : f i ∈ Q ↔ parPrime (S := S) f i ≤ Q := by
  refine ⟨fun h => ?_, fun h => h (parPrime_spec (p := p) S hrsp i).2.2⟩
  have hdisj : Disjoint (p.primeCompl : Set A) Q := by
    rw [Set.disjoint_left]
    intro a ha haQ
    exact ha (hQ haQ)
  have hQ' := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S ‹Q.IsPrime› hdisj
  intro a ha
  rw [← hQ']
  show algebraMap A S a ∈ Q.map (algebraMap A S)
  have h1 : Ideal.span {algebraMap A S (f i)} ≤ Q.map (algebraMap A S) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ h
  exact h1 (Ideal.mem_comap.mp ha)

variable (S) in
/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem eq_of_mem_parPrime (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) {i j : Fin n}
    (h : f j ∈ parPrime (S := S) f i) : j = i := by
  by_contra hji
  have : IsDomain S := isDomain_of_isRegularLocalRing
  have hpi := prime_of_regular_params _ hrsp.1 hrsp.2 i
  have hpj := prime_of_regular_params _ hrsp.1 hrsp.2 j
  have hd : algebraMap A S (f i) ∣ algebraMap A S (f j) :=
    Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp h)
  have hass : Associated (algebraMap A S (f i)) (algebraMap A S (f j)) :=
    hpi.associated_of_dvd hpj hd
  exact (regular_params_spec _ hrsp.1 hrsp.2).2 i j (Ne.symm hji) hass

end Alg

noncomputable section

section Pts

variable {W : Scheme.{0}} {U : W.Opens}

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem specializes_iff_pOf (hU : IsAffineOpen U) {z z' : W} (hz : z ∈ U) (hz' : z' ∈ U) :
    z ⤳ z' ↔ hU.primeIdealOf ⟨z, hz⟩ ≤ hU.primeIdealOf ⟨z', hz'⟩ := by
  have := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff
    (x := hU.primeIdealOf ⟨z, hz⟩) (y := hU.primeIdealOf ⟨z', hz'⟩)
  rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
  rw [PrimeSpectrum.le_iff_specializes]
  exact this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_of_pOf_eq (hU : IsAffineOpen U) {z z' : W} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩) : z = z' := by
  have h1 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  have h2 := hU.fromSpec_primeIdealOf ⟨z', hz'⟩
  rw [h] at h1
  exact h1.symm.trans h2

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem fromSpec_mem (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(W, U)) : hU.fromSpec P ∈ U := by
  have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
  rwa [hU.range_fromSpec] at this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pOf_fromSpec (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(W, U)) :
    hU.primeIdealOf ⟨hU.fromSpec P, fromSpec_mem hU P⟩ = P :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

end Pts

end

end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
