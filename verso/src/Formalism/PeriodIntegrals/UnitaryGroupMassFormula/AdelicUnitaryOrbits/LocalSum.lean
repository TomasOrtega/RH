import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice

noncomputable section

namespace PIW.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped RestrictedProduct

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem uc_coeffs {A : Type} [CommRing A] {k : ℕ} {f : Fin k → A}
    (hf : Ideal.span (Set.range f) = ⊤) : ∃ a : Fin k → A, ∑ i, a i * f i = 1 := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range f) := by
    rw [hf]
    exact Submodule.mem_top
  exact Ideal.mem_span_range_iff_exists_fun.mp h1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uc_span {A : Type} [CommRing A] {k : ℕ} (f a : Fin k → A) (h : ∑ i, a i * f i = 1) :
    Ideal.span (Set.range f) = ⊤ := by
  exact (Ideal.eq_top_iff_one _).mpr (Ideal.mem_span_range_iff_exists_fun.mpr ⟨a, h⟩)

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem uc_prod {A B : Type} [CommRing A] [CommRing B] (hA : UnitChoice A) (hB : UnitChoice B) :
    UnitChoice (A × B) := by
  unfold UnitChoice at hA hB ⊢
  intro k f hf
  obtain ⟨a, ha⟩ := uc_coeffs hf
  have hA1 : Ideal.span (Set.range fun i => (f i).1) = ⊤ :=
    uc_span (fun i => (f i).1) (fun i => (a i).1) (by
      have h := congrArg Prod.fst ha
      simpa [Prod.fst_sum] using h)
  have hB1 : Ideal.span (Set.range fun i => (f i).2) = ⊤ :=
    uc_span (fun i => (f i).2) (fun i => (a i).2) (by
      have h := congrArg Prod.snd ha
      simpa [Prod.snd_sum] using h)
  obtain ⟨eA, hA1', hA2, hA3, hA4⟩ := hA k _ hA1
  obtain ⟨eB, hB1', hB2, hB3, hB4⟩ := hB k _ hB1
  refine ⟨fun i => (eA i, eB i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact Prod.ext (hA1' i) (hB1' i)
  · intro i j hij
    exact Prod.ext (hA2 i j hij) (hB2 i j hij)
  · exact Prod.ext (by simpa [Prod.fst_sum] using hA3) (by simpa [Prod.snd_sum] using hB3)
  · rw [Prod.isUnit_iff]
    constructor
    · simpa [Prod.fst_sum] using hA4
    · simpa [Prod.snd_sum] using hB4

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem uc_pi {ι : Type} (K : ι → Type) [∀ v, Field (K v)] : UnitChoice (∀ v, K v) := by
  intro k f hf
  obtain ⟨a, ha⟩ := uc_coeffs hf
  have hex : ∀ v, ∃ i, f i v ≠ 0 := by
    intro v
    by_contra hne
    push_neg at hne
    have h := congrFun ha v
    simp [Finset.sum_apply, hne] at h
  choose c hc using hex
  classical
  refine ⟨fun i v => if c v = i then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro i
    funext v
    simp only [Pi.mul_apply]
    split_ifs <;> simp
  · intro i j hij
    funext v
    simp only [Pi.mul_apply, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all
  · funext v
    simp [Finset.sum_apply]
  · rw [Pi.isUnit_iff]
    intro v
    apply isUnit_iff_ne_zero.mpr
    rw [Finset.sum_apply, Finset.sum_eq_single (c v)]
    · simpa using hc v
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem local_sum {A : Type} [CommRing A] [IsLocalRing A] {k : ℕ} (a f : Fin k → A)
    (h : ∑ i, a i * f i = 1) : ∃ i, IsUnit (f i) := by
  by_contra hne
  push_neg at hne
  have hmem : ∀ i, a i * f i ∈ IsLocalRing.maximalIdeal A := fun i =>
    Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (hne i))
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← h]
    exact Ideal.sum_mem _ fun i _ => hmem i
  exact (IsLocalRing.mem_maximalIdeal _).mp h1 isUnit_one

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem uc_rp {ι : Type} (K : ι → Type) [∀ v, Field (K v)] {S : ι → Type} [∀ v, SetLike (S v) (K v)]
    [∀ v, SubringClass (S v) (K v)] (B : ∀ v, S v) (𝓕 : Filter ι)
    (hloc : ∀ v (k : ℕ) (a f : Fin k → B v), ∑ i, a i * f i = 1 → ∃ i, IsUnit (f i)) :
    UnitChoice (Πʳ v, [K v, B v]_[𝓕]) := by
  intro k f hf
  obtain ⟨a, ha⟩ := uc_coeffs hf
  have hev : ∀ (x : Fin k → Πʳ v, [K v, B v]_[𝓕]) (v : ι), (∑ i, x i) v = ∑ i, x i v :=
    fun x v => map_sum (RestrictedProduct.evalRingHom K v) x Finset.univ
  have hcomp : ∀ v, ∑ i, a i v * f i v = 1 := by
    intro v
    have h := congrArg (fun x : Πʳ v, [K v, B v]_[𝓕] => x v) ha
    simp only [hev, RestrictedProduct.mul_apply] at h
    exact h
  have hex : ∀ v, ∃ i, f i v ≠ 0 ∧ ((∀ j, a j v ∈ B v ∧ f j v ∈ B v) → (f i v)⁻¹ ∈ B v) := by
    intro v
    by_cases hg : ∀ j, a j v ∈ B v ∧ f j v ∈ B v
    · have hsum : ∑ j, (⟨a j v, (hg j).1⟩ : B v) * ⟨f j v, (hg j).2⟩ = 1 := by
        apply Subtype.ext
        have h1 := map_sum (SubringClass.subtype (B v))
          (fun j => (⟨a j v, (hg j).1⟩ : B v) * ⟨f j v, (hg j).2⟩) Finset.univ
        simp only [map_mul] at h1
        exact h1.trans (hcomp v)
      obtain ⟨i, hi⟩ := hloc v k (fun j => ⟨a j v, (hg j).1⟩) (fun j => ⟨f j v, (hg j).2⟩) hsum
      obtain ⟨b, hb⟩ := hi.exists_right_inv
      have hb' : f i v * (b : K v) = 1 := congrArg Subtype.val hb
      refine ⟨i, ?_, fun _ => ?_⟩
      · intro h0
        rw [h0, zero_mul] at hb'
        exact zero_ne_one hb'
      · rw [inv_eq_of_mul_eq_one_right hb']
        exact b.2
    · obtain ⟨i, hi⟩ : ∃ i, f i v ≠ 0 := by
        by_contra hne
        push_neg at hne
        have h := hcomp v
        simp [hne] at h
      exact ⟨i, hi, fun h => absurd h hg⟩
  choose c hc using hex
  classical
  let e : Fin k → Πʳ v, [K v, B v]_[𝓕] := fun i =>
    RestrictedProduct.mk (fun v => if c v = i then (1 : K v) else 0)
      (Filter.Eventually.of_forall fun v => by
        show (if c v = i then (1 : K v) else 0) ∈ B v
        split_ifs
        exacts [one_mem (B v), zero_mem (B v)])
  have he : ∀ i v, e i v = if c v = i then (1 : K v) else 0 := fun i v => rfl
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i
    apply RestrictedProduct.ext
    intro v
    rw [RestrictedProduct.mul_apply, he]
    split_ifs <;> simp
  · intro i j hij
    apply RestrictedProduct.ext
    intro v
    rw [RestrictedProduct.mul_apply, he, he,
      show ((0 : Πʳ v, [K v, B v]_[𝓕]) v) = 0 from rfl]
    split_ifs with h1 h2 <;> simp_all
  · apply RestrictedProduct.ext
    intro v
    rw [hev, show ((1 : Πʳ v, [K v, B v]_[𝓕]) v) = 1 from rfl]
    simp [he]
  · have hgood : ∀ᶠ v in 𝓕, ∀ j, a j v ∈ B v ∧ f j v ∈ B v := by
      rw [Filter.eventually_all]
      intro j
      exact (a j).2.and (f j).2
    let z : Πʳ v, [K v, B v]_[𝓕] := RestrictedProduct.mk (fun v => (f (c v) v)⁻¹)
      (hgood.mono fun v hv => (hc v).2 hv)
    refine isUnit_iff_exists_inv.mpr ⟨z, ?_⟩
    apply RestrictedProduct.ext
    intro v
    rw [RestrictedProduct.mul_apply, hev]
    have hs : ∑ i, (e i * f i) v = f (c v) v := by
      rw [Finset.sum_eq_single (c v)]
      · rw [RestrictedProduct.mul_apply, he, if_pos rfl, one_mul]
      · intro b _ hb
        rw [RestrictedProduct.mul_apply, he, if_neg (Ne.symm hb), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hs]
    exact mul_inv_cancel₀ (hc v).1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uc_fin (F : Type) [Field F] [NumberField F] :
    UnitChoice (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) := by
  exact uc_rp (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
    v.adicCompletion F) (fun v => v.adicCompletionIntegers F) Filter.cofinite
    (fun v k a f h => local_sum a f h)

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem stP : StP := by
  unfold StP
  intro F _ _
  unfold AF
  exact uc_prod (uc_pi (fun v : NumberField.InfinitePlace F => v.Completion)) (uc_fin F)

end PIW.AdelicOrbitU
