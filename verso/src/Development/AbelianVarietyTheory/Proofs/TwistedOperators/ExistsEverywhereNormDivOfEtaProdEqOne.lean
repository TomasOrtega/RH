import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone

open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex

noncomputable section

namespace GlobalTheory.HilbertRecip

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_not_mem_nrm_iff {b : Fˣ} (L : Finset (Place F)) (hb : ∀ p ∈ L, b ∉ sqr p)
    (hev : Even L.card) : ∃ a : Fˣ, ∀ p, a ∉ nrm p b ↔ p ∈ L := by
  classical
  rcases L.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨1, fun p => by simp [one_mem]⟩
  have hns : ¬ IsSquare (b : F) := fun h => hb p₀ hp₀ (mem_sqr_of_isSquare _ h)
  choose O hO using exists_over (F := F)
  obtain ⟨S₁, hS₁, h₁⟩ := exists_superset_mem_sUnits F {b} (L.biUnion O)
  obtain ⟨S₂, hS₂, hadm⟩ := exists_admissible_superset_finite_places F S₁
  obtain ⟨S, hS, hidx⟩ := exists_index_le_two hns hadm (h₁ S₂ hS₂ b (by simp))
  have hadm' := hadm.mono hS
  have hbS : b ∈ sUnits F S := h₁ S (hS₂.trans hS) b (by simp)
  have hover : ∀ p ∈ L, Over S p := fun p hp =>
    (hO p).mono ((Finset.subset_biUnion_of_mem O hp).trans (hS₁.trans (hS₂.trans hS)))
  have hex : ∀ p, ∃ x : Fˣ, p ∈ L → x ∉ nrm p b ∧ ∀ q, Over S q → q ≠ p → x ∈ sqr q := by
    intro p
    by_cases hp : p ∈ L
    · obtain ⟨x, hx⟩ := exists_single S (hover p hp) (hb p hp)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose x hx using hex
  have hxH : ∀ p ∈ L, x p ∉ sUnits F S ⊔ locNorm F b S := by
    intro p hp hmem
    obtain ⟨u, hu, n, hn, hun⟩ := Subgroup.mem_sup.1 hmem
    rw [mem_locNorm_iff] at hn
    refine not_lone p ⟨u, b, fun h => (hx p hp).1 (hun ▸ mul_mem h (hn p (hover p hp))),
      fun q hq => ?_⟩
    by_cases hq' : Over S q
    · have := sqr_le_nrm q b ((hx p hp).2 q hq' hq)
      rw [← hun] at this
      exact (mul_mem_cancel_right (hn q hq')).1 this
    · exact mem_nrm_of_not_over hadm' hu hbS hq'
  have h2 : (sUnits F S ⊔ locNorm F b S).index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
    · rw [Subgroup.index_eq_one] at h
      exact absurd (h ▸ Subgroup.mem_top _) (hxH p₀ hp₀)
    · exact h
  obtain ⟨u, hu, n, hn, hun⟩ := Subgroup.mem_sup.1 ((even_of_prod_mem h2 L x hxH).2 hev)
  rw [mem_locNorm_iff] at hn
  refine ⟨u, fun q => ?_⟩
  by_cases hq : Over S q
  · have e := hs_prod L x q b (fun h => (hx q h).1)
      fun p hp hpq => sqr_le_nrm q b ((hx p hp).2 q hq hpq.symm)
    rw [← hun, hs_mul_left, hs_eq_one_iff.2 (hn q hq), mul_one] at e
    split_ifs at e with h
    · exact iff_of_true (hs_eq_neg_one_iff.1 e) h
    · exact iff_of_false (not_not.2 (hs_eq_one_iff.1 e)) h
  · exact iff_of_false (not_not.2 (mem_nrm_of_not_over hadm' hu hbS hq)) fun h => hq (hover q h)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_hs_eq {b : Fˣ} (ε : Place F → ℤˣ) (T : Finset (Place F))
    (hT : ∀ p, ε p ≠ 1 → p ∈ T) (hb : ∀ p, b ∈ sqr p → ε p = 1) (hprod : ∏ p ∈ T, ε p = 1) :
    ∃ a : Fˣ, ∀ p, hs p a b = ε p := by
  classical
  have hneg : ∀ p, ε p ≠ 1 → ε p = -1 := fun p h => (Int.units_eq_one_or (ε p)).resolve_left h
  rw [← Finset.prod_filter_mul_prod_filter_not T fun p => ε p ≠ 1,
    Finset.prod_eq_one (s := T.filter fun p => ¬ ε p ≠ 1)
      fun p hp => not_not.1 (Finset.mem_filter.1 hp).2, mul_one,
    Finset.prod_congr rfl fun p hp => hneg p (Finset.mem_filter.1 hp).2,
    Finset.prod_const] at hprod
  obtain ⟨a, ha⟩ := exists_not_mem_nrm_iff (b := b) (T.filter fun p => ε p ≠ 1)
    (fun p hp h => (Finset.mem_filter.1 hp).2 (hb p h))
    ((neg_one_pow_eq_one_iff_even (by decide)).1 hprod)
  refine ⟨a, fun p => ?_⟩
  by_cases h : ε p = 1
  · rw [h, hs_eq_one_iff]
    exact not_not.1 fun h' => (Finset.mem_filter.1 ((ha p).1 h')).2 h
  · rw [hneg p h, hs_eq_neg_one_iff, ha]
    exact Finset.mem_filter.2 ⟨hT p h, h⟩

end GlobalTheory.HilbertRecip

namespace GlobalTheory.QuadSymbol

open GlobalTheory.HilbertRecip

namespace Converse

variable {K : Type} [Field K]

def realPlace (σ : K →+* ℝ) : InfinitePlace K := InfinitePlace.mk (Complex.ofRealHom.comp σ)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem isReal_comp (σ : K →+* ℝ) : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isReal_realPlace (σ : K →+* ℝ) : (realPlace σ).IsReal :=
  InfinitePlace.isReal_mk_iff.2 (isReal_comp σ)

/- English proof (translation)
By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem embedding_realPlace (σ : K →+* ℝ) :
    InfinitePlace.embedding_of_isReal (isReal_realPlace σ) = σ := by
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, realPlace,
    InfinitePlace.embedding_mk_eq_of_isReal (isReal_comp σ)]
  simp

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem realPlace_embedding {w : InfinitePlace K} (h : w.IsReal) :
    realPlace (InfinitePlace.embedding_of_isReal h) = w := by
  have : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal h) = w.embedding := by
    ext x
    simp
  rw [realPlace, this, InfinitePlace.mk_embedding]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem realPlace_injective : Function.Injective (realPlace (K := K)) := by
  intro σ τ h
  have H : ∀ (w w' : InfinitePlace K) (h : w.IsReal) (h' : w'.IsReal), w = w' →
      InfinitePlace.embedding_of_isReal h = InfinitePlace.embedding_of_isReal h' := by
    rintro w _ h h' rfl
    rfl
  rw [← embedding_realPlace σ, ← embedding_realPlace τ]
  exact H _ _ _ _ h

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem isSquare_completion {σ : K →+* ℝ} {δ : K} (h : IsSquare (σ δ)) :
    IsSquare (algebraMap K (realPlace σ).Completion δ) := by
  have hw := isReal_realPlace σ
  let f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hf : f (algebraMap K (realPlace σ).Completion δ) = InfinitePlace.embedding_of_isReal hw δ :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm δ)
  rw [embedding_realPlace] at hf
  rw [← hf] at h
  simpa using h.map f.symm

variable {L : Type} [Field L] [Algebra K L]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem mem_normGroup_of_isComplex (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : K}
    (h1 : e 1 * e 1 = algebraMap K L δ) {w : InfinitePlace K} (h : w.IsComplex)
    (z : (w.Completion)ˣ) : z ∈ normGroup K L w.Completion := by
  rw [mem_normGroup_iff_form e h0 h1]
  let f := InfinitePlace.Completion.ringEquivComplexOfIsComplex h
  have h2 : IsSquare (f z) := IsAlgClosed.exists_eq_mul_self _
  exact Nm.of_isSquare _ (by simpa using h2.map f.symm)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_normGroup_of_isSquare [CharZero K] (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : K}
    (hδ : δ ≠ 0) (h1 : e 1 * e 1 = algebraMap K L δ) {A : Type} [Field A] [Algebra K A]
    (h : IsSquare (algebraMap K A δ)) (z : Aˣ) : z ∈ normGroup K L A := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  rw [mem_normGroup_iff_form e h0 h1]
  exact Nm.of_isSquare_left two_ne_zero ((map_ne_zero _).2 hδ) h _

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem div_mem_normGroup {A : Type} [CommRing A] [Algebra K A]
    (h : ∀ a b : Aˣ, eta K L A (a * b) = eta K L A a * eta K L A b) {a b : Aˣ}
    (hab : eta K L A b = eta K L A a) : a / b ∈ normGroup K L A := by
  have := h (a / b) b
  rw [div_mul_cancel, hab, right_eq_mul] at this
  exact eta_eq_one_iff.1 this

end Converse

open Converse in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_everywhereNorm_div_of_etaProd_eq_one :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L], ∀ (x : FinFam K) (y : InfFam K),
      AlmostNorm K L x → etaProd K L x y = 1 →
        ∃ t : Kˣ, EverywhereNorm K L (x / finDiag K t) (y / infDiag K t) := by
  intro K L _ _ _ _ _ _ x y hA hprod
  classical
  obtain ⟨δ, e, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  lift δ to Kˣ using hδ0.isUnit
  haveI : Fintype (K →+* ℝ) := Fintype.ofFinite _
  have hA' : {v | x v ∉ normGroup K L (v.adicCompletion K)}.Finite := hA
  have hinf : ∏ σ : K →+* ℝ, eta K L (realPlace σ).Completion (y (realPlace σ)) =
      ∏ w : InfinitePlace K, eta K L w.Completion (y w) := by
    refine Finset.prod_of_injOn realPlace realPlace_injective.injOn (fun _ _ => by simp)
      (fun w _ hn => ?_) fun σ _ => rfl
    rcases w.isReal_or_isComplex with h | h
    · exact absurd ⟨InfinitePlace.embedding_of_isReal h, by simp, realPlace_embedding h⟩ hn
    · exact eta_eq_one_iff.2 (mem_normGroup_of_isComplex e h0 h1 h _)
  obtain ⟨t, ht⟩ := exists_hs_eq (b := δ)
    (Sum.elim (fun v => eta K L (v.adicCompletion K) (x v))
      fun σ => eta K L (realPlace σ).Completion (y (realPlace σ)))
    (hA'.toFinset.disjSum Finset.univ)
    (by
      rintro (v | σ) hv
      · rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
        exact fun h' => hv (eta_eq_one_iff.2 h')
      · simp)
    (by
      rintro (v | σ) hv
      · exact eta_eq_one_iff.2 (mem_normGroup_of_isSquare e h0 hδ0 h1 hv _)
      · exact eta_eq_one_iff.2 (mem_normGroup_of_isSquare e h0 hδ0 h1 (isSquare_completion hv) _))
    (by
      rw [etaProd, ← hinf, finprod_eq_prod_of_mulSupport_subset _ (s := hA'.toFinset) fun v hv => by
        rw [Set.Finite.coe_toFinset]
        exact fun hm => hv (eta_eq_one_iff.2 hm)] at hprod
      rw [Finset.prod_disjSum]
      exact hprod)
  obtain ⟨hc1, hc2⟩ := localCharacters K L
  refine ⟨t, fun v => div_mem_normGroup (hc1 v) ?_, fun w => ?_⟩
  · have key : finDiag K t v ∈ normGroup K L (v.adicCompletion K) ↔ t ∈ nrm (.inl v) δ :=
      mem_normGroup_iff_form e h0 h1
    refine Eq.trans ?_ (ht (.inl v))
    by_cases h : finDiag K t v ∈ normGroup K L (v.adicCompletion K)
    · rw [eta_eq_one_iff.2 h, hs_eq_one_iff.2 (key.1 h)]
    · rw [eta_eq_neg_one_iff.2 h, hs_eq_neg_one_iff.2 fun h' => h (key.2 h')]
  · rcases w.isReal_or_isComplex with h | h
    · refine div_mem_normGroup (hc2 w) ?_
      rw [eta_infinite_real e h0 h1 t h, ht]
      exact congrArg (fun w : InfinitePlace K => eta K L w.Completion (y w)) (realPlace_embedding h)
    · exact mem_normGroup_of_isComplex e h0 h1 h _

end GlobalTheory.QuadSymbol

end
