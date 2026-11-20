import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

noncomputable section

namespace GlobalTheory.StableRange

open IsDedekindDomain NumberField

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Consider separately whether the proposition holds or fails. It suffices to derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative. A detailed English derivation is pending.
-/
theorem exists_inv_mod_maximal {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (b : S) :
    ∃ y : S, ∀ m : Ideal S, m.IsMaximal → b ∈ m ∨ 1 - b * y ∈ m := by
  let I : Ideal S := (Ideal.jacobson (⊥ : Ideal B)).map (algebraMap B S)
  have hI : ∀ m : Ideal S, m.IsMaximal → I ≤ m := by
    intro m hm
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap B S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    exact sInf_le ⟨bot_le, this⟩
  have hp : ∀ p : Ideal S, p.IsPrime → I ≤ p → p.IsMaximal := by
    intro p hp hIp
    rw [Ideal.map_le_iff_le_comap] at hIp
    have hq : (p.comap (algebraMap B S)).IsPrime := Ideal.comap_isPrime _ _
    have hmax : (p.comap (algebraMap B S)).IsMaximal := by
      rw [Ideal.isMaximal_iff]
      refine ⟨(Ideal.ne_top_iff_one _).1 hq.ne_top, fun J x hJ hx hxJ => ?_⟩
      obtain ⟨y, hy⟩ := hB x
      have h1 : x * (1 - x * y) ∈ p.comap (algebraMap B S) :=
        hIp (Ideal.mem_jacobson_bot.2 hy)
      have h2 := (hq.mem_or_mem h1).resolve_left hx
      have := J.add_mem (hJ h2) (J.mul_mem_right y hxJ)
      simpa using this
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B) p hmax
  let M : Submonoid S :=
    { carrier := {s | ∃ (n : ℕ) (y : S), s = b ^ n * (1 - b * y)}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, y, rfl⟩ ⟨k, w, rfl⟩
        exact ⟨n + k, y + w - b * y * w, by ring⟩ }
  by_cases hd : Disjoint (I : Set S) (M : Set S)
  · exfalso
    obtain ⟨p, hpp, hIp, hdis⟩ := Ideal.exists_le_prime_disjoint I M hd
    have hm := hp p hpp hIp
    have hb : b ∉ p := fun h => Set.disjoint_left.1 hdis h ⟨1, 0, by simp⟩
    obtain ⟨y, i, hi, hy⟩ := hm.exists_inv hb
    refine Set.disjoint_left.1 hdis hi ⟨0, y, ?_⟩
    rw [← hy]; ring
  · obtain ⟨s, hsI, n, y, rfl⟩ := Set.not_disjoint_iff.1 hd
    refine ⟨y, fun m hm => ?_⟩
    rcases hm.isPrime.mem_or_mem (hI m hm hsI) with h | h
    · exact Or.inl (hm.isPrime.mem_of_pow_mem n h)
    · exact Or.inr h

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem stable_of_isIntegral {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (a b : S)
    (h : IsCoprime a b) : ∃ t : S, IsUnit (a + t * b) := by
  obtain ⟨y, hy⟩ := exists_inv_mod_maximal hB b
  obtain ⟨u, w, huw⟩ := h
  refine ⟨y * (1 - a), ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (a := a + y * (1 - a) * b) hn
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hy m hm with hb | hb
  · have e : (1 : S) = u * (a + y * (1 - a) * b) + (w - u * (y * (1 - a))) * b := by
      linear_combination -huw
    rw [e]
    exact m.add_mem (m.mul_mem_left _ hmem) (m.mul_mem_left _ hb)
  · have e : (1 : S) = (a + y * (1 - a) * b) + (1 - a) * (1 - b * y) := by ring
    rw [e]
    exact m.add_mem hmem (m.mul_mem_left _ hb)

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem stable_of_subrings {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R]
    (hA : ∀ s : Finset A, ∃ B : Subring A, (s : Set A) ⊆ B ∧
      ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1))
    (a b : R) (h : IsCoprime a b) : ∃ t : R, IsUnit (a + t * b) := by
  classical
  obtain ⟨u, w, huw⟩ := h
  choose p hpm hp using fun r : R => (Algebra.IsIntegral.isIntegral (R := A) r)
  obtain ⟨B, hs, hB⟩ := hA ((p a).coeffs ∪ (p b).coeffs ∪ (p u).coeffs ∪ (p w).coeffs)
  have key : ∀ r : R, ((p r).coeffs : Set A) ⊆ B → IsIntegral B r := by
    intro r hr
    refine ⟨(p r).toSubring B hr, (Polynomial.monic_toSubring _ _ hr).2 (hpm r), ?_⟩
    have e : algebraMap B R = (algebraMap A R).comp B.subtype := rfl
    rw [e, ← Polynomial.eval₂_map, Polynomial.map_toSubring]
    exact hp r
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  obtain ⟨t, ht⟩ := stable_of_isIntegral (S := integralClosure B R) hB ⟨a, key a h1⟩ ⟨b, key b h2⟩
    ⟨⟨u, key u h3⟩, ⟨w, key w h4⟩, Subtype.ext huw⟩
  exact ⟨t, ht.map (integralClosure B R).val⟩

variable (K : Type*) [Field K] [NumberField K]

def intOutside (T : Set (HeightOneSpectrum (𝓞 K))) : Subring (AdeleRing (𝓞 K) K) where
  carrier := {x | ∀ v ∉ T, x.2 v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v hv := mul_mem (ha v hv) (hb v hv)
  one_mem' v _ := one_mem (v.adicCompletionIntegers K)
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := zero_mem (v.adicCompletionIntegers K)
  neg_mem' ha v hv := neg_mem (ha v hv)

def mkAdele {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (f : ∀ w : InfinitePlace K, w.Completion) (g : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hg : ∀ v ∉ T, g v ∈ v.adicCompletionIntegers K) : intOutside K T :=
  ⟨(f, ⟨g, hT.subset fun v hv => by
    by_contra h
    exact hv (hg v h)⟩), hg⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isUnit_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) (x : intOutside K T)
    (h1 : ∀ w, x.1.1 w ≠ 0) (h2 : ∀ v, x.1.2 v ≠ 0) (h3 : ∀ v ∉ T, Valued.v (x.1.2 v) = 1) :
    IsUnit x := by
  refine IsUnit.of_mul_eq_one (mkAdele K hT (fun w => (x.1.1 w)⁻¹) (fun v => (x.1.2 v)⁻¹)
    fun v hv => ?_) ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h3 v hv, inv_one]
  · refine Subtype.ext (Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_))
    · exact mul_inv_cancel₀ (h1 w)
    · exact mul_inv_cancel₀ (h2 v)

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem mul_one_sub_mul_inv {L : Type*} [Field L] (x : L) : x * (1 - x * x⁻¹) = 0 := by
  by_cases h : x = 0
  · simp [h]
  · simp [h]

open Classical in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem regular_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (x : intOutside K T) :
    ∃ y : intOutside K T, ∀ z : intOutside K T, IsUnit (x * (1 - x * y) * z + 1) := by
  refine ⟨mkAdele K hT (fun w => (x.1.1 w)⁻¹)
    (fun v => if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0) fun v hv => ?_, fun z => ?_⟩
  · split_ifs with h
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h.resolve_left hv, inv_one]
    · exact zero_mem _
  · have hv : ∀ v, Valued.v (x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1) = 1 := by
      intro v
      split_ifs with h
      · rw [mul_one_sub_mul_inv]; simp
      · obtain ⟨hT', h1⟩ := not_or.1 h
        have hx : Valued.v (x.1.2 v) ≤ 1 := x.2 v hT'
        have hz : Valued.v (z.1.2 v) ≤ 1 := z.2 v hT'
        rw [mul_zero, sub_zero, mul_one, add_comm]
        apply Valuation.map_one_add_of_lt
        rw [map_mul]
        exact (mul_le_of_le_one_right' hz).trans_lt (lt_of_le_of_ne hx h1)
    refine isUnit_intOutside K hT _ (fun w => ?_) (fun v => ?_) (fun v _ => hv v)
    · change x.1.1 w * (1 - x.1.1 w * (x.1.1 w)⁻¹) * z.1.1 w + 1 ≠ 0
      rw [mul_one_sub_mul_inv]; simp
    · intro h0
      have h1 := hv v
      have h2 : x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1 = 0 := h0
      rw [h2] at h1
      simp at h1

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem stable_adele {R : Type*} [CommRing R] [Algebra (AdeleRing (𝓞 K) K) R]
    [Algebra.IsIntegral (AdeleRing (𝓞 K) K) R] (a b : R) (h : IsCoprime a b) :
    ∃ t : R, IsUnit (a + t * b) := by
  refine stable_of_subrings (A := AdeleRing (𝓞 K) K) (fun s => ?_) a b h
  have hT : (⋃ x ∈ (s : Set (AdeleRing (𝓞 K) K)),
      {v : HeightOneSpectrum (𝓞 K) | x.2 v ∉ v.adicCompletionIntegers K}).Finite :=
    s.finite_toSet.biUnion fun x _ => x.2.2
  refine ⟨intOutside K _, fun x hx v hv => ?_, regular_intOutside K hT⟩
  by_contra h
  exact hv (Set.mem_biUnion hx h)

end GlobalTheory.StableRange

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem GlobalTheory.StableRange.adeles_stableRange_one :
    ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) :=
  fun D a b h => GlobalTheory.StableRange.stable_adele D.host.F a b h
