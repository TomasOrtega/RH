import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

open NumberField IsDedekindDomain

namespace PI.TameSurjW

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem liesOver_span_iff {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    P.LiesOver (Ideal.span {(p : ℤ)}) ↔ ((p : ℕ) : 𝓞 E) ∈ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  constructor
  · intro h
    have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
    rw [Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)})] at h1
    simpa using h1
  · intro h
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap]
    simpa using h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem notMem_sq_of_split {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ Formalism.BasicNotions.placesOver E p) :
    ((p : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 := by
  set P0 : Ideal ℤ := Ideal.span {(p : ℤ)} with hP0def
  have : Fact p.Prime := ⟨hp⟩
  have hmax : P0.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0 : P0 ≠ ⊥ := by
    simp [P0, hp.ne_zero]
  have himg : HeightOneSpectrum.asIdeal '' (Formalism.BasicNotions.placesOver E p) = P0.primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.isPrime, (liesOver_span_iff hp w.asIdeal).2 hw⟩
    · rintro ⟨hPp, hPl⟩
      have hPne : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hP0 ⟨hPp, hPl⟩
      exact ⟨⟨P, hPp, hPne⟩, (liesOver_span_iff hp P).1 hPl, rfl⟩
  have hcard : Fintype.card (P0.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, ← himg,
      Set.ncard_image_of_injective _ (fun a b hab => HeightOneSpectrum.ext hab), h]
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P0 (𝓞 E)
  rw [RingOfIntegers.rank] at hsum
  intro hsq
  have hlo : v.asIdeal.LiesOver P0 := (liesOver_span_iff hp v.asIdeal).2 hv
  let q : P0.primesOver (𝓞 E) := ⟨v.asIdeal, v.isPrime, hlo⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) P0 ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0
  have hdvd : v.asIdeal ^ 2 ∣ Ideal.map (algebraMap ℤ (𝓞 E)) P0 := by
    rw [Ideal.dvd_iff_le, hP0def, Ideal.map_span, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe]
    simpa using hsq
  have hfin : FiniteMultiplicity v.asIdeal (Ideal.map (algebraMap ℤ (𝓞 E)) P0) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime v.ne_bot v.isPrime) hmap
  have he : 2 ≤ v.asIdeal.ramificationIdx ℤ := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P0 v.asIdeal hmap]
    exact hfin.le_multiplicity_of_pow_dvd hdvd
  have hlt : Fintype.card (P0.primesOver (𝓞 E)) <
      ∑ r : P0.primesOver (𝓞 E), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
    rw [Fintype.card_eq_sum_ones]
    apply Finset.sum_lt_sum
    · intro r _
      exact Nat.mul_pos (Ideal.ramificationIdx_pos r.1 ℤ) (Ideal.inertiaDeg_pos r.1 ℤ)
    · refine ⟨q, Finset.mem_univ _, ?_⟩
      have hf : 0 < v.asIdeal.inertiaDeg ℤ := Ideal.inertiaDeg_pos v.asIdeal ℤ
      show 1 < v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ
      nlinarith
  omega

end PI.TameSurjW
