import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridPlaces

open Formalism.L2.Col

variable {D : D7}

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨a, b, hab⟩ : IsCoprime (p : 𝓞 M) (q : 𝓞 M)` from `Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)`. Apply `P.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)`.
-/
theorem prime_eq_of_mem {M : Type} [Field M] [NumberField M] (P : HeightOneSpectrum (𝓞 M)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 M) ∈ P.asIdeal) (h2 : (q : 𝓞 M) ∈ P.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 M) (q : 𝓞 M) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hm : (Ideal.span {(p : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime p`. Take `⟨⟨W, hW, hWQ⟩⟩` from `(inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 M)))`. Establish `hm : (p : 𝓞 M) ∈ W`. Establish `: (p : ℤ) ∈ W.under ℤ` using `by rw [← hWQ.over]; exact Ideal.mem_span_singleton_self _`.

Simplify using `using (show algebraMap ℤ (𝓞 M) (p : ℤ) ∈ W from this)`. Use `⟨⟨W, hW, ?_⟩, hm⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))`.
-/
theorem exists_place (M : Type) [Field M] [NumberField M] {p : ℕ} (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 M), (p : 𝓞 M) ∈ P.asIdeal := by
  have : Fact p.Prime := ⟨hp⟩
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 M)))
  have hm : (p : 𝓞 M) ∈ W := by
    have : (p : ℤ) ∈ W.under ℤ := by rw [← hWQ.over]; exact Ideal.mem_span_singleton_self _
    simpa using (show algebraMap ℤ (𝓞 M) (p : ℤ) ∈ W from this)
  refine ⟨⟨W, hW, ?_⟩, hm⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))

/- English proof (translation)
Use `show algebraMap (𝓞 M) (𝓞 N) (n : 𝓞 M) ∈ P.asIdeal ↔ _`. Rewrite using `[map_natCast]`.
-/
theorem natCast_mem_under {M N : Type} [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]
    (P : HeightOneSpectrum (𝓞 N)) (n : ℕ) : (n : 𝓞 M) ∈ (P.under (𝓞 M)).asIdeal ↔ (n : 𝓞 N) ∈ P.asIdeal := by
  show algebraMap (𝓞 M) (𝓞 N) (n : 𝓞 M) ∈ P.asIdeal ↔ _
  rw [map_natCast]

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Use `show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ (conjPrime₂ P).asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal`. Establish `e : cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x`. Use `letI := D.host.isCMField_hostE`.

Conclude with `RingOfIntegers.ext (IsCMField.complexConj_apply_eq_self D.host.E (x : D.host.F))`. Rewrite using `[mem_conjP, e]`.
-/
theorem under_conjP (P : HeightOneSpectrum (𝓞 D.host.E)) :
    (conjPrime₂ P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ (conjPrime₂ P).asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal
  have e : cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    letI := D.host.isCMField_hostE
    exact RingOfIntegers.ext (IsCMField.complexConj_apply_eq_self D.host.E (x : D.host.F))
  rw [mem_conjP, e]

/- English proof (translation)
Establish `hsub : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (conjPrime₂ P).asIdeal`. Introduce `x hx`. Take `⟨n, hn, -⟩` from `GlobalTheory.MovedSplit.exists_int D (x * cO _ x) (by show star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)`. Rewrite using `[star_mul', star_star, mul_comm])`. Establish `h1 : n ∈ (Q.under (𝓞 D.host.F)).asIdeal` using `by show algebraMap _ (𝓞 D.host.E) n ∈ Q.asIdeal`.

Rewrite using `[hn]`. Conclude with `Ideal.mul_mem_right _ _ hx`. Rewrite `h1` using `[h]`. Establish `h2 : algebraMap _ (𝓞 D.host.E) n ∈ P.asIdeal` using `h1`. Rewrite `h2` using `[hn]`.

Conclude with `(P.isPrime.mem_or_mem h2).imp id fun h3 => (mem_conjP _ _).2 h3`. Conclude with `(Ideal.subset_union.1 hsub).imp (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)) (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (conjPrime₂ P).isPrime.ne_top h))`.
-/
theorem eq_or_eq_conjP {P Q : HeightOneSpectrum (𝓞 D.host.E)} (h : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) :
    Q = P ∨ Q = conjPrime₂ P := by
  have hsub : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (conjPrime₂ P).asIdeal := by
    intro x hx
    obtain ⟨n, hn, -⟩ := GlobalTheory.MovedSplit.exists_int D (x * cO _ x) (by
      show star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul', star_star, mul_comm])
    have h1 : n ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) n ∈ Q.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [h] at h1
    have h2 : algebraMap _ (𝓞 D.host.E) n ∈ P.asIdeal := h1
    rw [hn] at h2
    exact (P.isPrime.mem_or_mem h2).imp id fun h3 => (mem_conjP _ _).2 h3
  exact (Ideal.subset_union.1 hsub).imp
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h))
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (conjPrime₂ P).isPrime.ne_top h))

/- English proof (translation)
Introduce `h`. Establish `hcl` using `GlobalTheory.Mem.cls_eq_splitK_of_cond D.host hc`. Establish `: Fact p.Prime` using `⟨hp⟩`. Choose the witnesses or unpack the hypotheses as in `⟨h2, hd, hj⟩ : p ≠ 2 ∧ p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p = 1 := by`. Unfold `Host.cls primeClass at hcl`.

Use `split_ifs at hcl with h1 h2 h3 h4`. Conclude with `⟨fun e => h1 (e ▸ D.host.two_mem_small), h3, h4⟩`. Take `⟨s, hs⟩` from `ZMod.isSquare_of_jacobiSym_eq_one hj`. Take `⟨s, rfl⟩` from `ZMod.intCast_surjective s`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : (p : ℤ) ∣ s * s + D.host.d := by`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hs ⊢`. Rewrite using `[← hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsq` using `D.host.sqrtMinusD_sq`.

Establish `hint : IsIntegral ℤ D.host.sqrtMinusD`. Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Rewrite using `[hsq]`. Use `(isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ))).neg` as an intermediate fact. Simplify using `using this`.

Set `b : 𝓞 D.host.K` to `⟨⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩, (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.K D.host.E) Subtype.val_injective).1 hint⟩`. Take `⟨β, hβ⟩ : ∃ β, β = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) b` from `⟨_, rfl⟩`. Establish `hβ1 : (β : D.host.E) = D.host.sqrtMinusD` using `by rw [hβ]; rfl`. Establish `hβ2 : β * β = -(D.host.d : 𝓞 D.host.E)` using `RingOfIntegers.ext (by simpa [hβ1, sq] using hsq)`. Establish `hβ3 : cO D.host.E β = -β` using `RingOfIntegers.ext (by show star (β : D.host.E) = ((-β : 𝓞 D.host.E) : D.host.E)`.

Rewrite using `[bridge_star_holds D.R D.host, hβ1, D.host.conj_sqrtMinusD, ← hβ1]`. Use the proof step `simp)`. Establish `key : ∀ t : ℤ, (t : 𝓞 D.host.E) + β ∈ P.asIdeal ↔ (t : 𝓞 D.host.E) - β ∈ P.asIdeal`. Introduce `t`. Establish `h1 : (t : 𝓞 D.host.K) + b ∈ ((conjPrime₂ P).under (𝓞 D.host.K)).asIdeal ↔ (t : 𝓞 D.host.K) + b ∈ (P.under (𝓞 D.host.K)).asIdeal` using `by rw [h]`.

Establish `h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) = t + β`. Rewrite using `[map_add, map_intCast, hβ]`. Establish `h4 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ (conjPrime₂ P).asIdeal ↔ algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ P.asIdeal` using `h1`. Rewrite `h4` using `[h3, mem_conjP, map_add, map_intCast, hβ3, ← sub_eq_add_neg]`. Conclude with `h4.symm`.

Establish `hprod : ((s : 𝓞 D.host.E) + β) * (s - β) ∈ P.asIdeal`. Establish `e : ((s : 𝓞 D.host.E) + β) * (s - β) = (p : 𝓞 D.host.E) * m`. Use `congrArg (Int.cast : ℤ → 𝓞 D.host.E) hm` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this - hβ2`.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ hP`. Establish `ha : (s : 𝓞 D.host.E) + β ∈ P.asIdeal` using `(P.isPrime.mem_or_mem hprod).elim id (key s).2`. Establish `hb` using `(key s).1 ha`. Establish `h5 : (2 : 𝓞 D.host.E) * β ∈ P.asIdeal`.

Use `sub_mem ha hb` as an intermediate fact. Rewrite `this` using `[show (s : 𝓞 D.host.E) + β - (s - β) = 2 * β by ring]`. Then use the resulting hypothesis. Break down `P.isPrime.mem_or_mem h5 with h6 | h6` into its components or cases. Conclude with `h2 (prime_eq_of_mem P hp Nat.prime_two hP (by exact_mod_cast h6))`. Establish `h7` using `neg_mem (Ideal.mul_mem_left _ β h6)`.

Rewrite `h7` using `[hβ2, neg_neg]`. Conclude with `hd (prime_eq_of_mem P hp D.host.hyp.2.1 hP h7)`.
-/
theorem under_conjugatePrime_ne {p : ℕ} (hp : p.Prime) (hc : p % LevelStarExponents.condE D = 1) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : (p : 𝓞 D.host.E) ∈ P.asIdeal) : (conjPrime₂ P).under (𝓞 D.host.K) ≠ P.under (𝓞 D.host.K) := by
  intro h
  have hcl := GlobalTheory.Mem.cls_eq_splitK_of_cond D.host hc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h2, hd, hj⟩ : p ≠ 2 ∧ p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p = 1 := by
    unfold Host.cls primeClass at hcl
    split_ifs at hcl with h1 h2 h3 h4
    exact ⟨fun e => h1 (e ▸ D.host.two_mem_small), h3, h4⟩
  obtain ⟨s, hs⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨s, rfl⟩ := ZMod.intCast_surjective s
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ s * s + D.host.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hs ⊢
    rw [← hs]; ring
  have hsq := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hsq]
    have := (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ))).neg
    simpa using this
  let b : 𝓞 D.host.K := ⟨⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩,
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.K D.host.E) Subtype.val_injective).1 hint⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) b := ⟨_, rfl⟩
  have hβ1 : (β : D.host.E) = D.host.sqrtMinusD := by rw [hβ]; rfl
  have hβ2 : β * β = -(D.host.d : 𝓞 D.host.E) := RingOfIntegers.ext (by simpa [hβ1, sq] using hsq)
  have hβ3 : cO D.host.E β = -β := RingOfIntegers.ext (by
    show star (β : D.host.E) = ((-β : 𝓞 D.host.E) : D.host.E)
    rw [bridge_star_holds D.R D.host, hβ1, D.host.conj_sqrtMinusD, ← hβ1]
    simp)
  have key : ∀ t : ℤ, (t : 𝓞 D.host.E) + β ∈ P.asIdeal ↔ (t : 𝓞 D.host.E) - β ∈ P.asIdeal := by
    intro t
    have h1 : (t : 𝓞 D.host.K) + b ∈ ((conjPrime₂ P).under (𝓞 D.host.K)).asIdeal ↔
        (t : 𝓞 D.host.K) + b ∈ (P.under (𝓞 D.host.K)).asIdeal := by rw [h]
    have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) = t + β := by
      rw [map_add, map_intCast, hβ]
    have h4 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ (conjPrime₂ P).asIdeal ↔
      algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ P.asIdeal := h1
    rw [h3, mem_conjP, map_add, map_intCast, hβ3, ← sub_eq_add_neg] at h4
    exact h4.symm
  have hprod : ((s : 𝓞 D.host.E) + β) * (s - β) ∈ P.asIdeal := by
    have e : ((s : 𝓞 D.host.E) + β) * (s - β) = (p : 𝓞 D.host.E) * m := by
      have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hm
      push_cast at this
      linear_combination this - hβ2
    rw [e]
    exact Ideal.mul_mem_right _ _ hP
  have ha : (s : 𝓞 D.host.E) + β ∈ P.asIdeal := (P.isPrime.mem_or_mem hprod).elim id (key s).2
  have hb := (key s).1 ha
  have h5 : (2 : 𝓞 D.host.E) * β ∈ P.asIdeal := by
    have := sub_mem ha hb
    rwa [show (s : 𝓞 D.host.E) + β - (s - β) = 2 * β by ring] at this
  rcases P.isPrime.mem_or_mem h5 with h6 | h6
  · exact h2 (prime_eq_of_mem P hp Nat.prime_two hP (by exact_mod_cast h6))
  · have h7 := neg_mem (Ideal.mul_mem_left _ β h6)
    rw [hβ2, neg_neg] at h7
    exact hd (prime_eq_of_mem P hp D.host.hyp.2.1 hP h7)

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Take `⟨⟨W, hW, hWv⟩⟩` from `(inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 D.host.E)))`. Set `w : HeightOneSpectrum (𝓞 D.host.E)` to `⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W⟩`. Establish `hwv : w.under (𝓞 D.host.F) = v` using `HeightOneSpectrum.ext hWv.over.symm`. Establish `hw : (p : 𝓞 D.host.E) ∈ w.asIdeal` using `(natCast_mem_under (M := D.host.F) w p).1 (hwv ▸ hv)`.

Establish `hG : IsGalois ℚ D.host.E` using `D.host.hostE_isGalois`. Establish `hsq` using `D.host.sqrtMinusD_sq`. Establish `hb : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ D.host.sqrtMinusD = D.host.sqrtMinusD ∨ σ D.host.sqrtMinusD = -D.host.sqrtMinusD`. Introduce `σ`. Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises.

Rewrite using `[← map_pow, hsq, map_neg, map_natCast]`. Break down `@GlobalTheory.ConjOverQuad.under_eq_or_smul_under_eq _ _ _ _ _ hp D.host.sqrtMinusD hb D.host.conj D.host.conj_sqrtMinusD w.asIdeal hW hw 𝔭.asIdeal 𝔭.isPrime h𝔭 with h | h` into its components or cases. Conclude with `⟨w, hwv, HeightOneSpectrum.ext h⟩`. Use `⟨conjPrime₂ w, (under_conjP w).trans hwv, HeightOneSpectrum.ext ?_⟩` and prove the remaining obligations. Establish `e : (conjPrime₂ w).asIdeal = D.host.conj⁻¹ • w.asIdeal`.

Use extensionality with `y`. Rewrite using `[mem_conjP, Ideal.mem_inv_pointwise_smul_iff]`. Establish `: cO D.host.E y = D.host.conj • y` using `RingOfIntegers.ext (bridge_star_holds D.R D.host (y : D.host.E))`. Rewrite using `[this]`. Use `show ((conjPrime₂ w).asIdeal).under (𝓞 D.host.K) = _`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem exists_over_both {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (p : 𝓞 D.host.F) ∈ v.asIdeal)
    (𝔭 : HeightOneSpectrum (𝓞 D.host.K)) (h𝔭 : (p : 𝓞 D.host.K) ∈ 𝔭.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v ∧ w.under (𝓞 D.host.K) = 𝔭 := by
  have := v.isPrime
  obtain ⟨⟨W, hW, hWv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 D.host.E)))
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W⟩
  have hwv : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hWv.over.symm
  have hw : (p : 𝓞 D.host.E) ∈ w.asIdeal := (natCast_mem_under (M := D.host.F) w p).1 (hwv ▸ hv)
  have hG : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hsq := D.host.sqrtMinusD_sq
  have hb : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      σ D.host.sqrtMinusD = D.host.sqrtMinusD ∨ σ D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  rcases @GlobalTheory.ConjOverQuad.under_eq_or_smul_under_eq _ _ _ _ _ hp D.host.sqrtMinusD hb D.host.conj
    D.host.conj_sqrtMinusD w.asIdeal hW hw 𝔭.asIdeal 𝔭.isPrime h𝔭 with h | h
  · exact ⟨w, hwv, HeightOneSpectrum.ext h⟩
  · refine ⟨conjPrime₂ w, (under_conjP w).trans hwv, HeightOneSpectrum.ext ?_⟩
    have e : (conjPrime₂ w).asIdeal = D.host.conj⁻¹ • w.asIdeal := by
      ext y
      rw [mem_conjP, Ideal.mem_inv_pointwise_smul_iff]
      have : cO D.host.E y = D.host.conj • y :=
        RingOfIntegers.ext (bridge_star_holds D.R D.host (y : D.host.E))
      rw [this]
    show ((conjPrime₂ w).asIdeal).under (𝓞 D.host.K) = _
    rw [e]
    exact h

/- English proof (translation)
Take `⟨⟨q, hq, hc, -, hne⟩, -⟩` from `hQ P h`. Use `⟨q, hq, ?_, hne⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]`. Conclude with `card_nsmul_eq_zero'`.
-/
theorem exists_prime_mem {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (hQ : Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (h : P ∈ Q) :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P.asIdeal ∧ ∀ i, q ≠ D.host.g i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ P h
  refine ⟨q, hq, ?_, hne⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

/- English proof (translation)
Distinguish the cases in `hp : p.Prime`. Use `swap`. Conclude with `⟨L.C.P.pb 0, fun h => absurd h hp⟩`. Distinguish the cases in `hg : ∃ k, p = D.host.g k`. Take `⟨k, rfl⟩` from `hg`.

Use `⟨L.C.P.pb k, fun _ => ⟨L.C.P.pb_over k, fun k' hk => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Apply the tactic sequence `have := D.host.g_ne fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hk this | exact absurd hk.symm this`. Break down `h with h | h` into its components or cases. Conclude with `absurd h.symm (D.host.pde_ne_g k).1`. Conclude with `absurd h.symm (D.host.pde_ne_g k).2`.

Distinguish the cases in `hq : (p = D.host.pde ∨ p = D.host.pde') ∧ ∃ t, ∃ P ∈ L.Q t, (p : 𝓞 D.host.E) ∈ P.asIdeal`. Take `⟨h1, t, P, hP, hpP⟩` from `hq`. Take `⟨𝔭, h𝔭⟩` from `hL.Q_de p h1`. Use `⟨𝔭, fun _ => ⟨?_, fun k hk => absurd ⟨k, hk⟩ hg, fun _ => h𝔭⟩⟩` and prove the remaining obligations. Rewrite using `[← h𝔭 t P hP hpP]`.

Conclude with `(natCast_mem_under P p).2 hpP`. Take `⟨𝔭, h𝔭⟩` from `exists_place D.host.K hp`. Conclude with `⟨𝔭, fun _ => ⟨h𝔭, fun k hk => absurd ⟨k, hk⟩ hg, fun h t P hP hpP => absurd ⟨h, t, P, hP, hpP⟩ hq⟩⟩`.
-/
theorem exists_primes {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (p : ℕ) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K), p.Prime → (p : 𝓞 D.host.K) ∈ 𝔭.asIdeal ∧
      (∀ k, p = D.host.g k → 𝔭 = L.C.P.pb k) ∧
      (p = D.host.pde ∨ p = D.host.pde' →
        ∀ t, ∀ P ∈ L.Q t, (p : 𝓞 D.host.E) ∈ P.asIdeal → P.under (𝓞 D.host.K) = 𝔭) := by
  by_cases hp : p.Prime
  swap
  · exact ⟨L.C.P.pb 0, fun h => absurd h hp⟩
  by_cases hg : ∃ k, p = D.host.g k
  · obtain ⟨k, rfl⟩ := hg
    refine ⟨L.C.P.pb k, fun _ => ⟨L.C.P.pb_over k, fun k' hk => ?_, fun h => ?_⟩⟩
    · have := D.host.g_ne
      fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hk this | exact absurd hk.symm this
    · rcases h with h | h
      · exact absurd h.symm (D.host.pde_ne_g k).1
      · exact absurd h.symm (D.host.pde_ne_g k).2
  by_cases hq : (p = D.host.pde ∨ p = D.host.pde') ∧ ∃ t, ∃ P ∈ L.Q t, (p : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨h1, t, P, hP, hpP⟩ := hq
    obtain ⟨𝔭, h𝔭⟩ := hL.Q_de p h1
    refine ⟨𝔭, fun _ => ⟨?_, fun k hk => absurd ⟨k, hk⟩ hg, fun _ => h𝔭⟩⟩
    rw [← h𝔭 t P hP hpP]
    exact (natCast_mem_under P p).2 hpP
  · obtain ⟨𝔭, h𝔭⟩ := exists_place D.host.K hp
    exact ⟨𝔭, fun _ => ⟨h𝔭, fun k hk => absurd ⟨k, hk⟩ hg, fun h t P hP hpP => absurd ⟨h, t, P, hP, hpP⟩ hq⟩⟩

/- English proof (translation)
Introduce `D T L μ0 hL hg hde hde' hq hQ`. Use `choose 𝔭 h𝔭 using exists_primes L hL`. Take `⟨hq0, hq1, -⟩` from `leastSplitAuxiliaryPrimeThetaChain_spec D`. Establish `hq2 : q0 D % LevelStarExponents.condE D = 1`. Establish `h1 : 1 < LevelStarExponents.condE D`.

Establish `h0 : 0 < LevelStarExponents.condE D` using `Nat.mul_pos (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos) D.host.hyp.2.1.pos`. Use `Nat.mod_lt D.host.pde h0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Nat.mod_mod_of_dvd _ (dvd_mul_left _ (Formalism.MainNotions.rPrAv D)), hq1, Nat.mod_eq_of_lt h1]`. Take `⟨v0, hv0⟩` from `exists_place D.host.F hq0`.

Establish `hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ w : HeightOneSpectrum (𝓞 D.host.E), ∀ p : ℕ, p.Prime → (p : 𝓞 D.host.F) ∈ v.asIdeal → w.under (𝓞 D.host.F) = v ∧ w.under (𝓞 D.host.K) = 𝔭 p`. Introduce `v`. Distinguish the cases in `h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal`. Take `⟨p, hp, hv⟩` from `h`. Take `⟨w, hw⟩` from `exists_over_both hp v hv (𝔭 p) (h𝔭 p hp).1`.

Conclude with `⟨w, fun p' hp' hv' => prime_eq_of_mem v hp hp' hv hv' ▸ hw⟩`. Take `⟨w, -⟩` from `exists_place D.host.E hq0`. Conclude with `⟨w, fun p hp hv => absurd ⟨p, hp, hv⟩ h⟩`. Use `choose w hw using hw`. Establish `hS : ∀ v ∈ insert v0 (S1 D), ∃ p : ℕ, p.Prime ∧ p % LevelStarExponents.condE D = 1 ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal`.

Introduce `v hv`. Break down `Finset.mem_insert.1 hv with rfl | hv` into its components or cases. Conclude with `⟨_, hq0, hq2, hv0⟩`. Break down `(S1_mem_OmF D).1 hv with h | h | h | h` into its components or cases. Conclude with `⟨_, D.host.g_prime 0, hg 0, h⟩`.

Conclude with `⟨_, D.host.g_prime 1, hg 1, h⟩`. Conclude with `⟨_, D.host.pde_prime, hde, h⟩`. Conclude with `⟨_, D.host.pde'_prime, hde', h⟩`. Establish `hde2 : ∀ p : ℕ, p = D.host.pde ∨ p = D.host.pde' → p.Prime ∧ p % LevelStarExponents.condE D = 1`. Introduce and unpack `p (rfl | rfl)`.

Conclude with `⟨D.host.pde_prime, hde⟩`. Conclude with `⟨D.host.pde'_prime, hde'⟩`. Use `⟨⟨v0, hv0, w, fun v hv => ?_, fun v hv => ?_, fun v k hv => ?_, fun p hp => ⟨𝔭 p, fun v hv => ?_⟩, fun t P hP hS1 => ?_, fun t P hP h => ?_⟩, fun h => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, -, h⟩` from `hS v (by convert hv)`. Conclude with `(hw v p hp h).1`.

Take `⟨p, hp, hc, h⟩` from `hS v (by convert hv)`. Use `GlobalTheory.MovedIdem.exists_isIdemAt (w v) fun e => under_conjugatePrime_ne hp hc (w v) ((natCast_mem_under (M := D.host.F) (w v) p).1 (by rw [(hw v p hp h).1]; exact h)) ?_` and prove the remaining obligations. Rewrite using `[show conjPrime₂ (w v) = w v from HeightOneSpectrum.ext ((conjIdeal_asIdeal (w v)).symm.trans e)]`. Conclude with `(hL.Pg _).2 ⟨k, (hw v _ (D.host.g_prime k) hv).2.trans ((h𝔭 _ (D.host.g_prime k)).2.1 k rfl)⟩`. Conclude with `(hw v p (hde2 p hp).1 hv).2`.

Take `⟨q, hq', hqP, hne⟩` from `exists_prime_mem (hL.Q_pl t) hP`. Establish `hqv` using `(natCast_mem_under (M := D.host.F) P q).2 hqP`. Establish `h1 : q = D.host.pde ∨ q = D.host.pde'`. Break down `(S1_mem_OmF D).1 hS1 with h | h | h | h` into its components or cases. Conclude with `absurd (prime_eq_of_mem _ hq' (D.host.g_prime 0) hqv h) (hne 0)`.

Conclude with `absurd (prime_eq_of_mem _ hq' (D.host.g_prime 1) hqv h) (hne 1)`. Conclude with `Or.inl (prime_eq_of_mem _ hq' D.host.pde_prime hqv h)`. Conclude with `Or.inr (prime_eq_of_mem _ hq' D.host.pde'_prime hqv h)`. Take `⟨h2, h3⟩` from `hw _ q hq' hqv`. Break down `eq_or_eq_conjP h2 with h | h` into its components or cases.

Conclude with `h.symm`. It suffices to derive a contradiction. Apply `under_conjugatePrime_ne hq' (hde2 q h1).2 P hqP` to reduce the goal to its premises. Rewrite using `[← h, h3, (h𝔭 q hq').2.2 h1 t P hP hqP]`. Conclude with `hQ t P hP ((natCast_mem_under (M := D.host.F) P _).1 (h ▸ hv0))`.

Break down `(S1_mem_OmF D).1 h with h | h | h | h` into its components or cases. Conclude with `hq 0 (prime_eq_of_mem _ hq0 (D.host.g_prime 0) hv0 h)`. Conclude with `hq 1 (prime_eq_of_mem _ hq0 (D.host.g_prime 1) hv0 h)`. Conclude with `(leastSplitAuxiliaryPrime_ne_typePrimes D).1 (prime_eq_of_mem _ hq0 D.host.pde_prime hv0 h)`. Conclude with `(leastSplitAuxiliaryPrime_ne_typePrimes D).2 (prime_eq_of_mem _ hq0 D.host.pde'_prime hv0 h)`.
-/
theorem exists_places : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ k, D.host.g k % LevelStarExponents.condE D = 1) → D.host.pde % LevelStarExponents.condE D = 1 → D.host.pde' % LevelStarExponents.condE D = 1 → (∀ k, q0 D ≠ D.host.g k) → (∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ P : Places L, P.v0 ∉ S1 D := by
  classical
  intro D T L μ0 hL hg hde hde' hq hQ
  choose 𝔭 h𝔭 using exists_primes L hL
  obtain ⟨hq0, hq1, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hq2 : q0 D % LevelStarExponents.condE D = 1 := by
    have h1 : 1 < LevelStarExponents.condE D := by
      have h0 : 0 < LevelStarExponents.condE D := Nat.mul_pos (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos) D.host.hyp.2.1.pos
      have := Nat.mod_lt D.host.pde h0
      omega
    rw [← Nat.mod_mod_of_dvd _ (dvd_mul_left _ (Formalism.MainNotions.rPrAv D)), hq1, Nat.mod_eq_of_lt h1]
  obtain ⟨v0, hv0⟩ := exists_place D.host.F hq0
  have hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ w : HeightOneSpectrum (𝓞 D.host.E), ∀ p : ℕ, p.Prime →
      (p : 𝓞 D.host.F) ∈ v.asIdeal → w.under (𝓞 D.host.F) = v ∧ w.under (𝓞 D.host.K) = 𝔭 p := by
    intro v
    by_cases h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal
    · obtain ⟨p, hp, hv⟩ := h
      obtain ⟨w, hw⟩ := exists_over_both hp v hv (𝔭 p) (h𝔭 p hp).1
      exact ⟨w, fun p' hp' hv' => prime_eq_of_mem v hp hp' hv hv' ▸ hw⟩
    · obtain ⟨w, -⟩ := exists_place D.host.E hq0
      exact ⟨w, fun p hp hv => absurd ⟨p, hp, hv⟩ h⟩
  choose w hw using hw
  have hS : ∀ v ∈ insert v0 (S1 D), ∃ p : ℕ, p.Prime ∧ p % LevelStarExponents.condE D = 1 ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact ⟨_, hq0, hq2, hv0⟩
    · rcases (S1_mem_OmF D).1 hv with h | h | h | h
      · exact ⟨_, D.host.g_prime 0, hg 0, h⟩
      · exact ⟨_, D.host.g_prime 1, hg 1, h⟩
      · exact ⟨_, D.host.pde_prime, hde, h⟩
      · exact ⟨_, D.host.pde'_prime, hde', h⟩
  have hde2 : ∀ p : ℕ, p = D.host.pde ∨ p = D.host.pde' → p.Prime ∧ p % LevelStarExponents.condE D = 1 := by
    rintro p (rfl | rfl)
    · exact ⟨D.host.pde_prime, hde⟩
    · exact ⟨D.host.pde'_prime, hde'⟩
  refine ⟨⟨v0, hv0, w, fun v hv => ?_, fun v hv => ?_, fun v k hv => ?_, fun p hp => ⟨𝔭 p, fun v hv => ?_⟩,
    fun t P hP hS1 => ?_, fun t P hP h => ?_⟩, fun h => ?_⟩
  · obtain ⟨p, hp, -, h⟩ := hS v (by convert hv)
    exact (hw v p hp h).1
  · obtain ⟨p, hp, hc, h⟩ := hS v (by convert hv)
    refine GlobalTheory.MovedIdem.exists_isIdemAt (w v) fun e => under_conjugatePrime_ne hp hc (w v)
      ((natCast_mem_under (M := D.host.F) (w v) p).1 (by rw [(hw v p hp h).1]; exact h)) ?_
    rw [show conjPrime₂ (w v) = w v from HeightOneSpectrum.ext ((conjIdeal_asIdeal (w v)).symm.trans e)]
  · exact (hL.Pg _).2 ⟨k, (hw v _ (D.host.g_prime k) hv).2.trans ((h𝔭 _ (D.host.g_prime k)).2.1 k rfl)⟩
  · exact (hw v p (hde2 p hp).1 hv).2
  · obtain ⟨q, hq', hqP, hne⟩ := exists_prime_mem (hL.Q_pl t) hP
    have hqv := (natCast_mem_under (M := D.host.F) P q).2 hqP
    have h1 : q = D.host.pde ∨ q = D.host.pde' := by
      rcases (S1_mem_OmF D).1 hS1 with h | h | h | h
      · exact absurd (prime_eq_of_mem _ hq' (D.host.g_prime 0) hqv h) (hne 0)
      · exact absurd (prime_eq_of_mem _ hq' (D.host.g_prime 1) hqv h) (hne 1)
      · exact Or.inl (prime_eq_of_mem _ hq' D.host.pde_prime hqv h)
      · exact Or.inr (prime_eq_of_mem _ hq' D.host.pde'_prime hqv h)
    obtain ⟨h2, h3⟩ := hw _ q hq' hqv
    rcases eq_or_eq_conjP h2 with h | h
    · exact h.symm
    · exfalso
      apply under_conjugatePrime_ne hq' (hde2 q h1).2 P hqP
      rw [← h, h3, (h𝔭 q hq').2.2 h1 t P hP hqP]
  · exact hQ t P hP ((natCast_mem_under (M := D.host.F) P _).1 (h ▸ hv0))
  · rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact hq 0 (prime_eq_of_mem _ hq0 (D.host.g_prime 0) hv0 h)
    · exact hq 1 (prime_eq_of_mem _ hq0 (D.host.g_prime 1) hv0 h)
    · exact (leastSplitAuxiliaryPrime_ne_typePrimes D).1 (prime_eq_of_mem _ hq0 D.host.pde_prime hv0 h)
    · exact (leastSplitAuxiliaryPrime_ne_typePrimes D).2 (prime_eq_of_mem _ hq0 D.host.pde'_prime hv0 h)

end GlobalTheory.GridPlaces
