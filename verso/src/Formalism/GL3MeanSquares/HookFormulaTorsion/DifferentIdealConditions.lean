import Mathlib
import Formalism.GL3MeanSquares.OrbitPointsDistinct
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.DirichletDensity.HostDensityArith

namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

namespace PfN

section
open Ideal UniqueFactorizationMonoid

/- English proof (translation)
Establish `h1 : ∀ P ∈ (normalizedFactors I).map f, Prime P`. Introduce `P hP`. Take `⟨P', hP', rfl⟩` from `Multiset.mem_map.mp hP`. Conclude with `(MulEquiv.prime_iff f).mpr (prime_of_normalized_factor P' hP')`. Establish `h2 : ((normalizedFactors I).map f).prod = f I`.

Rewrite using `[← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]`. Establish `h3` using `normalizedFactors_prod_of_prime h1`. Rewrite `h3` using `[h2]`. Conclude with `h3`.
-/
theorem nf_map {S : Type*} [CommRing S] [IsDedekindDomain S] (I : Ideal S) (hI : I ≠ ⊥)
    (f : Ideal S ≃* Ideal S) : normalizedFactors (f I) = (normalizedFactors I).map f := by
  have h1 : ∀ P ∈ (normalizedFactors I).map f, Prime P := by
    intro P hP
    obtain ⟨P', hP', rfl⟩ := Multiset.mem_map.mp hP
    exact (MulEquiv.prime_iff f).mpr (prime_of_normalized_factor P' hP')
  have h2 : ((normalizedFactors I).map f).prod = f I := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
  have h3 := normalizedFactors_prod_of_prime h1
  rw [h2] at h3
  exact h3

/- English proof (translation)
Use `set F := normalizedFactors D with hF`. Establish `hprime : ∀ P ∈ F, Prime P` using `fun P hP => prime_of_normalized_factor P hP`. Establish `hFf : ∀ g : Ideal S ≃* Ideal S, g D = D → F.map g = F`. Introduce `g hg`. Rewrite using `[hF, ← nf_map D hD0 g, hg]`.

Establish `hmax : ∀ P ∈ F, P.IsMaximal`. Introduce `P hP`. Establish `hp` using `hprime P hP`. Conclude with `Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hp) (by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero)`. Use `⟨(F.filter p).prod, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hsplit : F.filter (fun P => ¬ p P) = (F.filter p).map f` using `by conv_lhs => rw [← hFf f hfD]`. Rewrite using `[Multiset.filter_map]`. Use `congr 1`. Apply `Multiset.filter_congr` to reduce the goal to its premises. Introduce `P hP`.

Simplify using `only [Function.comp_apply, hp P hP, not_not]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Multiset.prod_add, Multiset.filter_add_not]`. Use `_ = _ := by rw [hsplit, map_multiset_prod]`. Introduce `P hP hdvd`.

Take `⟨Q, hQ, hQP⟩` from `hP.multiset_prod_le.mp (Ideal.dvd_iff_le.mp hdvd)`. Rewrite `hQ` using `[Multiset.mem_filter]`. Rewrite using `[← (hmax Q hQ.1).eq_of_le hP.ne_top hQP]`. Conclude with `hQ.2`. Assume the negation of the conclusion as `hne`.

Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hMp` using `hM.isPrime`. Establish `h1 : (F.filter p).prod ≤ M` using `le_trans le_sup_left hle`. Establish `h2 : f (F.filter p).prod ≤ M` using `le_trans le_sup_right hle`. Rewrite `h2` using `[map_multiset_prod]`.

Take `⟨P, hP, hPM⟩` from `hMp.multiset_prod_le.mp h1`. Take `⟨Q, hQ, hQM⟩` from `hMp.multiset_prod_le.mp h2`. Take `⟨P', hP', rfl⟩` from `Multiset.mem_map.mp hQ`. Rewrite `hP`, `hP'` using `[Multiset.mem_filter]`. Establish `eqP : P = M` using `(hmax P hP.1).eq_of_le hM.ne_top hPM`.

Establish `hfP' : f P' ∈ F` using `by rw [← hFf f hfD]; exact Multiset.mem_map_of_mem f hP'.1`. Establish `eqQ : f P' = M` using `(hmax _ hfP').eq_of_le hM.ne_top hQM`. Use `(hp P' hP'.1).mp (by rw [eqQ, ← eqP]; exact hP.2)` as an intermediate fact. Conclude with `this hP'.2`. Introduce `g hg hpg`.

Rewrite using `[map_multiset_prod]`. Use `congr 1`. Use `conv_rhs => rw [← hFf g hg]`. Rewrite using `[Multiset.filter_map]`. Use `congr 1`.

Apply `Multiset.filter_congr` to reduce the goal to its premises. Introduce `P hP`. Simplify using `only [Function.comp_apply, hpg P hP]`. Introduce `B' hB' hpB'`. Establish `hB0 : B' ≠ ⊥`.

Introduce and unpack `rfl`. Apply `hD0` to reduce the goal to its premises. Rewrite using `[hB', ← Ideal.zero_eq_bot, zero_mul]`. Establish `hfB0 : f B' ≠ ⊥`. Introduce `h0`.

Apply `hD0` to reduce the goal to its premises. Rewrite using `[hB', h0, ← Ideal.zero_eq_bot, mul_zero]`. Establish `hsum : F = normalizedFactors B' + (normalizedFactors B').map f`. Rewrite using `[hF, hB', normalizedFactors_mul hB0 hfB0, nf_map B' hB0 f]`. Establish `hall : ∀ P ∈ normalizedFactors B', p P`.

Introduce `P hP`. Conclude with `hpB' P (Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)) (dvd_of_mem_normalizedFactors hP)`. Establish `e1 : (normalizedFactors B').filter p = normalizedFactors B'` using `Multiset.filter_eq_self.mpr hall`. Establish `e2 : ((normalizedFactors B').map f).filter p = 0`. Rewrite using `[Multiset.filter_eq_nil]`.

Introduce `Q hQ`. Take `⟨P, hP, rfl⟩` from `Multiset.mem_map.mp hQ`. Establish `hPF : P ∈ F` using `by rw [hsum]; exact Multiset.mem_add.mpr (Or.inl hP)`. Rewrite using `[hp P hPF, not_not]`. Conclude with `hall P hP`.

Rewrite using `[hsum, Multiset.filter_add, e1, e2, add_zero, Ideal.prod_normalizedFactors_eq_self hB0]`.
-/
theorem idealConjugateFactorizationUnique {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (p : Ideal S → Prop)
    (hp : ∀ P ∈ normalizedFactors D, (p (f P) ↔ ¬ p P)) :
    ∃ B : Ideal S, D = B * f B ∧ (∀ P : Ideal S, P.IsPrime → P ∣ B → p P) ∧ B ⊔ f B = ⊤ ∧
      (∀ g : Ideal S ≃* Ideal S, g D = D → (∀ P ∈ normalizedFactors D, (p (g P) ↔ p P)) → g B = B) ∧
      ∀ B' : Ideal S, D = B' * f B' → (∀ P : Ideal S, P.IsPrime → P ∣ B' → p P) → B' = B := by
  classical
  set F := normalizedFactors D with hF
  have hprime : ∀ P ∈ F, Prime P := fun P hP => prime_of_normalized_factor P hP
  have hFf : ∀ g : Ideal S ≃* Ideal S, g D = D → F.map g = F := by
    intro g hg
    rw [hF, ← nf_map D hD0 g, hg]
  have hmax : ∀ P ∈ F, P.IsMaximal := by
    intro P hP
    have hp := hprime P hP
    exact Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hp)
      (by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero)
  refine ⟨(F.filter p).prod, ?_, ?_, ?_, ?_, ?_⟩
  · have hsplit : F.filter (fun P => ¬ p P) = (F.filter p).map f := by
      conv_lhs => rw [← hFf f hfD]
      rw [Multiset.filter_map]
      congr 1
      apply Multiset.filter_congr
      intro P hP
      simp only [Function.comp_apply, hp P hP, not_not]
    calc D = F.prod := (Ideal.prod_normalizedFactors_eq_self hD0).symm
      _ = (F.filter p).prod * (F.filter (fun P => ¬ p P)).prod := by
          rw [← Multiset.prod_add, Multiset.filter_add_not]
      _ = _ := by rw [hsplit, map_multiset_prod]
  · intro P hP hdvd
    obtain ⟨Q, hQ, hQP⟩ := hP.multiset_prod_le.mp (Ideal.dvd_iff_le.mp hdvd)
    rw [Multiset.mem_filter] at hQ
    rw [← (hmax Q hQ.1).eq_of_le hP.ne_top hQP]
    exact hQ.2
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMp := hM.isPrime
    have h1 : (F.filter p).prod ≤ M := le_trans le_sup_left hle
    have h2 : f (F.filter p).prod ≤ M := le_trans le_sup_right hle
    rw [map_multiset_prod] at h2
    obtain ⟨P, hP, hPM⟩ := hMp.multiset_prod_le.mp h1
    obtain ⟨Q, hQ, hQM⟩ := hMp.multiset_prod_le.mp h2
    obtain ⟨P', hP', rfl⟩ := Multiset.mem_map.mp hQ
    rw [Multiset.mem_filter] at hP hP'
    have eqP : P = M := (hmax P hP.1).eq_of_le hM.ne_top hPM
    have hfP' : f P' ∈ F := by rw [← hFf f hfD]; exact Multiset.mem_map_of_mem f hP'.1
    have eqQ : f P' = M := (hmax _ hfP').eq_of_le hM.ne_top hQM
    have := (hp P' hP'.1).mp (by rw [eqQ, ← eqP]; exact hP.2)
    exact this hP'.2
  · intro g hg hpg
    rw [map_multiset_prod]
    congr 1
    conv_rhs => rw [← hFf g hg]
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro P hP
    simp only [Function.comp_apply, hpg P hP]
  · intro B' hB' hpB'
    have hB0 : B' ≠ ⊥ := by
      rintro rfl
      apply hD0
      rw [hB', ← Ideal.zero_eq_bot, zero_mul]
    have hfB0 : f B' ≠ ⊥ := by
      intro h0
      apply hD0
      rw [hB', h0, ← Ideal.zero_eq_bot, mul_zero]
    have hsum : F = normalizedFactors B' + (normalizedFactors B').map f := by
      rw [hF, hB', normalizedFactors_mul hB0 hfB0, nf_map B' hB0 f]
    have hall : ∀ P ∈ normalizedFactors B', p P := by
      intro P hP
      exact hpB' P (Ideal.isPrime_of_prime (prime_of_normalized_factor P hP))
        (dvd_of_mem_normalizedFactors hP)
    have e1 : (normalizedFactors B').filter p = normalizedFactors B' :=
      Multiset.filter_eq_self.mpr hall
    have e2 : ((normalizedFactors B').map f).filter p = 0 := by
      rw [Multiset.filter_eq_nil]
      intro Q hQ
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hQ
      have hPF : P ∈ F := by rw [hsum]; exact Multiset.mem_add.mpr (Or.inl hP)
      rw [hp P hPF, not_not]
      exact hall P hP
    rw [hsum, Multiset.filter_add, e1, e2, add_zero, Ideal.prod_normalizedFactors_eq_self hB0]

end

section
open Ideal NumberField Polynomial

/- English proof (translation)
Establish `hdisc : discr K = -(d : ℤ)` using `Formalism.HF.Final.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)`. Establish `hN : (differentIdeal ℤ (𝓞 K)).absNorm = d`. Rewrite using `[absNorm_differentIdeal K, hdisc]`. Simplify using the standard rewrite rules. Establish `hβ2 : β ^ 2 = -(d : 𝓞 K)`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `: ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2` using `by push_cast; rfl`. Rewrite using `[this, hβ, hx]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤`. Establish `h1 : IsAlgebraic ℚ x` using `Algebra.IsAlgebraic.isAlgebraic x`. Establish `h2` using `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1`. Rewrite `h2` using `[hadj]`. Use `show Algebra.adjoin ℚ {(β : K)} = ⊤`.

Rewrite using `[hβ, ← h2]`. Both sides reduce to the same expression. Establish `hmem` using `aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'`. Establish `hint : IsIntegral ℤ β` using `Algebra.IsIntegral.isIntegral β`. Take `⟨r, hr⟩` from `minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ)) (by simp [hβ2])`.

Establish `h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K)`. Use `congrArg (fun p => aeval β (derivative p)) hr` as an intermediate fact. Simplify using `only [derivative_X_pow, derivative_C, derivative_mul, map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at this`. Establish `e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r`. Rewrite using `[← this]`.

Simplify using `[map_ofNat]`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ hmem`. Establish `hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K)`. Use `Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))` as an intermediate fact.

Rewrite `this` using `[hN]`. Then use the resulting hypothesis. Establish `hβmem : β ∈ differentIdeal ℤ (𝓞 K)`. Establish `e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β)`. Establish `h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1`. Establish `: d = 2 * (d / 2) + 1` using `by omega`.

Conclude with `this` after adjusting the coercions. Take the linear combination `(-β) * h`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)`. Establish `hle : span {β} ≤ differentIdeal ℤ (𝓞 K)`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hβmem`. Take `⟨C, hC⟩` from `Ideal.dvd_iff_le.mpr hle`. Establish `hrank : Module.finrank ℚ K = 2`. Use `Formalism.FrobeniusOrbits.SplitK.finrank_K (L := K) (b := x) hd.pos hx` as an intermediate fact.

Unfold `Formalism.FrobeniusOrbits.Kd at this`. Rewrite `this` using `[hadj, IntermediateField.finrank_top']`. Conclude with `this`. Establish `hNβ : (span {β}).absNorm ^ 2 = d ^ 2`. Rewrite using `[← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]`.

Establish `: (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ))` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]`. Simplify using `[Int.natAbs_pow]`. Establish `hNβ' : (span {β}).absNorm = d`. Conclude with `Nat.pow_left_injective (n := 2) (by norm_num) hNβ`.

Establish `hC1 : C.absNorm = 1`. Use `congrArg Ideal.absNorm hC` as an intermediate fact. Rewrite `this` using `[map_mul, hNβ', hN]`. Conclude with `Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)`. Rewrite `hC1` using `[Ideal.absNorm_eq_one_iff]`.

Rewrite using `[hC, hC1, Ideal.mul_top]`.
-/
theorem diffQuad (K : Type) [Field K] [NumberField K] (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤)
    (β : 𝓞 K) (hβ : (β : K) = x) : differentIdeal ℤ (𝓞 K) = span {β} := by
  have hdisc : discr K = -(d : ℤ) :=
    Formalism.HF.Final.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj
      ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)
  have hN : (differentIdeal ℤ (𝓞 K)).absNorm = d := by
    rw [absNorm_differentIdeal K, hdisc]; simp
  have hβ2 : β ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.ext
    have : ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2 := by push_cast; rfl
    rw [this, hβ, hx]
    push_cast; rfl
  have hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤ := by
    have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1
    rw [hadj] at h2
    show Algebra.adjoin ℚ {(β : K)} = ⊤
    rw [hβ, ← h2]
    rfl
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'
  have hint : IsIntegral ℤ β := Algebra.IsIntegral.isIntegral β
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ))
    (by simp [hβ2])
  have h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K) := by
    have := congrArg (fun p => aeval β (derivative p)) hr
    simp only [derivative_X_pow, derivative_C, derivative_mul, map_add, map_mul,
      minpoly.aeval, zero_mul, add_zero] at this
    have e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r := by
      rw [← this]; simp [map_ofNat]
    rw [e]
    exact Ideal.mul_mem_right _ _ hmem
  have hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    have := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))
    rwa [hN] at this
  have hβmem : β ∈ differentIdeal ℤ (𝓞 K) := by
    have e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β) := by
      have h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1 := by
        have : d = 2 * (d / 2) + 1 := by omega
        exact_mod_cast this
      linear_combination (-β) * h
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)
  have hle : span {β} ≤ differentIdeal ℤ (𝓞 K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hβmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hrank : Module.finrank ℚ K = 2 := by
    have := Formalism.FrobeniusOrbits.SplitK.finrank_K (L := K) (b := x) hd.pos hx
    unfold Formalism.FrobeniusOrbits.Kd at this
    rw [hadj, IntermediateField.finrank_top'] at this
    exact this
  have hNβ : (span {β}).absNorm ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]
    have : (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ)) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
    simp [Int.natAbs_pow]
  have hNβ' : (span {β}).absNorm = d := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) hNβ
  have hC1 : C.absNorm = 1 := by
    have := congrArg Ideal.absNorm hC
    rw [map_mul, hNβ', hN] at this
    exact Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)
  rw [Ideal.absNorm_eq_one_iff] at hC1
  rw [hC, hC1, Ideal.mul_top]

end

section
open NumberField IntermediateField Ideal
open scoped Pointwise

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/- English proof (translation)
Introduce `e q d hH L _ _ ζ a b h`. Establish `hsq : bE ζ a b ^ 2 = -(d : hostE ζ a b)` using `DiscrB.bE_sq h`. Set `x : KinE ζ a b` to `⟨bE ζ a b, Principal.bE_mem_KinE ζ a b⟩`. Establish `hx : x ^ 2 = -(d : KinE ζ a b)`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify `hsq` using `[x]`. Establish `hint : IsIntegral ℤ x`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hx]`. Conclude with `(isIntegral_natCast d).neg`.

Establish `hadj : IntermediateField.adjoin ℚ {x} = ⊤`. Apply `Formalism.HF.P.adjoin_top_of_lift` to reduce the goal to its premises. Rewrite using `[Set.image_singleton]`. Both sides reduce to the same expression. Take `⟨β, hβ⟩ : ∃ β : 𝓞 (KinE ζ a b), (β : KinE ζ a b) = x` from `⟨⟨x, hint⟩, rfl⟩`.

Establish `hK` using `diffQuad (KinE ζ a b) d hH.2.1 (by have := hH.2.2.2.1; omega) x hx hadj β hβ`. Use `⟨algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) β, ?_, ?_⟩` and prove the remaining obligations. Use `show (((β : KinE ζ a b)) : hostE ζ a b) = bE ζ a b`. Rewrite using `[hβ]`. Rewrite using `[differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)), hK, Ideal.map_span, Set.image_singleton]`.
-/
theorem diffAbs : DiffAbs := by
  intro e q d hH L _ _ ζ a b h
  have hsq : bE ζ a b ^ 2 = -(d : hostE ζ a b) := DiscrB.bE_sq h
  let x : KinE ζ a b := ⟨bE ζ a b, Principal.bE_mem_KinE ζ a b⟩
  have hx : x ^ 2 = -(d : KinE ζ a b) := by
    apply Subtype.ext
    simpa [x] using hsq
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx]
    exact (isIntegral_natCast d).neg
  have hadj : IntermediateField.adjoin ℚ {x} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
    rfl
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 (KinE ζ a b), (β : KinE ζ a b) = x := ⟨⟨x, hint⟩, rfl⟩
  have hK := diffQuad (KinE ζ a b) d hH.2.1 (by have := hH.2.2.2.1; omega) x hx hadj β hβ
  refine ⟨algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) β, ?_, ?_⟩
  · show (((β : KinE ζ a b)) : hostE ζ a b) = bE ζ a b
    rw [hβ]
  · rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)),
      hK, Ideal.map_span, Set.image_singleton]

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (translation)
Rewrite `hσ` using `[galE_mem_Psi_iff]`. Establish `: (σ : hostE ζ a b →ₐ[ℚ] hostE ζ a b).comp (KinE ζ a b).val = (KinE ζ a b).val`. Use `algHom_ext_of_eq_adjoin ℚ (S := KinE ζ a b) (s := {bE ζ a b}) rfl ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`.

Substitute `hy` using the available equality. Conclude with `hσ`. Conclude with `DFunLike.congr_fun this x`.
-/
theorem fixK (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ ∈ Psi e)
    (x : KinE ζ a b) : σ (x : hostE ζ a b) = x := by
  rw [galE_mem_Psi_iff] at hσ
  have : (σ : hostE ζ a b →ₐ[ℚ] hostE ζ a b).comp (KinE ζ a b).val = (KinE ζ a b).val := by
    refine algHom_ext_of_eq_adjoin ℚ (S := KinE ζ a b) (s := {bE ζ a b}) rfl ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hσ
  exact DFunLike.congr_fun this x

abbrev cm (P : Ideal (𝓞 (hostE ζ a b))) : Ideal (𝓞 (KinE ζ a b)) :=
  P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)))

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `: σ⁻¹ • algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) x = algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `fixK (e := e) σ⁻¹ (by rw [galE_inv hqd h]; exact (Psi e).inv_mem hσ) (x : KinE ζ a b)`.

Rewrite using `[this]`.
-/
theorem cm_smul (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ ∈ Psi e)
    (P : Ideal (𝓞 (hostE ζ a b))) : cm (σ • P) = cm P := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) x =
      algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) x := by
    apply RingOfIntegers.ext
    exact fixK (e := e) σ⁻¹ (by rw [galE_inv hqd h]; exact (Psi e).inv_mem hσ) (x : KinE ζ a b)
  rw [this]

/- English proof (translation)
The claim follows from `map_intCast (MulSemiringAction.toRingHom _ (𝓞 (hostE ζ a b)) σ) n`.
-/
theorem smul_int (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (n : ℤ) :
    σ • (n : 𝓞 (hostE ζ a b)) = n :=
  map_intCast (MulSemiringAction.toRingHom _ (𝓞 (hostE ζ a b)) σ) n

/- English proof (translation)
Rewrite using `[← smul_int σ n]`. Conclude with `Ideal.smul_mem_pointwise_smul σ _ P hn`.
-/
theorem int_mem_smul (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (n : ℤ) (P : Ideal (𝓞 (hostE ζ a b)))
    (hn : (n : 𝓞 (hostE ζ a b)) ∈ P) : (n : 𝓞 (hostE ζ a b)) ∈ σ • P := by
  rw [← smul_int σ n]
  exact Ideal.smul_mem_pointwise_smul σ _ P hn

/- English proof (translation)
Rewrite `hn` using `[← hP, Ideal.mem_comap, map_intCast]`. Conclude with `hn`.
-/
theorem int_mem_of_cm (P : Ideal (𝓞 (hostE ζ a b))) (𝔭 : Ideal (𝓞 (KinE ζ a b))) (hP : cm P = 𝔭)
    (n : ℤ) (hn : (n : 𝓞 (KinE ζ a b)) ∈ 𝔭) : (n : 𝓞 (hostE ζ a b)) ∈ P := by
  rw [← hP, Ideal.mem_comap, map_intCast] at hn
  exact hn

/- English proof (translation)
Establish `hq2 : Nat.Coprime q (2 ^ (e + 2))`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Rewrite using `[Nat.coprime_two_right, Nat.odd_iff]`. Use `hH.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hd2 : Nat.Coprime d (2 ^ (e + 2))`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Rewrite using `[Nat.coprime_two_right, Nat.odd_iff]`. Use `hH.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hD` using `hostDecomp e q d hH L ζ a b h (ZMod.unitOfCoprime q hq2) (ZMod.unitOfCoprime d hd2) (by simp) (by simp) σ`. Establish `hst : σ ∈ MulAction.stabilizer _ P` using `hσ`. Break down `hr with rfl | rfl` into its components or cases. Establish `: P.LiesOver (span {(2 : ℤ)})`. Use `liesOver_span_of_natCast_mem_frobenius_orbits P 2 Nat.prime_two hm` as an intermediate fact.

Simplify using `using this`. Conclude with `(hD.1 P).mp hst`. Establish `: P.LiesOver (span {(r : ℤ)})` using `liesOver_span_of_natCast_mem_frobenius_orbits P r hH.1 hm`. Rewrite using `[mem_Psi_iff]`. Conclude with `((hD.2.1 P).mp hst).1`.
-/
theorem stab_Psi (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b) (r : ℕ) (hr : r = 2 ∨ r = q)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : σ • P = P) : galE e ζ a b σ ∈ Psi e := by
  have hq2 : Nat.Coprime q (2 ^ (e + 2)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right, Nat.odd_iff]
    have := hH.2.2.1; omega
  have hd2 : Nat.Coprime d (2 ^ (e + 2)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right, Nat.odd_iff]
    have := hH.2.2.2.1; omega
  have hD := hostDecomp e q d hH L ζ a b h (ZMod.unitOfCoprime q hq2) (ZMod.unitOfCoprime d hd2)
    (by simp) (by simp) σ
  have hst : σ ∈ MulAction.stabilizer _ P := hσ
  rcases hr with rfl | rfl
  · have : P.LiesOver (span {(2 : ℤ)}) := by
      have := liesOver_span_of_natCast_mem_frobenius_orbits P 2 Nat.prime_two hm
      simpa using this
    exact (hD.1 P).mp hst
  · have : P.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P r hH.1 hm
    rw [mem_Psi_iff]
    exact ((hD.2.1 P).mp hst).1

/- English proof (translation)
Rewrite using `[mem_Psi_iff]`. Simplify using `[cc, c0]`.
-/
theorem cc_not_mem (e : ℕ) : cc e ∉ Psi e := by
  rw [mem_Psi_iff]
  simp [cc, c0]

/- English proof (translation)
Establish `hqd` using `hH.toHypOdd`. Establish `hEgal : IsGalois ℚ (hostE ζ a b)` using `hostE_isGalois hqd h`. Establish `hKgal : IsGalois (KinE ζ a b) (hostE ζ a b)` using `IsGalois.tower_top_of_isGalois ℚ _ _`. Establish `: IsGaloisGroup (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))` using `IsGaloisGroup.of_isFractionRing _ _ _ (KinE ζ a b) (hostE ζ a b)`. Establish `l1 : P.LiesOver 𝔭` using `⟨h1.symm⟩`.

Establish `l2 : (c • P).LiesOver 𝔭` using `⟨h2.symm⟩`. Take `⟨τ, hτ⟩` from `exists_smul_eq_of_isGaloisGroup 𝔭 P (c • P) (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)`. Establish `hτ' : (τ.restrictScalars ℚ) • P = c • P` using `hτ`. Establish `hfix : ((τ.restrictScalars ℚ)⁻¹ * c) • P = P`. Rewrite using `[mul_smul, ← hτ', inv_smul_smul]`.

Establish `hmem` using `stab_Psi hH h r hr P hm _ hfix`. Rewrite `hmem` using `[galE_mul hqd h, galE_inv hqd h, hc]`. Establish `hτΨ` using `Principal.galE_restrict_mem_Psi (e := e) τ`. Use `(Psi e).mul_mem hτΨ hmem` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`.

Conclude with `cc_not_mem e this`.
-/
theorem not_cm_eq_of_conj_smul_prime (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ)
    (hr : r = 2 ∨ r = q) (𝔭 : Ideal (𝓞 (KinE ζ a b)))
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P)
    (h1 : cm P = 𝔭) (h2 : cm (c • P) = 𝔭) : False := by
  have hqd := hH.toHypOdd
  have hEgal : IsGalois ℚ (hostE ζ a b) := hostE_isGalois hqd h
  have hKgal : IsGalois (KinE ζ a b) (hostE ζ a b) := IsGalois.tower_top_of_isGalois ℚ _ _
  have : IsGaloisGroup (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) (𝓞 (KinE ζ a b))
      (𝓞 (hostE ζ a b)) := IsGaloisGroup.of_isFractionRing _ _ _ (KinE ζ a b) (hostE ζ a b)
  have l1 : P.LiesOver 𝔭 := ⟨h1.symm⟩
  have l2 : (c • P).LiesOver 𝔭 := ⟨h2.symm⟩
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isGaloisGroup 𝔭 P (c • P)
    (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)
  have hτ' : (τ.restrictScalars ℚ) • P = c • P := hτ
  have hfix : ((τ.restrictScalars ℚ)⁻¹ * c) • P = P := by
    rw [mul_smul, ← hτ', inv_smul_smul]
  have hmem := stab_Psi hH h r hr P hm _ hfix
  rw [galE_mul hqd h, galE_inv hqd h, hc] at hmem
  have hτΨ := Principal.galE_restrict_mem_Psi (e := e) τ
  have := (Psi e).mul_mem hτΨ hmem
  rw [mul_inv_cancel_left] at this
  exact cc_not_mem e this

/- English proof (translation)
Establish `hqd` using `hH.toHypOdd`. Establish `hEgal : IsGalois ℚ (hostE ζ a b)` using `hostE_isGalois hqd h`. Establish `: IsGaloisGroup (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) ℤ (𝓞 (hostE ζ a b))` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostE ζ a b)`. Take `⟨P₀, -, hP₀, hcm⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal (𝓞 (hostE ζ a b))) (by simp [← RingHom.ker_eq_comap_bot])`. Establish `hm₀` using `int_mem_of_cm P₀ 𝔭 hcm r hm𝔭`.

Establish `l0 : P₀.LiesOver (span {(r : ℤ)})` using `liesOver_span_of_natCast_mem_frobenius_orbits P₀ r hr hm₀`. Establish `l1 : P.LiesOver (span {(r : ℤ)})` using `liesOver_span_of_natCast_mem_frobenius_orbits P r hr hm`. Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isGaloisGroup (span {(r : ℤ)}) P₀ P (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)`. Distinguish the cases in `hΨ : galE e ζ a b σ ∈ Psi e`. Use `left`.

Rewrite using `[← hσ, cm_smul hqd h σ hΨ]`. Conclude with `hcm`. Use `right`. Rewrite using `[← hσ, ← mul_smul, cm_smul hqd h (c * σ) ?_]`. Conclude with `hcm`.

Rewrite using `[galE_mul hqd h, hc, mem_Psi_iff]`. Rewrite `hΨ` using `[mem_Psi_iff]`. Break down `Int.units_eq_one_or (galE e ζ a b σ).1.2 with h1 | h1` into its components or cases. Conclude with `absurd h1 hΨ`. Simplify using `[cc, c0, h1]`.
-/
theorem atLeast (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ) (hr : r.Prime)
    (𝔭 : Ideal (𝓞 (KinE ζ a b))) [𝔭.IsPrime] (hm𝔭 : ((r : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm P = 𝔭 ∨ cm (c • P) = 𝔭 := by
  have hqd := hH.toHypOdd
  have hEgal : IsGalois ℚ (hostE ζ a b) := hostE_isGalois hqd h
  have : IsGaloisGroup (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) ℤ (𝓞 (hostE ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostE ζ a b)
  obtain ⟨P₀, -, hP₀, hcm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭
    (⊥ : Ideal (𝓞 (hostE ζ a b))) (by simp [← RingHom.ker_eq_comap_bot])
  have hm₀ := int_mem_of_cm P₀ 𝔭 hcm r hm𝔭
  have l0 : P₀.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P₀ r hr hm₀
  have l1 : P.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P r hr hm
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup (span {(r : ℤ)}) P₀ P
    (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
  by_cases hΨ : galE e ζ a b σ ∈ Psi e
  · left
    rw [← hσ, cm_smul hqd h σ hΨ]; exact hcm
  · right
    rw [← hσ, ← mul_smul, cm_smul hqd h (c * σ) ?_]
    · exact hcm
    rw [galE_mul hqd h, hc, mem_Psi_iff]
    rw [mem_Psi_iff] at hΨ
    rcases Int.units_eq_one_or (galE e ζ a b σ).1.2 with h1 | h1
    · exact absurd h1 hΨ
    · simp [cc, c0, h1]

/- English proof (translation)
Establish `hrp : r.Prime`. Break down `hr with rfl | rfl` into its components or cases. Conclude with `Nat.prime_two`. Conclude with `hH.1`. Prove the components needed by the constructor for the conclusion.

Introduce `h2 h1`. Conclude with `not_cm_eq_of_conj_smul_prime hH h c hc r hr 𝔭 P hm h1 h2`. Introduce `h1`. Conclude with `(atLeast hH h c hc r hrp 𝔭 hm𝔭 P hm).resolve_left h1`.
-/
theorem key (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ) (hr : r = 2 ∨ r = q)
    (𝔭 : Ideal (𝓞 (KinE ζ a b))) [𝔭.IsPrime] (hm𝔭 : ((r : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm (c • P) = 𝔭 ↔ ¬ cm P = 𝔭 := by
  have hrp : r.Prime := by
    rcases hr with rfl | rfl
    · exact Nat.prime_two
    · exact hH.1
  constructor
  · intro h2 h1
    exact not_cm_eq_of_conj_smul_prime hH h c hc r hr 𝔭 P hm h1 h2
  · intro h1
    exact (atLeast hH h c hc r hrp 𝔭 hm𝔭 P hm).resolve_left h1

/- English proof (translation)
Introduce `h1`. Establish `hs'` using `int_mem_of_cm P 𝔭 h1 s hs`. Take `⟨u, v, huv⟩` from `(Nat.isCoprime_iff_coprime.mpr hrs)`. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`.

Establish `: (1 : 𝓞 (hostE ζ a b)) = (u : 𝓞 (hostE ζ a b)) * ((r : ℤ) : 𝓞 (hostE ζ a b)) + (v : 𝓞 (hostE ζ a b)) * ((s : ℤ) : 𝓞 (hostE ζ a b))`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 (hostE ζ a b)) huv.symm` after adjusting the coercions. Rewrite using `[this]`. Conclude with `P.add_mem (P.mul_mem_left _ hm) (P.mul_mem_left _ hs')`.
-/
theorem excl (r s : ℕ) (hrs : Nat.Coprime r s) (𝔭 : Ideal (𝓞 (KinE ζ a b)))
    (hs : ((s : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [hP : P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm P ≠ 𝔭 := by
  intro h1
  have hs' := int_mem_of_cm P 𝔭 h1 s hs
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hrs)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have : (1 : 𝓞 (hostE ζ a b)) = (u : 𝓞 (hostE ζ a b)) * ((r : ℤ) : 𝓞 (hostE ζ a b)) +
      (v : 𝓞 (hostE ζ a b)) * ((s : ℤ) : 𝓞 (hostE ζ a b)) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 (hostE ζ a b)) huv.symm
  rw [this]
  exact P.add_mem (P.mul_mem_left _ hm) (P.mul_mem_left _ hs')

/- English proof (translation)
Introduce `e q d hH L _ _ ζ a b h c hc 𝔭₂ 𝔭q h𝔭₂ h𝔭q h2 hq`. Establish `hqd` using `hH.toHypOdd`. Establish `hD0 : differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ≠ ⊥`. Use `differentIdeal_ne_bot (A := 𝓞 (KinE ζ a b)) (B := 𝓞 (hostE ζ a b))` as an intermediate fact. Conclude with `this`.

Set `f : (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) → (Ideal (𝓞 (hostE ζ a b)) ≃* Ideal (𝓞 (hostE ζ a b)))` to `fun σ => (MulSemiringAction.toRingEquiv (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (Ideal (𝓞 (hostE ζ a b))) σ).toMulEquiv`. Establish `hf : ∀ σ I, f σ I = σ • I` using `fun σ I => rfl`. Establish `hcop : Nat.Coprime 2 q`. Rewrite using `[Nat.coprime_two_left, Nat.odd_iff]`. Use `hH.2.2.1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨B, hB1, hB2, hB3, hB4, hB5⟩` from `idealConjugateFactorizationUnique _ hD0 (f c) (by rw [hf]; exact Principal.diff_smul_eq hqd h c) (fun P => cm P = 𝔭₂ ∨ cm P = 𝔭q) (by`. Introduce `P hP`. Rewrite using `[hf]`. Rewrite `hP` using `[Ideal.mem_normalizedFactors_iff hD0]`.

Take `⟨hPp, hle⟩` from `hP`. Establish `hdvd : P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))` using `Ideal.dvd_iff_le.mpr hle`. Break down `hostDiffSupport e q d hH L ζ a b h P hPp hdvd with hm | hm` into its components or cases. Establish `hm' : (((2 : ℕ) : ℤ) : 𝓞 (hostE ζ a b)) ∈ P` using `by exact_mod_cast hm`. Establish `h2' : (((2 : ℕ) : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂` using `by exact_mod_cast h2`.

Rewrite using `[or_iff_left (excl 2 q hcop 𝔭q hq (c • P) (int_mem_smul c _ P hm')), or_iff_left (excl 2 q hcop 𝔭q hq P hm')]`. Conclude with `key hH h c hc 2 (Or.inl rfl) 𝔭₂ h2' P hm'`. Establish `h2' : (((2 : ℕ) : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂` using `by exact_mod_cast h2`. Rewrite using `[or_iff_right (excl q 2 hcop.symm 𝔭₂ h2' (c • P) (int_mem_smul c _ P hm)), or_iff_right (excl q 2 hcop.symm 𝔭₂ h2' P hm)]`. Conclude with `key hH h c hc q (Or.inr rfl) 𝔭q hq P hm)`.

Use `⟨B, hB1, hB2, hB3, ?_, hB5⟩` and prove the remaining obligations. Introduce `σ hσ`. Use `hB4 (f σ) (by rw [hf]; exact Principal.diff_smul_eq hqd h σ) ?_` and prove the remaining obligations. Introduce `P _`. Rewrite using `[hf, cm_smul hqd h σ hσ]`.
-/
theorem principalStable : PrincipalStable := by
  intro e q d hH L _ _ ζ a b h c hc 𝔭₂ 𝔭q h𝔭₂ h𝔭q h2 hq
  have hqd := hH.toHypOdd
  have hD0 : differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ≠ ⊥ := by
    have := differentIdeal_ne_bot (A := 𝓞 (KinE ζ a b)) (B := 𝓞 (hostE ζ a b))
    exact this
  let f : (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) → (Ideal (𝓞 (hostE ζ a b)) ≃* Ideal (𝓞 (hostE ζ a b))) :=
    fun σ => (MulSemiringAction.toRingEquiv (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
      (Ideal (𝓞 (hostE ζ a b))) σ).toMulEquiv
  have hf : ∀ σ I, f σ I = σ • I := fun σ I => rfl
  have hcop : Nat.Coprime 2 q := by
    rw [Nat.coprime_two_left, Nat.odd_iff]
    have := hH.2.2.1; omega
  obtain ⟨B, hB1, hB2, hB3, hB4, hB5⟩ := idealConjugateFactorizationUnique _ hD0 (f c)
    (by rw [hf]; exact Principal.diff_smul_eq hqd h c)
    (fun P => cm P = 𝔭₂ ∨ cm P = 𝔭q)
    (by
      intro P hP
      rw [hf]
      rw [Ideal.mem_normalizedFactors_iff hD0] at hP
      obtain ⟨hPp, hle⟩ := hP
      have hdvd : P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := Ideal.dvd_iff_le.mpr hle
      rcases hostDiffSupport e q d hH L ζ a b h P hPp hdvd with hm | hm
      · have hm' : (((2 : ℕ) : ℤ) : 𝓞 (hostE ζ a b)) ∈ P := by exact_mod_cast hm
        have h2' : (((2 : ℕ) : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ := by exact_mod_cast h2
        rw [or_iff_left (excl 2 q hcop 𝔭q hq (c • P) (int_mem_smul c _ P hm')),
          or_iff_left (excl 2 q hcop 𝔭q hq P hm')]
        exact key hH h c hc 2 (Or.inl rfl) 𝔭₂ h2' P hm'
      · have h2' : (((2 : ℕ) : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ := by exact_mod_cast h2
        rw [or_iff_right (excl q 2 hcop.symm 𝔭₂ h2' (c • P) (int_mem_smul c _ P hm)),
          or_iff_right (excl q 2 hcop.symm 𝔭₂ h2' P hm)]
        exact key hH h c hc q (Or.inr rfl) 𝔭q hq P hm)
  refine ⟨B, hB1, hB2, hB3, ?_, hB5⟩
  intro σ hσ
  refine hB4 (f σ) (by rw [hf]; exact Principal.diff_smul_eq hqd h σ) ?_
  intro P _
  rw [hf, cm_smul hqd h σ hσ]

end

end PfN

/- English proof (translation)
The claim follows from `PfN.diffAbs`.
-/
theorem difference_absolute_bound : DiffAbs := PfN.diffAbs
/- English proof (translation)
The claim follows from `PfN.principalStable`.
-/
theorem principal_part_stable : PrincipalStable := PfN.principalStable

end Formalism.HermitianLattices.FiltrationBoundaryCriterion
