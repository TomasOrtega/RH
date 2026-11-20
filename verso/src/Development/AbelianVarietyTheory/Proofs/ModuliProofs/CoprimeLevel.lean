import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmGeneratorSqQuadraticEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

/- English proof (translation)
Use `haveI : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩`. Take `⟨n, hn, hp, hmod⟩` from `Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * d) (a := -1) isUnit_one.neg (max b d)`. Establish `hdvd : 4 * d ∣ n + 1`. Rewrite using `[← ZMod.natCast_eq_zero_iff]`. Use `push_cast`.

Rewrite using `[hmod]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : n % 4 = 3`. Establish `: 4 ∣ n + 1` using `Dvd.dvd.trans (Dvd.intro _ rfl) hdvd`. Use linear arithmetic over natural numbers and integers.

Establish `hdn : (n : ZMod d) = -1`. Establish `: d ∣ n + 1` using `Dvd.dvd.trans (Dvd.intro_left _ rfl) hdvd`. Rewrite `this` using `[← ZMod.natCast_eq_zero_iff]`. Move the coercions through the operations in `at this`. Conclude with `eq_neg_of_add_eq_zero_left this`.

Establish `hlt : d < n` using `lt_of_le_of_lt (le_max_right _ _) hn`. Use `haveI : Fact n.Prime := ⟨hp⟩`. Use `haveI : Fact d.Prime := ⟨hd⟩`. Use `⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, by rw [Nat.odd_iff]; omega, ?_⟩` and prove the remaining obligations. Establish `h1 : IsSquare (d : ZMod n)`.

Rewrite using `[ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 hd4 hlt.ne', hdn, ZMod.exists_sq_eq_neg_one_iff]`. Simplify using `[hd4]`. Establish `h0 : (d : ZMod n) ≠ 0`. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]`. Conclude with `Nat.not_dvd_of_pos_of_lt hd.pos hlt`.

Introduce `h2`. Establish `h3 : IsSquare (-1 : ZMod n)`. Use `h2.div h1` as an intermediate fact. Rewrite `this` using `[neg_div, div_self h0]`. Then use the resulting hypothesis. Rewrite `h3` using `[ZMod.exists_sq_eq_neg_one_iff]`.

Conclude with `h3 h4`.
-/
theorem exists_prime_gt_neg_not_isSquare (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3) (b : ℕ) :
    ∃ n : ℕ, b < n ∧ n.Prime ∧ Odd n ∧ ¬ IsSquare (-(d : ZMod n)) := by
  haveI : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩
  obtain ⟨n, hn, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * d) (a := -1) isUnit_one.neg (max b d)
  have hdvd : 4 * d ∣ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hmod]; ring
  have h4 : n % 4 = 3 := by
    have : 4 ∣ n + 1 := Dvd.dvd.trans (Dvd.intro _ rfl) hdvd
    omega
  have hdn : (n : ZMod d) = -1 := by
    have : d ∣ n + 1 := Dvd.dvd.trans (Dvd.intro_left _ rfl) hdvd
    rw [← ZMod.natCast_eq_zero_iff] at this
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hlt : d < n := lt_of_le_of_lt (le_max_right _ _) hn
  haveI : Fact n.Prime := ⟨hp⟩
  haveI : Fact d.Prime := ⟨hd⟩
  refine ⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, by rw [Nat.odd_iff]; omega, ?_⟩
  have h1 : IsSquare (d : ZMod n) := by
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 hd4 hlt.ne', hdn,
      ZMod.exists_sq_eq_neg_one_iff]
    simp [hd4]
  have h0 : (d : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hd.pos hlt
  intro h2
  have h3 : IsSquare (-1 : ZMod n) := by
    have := h2.div h1
    rwa [neg_div, div_self h0] at this
  rw [ZMod.exists_sq_eq_neg_one_iff] at h3
  exact h3 h4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CMGeneratorSquareModuli.main`. Consider the case `exact _root_.GlobalTheory.CMGeneratorSquareModuli.main`. Consider the case `(apply _root_.GlobalTheory.CMGeneratorSquareModuli.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CMGeneratorSquareModuli.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CMGeneratorSquareModuli.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CMGeneratorSquareModuli.main ..)`.
-/
theorem exists_eq_of_mem_adjoin_quadratic_generator (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    ∃ u v : ℤ, a = (u : 𝓞 E) + (v : 𝓞 E) * H.w0 := by
  first
  | exact @_root_.GlobalTheory.CMGeneratorSquareModuli.main
  | exact _root_.GlobalTheory.CMGeneratorSquareModuli.main
  | (apply _root_.GlobalTheory.CMGeneratorSquareModuli.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMGeneratorSquareModuli.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMGeneratorSquareModuli.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMGeneratorSquareModuli.main ..)

/- English proof (translation)
Take `⟨hp, hodd, hsq, -⟩` from `hn`. Use `haveI : Fact n.Prime := ⟨hp⟩`. Establish `key : ∀ m : ℤ, (m : 𝓞 E) ∈ P → (n : ℤ) ∣ m`. Introduce `m hm`. Assume the negation of the conclusion as `h`.

Establish `hc : IsCoprime (n : ℤ) m` using `(Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr h`. Take `⟨s, t, hst⟩` from `hc`. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: (1 : 𝓞 E) = (s : 𝓞 E) * n + (t : 𝓞 E) * m`.

Conclude with `congrArg (Int.cast : ℤ → 𝓞 E) hst.symm` after adjusting the coercions. Rewrite using `[this]`. Conclude with `P.add_mem (P.mul_mem_left _ hnP) (P.mul_mem_left _ hm)`. Take `⟨u, v, rfl⟩` from `exists_eq_of_mem_adjoin_quadratic_generator H ha`. Establish `hN : (n : ℤ) ∣ (2 * u + v) ^ 2 + H.d * v ^ 2`.

Apply `key` to reduce the goal to its premises. Establish `: (((2 * u + v) ^ 2 + H.d * v ^ 2 : ℤ) : 𝓞 E) = (2 * ((2 * u + v : 𝓞 E) - v * H.rt)) * ((u : 𝓞 E) + v * H.w0)`. Use `push_cast`. Take the linear combination `(-((2 * u + v : 𝓞 E) - v * H.rt) * v) * H.two_weight_eq_one_add_root + (v : 𝓞 E) ^ 2 * H.rt_sq`. Rewrite using `[this]`.

Conclude with `P.mul_mem_left _ haP`. Rewrite `hN` using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hN`. Establish `hv : (v : ZMod n) = 0`. Assume the negation of the conclusion as `hv`.

Apply `hsq` to reduce the goal to its premises. Use `⟨(2 * u + v) / v, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hN`. Establish `h2 : (2 : ZMod n) ≠ 0`.

Introduce `h`. Establish `: ((2 : ℕ) : ZMod n) = 0` using `by exact_mod_cast h`. Rewrite `this` using `[ZMod.natCast_eq_zero_iff]`. Use `(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this` as an intermediate fact. Substitute `this` using the available equality.

Conclude with `absurd hodd (by decide)`. Establish `hu : (u : ZMod n) = 0`. Rewrite `hN` using `[hv]`. Simplify `hN` using `[h2]`. Rewrite `hu`, `hv` using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Take `⟨u', rfl⟩` from `hu`. Take `⟨v', rfl⟩` from `hv`. Establish `: H.bar (((n * u' : ℤ) : 𝓞 E) + ((n * v' : ℤ) : 𝓞 E) * H.w0) = ((u' : 𝓞 E) + v' * H.bar H.w0) * n`. Simplify using `only [map_add, map_mul, map_intCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `P.mul_mem_left _ hnP`.
-/
theorem bar_mem_of_mem (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) (haP : a ∈ P) : H.bar a ∈ P := by
  obtain ⟨hp, hodd, hsq, -⟩ := hn
  haveI : Fact n.Prime := ⟨hp⟩
  have key : ∀ m : ℤ, (m : 𝓞 E) ∈ P → (n : ℤ) ∣ m := by
    intro m hm
    by_contra h
    have hc : IsCoprime (n : ℤ) m :=
      (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr h
    obtain ⟨s, t, hst⟩ := hc
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 E) = (s : 𝓞 E) * n + (t : 𝓞 E) * m := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hst.symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hnP) (P.mul_mem_left _ hm)
  obtain ⟨u, v, rfl⟩ := exists_eq_of_mem_adjoin_quadratic_generator H ha
  have hN : (n : ℤ) ∣ (2 * u + v) ^ 2 + H.d * v ^ 2 := by
    apply key
    have : (((2 * u + v) ^ 2 + H.d * v ^ 2 : ℤ) : 𝓞 E) =
        (2 * ((2 * u + v : 𝓞 E) - v * H.rt)) * ((u : 𝓞 E) + v * H.w0) := by
      push_cast
      linear_combination (-((2 * u + v : 𝓞 E) - v * H.rt) * v) * H.two_weight_eq_one_add_root + (v : 𝓞 E) ^ 2 * H.rt_sq
    rw [this]
    exact P.mul_mem_left _ haP
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hN
  push_cast at hN
  have hv : (v : ZMod n) = 0 := by
    by_contra hv
    apply hsq
    refine ⟨(2 * u + v) / v, ?_⟩
    field_simp
    linear_combination -hN
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    subst this
    exact absurd hodd (by decide)
  have hu : (u : ZMod n) = 0 := by
    rw [hv] at hN
    simpa [h2] using hN
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hu hv
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  have : H.bar (((n * u' : ℤ) : 𝓞 E) + ((n * v' : ℤ) : 𝓞 E) * H.w0) =
      ((u' : 𝓞 E) + v' * H.bar H.w0) * n := by
    simp only [map_add, map_mul, map_intCast]
    push_cast
    ring
  rw [this]
  exact P.mul_mem_left _ hnP

/- English proof (translation)
Introduce `h`. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← l.coprime]`. Use `sup_le h ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap, l.fromK, Ideal.span_le]`.

Introduce and unpack `a ⟨haM, ha⟩`. Conclude with `bar_mem_of_mem H hn P hP hnP ha (h haM)`.
-/
theorem not_Mb_le (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (l : Level H) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) : ¬ l.Mb ≤ P := by
  intro h
  apply hP.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le h ?_
  rw [Ideal.map_le_iff_le_comap, l.fromK, Ideal.span_le]
  rintro a ⟨haM, ha⟩
  exact bar_mem_of_mem H hn P hP hnP ha (h haM)

/- English proof (translation)
Rewrite using `[Nat.Prime.coprime_iff_not_dvd hn.1]`. Introduce and unpack `⟨m, hm⟩`. Establish `hnu : Ideal.span {(n : 𝓞 E)} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Introduce `hu`.

Establish `h1` using `hu.map (Algebra.norm ℤ)`. Establish `h2 : Algebra.norm ℤ (n : 𝓞 E) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E)`. Rewrite using `[← Algebra.norm_algebraMap]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2, isUnit_pow_iff Module.finrank_pos.ne']`.

Conclude with `(Nat.prime_iff_prime_int.mp hn.1).not_unit h1`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hnu`. Establish `hnP : (n : 𝓞 E) ∈ P` using `hle (Ideal.mem_span_singleton_self _)`. Establish `hM : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ P`. Rewrite using `[l.prod, Ideal.span_singleton_le_iff_mem, hm]`.

Use `push_cast`. Conclude with `P.mul_mem_right _ hnP`. Break down `hP.isPrime.mul_le.mp hM with h | h` into its components or cases. Conclude with `not_Mb_le H hn l P hP.isPrime hnP h`. Rewrite using `[Ideal.map_le_iff_le_comap] at h haveI := hP.isPrime`.

Use `not_Mb_le H hn l _ (Ideal.comap_isPrime _ P) ?_ h` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hnP`.
-/
theorem AuxiliaryInertOddPrime.coprime_level {H : Host E} {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (l : Level H) : n.Coprime l.M := by
  rw [Nat.Prime.coprime_iff_not_dvd hn.1]
  rintro ⟨m, hm⟩
  have hnu : Ideal.span {(n : 𝓞 E)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ (n : 𝓞 E) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [← Algebra.norm_algebraMap]; simp
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne'] at h1
    exact (Nat.prime_iff_prime_int.mp hn.1).not_unit h1
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hnP : (n : 𝓞 E) ∈ P := hle (Ideal.mem_span_singleton_self _)
  have hM : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ P := by
    rw [l.prod, Ideal.span_singleton_le_iff_mem, hm]
    push_cast
    exact P.mul_mem_right _ hnP
  rcases hP.isPrime.mul_le.mp hM with h | h
  · exact not_Mb_le H hn l P hP.isPrime hnP h
  · rw [Ideal.map_le_iff_le_comap] at h
    haveI := hP.isPrime
    refine not_Mb_le H hn l _ (Ideal.comap_isPrime _ P) ?_ h
    rw [Ideal.mem_comap, map_natCast]
    exact hnP

/- English proof (translation)
Take `⟨n, hn, hp, hodd, hsq⟩` from `exists_prime_gt_neg_not_isSquare H.d H.d_prime (by have := H.d_mod; omega) (max b (NumberField.discr E).natAbs)`. Use `⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, hodd, hsq, ?_⟩` and prove the remaining obligations. Rewrite using `[Int.natCast_dvd]`. Conclude with `Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)) (lt_of_le_of_lt (le_max_right _ _) hn)`.
-/
theorem exists_large_auxiliary_prime (H : Host E) (b : ℕ) : ∃ n : ℕ, b < n ∧ AuxiliaryInertOddPrime H n := by
  obtain ⟨n, hn, hp, hodd, hsq⟩ := exists_prime_gt_neg_not_isSquare H.d H.d_prime
    (by have := H.d_mod; omega) (max b (NumberField.discr E).natAbs)
  refine ⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, hodd, hsq, ?_⟩
  rw [Int.natCast_dvd]
  exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr (NumberField.discr_ne_zero E))
    (lt_of_le_of_lt (le_max_right _ _) hn)

/- English proof (translation)
Introduce `E _ _ _ H`. Take `⟨n, -, hn⟩` from `exists_large_auxiliary_prime H 0`. Take `⟨n', hlt, hn'⟩` from `exists_large_auxiliary_prime H n`. Conclude with `⟨⟨n, n', hn, hn', hlt.ne⟩, fun _ h l => h.coprime_level l⟩`.
-/
theorem exists_two_auxiliary_inert_odd_primes_coprime_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
      (∃ n n' : ℕ, AuxiliaryInertOddPrime H n ∧ AuxiliaryInertOddPrime H n' ∧ n ≠ n') ∧
        ∀ n : ℕ, AuxiliaryInertOddPrime H n → ∀ l : Level H, n.Coprime l.M := by
  intro E _ _ _ H
  obtain ⟨n, -, hn⟩ := exists_large_auxiliary_prime H 0
  obtain ⟨n', hlt, hn'⟩ := exists_large_auxiliary_prime H n
  exact ⟨⟨n, n', hn, hn', hlt.ne⟩, fun _ h l => h.coprime_level l⟩

end GlobalTheory.Models
