import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open GroundTheory.Heights₂.Heights.NumbersDVR (blockWeight bundleIdx pairProjCoord projCoord segreVec)
open GroundTheory.Heights₂.Heights.Bridge (isMultiHomog_iff weight_blockWeight)

namespace PositivityTheory.HtPt.Gf

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

section Homog

omit [Fintype K] in
/- English proof (translation)
The claim follows from `(isMultiHomog_iff f a).symm`.
-/
theorem hom_iff [DecidableEq K] {R : Type} [CommRing R] (f : MRingOver R J) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (blockWeight J) f a :=
  (isMultiHomog_iff f a).symm

omit [Fintype K] in
/- English proof (translation)
Rewrite `*` using `[hom_iff]`. Conclude with `hf.mul hg`.
-/
theorem hom_mul {f g : MRing J} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  rw [hom_iff] at *
  exact hf.mul hg

omit [Fintype K] in
/- English proof (translation)
Rewrite `*` using `[hom_iff]`. Conclude with `hf.add hg`.
-/
theorem hom_add {f g : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  rw [hom_iff] at *
  exact hf.add hg

omit [Fintype K] in
/- English proof (translation)
Rewrite `*` using `[hom_iff]`. Conclude with `(weightedHomogeneousSubmodule ℤ (blockWeight J) a).sub_mem hf hg`.
-/
theorem hom_sub {f g : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  rw [hom_iff] at *
  exact (weightedHomogeneousSubmodule ℤ (blockWeight J) a).sub_mem hf hg

omit [Fintype K] in
/- English proof (translation)
Rewrite `*` using `[hom_iff]`. Rewrite using `[← nsmul_eq_mul]`. Conclude with `(weightedHomogeneousSubmodule ℤ (blockWeight J) a).toAddSubmonoid.nsmul_mem hf n`.
-/
theorem hom_nat_mul (n : ℕ) {f : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog ((n : MRing J) * f) a := by
  classical
  rw [hom_iff] at *
  rw [← nsmul_eq_mul]
  exact (weightedHomogeneousSubmodule ℤ (blockWeight J) a).toAddSubmonoid.nsmul_mem hf n

omit [Fintype K] in
/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem hom_zero (a : K → ℕ) : IsMultiHomog (0 : MRing J) a := by
  intro m hm
  simp at hm

omit [Fintype K] in
/- English proof (translation)
The claim follows from `funext h ▸ hf`.
-/
theorem hom_of_eq {f : MRing J} {a b : K → ℕ} (hf : IsMultiHomog f a) (h : ∀ k, a k = b k) :
    IsMultiHomog f b := funext h ▸ hf

noncomputable def mon (s : ∀ k, J k) (c : K → ℕ) : MRing J := ∏ k, X ⟨k, s k⟩ ^ c k

/- English proof (translation)
Rewrite using `[hom_iff]`. Establish `h` using `IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight J) Finset.univ (fun k => (X ⟨k, s k⟩ : MRing J) ^ c k) (fun k => c k • blockWeight J ⟨k, s k⟩) (fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow _)`. Establish `e : (∑ k, c k • blockWeight J ⟨k, s k⟩) = c`. Use function extensionality and compare the values at `j`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem hom_mon (s : ∀ k, J k) (c : K → ℕ) : IsMultiHomog (mon s c) c := by
  classical
  rw [hom_iff]
  have h := IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight J) Finset.univ
    (fun k => (X ⟨k, s k⟩ : MRing J) ^ c k) (fun k => c k • blockWeight J ⟨k, s k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow _)
  have e : (∑ k, c k • blockWeight J ⟨k, s k⟩) = c := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rwa [e] at h

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
Simplify using `[mon]`.
-/
theorem aeval_mon (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (c : K → ℕ) :
    aeval y (mon s c) = ∏ k, y ⟨k, s k⟩ ^ c k := by
  simp [mon]

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
Simplify using `[mon, mseg, Finset.prod_pow]`.
-/
theorem aeval_mon_const (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (d : ℕ) :
    aeval y (mon s fun _ => d) = mseg y s ^ d := by
  simp [mon, mseg, Finset.prod_pow]

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
Introduce `h`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h`. Conclude with `hs k (hW.mem_of_pow_mem _ hk)`.
-/
theorem mon_not_mem {W : Ideal (MRing J)} (hW : W.IsPrime) {s : ∀ k, J k}
    (hs : ∀ k, (X ⟨k, s k⟩ : MRing J) ∉ W) (c : K → ℕ) : mon s c ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h
  exact hs k (hW.mem_of_pow_mem _ hk)

/- English proof (translation)
Establish `key : mConeMap y g = C (aeval y g) * ∏ k, X k ^ d k` using `by conv_lhs => rw [g.as_sum] conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[mConeMap, aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]`.

Use `congr 1`. Use `congr 1`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_pow_eq_pow_sum, hg m hm k]`.

Rewrite using `[mCoordIdeal, RingHom.mem_ker]`. Rewrite using `[key, h, map_zero, zero_mul]`.
-/
theorem mem_mCoordIdeal {y : (Σ k, J k) → Ω} {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h : aeval y g = 0) : g ∈ mCoordIdeal y := by
  classical
  have key : mConeMap y g = C (aeval y g) * ∏ k, X k ^ d k := by
    conv_lhs => rw [g.as_sum]
    conv_rhs => rw [g.as_sum]
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [mConeMap, aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp)]
    simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]
    congr 1
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [mCoordIdeal, RingHom.mem_ker]
  rw [key, h, map_zero, zero_mul]

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
Use `Finset.prod_ne_zero_iff.2 fun k _ h => hs k (hle ?_)` and prove the remaining obligations. Rewrite using `[mCoordIdeal, RingHom.mem_ker]`. Simplify using `[mConeMap, h]`.
-/
theorem mseg_ne_zero {y : (Σ k, J k) → Ω} {W : Ideal (MRing J)} (hle : mCoordIdeal y ≤ W) {s : ∀ k, J k}
    (hs : ∀ k, (X ⟨k, s k⟩ : MRing J) ∉ W) : mseg y s ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun k _ h => hs k (hle ?_)
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h]

omit [Fintype K] [∀ k, Fintype (J k)] in
/- English proof (translation)
Establish `h1` using `Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing J))`. Establish `h2 : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing J)`. Rewrite using `[← h, charOf]`. Break down `Int.natAbs_eq (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing J))) with e | e` into its components or cases. Rewrite using `[← e]`.

Conclude with `h1`. Rewrite using `[← neg_mem_iff, ← e]`. Conclude with `h1`. Simplify using `using h2`.
-/
theorem natCast_mem_of_charOf {W : Ideal (MRing J)} {p : ℕ} (h : charOf W = p) : (p : MRing J) ∈ W := by
  have h1 := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing J))
  have h2 : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing J) := by
    rw [← h, charOf]
    rcases Int.natAbs_eq (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing J))) with e | e
    · rw [← e]; exact h1
    · rw [← neg_mem_iff, ← e]; exact h1
  simpa using h2

/- English proof (translation)
Introduce `hm`. Establish `hc : IsCoprime (p : R) (n : R)` using `((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn).cast`. Take `⟨a, b, e⟩` from `hc`. Conclude with `hW ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (W.mul_mem_left _ h) (W.mul_mem_left _ hm)))`.
-/
theorem natCast_not_mem {R : Type} [CommRing R] {W : Ideal R} (hW : W ≠ ⊤) {p n : ℕ} [hp : Fact p.Prime]
    (h : (p : R) ∈ W) (hn : ¬ p ∣ n) : (n : R) ∉ W := by
  intro hm
  have hc : IsCoprime (p : R) (n : R) := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn).cast
  obtain ⟨a, b, e⟩ := hc
  exact hW ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (W.mul_mem_left _ h) (W.mul_mem_left _ hm)))

end Homog

section Rep

noncomputable def dropVar : (Σ o, bundleIdx (bundleIdx J 0) 0 o) → MRing J
  | ⟨some (some k), i⟩ => X ⟨k, i⟩
  | ⟨some none, i⟩ => Fin.elim0 i
  | ⟨none, i⟩ => Fin.elim0 i

/- English proof (translation)
Take `⟨d, U, hU, e⟩` from `GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor.chart_form (O := o) (Φ := Ω) (M := 0) (M' := 0) y (Pi.basisFun Ω (Fin 0)) Fin.elim0 Fin.elim0 Fin.elim0 s hs hx`. Express the relevant statement in the definitionally equal form `aeval _ U = x * mseg y s ^ d at e`. Use `set z := pairProjCoord (Φ := Ω) (M := 0) (M' := 0) y (Pi.basisFun Ω (Fin 0)) Fin.elim0 Fin.elim0 Fin.elim0`. Establish `hz : ∀ v, aeval y (dropVar v) = z v`. Introduce and unpack `⟨_ | _ | k, i⟩`.

Conclude with `Fin.elim0 i`. Conclude with `Fin.elim0 i`. Simplify using `[dropVar, z, pairProjCoord, projCoord]`. Set `w : (Σ o, bundleIdx (bundleIdx J 0) 0 o) → K → ℕ` to `fun v k => blockWeight _ v (some (some k))`. Establish `hw : ∀ v, IsWeightedHomogeneous (blockWeight J) (dropVar v) (w v)`.

Introduce and unpack `⟨_ | _ | k, i⟩`. Conclude with `Fin.elim0 i`. Conclude with `Fin.elim0 i`. Establish `: w ⟨some (some k), i⟩ = blockWeight J ⟨k, i⟩`. Use function extensionality and compare the values at `j`.

Simplify using `[w, blockWeight, Pi.single_apply]`. Rewrite using `[this]`. Conclude with `isWeightedHomogeneous_X ℤ (blockWeight J) ⟨k, i⟩`. It suffices to establish `H : ∃ (n : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ n * aeval z U = aeval y g by`. Take `⟨n, g, h1, h2, h3⟩` from `H`.

Conclude with `⟨n, d, g, h1, h2, by rw [mul_assoc, ← e, h3]⟩`. Rewrite using `[U.as_sum, map_sum]`. Use `Finset.sum_induction _ (fun u : Ω => ∃ (n : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ n * u = aeval y g) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `u v ⟨n, g, h1, h2, h3⟩ ⟨n', g', h1', h2', h3'⟩`. Use `⟨n * n', n' * g + n * g', fun h => (hp.out.dvd_mul.1 h).elim h1 h1', hom_add (hom_nat_mul _ h2) (hom_nat_mul _ h2'), ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_natCast, ← h3, ← h3']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨1, 0, hp.out.not_dvd_one, hom_zero _, by simp⟩`. Introduce `m hm`.

Take `⟨a, b, hb, hab⟩` from `(ho _).1 ⟨coeff m U, rfl⟩`. Establish `hb0 : (b : Ω) ≠ 0`. Rewrite using `[Nat.cast_ne_zero]`. Introduce and unpack `rfl`. Conclude with `hb (dvd_zero _)`.

Use `⟨b, C a * ∏ v ∈ m.support, dropVar v ^ m v, hb, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hom_iff]`. Establish `h` using `(IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight J) m.support (fun v => dropVar v ^ m v) (fun v => m v • w v) (fun v _ => (hw v).pow _)).C_mul a`. Establish `e : (∑ v ∈ m.support, m v • w v) = fun _ => d`. Use function extensionality and compare the values at `k`.

Use `congrFun (hU (mem_support_iff.1 hm)) (some (some k))` as an intermediate fact. Rewrite `this` using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Rewrite using `[Finset.sum_apply]`. Conclude with `this`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Rewrite using `[aeval_monomial, hab, map_mul, map_prod]`. Simplify using `only [map_pow, hz, Finsupp.prod, eq_intCast, map_intCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_rep [CharZero Ω] {y : (Σ k, J k) → Ω} {p : ℕ} [hp : Fact p.Prime] {o : Type} [CommRing o]
    [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {s : ∀ k, J k} (hs : mseg y s ≠ 0) {x : Ω} (hx : x ∈ chartRing o (mseg y) s) :
    ∃ (n d : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ n * x * mseg y s ^ d = aeval y g := by
  classical
  obtain ⟨d, U, hU, e⟩ := GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor.chart_form (O := o) (Φ := Ω)
    (M := 0) (M' := 0) y (Pi.basisFun Ω (Fin 0)) Fin.elim0 Fin.elim0 Fin.elim0 s hs hx
  change aeval _ U = x * mseg y s ^ d at e
  set z := pairProjCoord (Φ := Ω) (M := 0) (M' := 0) y (Pi.basisFun Ω (Fin 0)) Fin.elim0 Fin.elim0 Fin.elim0
  have hz : ∀ v, aeval y (dropVar v) = z v := by
    rintro ⟨_ | _ | k, i⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · simp [dropVar, z, pairProjCoord, projCoord]
  let w : (Σ o, bundleIdx (bundleIdx J 0) 0 o) → K → ℕ := fun v k => blockWeight _ v (some (some k))
  have hw : ∀ v, IsWeightedHomogeneous (blockWeight J) (dropVar v) (w v) := by
    rintro ⟨_ | _ | k, i⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · have : w ⟨some (some k), i⟩ = blockWeight J ⟨k, i⟩ := by
        funext j
        simp [w, blockWeight, Pi.single_apply]
      rw [this]
      exact isWeightedHomogeneous_X ℤ (blockWeight J) ⟨k, i⟩
  suffices H : ∃ (n : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ n * aeval z U = aeval y g by
    obtain ⟨n, g, h1, h2, h3⟩ := H
    exact ⟨n, d, g, h1, h2, by rw [mul_assoc, ← e, h3]⟩
  rw [U.as_sum, map_sum]
  refine Finset.sum_induction _
    (fun u : Ω => ∃ (n : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ n * u = aeval y g) ?_ ?_ ?_
  · rintro u v ⟨n, g, h1, h2, h3⟩ ⟨n', g', h1', h2', h3'⟩
    refine ⟨n * n', n' * g + n * g', fun h => (hp.out.dvd_mul.1 h).elim h1 h1',
      hom_add (hom_nat_mul _ h2) (hom_nat_mul _ h2'), ?_⟩
    simp only [map_add, map_mul, map_natCast, ← h3, ← h3']
    push_cast; ring
  · exact ⟨1, 0, hp.out.not_dvd_one, hom_zero _, by simp⟩
  · intro m hm
    obtain ⟨a, b, hb, hab⟩ := (ho _).1 ⟨coeff m U, rfl⟩
    have hb0 : (b : Ω) ≠ 0 := by
      rw [Nat.cast_ne_zero]; rintro rfl; exact hb (dvd_zero _)
    refine ⟨b, C a * ∏ v ∈ m.support, dropVar v ^ m v, hb, ?_, ?_⟩
    · rw [hom_iff]
      have h := (IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight J) m.support
        (fun v => dropVar v ^ m v) (fun v => m v • w v) (fun v _ => (hw v).pow _)).C_mul a
      have e : (∑ v ∈ m.support, m v • w v) = fun _ => d := by
        funext k
        have := congrFun (hU (mem_support_iff.1 hm)) (some (some k))
        rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
        rw [Finset.sum_apply]
        exact this
      rwa [e] at h
    · rw [aeval_monomial, hab, map_mul, map_prod]
      simp only [map_pow, hz, Finsupp.prod, eq_intCast, map_intCast]
      field_simp

end Rep

section Trans

variable {o : Type} [CommRing o] [Algebra o Ω]

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
Establish `h` using `div_mem_chartRing (o := o) (mseg y) t (Function.update t k i)`. Use `h using 1` and compare the differences between its conclusion and the goal. Unfold `mseg`. Rewrite using `[← Finset.prod_div_distrib, Finset.prod_eq_single k (fun j _ hj => ?_) (by simp)]`. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne hj, div_self (Finset.prod_ne_zero_iff.1 ht j (Finset.mem_univ j))]`.
-/
theorem coord_div_mem {y : (Σ k, J k) → Ω} {t : ∀ k, J k} (ht : mseg y t ≠ 0) (k : K) (i : J k) :
    y ⟨k, i⟩ / y ⟨k, t k⟩ ∈ chartRing o (mseg y) t := by
  classical
  have h := div_mem_chartRing (o := o) (mseg y) t (Function.update t k i)
  convert h using 1
  unfold mseg
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k (fun j _ hj => ?_) (by simp)]
  · simp
  · rw [Function.update_of_ne hj, div_self (Finset.prod_ne_zero_iff.1 ht j (Finset.mem_univ j))]

omit [∀ k, Fintype (J k)] in

/- English proof (translation)
Use `⟨∑ k, (a k).natAbs, ?_⟩` and prove the remaining obligations. Use `set n := ∑ k, (a k).natAbs with hn`. Establish `e : (mseg y s / mseg y t) ^ n * (chartMon y s a / chartMon y t a) = ∏ k, (y ⟨k, s k⟩ / y ⟨k, t k⟩) ^ ((n : ℤ) + a k).toNat`. Unfold `mseg chartMon`. Rewrite using `[← Finset.prod_div_distrib, ← Finset.prod_div_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h1 : (a k).natAbs ≤ n` using `Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`. Establish `h2 : y ⟨k, s k⟩ / y ⟨k, t k⟩ ≠ 0` using `div_ne_zero (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)) (Finset.prod_ne_zero_iff.1 ht k (Finset.mem_univ k))`. Rewrite using `[← div_zpow, ← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_add₀ h2]`. Rewrite using `[e]`.

Conclude with `prod_mem fun k _ => pow_mem (coord_div_mem ht k _) _`.
-/
theorem exists_pow_mul_trans_mem {y : (Σ k, J k) → Ω} {s t : ∀ k, J k} (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0)
    (a : K → ℤ) : ∃ n : ℕ, (mseg y s / mseg y t) ^ n * (chartMon y s a / chartMon y t a) ∈
      chartRing o (mseg y) t := by
  refine ⟨∑ k, (a k).natAbs, ?_⟩
  set n := ∑ k, (a k).natAbs with hn
  have e : (mseg y s / mseg y t) ^ n * (chartMon y s a / chartMon y t a) =
      ∏ k, (y ⟨k, s k⟩ / y ⟨k, t k⟩) ^ ((n : ℤ) + a k).toNat := by
    unfold mseg chartMon
    rw [← Finset.prod_div_distrib, ← Finset.prod_div_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h1 : (a k).natAbs ≤ n := Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
    have h2 : y ⟨k, s k⟩ / y ⟨k, t k⟩ ≠ 0 := div_ne_zero (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k))
      (Finset.prod_ne_zero_iff.1 ht k (Finset.mem_univ k))
    rw [← div_zpow, ← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_add₀ h2]
  rw [e]
  exact prod_mem fun k _ => pow_mem (coord_div_mem ht k _) _

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k))`.
-/
theorem chartMon_ne_zero {y : (Σ k, J k) → Ω} {s : ∀ k, J k} (hs : mseg y s ≠ 0) (a : K → ℤ) :
    chartMon y s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k))

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
Simplify using `[chartMon]`.
-/
theorem chartMon_neg (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (a : K → ℤ) :
    chartMon y s (-a) = (chartMon y s a)⁻¹ := by
  simp [chartMon]

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp [chartMon]`. Consider the case `insert j S hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.prod_insert hj, ← ih]`. Unfold `chartMon`.

Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => zpow_add₀ (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)) _ _`.
-/
theorem chartMon_sum {y : (Σ k, J k) → Ω} {s : ∀ k, J k} (hs : mseg y s ≠ 0) {ι : Type} (S : Finset ι)
    (b : ι → K → ℤ) : chartMon y s (∑ l ∈ S, b l) = ∏ l ∈ S, chartMon y s (b l) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [chartMon]
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, ← ih]
    unfold chartMon
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ =>
      zpow_add₀ (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)) _ _

omit [∀ k, Fintype (J k)] in
/- English proof (translation)
Rewrite using `[aeval_mon, aeval_mon, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k))]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem chartMon_eq_div {y : (Σ k, J k) → Ω} {s : ∀ k, J k} (hs : mseg y s ≠ 0) (a : K → ℤ) :
    chartMon y s a = aeval y (mon s fun k => (a k).toNat) / aeval y (mon s fun k => (-a k).toNat) := by
  rw [aeval_mon, aeval_mon, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k))]
  congr 1
  omega

end Trans

omit [∀ k, Fintype (J k)] in

/- English proof (translation)
Distinguish the cases in `h : IsRelevant W`. Use `⟨fun k => ∑ᶠ W' ∈ divSupp W (X ⟨k, (h k).choose⟩), (multAt (W ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing J)}) W' : ℤ) * geoNum 0 W' Fin.elim0, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[geoNum, dif_pos h, Subsingleton.elim (Fin.init fun _ : Fin (0 + 1) => a) Fin.elim0]`. Conclude with `⟨0, fun a => by rw [geoNum, dif_neg h]; simp⟩`.
-/
theorem geoNum_one_linear (W : Ideal (MRing J)) :
    ∃ c : K → ℤ, ∀ a : K → ℤ, geoNum 1 W (fun _ => a) = ∑ k, a k * c k := by
  by_cases h : IsRelevant W
  · refine ⟨fun k => ∑ᶠ W' ∈ divSupp W (X ⟨k, (h k).choose⟩),
      (multAt (W ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing J)}) W' : ℤ) * geoNum 0 W' Fin.elim0, fun a => ?_⟩
    rw [geoNum, dif_pos h, Subsingleton.elim (Fin.init fun _ : Fin (0 + 1) => a) Fin.elim0]
  · exact ⟨0, fun a => by rw [geoNum, dif_neg h]; simp⟩

end PositivityTheory.HtPt.Gf
