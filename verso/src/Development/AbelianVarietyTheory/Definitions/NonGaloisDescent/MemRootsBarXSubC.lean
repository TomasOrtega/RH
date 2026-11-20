import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section
namespace GlobalTheory.GLq.Model
open Polynomial Formalism.CyclotomicNorms

abbrev ZC : Type := integralClosure ℤ ℂ

variable (g : ℕ) [hg : Fact g.Prime]

/- English proof (translation)
Establish `hgZ : Prime (g : ℤ)` using `Nat.prime_iff_prime_int.mp hg.out`. Establish `: (Ideal.span {(g : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hgZ.irreducible`. Establish `hinj : Function.Injective (algebraMap ℤ ZC)`. Introduce `a b hab`. Use `congrArg (fun z : ZC => (z : ℂ)) hab` as an intermediate fact.

Simplify using `using this`. Take `⟨Q, hQ, hQP⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := ZC) (Ideal.span {(g : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)`. Set `_ : Field (ZC ⧸ Q)` to `Ideal.Quotient.field Q`. Establish `hg0 : ((g : ℕ) : ZC ⧸ Q) = 0`. Establish `hmem : (g : ℤ) ∈ Q.comap (algebraMap ℤ ZC)`.

Rewrite using `[hQP]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `hmem` using `[Ideal.mem_comap]`. Use `(Ideal.Quotient.eq_zero_iff_mem).mpr hmem` as an intermediate fact. Simplify using `using this`.

Establish `: CharP (ZC ⧸ Q) g` using `(CharP.charP_iff_prime_eq_zero hg.out).mpr hg0`. Set `_ : Algebra (ZMod g) (ZC ⧸ Q)` to `ZMod.algebra' (ZC ⧸ Q) g (dvd_refl g)`. Establish `: Algebra.IsIntegral (ZMod g) (ZC ⧸ Q)`. Prove the components needed by the constructor for the conclusion. Introduce `y`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `hb : IsIntegral ℤ b` using `Algebra.IsIntegral.isIntegral b`. Establish `h1 : IsIntegral ℤ (Ideal.Quotient.mk Q b)`. Simplify using `using hb.map (Ideal.Quotient.mkₐ ℤ Q)`. Conclude with `h1.tower_top`.

Conclude with `⟨(IsAlgClosed.lift : (ZC ⧸ Q) →ₐ[ZMod g] Fbar g).toRingHom.comp (Ideal.Quotient.mk Q)⟩`.
-/
theorem exists_red : Nonempty (ZC →+* Fbar g) := by

  have hgZ : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg.out
  have : (Ideal.span {(g : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hgZ.irreducible
  have hinj : Function.Injective (algebraMap ℤ ZC) := by
    intro a b hab
    have := congrArg (fun z : ZC => (z : ℂ)) hab
    simpa using this
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := ZC)
    (Ideal.span {(g : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  let _ : Field (ZC ⧸ Q) := Ideal.Quotient.field Q
  have hg0 : ((g : ℕ) : ZC ⧸ Q) = 0 := by
    have hmem : (g : ℤ) ∈ Q.comap (algebraMap ℤ ZC) := by
      rw [hQP]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at hmem
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    simpa using this
  have : CharP (ZC ⧸ Q) g := (CharP.charP_iff_prime_eq_zero hg.out).mpr hg0
  let _ : Algebra (ZMod g) (ZC ⧸ Q) := ZMod.algebra' (ZC ⧸ Q) g (dvd_refl g)
  have : Algebra.IsIntegral (ZMod g) (ZC ⧸ Q) := by
    constructor
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hb : IsIntegral ℤ b := Algebra.IsIntegral.isIntegral b
    have h1 : IsIntegral ℤ (Ideal.Quotient.mk Q b) := by
      simpa using hb.map (Ideal.Quotient.mkₐ ℤ Q)
    exact h1.tower_top
  exact ⟨(IsAlgClosed.lift : (ZC ⧸ Q) →ₐ[ZMod g] Fbar g).toRingHom.comp (Ideal.Quotient.mk Q)⟩

def red : ZC →+* Fbar g := (exists_red g).some

/- English proof (translation)
The claim follows from `Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)`.
-/
theorem N_pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[CharP.cast_eq_zero_iff (Fbar g) g]`. Establish `h2 : g ∣ (g ^ d - 1) + 1`. Rewrite using `[Nat.sub_add_cancel (Nat.one_le_pow _ _ hg.out.pos)]`. Conclude with `dvd_pow_self g hd.ne'`.

Conclude with `hg.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp h2))`.
-/
theorem N_ne {d : ℕ} (hd : 0 < d) : ((g ^ d - 1 : ℕ) : Fbar g) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff (Fbar g) g] at h
  have h2 : g ∣ (g ^ d - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hg.out.pos)]
    exact dvd_pow_self g hd.ne'
  exact hg.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp h2))

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `only [Nat.cast_zero, div_zero, Complex.exp_zero]`. Conclude with `isIntegral_one`. Conclude with `(Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn`.
-/
theorem exp_int (n : ℕ) : IsIntegral ℤ (Complex.exp (2 * Real.pi * Complex.I / n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero, Complex.exp_zero]
    exact isIntegral_one
  · exact (Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn

def ez (n : ℕ) : ZC := ⟨Complex.exp (2 * Real.pi * Complex.I / n), exp_int n⟩

/- English proof (translation)
Establish `h : IsPrimitiveRoot ((integralClosure ℤ ℂ).val (ez n)) n` using `Complex.isPrimitiveRoot_exp n hn.ne'`. Conclude with `h.of_map_of_injective (fun a b hab => Subtype.ext hab)`.
-/
theorem ez_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (ez n) n := by
  have h : IsPrimitiveRoot ((integralClosure ℤ ℂ).val (ez n)) n :=
    Complex.isPrimitiveRoot_exp n hn.ne'
  exact h.of_map_of_injective (fun a b hab => Subtype.ext hab)

/- English proof (translation)
Establish `hN : 0 < g ^ d - 1` using `N_pos g hd`. Establish `hz` using `ez_prim hN`. Establish `hmon : (X ^ (g ^ d - 1) - C (1 : ZC)).Monic` using `monic_X_pow_sub_C 1 hN.ne'`. Establish `hdeg : (X ^ (g ^ d - 1) - C (1 : ZC)).natDegree = g ^ d - 1` using `natDegree_X_pow_sub_C`. Establish `hcard : Multiset.card (X ^ (g ^ d - 1) - C (1 : ZC)).roots = (X ^ (g ^ d - 1) - C (1 : ZC)).natDegree`.

Rewrite using `[hdeg]`. Conclude with `hz.card_nthRoots_one`. Establish `hsplit : (((X ^ (g ^ d - 1) - C (1 : ZC)).roots).map fun a => X - C a).prod = X ^ (g ^ d - 1) - C 1`. Use `C_leadingCoeff_mul_prod_multiset_X_sub_C hcard` as an intermediate fact. Rewrite `this` using `[hmon.leadingCoeff, C_1, one_mul]`. Then use the resulting hypothesis.

Establish `hsep : (X ^ (g ^ d - 1) - C (1 : Fbar g)).Separable` using `separable_X_pow_sub_C 1 (N_ne g hd) one_ne_zero`. Establish `hmap' : ((((X ^ (g ^ d - 1) - C (1 : ZC)).roots).map (red g)).map fun b => X - C b).prod = X ^ (g ^ d - 1) - C 1`. Establish `hmap` using `congrArg (Polynomial.map (red g)) hsplit`. Rewrite `hmap` using `[Polynomial.map_multiset_prod, Multiset.map_map]`. Rewrite using `[Multiset.map_map]`.

Simplify `hmap` using `[Function.comp_def]`. Establish `hnodup` using `nodup_roots hsep`. Rewrite `hnodup` using `[← hmap', roots_multiset_prod_X_sub_C]`. Use `IsPrimitiveRoot.mk_of_lt _ hN ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_pow, hz.pow_eq_one, map_one]`.

Introduce `l hl hlN hred`. Establish `hmem1 : ez (g ^ d - 1) ^ l ∈ (X ^ (g ^ d - 1) - C (1 : ZC)).roots`. Rewrite using `[← nthRoots, mem_nthRoots hN, ← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]`. Establish `hmem2 : (1 : ZC) ∈ (X ^ (g ^ d - 1) - C (1 : ZC)).roots`. Rewrite using `[← nthRoots, mem_nthRoots hN, one_pow]`.

Use `Multiset.inj_on_of_nodup_map hnodup _ hmem1 _ hmem2 (by rw [map_pow, hred, map_one])` as an intermediate fact. Conclude with `hz.pow_ne_one_of_pos_of_lt hl.ne' hlN this`.
-/
theorem gen_prim {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (red g (ez (g ^ d - 1))) (g ^ d - 1) := by
  have hN : 0 < g ^ d - 1 := N_pos g hd
  have hz := ez_prim hN

  have hmon : (X ^ (g ^ d - 1) - C (1 : ZC)).Monic := monic_X_pow_sub_C 1 hN.ne'
  have hdeg : (X ^ (g ^ d - 1) - C (1 : ZC)).natDegree = g ^ d - 1 := natDegree_X_pow_sub_C
  have hcard : Multiset.card (X ^ (g ^ d - 1) - C (1 : ZC)).roots =
      (X ^ (g ^ d - 1) - C (1 : ZC)).natDegree := by
    rw [hdeg]; exact hz.card_nthRoots_one
  have hsplit : (((X ^ (g ^ d - 1) - C (1 : ZC)).roots).map fun a => X - C a).prod =
      X ^ (g ^ d - 1) - C 1 := by
    have := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
    rwa [hmon.leadingCoeff, C_1, one_mul] at this

  have hsep : (X ^ (g ^ d - 1) - C (1 : Fbar g)).Separable :=
    separable_X_pow_sub_C 1 (N_ne g hd) one_ne_zero
  have hmap' : ((((X ^ (g ^ d - 1) - C (1 : ZC)).roots).map (red g)).map fun b => X - C b).prod =
      X ^ (g ^ d - 1) - C 1 := by
    have hmap := congrArg (Polynomial.map (red g)) hsplit
    rw [Polynomial.map_multiset_prod, Multiset.map_map] at hmap
    rw [Multiset.map_map]
    simpa [Function.comp_def] using hmap
  have hnodup := nodup_roots hsep
  rw [← hmap', roots_multiset_prod_X_sub_C] at hnodup
  refine IsPrimitiveRoot.mk_of_lt _ hN ?_ ?_
  · rw [← map_pow, hz.pow_eq_one, map_one]
  · intro l hl hlN hred
    have hmem1 : ez (g ^ d - 1) ^ l ∈ (X ^ (g ^ d - 1) - C (1 : ZC)).roots := by
      rw [← nthRoots, mem_nthRoots hN, ← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    have hmem2 : (1 : ZC) ∈ (X ^ (g ^ d - 1) - C (1 : ZC)).roots := by
      rw [← nthRoots, mem_nthRoots hN, one_pow]
    have := Multiset.inj_on_of_nodup_map hnodup _ hmem1 _ hmem2 (by rw [map_pow, hred, map_one])
    exact hz.pow_ne_one_of_pos_of_lt hl.ne' hlN this

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Establish `hm : m ≠ 0` using `by rintro rfl; simp at hn`. Establish `hk : k ≠ 0` using `by rintro rfl; simp at hn`. Rewrite using `[Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hm)]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[SubmonoidClass.coe_pow]`. Use `show Complex.exp (2 * Real.pi * Complex.I / ((m * k : ℕ) : ℂ)) ^ k = Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Establish `hm' : (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hm`.

Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hk`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem ez_pow {m n : ℕ} (hn : 0 < n) (h : m ∣ n) : ez n ^ (n / m) = ez m := by
  obtain ⟨k, rfl⟩ := h
  have hm : m ≠ 0 := by rintro rfl; simp at hn
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hm)]
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  show Complex.exp (2 * Real.pi * Complex.I / ((m * k : ℕ) : ℂ)) ^ k =
    Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  rw [← Complex.exp_nat_mul]
  congr 1
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  push_cast
  field_simp

/- English proof (translation)
Simplify `Nat.sub_dvd_pow_sub_pow (g ^ d) 1 e` using `[pow_mul]`.
-/
theorem N_dvd (d e : ℕ) : g ^ d - 1 ∣ g ^ (d * e) - 1 := by
  simpa [pow_mul] using Nat.sub_dvd_pow_sub_pow (g ^ d) 1 e

def Lifts (x : Fbar g) (ω : ZC) : Prop := (∃ d, 0 < d ∧ ω ^ (g ^ d - 1) = 1) ∧ red g ω = x

/- English proof (translation)
Take `⟨⟨d, hd, hω⟩, hx⟩` from `h`. Take `⟨⟨d', hd', hω'⟩, hx'⟩` from `h'`. Establish `hD : 0 < d * d'` using `Nat.mul_pos hd hd'`. Establish `hN` using `N_pos g hD`. Establish `e1 : ω ^ (g ^ (d * d') - 1) = 1`.

Take `⟨c, hc⟩` from `N_dvd g d d'`. Rewrite using `[hc, pow_mul, hω, one_pow]`. Establish `e2 : ω' ^ (g ^ (d * d') - 1) = 1`. Take `⟨c, hc⟩` from `N_dvd g d' d`. Rewrite using `[Nat.mul_comm d d', hc, pow_mul, hω', one_pow]`.

Establish `: NeZero (g ^ (d * d') - 1)` using `⟨hN.ne'⟩`. Establish `hz` using `ez_prim hN`. Take `⟨i, hi, rfl⟩` from `hz.eq_pow_of_pow_eq_one e1`. Take `⟨j, hj, rfl⟩` from `hz.eq_pow_of_pow_eq_one e2`. Establish `hij : red g (ez (g ^ (d * d') - 1)) ^ i = red g (ez (g ^ (d * d') - 1)) ^ j`.

Rewrite using `[← map_pow, ← map_pow, hx, hx']`. Rewrite using `[(gen_prim g hD).pow_inj hi hj hij]`.
-/
theorem lifts_unique {x : Fbar g} {ω ω' : ZC} (h : Lifts g x ω) (h' : Lifts g x ω') : ω = ω' := by
  obtain ⟨⟨d, hd, hω⟩, hx⟩ := h
  obtain ⟨⟨d', hd', hω'⟩, hx'⟩ := h'
  have hD : 0 < d * d' := Nat.mul_pos hd hd'
  have hN := N_pos g hD

  have e1 : ω ^ (g ^ (d * d') - 1) = 1 := by
    obtain ⟨c, hc⟩ := N_dvd g d d'
    rw [hc, pow_mul, hω, one_pow]
  have e2 : ω' ^ (g ^ (d * d') - 1) = 1 := by
    obtain ⟨c, hc⟩ := N_dvd g d' d
    rw [Nat.mul_comm d d', hc, pow_mul, hω', one_pow]
  have : NeZero (g ^ (d * d') - 1) := ⟨hN.ne'⟩
  have hz := ez_prim hN
  obtain ⟨i, hi, rfl⟩ := hz.eq_pow_of_pow_eq_one e1
  obtain ⟨j, hj, rfl⟩ := hz.eq_pow_of_pow_eq_one e2
  have hij : red g (ez (g ^ (d * d') - 1)) ^ i = red g (ez (g ^ (d * d') - 1)) ^ j := by
    rw [← map_pow, ← map_pow, hx, hx']
  rw [(gen_prim g hD).pow_inj hi hj hij]

/- English proof (translation)
Set `K` to `IntermediateField.adjoin (ZMod g) ({x} : Set (Fbar g))`. Establish `: FiniteDimensional (ZMod g) K` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Establish `: Finite K` using `Module.finite_of_finite (ZMod g)`. Set `_ : Fintype K` to `Fintype.ofFinite K`. Use `⟨Module.finrank (ZMod g) K, Module.finrank_pos, ?_⟩` and prove the remaining obligations.

Establish `hcard : Fintype.card K = g ^ Module.finrank (ZMod g) K`. Rewrite using `[Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]`. Establish `hxK : (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : K) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Simplify using `using congrArg Subtype.val h0`. Use `FiniteField.pow_card_sub_one_eq_one _ hxK` as an intermediate fact. Rewrite `this` using `[hcard]`. Simplify using `using congrArg Subtype.val this`.
-/
theorem exists_level {x : Fbar g} (hx : x ≠ 0) : ∃ d, 0 < d ∧ x ^ (g ^ d - 1) = 1 := by

  let K := IntermediateField.adjoin (ZMod g) ({x} : Set (Fbar g))
  have : FiniteDimensional (ZMod g) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Finite K := Module.finite_of_finite (ZMod g)
  let _ : Fintype K := Fintype.ofFinite K
  refine ⟨Module.finrank (ZMod g) K, Module.finrank_pos, ?_⟩
  have hcard : Fintype.card K = g ^ Module.finrank (ZMod g) K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  have hxK : (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : K) ≠ 0 := by
    intro h0; apply hx; simpa using congrArg Subtype.val h0
  have := FiniteField.pow_card_sub_one_eq_one _ hxK
  rw [hcard] at this
  simpa using congrArg Subtype.val this

/- English proof (translation)
Take `⟨d, hd, hxd⟩` from `exists_level g hx`. Establish `: NeZero (g ^ d - 1)` using `⟨(N_pos g hd).ne'⟩`. Take `⟨i, -, hi⟩` from `(gen_prim g hd).eq_pow_of_pow_eq_one hxd`. Use `⟨ez (g ^ d - 1) ^ i, ⟨d, hd, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, (ez_prim (N_pos g hd)).pow_eq_one, one_pow]`.

Rewrite using `[map_pow, hi]`.
-/
theorem exists_lifts {x : Fbar g} (hx : x ≠ 0) : ∃ ω, Lifts g x ω := by
  obtain ⟨d, hd, hxd⟩ := exists_level g hx
  have : NeZero (g ^ d - 1) := ⟨(N_pos g hd).ne'⟩
  obtain ⟨i, -, hi⟩ := (gen_prim g hd).eq_pow_of_pow_eq_one hxd
  refine ⟨ez (g ^ d - 1) ^ i, ⟨d, hd, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, (ez_prim (N_pos g hd)).pow_eq_one, one_pow]
  · rw [map_pow, hi]

/- English proof (translation)
Take `⟨⟨d, hd, hω⟩, hx⟩` from `h`. Take `⟨⟨d', hd', hω'⟩, hy⟩` from `h'`. Use `⟨⟨d * d', Nat.mul_pos hd hd', ?_⟩, by rw [map_mul, hx, hy]⟩` and prove the remaining obligations. Establish `e1 : ω ^ (g ^ (d * d') - 1) = 1`. Take `⟨c, hc⟩` from `N_dvd g d d'`.

Rewrite using `[hc, pow_mul, hω, one_pow]`. Establish `e2 : ω' ^ (g ^ (d * d') - 1) = 1`. Take `⟨c, hc⟩` from `N_dvd g d' d`. Rewrite using `[Nat.mul_comm d d', hc, pow_mul, hω', one_pow]`. Rewrite using `[mul_pow, e1, e2, one_mul]`.
-/
theorem lifts_mul {x y : Fbar g} {ω ω' : ZC} (h : Lifts g x ω) (h' : Lifts g y ω') :
    Lifts g (x * y) (ω * ω') := by
  obtain ⟨⟨d, hd, hω⟩, hx⟩ := h
  obtain ⟨⟨d', hd', hω'⟩, hy⟩ := h'
  refine ⟨⟨d * d', Nat.mul_pos hd hd', ?_⟩, by rw [map_mul, hx, hy]⟩
  have e1 : ω ^ (g ^ (d * d') - 1) = 1 := by
    obtain ⟨c, hc⟩ := N_dvd g d d'
    rw [hc, pow_mul, hω, one_pow]
  have e2 : ω' ^ (g ^ (d * d') - 1) = 1 := by
    obtain ⟨c, hc⟩ := N_dvd g d' d
    rw [Nat.mul_comm d d', hc, pow_mul, hω', one_pow]
  rw [mul_pow, e1, e2, one_mul]

open Classical in

def tf (x : Fbar g) : ZC := if h : x ≠ 0 then (exists_lifts g h).choose else 0

/- English proof (translation)
Unfold `tf`. Rewrite using `[dif_pos hx]`. Conclude with `(exists_lifts g hx).choose_spec`.
-/
theorem tf_spec {x : Fbar g} (hx : x ≠ 0) : Lifts g x (tf g x) := by
  unfold tf
  rw [dif_pos hx]
  exact (exists_lifts g hx).choose_spec

/- English proof (translation)
Unfold `tf`. Conclude with `dif_neg (fun h => h rfl)`.
-/
theorem tf_zero : tf g 0 = 0 := by
  unfold tf
  exact dif_neg (fun h => h rfl)

def teichM : Fbar g →* ℂ where
  toFun x := (tf g x : ℂ)
  map_one' := by
    have : tf g 1 = 1 := lifts_unique g (tf_spec g one_ne_zero) ⟨⟨1, one_pos, one_pow _⟩, map_one _⟩
    rw [this]; rfl
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx, tf_zero]
    by_cases hy : y = 0
    · simp [hy, tf_zero]
    rw [lifts_unique g (tf_spec g (mul_ne_zero hx hy)) (lifts_mul g (tf_spec g hx) (tf_spec g hy))]
    rfl

/- English proof (translation)
Establish `h1 : tf g x = tf g y` using `Subtype.ext h`. Rewrite using `[← (tf_spec g hx).2, ← (tf_spec g hy).2, h1]`.
-/
theorem teichM_inj (x y : Fbar g) (hx : x ≠ 0) (hy : y ≠ 0) (h : teichM g x = teichM g y) : x = y := by
  have h1 : tf g x = tf g y := Subtype.ext h
  rw [← (tf_spec g hx).2, ← (tf_spec g hy).2, h1]

def datumOf (t : Fbar g →* ℂ) (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : LabelDatum g where
  teich := t
  teich_inj := ht
  gen d := red g (ez (g ^ d - 1))
  gen_order d hd := ((gen_prim g hd).eq_orderOf).symm
  gen_norm d e hd he := by
    rw [← map_pow, ez_pow (N_pos g (Nat.mul_pos hd he)) (N_dvd g d e)]

def datum : LabelDatum g := datumOf g (teichM g) (teichM_inj g)

instance : Nonempty (LabelDatum g) := ⟨datum g⟩

open Formalism.MainNotions.ArithmeticCylinders
variable {g}

/- English proof (translation)
Establish `hex : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m` using `⟨n, rfl⟩`. Rewrite using `[thetaOf, dif_pos hex]`. Establish `hm` using `hex.choose_spec`. Establish `hN` using `N_pos g hd`. Establish `hP : IsPrimitiveRoot (L.gen d) (g ^ d - 1)` using `L.gen_order d hd ▸ IsPrimitiveRoot.orderOf (L.gen d)`.

Establish `h1 : n % (g ^ d - 1) = hex.choose % (g ^ d - 1)`. Apply `hP.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)` to reduce the goal to its premises. Rewrite using `[← L.gen_order d hd, pow_mod_orderOf, pow_mod_orderOf]`. Conclude with `hm`. Establish `h2 : orderOf (L.teich x) ∣ g ^ d - 1` using `orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])`.

Establish `h3 : n % orderOf (L.teich x) = hex.choose % orderOf (L.teich x)` using `Nat.ModEq.of_dvd h2 h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem thetaOf_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have hex : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  rw [thetaOf, dif_pos hex]
  have hm := hex.choose_spec
  have hN := N_pos g hd
  have hP : IsPrimitiveRoot (L.gen d) (g ^ d - 1) :=
    L.gen_order d hd ▸ IsPrimitiveRoot.orderOf (L.gen d)

  have h1 : n % (g ^ d - 1) = hex.choose % (g ^ d - 1) := by
    apply hP.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
    rw [← L.gen_order d hd, pow_mod_orderOf, pow_mod_orderOf]
    exact hm
  have h2 : orderOf (L.teich x) ∣ g ^ d - 1 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h3 : n % orderOf (L.teich x) = hex.choose % orderOf (L.teich x) := Nat.ModEq.of_dvd h2 h1
  calc L.teich x ^ hex.choose = L.teich x ^ (hex.choose % orderOf (L.teich x)) :=
        (pow_mod_orderOf _ _).symm
    _ = L.teich x ^ (n % orderOf (L.teich x)) := by rw [h3]
    _ = L.teich x ^ n := pow_mod_orderOf _ _

/- English proof (translation)
Establish `hx' : x ^ (g ^ (d * e) - 1) = 1`. Take `⟨c, hc⟩` from `N_dvd g d e`. Rewrite using `[hc, pow_mul, hx, one_pow]`. Rewrite using `[thetaOf_gen_pow L (Nat.mul_pos hd he) hx', ← pow_mul, Nat.mul_comm n, pow_mul, L.gen_norm d e hd he, thetaOf_gen_pow L hd hx]`.
-/
theorem thetaOf_norm (L : LabelDatum g) {d e : ℕ} (hd : 0 < d) (he : 0 < e) {x : Fbar g}
    (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L (d * e) x (L.gen (d * e) ^ n) =
      thetaOf L d x ((L.gen (d * e) ^ n) ^ ((g ^ (d * e) - 1) / (g ^ d - 1))) := by
  have hx' : x ^ (g ^ (d * e) - 1) = 1 := by
    obtain ⟨c, hc⟩ := N_dvd g d e
    rw [hc, pow_mul, hx, one_pow]
  rw [thetaOf_gen_pow L (Nat.mul_pos hd he) hx', ← pow_mul, Nat.mul_comm n, pow_mul,
    L.gen_norm d e hd he, thetaOf_gen_pow L hd hx]

/- English proof (translation)
Proceed by induction on `Q with`. Consider the case `nil => simp [degL]`. Consider the case `cons p Q ih`. Take `⟨hm, hdeg, hc⟩` from `ih (fun q hq => h q (List.mem_cons_of_mem p hq))`. Take `⟨⟨pm, -, pc, pdeg⟩, -, -⟩` from `h p (List.mem_cons.mpr (Or.inl rfl))`.

Simplify using `only [List.map_cons, List.prod_cons]`. Use `⟨pm.mul hm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pm.natDegree_mul hm, pdeg, hdeg]`. Simplify using `[degL]`. Rewrite using `[Polynomial.mul_coeff_zero]`.

Conclude with `mul_ne_zero pc hc`.
-/
theorem cuspOf_prod (L : LabelDatum g) (Q : List ((ZMod g)[X] × Pc g)) (h : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) :
    (Q.map Prod.fst).prod.Monic ∧ (Q.map Prod.fst).prod.natDegree = degL (Q.map Prod.snd) ∧
      (Q.map Prod.fst).prod.coeff 0 ≠ 0 := by
  induction Q with
  | nil => simp [degL]
  | cons p Q ih =>
    obtain ⟨hm, hdeg, hc⟩ := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    obtain ⟨⟨pm, -, pc, pdeg⟩, -, -⟩ := h p (List.mem_cons.mpr (Or.inl rfl))
    simp only [List.map_cons, List.prod_cons]
    refine ⟨pm.mul hm, ?_, ?_⟩
    · rw [pm.natDegree_mul hm, pdeg, hdeg]
      simp [degL]
    · rw [Polynomial.mul_coeff_zero]
      exact mul_ne_zero pc hc

/- English proof (translation)
Establish `hempty : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} = ∅`. Use extensionality with `χ`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce and unpack `- ⟨Q, hQ, hdeg, rfl, -⟩`. Take `⟨h1, h2, h3⟩` from `cuspOf_prod L Q hQ`.

Conclude with `hf ⟨h1, h2.trans hdeg, h3⟩`. Rewrite using `[eSerC, hempty, finsum_mem_empty]`.
-/
theorem eSerC_zero (L : LabelDatum g) (n : ℕ) (f : (ZMod g)[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0)) : eSerC L n f = 0 := by
  have hempty : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} = ∅ := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨Q, hQ, hdeg, rfl, -⟩
    obtain ⟨h1, h2, h3⟩ := cuspOf_prod L Q hQ
    exact hf ⟨h1, h2.trans hdeg, h3⟩
  rw [eSerC, hempty, finsum_mem_empty]

/- English proof (translation)
Rewrite using `[toG, dif_pos x.isUnit]`. Conclude with `Units.ext (IsUnit.unit_spec _)`.
-/
theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  rw [toG, dif_pos x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[tl, entN]`.
-/
theorem tl_self {n : ℕ} (M : Mt g n) : tl n M = M := by
  ext i j
  simp [tl, entN]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hpar : ∀ M : Mt g n, InPar n M` using `fun M i j _ hi => absurd i.isLt (not_lt.mpr hi)`. Establish `hα' : ∀ y : Gn g n, α (y⁻¹ * x * y) = α x` using `fun y => by`. Simplify using `using hα x y⁻¹`. Establish `hcard : (Fintype.card (Gn g n) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`.

Simplify using `only [hc, hcT, hpar, if_true, mul_one, tl_self, toG_coe, hα', Finset.sum_const, Finset.filter_true, Finset.card_univ, nsmul_eq_mul]`. Conclude with `inv_mul_cancel_left₀ hcard _`.
-/
theorem hc_full {n : ℕ} (α : Gn g n → ℂ) (hα : IsClass α) : hc n 0 α (fun _ => 1) n = α := by
  funext x

  have hpar : ∀ M : Mt g n, InPar n M := fun M i j _ hi => absurd i.isLt (not_lt.mpr hi)
  have hα' : ∀ y : Gn g n, α (y⁻¹ * x * y) = α x := fun y => by
    simpa using hα x y⁻¹
  have hcard : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [hc, hcT, hpar, if_true, mul_one, tl_self, toG_coe, hα', Finset.sum_const,
    Finset.filter_true, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

/- English proof (translation)
Establish `: NeZero (Nat.card G : ℂ)` using `⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩`. Set `V : FDRep ℂ G` to `FDRep.of (Representation.trivial ℂ G ℂ)`. Establish `hchar : ∀ x, V.character x = 1`. Introduce `x`. Simplify using `[V, FDRep.character, Representation.trivial]`.

Use `⟨V, ?_, hchar⟩` and prove the remaining obligations. Rewrite using `[FDRep.simple_iff_char_is_norm_one]`. Simplify using `[hchar, Nat.card_eq_fintype_card]`.
-/
theorem isIrr_one {G : Type} [Group G] [Fintype G] : IsIrr (fun _ : G => (1 : ℂ)) := by
  have : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let V : FDRep ℂ G := FDRep.of (Representation.trivial ℂ G ℂ)
  have hchar : ∀ x, V.character x = 1 := by
    intro x
    simp [V, FDRep.character, Representation.trivial]
  refine ⟨V, ?_, hchar⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  simp [hchar, Nat.card_eq_fintype_card]

/- English proof (translation)
Simplify `hz` using `[rootsBar, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.roots_X_sub_C]`.
-/
theorem mem_rootsBar_X_sub_C {a : ZMod g} {z : Fbar g} (hz : z ∈ rootsBar (X - C a)) :
    z = algebraMap (ZMod g) (Fbar g) a := by
  simpa [rootsBar, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.roots_X_sub_C] using hz

/- English proof (translation)
Use `⟨⟨monic_X_sub_C 1, irreducible_X_sub_C 1, by simp, natDegree_X_sub_C 1⟩, ⟨one_pos, isIrr_one, fun a ha ha' => by omega⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx y _ z hz`. Establish `hx1 : x = 1` using `by simpa using mem_rootsBar_X_sub_C hx`. Substitute `hx1` using the available equality. Establish `hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0)`.

Rewrite using `[Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]`. Both sides reduce to the same expression. Rewrite `hz` using `[hcp]`. Establish `hz'` using `mem_rootsBar_X_sub_C hz`. Establish `hy0 : (y : Mt g 1) 0 0 ≠ 0`.

Use `(Matrix.isUnit_iff_isUnit_det _).mp y.isUnit` as an intermediate fact. Rewrite `this` using `[Matrix.det_unique]`. Conclude with `this.ne_zero`. Establish `hzN : z ^ (g ^ 1 - 1) = 1`. Rewrite using `[hz', ← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hy0, map_one]`.

Establish `hP : IsPrimitiveRoot (L.gen 1) (g ^ 1 - 1)` using `L.gen_order 1 one_pos ▸ IsPrimitiveRoot.orderOf (L.gen 1)`. Establish `: NeZero (g ^ 1 - 1)` using `⟨(N_pos g one_pos).ne'⟩`. Take `⟨i, -, hi⟩` from `hP.eq_pow_of_pow_eq_one hzN`. Simplify using `only [Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one]`. Rewrite using `[thetaOf, dif_pos ⟨i, hi.symm⟩, map_one, one_pow]`.
-/
theorem isCuspOf_one (L : LabelDatum g) : IsCuspOf L (X - C 1) (fun _ : Gn g 1 => (1 : ℂ)) := by
  refine ⟨⟨monic_X_sub_C 1, irreducible_X_sub_C 1, by simp, natDegree_X_sub_C 1⟩,
    ⟨one_pos, isIrr_one, fun a ha ha' => by omega⟩, ?_⟩
  intro x hx y _ z hz
  have hx1 : x = 1 := by simpa using mem_rootsBar_X_sub_C hx
  subst hx1

  have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
    rw [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]
    rfl
  rw [hcp] at hz
  have hz' := mem_rootsBar_X_sub_C hz
  have hy0 : (y : Mt g 1) 0 0 ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
    rw [Matrix.det_unique] at this
    exact this.ne_zero
  have hzN : z ^ (g ^ 1 - 1) = 1 := by
    rw [hz', ← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hy0, map_one]
  have hP : IsPrimitiveRoot (L.gen 1) (g ^ 1 - 1) :=
    L.gen_order 1 one_pos ▸ IsPrimitiveRoot.orderOf (L.gen 1)
  have : NeZero (g ^ 1 - 1) := ⟨(N_pos g one_pos).ne'⟩
  obtain ⟨i, -, hi⟩ := hP.eq_pow_of_pow_eq_one hzN
  simp only [Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one]
  rw [thetaOf, dif_pos ⟨i, hi.symm⟩, map_one, one_pow]

/- English proof (translation)
Establish `key : hcL [(⟨1, fun _ => 1⟩ : Pc g)] 1 = fun _ : Gn g 1 => (1 : ℂ)`. Rewrite using `[hcL_cons, hcL_nil]`. Conclude with `hc_full (fun _ => 1) (fun _ _ => rfl)`. Use `⟨[(X - C 1, ⟨1, fun _ => 1⟩)], ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Rewrite `hp` using `[List.mem_singleton]`. Substitute `hp` using the available equality. Conclude with `isCuspOf_one L`. Simplify using `[degL]`. Simplify using the standard rewrite rules.

Simplify using `only [List.map_cons, List.map_nil]`. Rewrite using `[key]`. Establish `hcard : (Fintype.card (Gn g 1) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Simplify using `only [ip, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[inv_mul_cancel₀ hcard]`.

Conclude with `one_ne_zero`.
-/
theorem hasLabel_one (L : LabelDatum g) : HasLabel L (fun _ : Gn g 1 => (1 : ℂ)) (X - C 1) := by
  have key : hcL [(⟨1, fun _ => 1⟩ : Pc g)] 1 = fun _ : Gn g 1 => (1 : ℂ) := by
    rw [hcL_cons, hcL_nil]
    exact hc_full (fun _ => 1) (fun _ _ => rfl)
  refine ⟨[(X - C 1, ⟨1, fun _ => 1⟩)], ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact isCuspOf_one L
  · simp [degL]
  · simp
  · simp only [List.map_cons, List.map_nil]
    rw [key]
    have hcard : (Fintype.card (Gn g 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [ip, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [inv_mul_cancel₀ hcard]
    exact one_ne_zero

/- English proof (translation)
Establish `hd : 0 < d` using `h.2.1.1`. Take `⟨τ, hτ, hinj, -⟩` from `hG g L d hd`. Establish `root : ∀ f : (ZMod g)[X], 0 < f.natDegree → ∃ x, x ∈ rootsBar f`. Introduce `f hf`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root (f.map (algebraMap (ZMod g) (Fbar g))) (by rw [Polynomial.degree_map]; exact (Polynomial.natDegree_pos_iff_degree_pos.mp hf).ne')`.

Use `⟨x, (Polynomial.mem_roots (Polynomial.map_ne_zero ?_)).mpr hx⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hf`. Establish `same : ∀ {Q : (ZMod g)[X]} {ψ ψ' : Gn g d → ℂ}, IsCuspOf L Q ψ → IsCuspOf L Q ψ' → ψ = ψ'`. Introduce `Q ψ ψ' hψ hψ'`.

Apply `hE ψ ψ' hψ.2.1 hψ'.2.1` to reduce the goal to its premises. Introduce `y hy`. Take `⟨x, hx⟩` from `root Q (by rw [hψ.1.2.2.2]; exact hd)`. Take `⟨z, hz⟩` from `root (y : Mt g d).charpoly (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hd)`. Rewrite using `[hψ.2.2 x hx y hy z hz, hψ'.2.2 x hx y hy z hz]`.

Apply `hinj P P' h.1 h'.1` to reduce the goal to its premises. Rewrite using `[← same h (hτ P h.1).1, ← same h' (hτ P' h'.1).1]`.
-/
theorem label_unique (hG : Green) (L : LabelDatum g) {d : ℕ}
    (hE : ∀ χ χ' : Gn g d → ℂ, IsCusp χ → IsCusp χ' →
      (∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → χ y = χ' y) → χ = χ')
    {P P' : (ZMod g)[X]} {χ : Gn g d → ℂ} (h : IsCuspOf L P χ) (h' : IsCuspOf L P' χ) : P = P' := by
  have hd : 0 < d := h.2.1.1
  obtain ⟨τ, hτ, hinj, -⟩ := hG g L d hd

  have root : ∀ f : (ZMod g)[X], 0 < f.natDegree → ∃ x, x ∈ rootsBar f := by
    intro f hf
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap (ZMod g) (Fbar g)))
      (by rw [Polynomial.degree_map]; exact (Polynomial.natDegree_pos_iff_degree_pos.mp hf).ne')
    refine ⟨x, (Polynomial.mem_roots (Polynomial.map_ne_zero ?_)).mpr hx⟩
    rintro rfl
    simp at hf

  have same : ∀ {Q : (ZMod g)[X]} {ψ ψ' : Gn g d → ℂ}, IsCuspOf L Q ψ → IsCuspOf L Q ψ' → ψ = ψ' := by
    intro Q ψ ψ' hψ hψ'
    apply hE ψ ψ' hψ.2.1 hψ'.2.1
    intro y hy
    obtain ⟨x, hx⟩ := root Q (by rw [hψ.1.2.2.2]; exact hd)
    obtain ⟨z, hz⟩ := root (y : Mt g d).charpoly
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hd)
    rw [hψ.2.2 x hx y hy z hz, hψ'.2.2 x hx y hy z hz]
  apply hinj P P' h.1 h'.1
  rw [← same h (hτ P h.1).1, ← same h' (hτ P' h'.1).1]

end GlobalTheory.GLq.Model
