import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.DecComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PowIne
import Mathlib.NumberTheory.Multiplicity

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

/- English proof (translation)
Assume the negation of the conclusion as `h1`. Establish `hm : PadicInt.toZMod (u - 1) = 0`. Use `congrArg PadicInt.toZMod hu` as an intermediate fact. Rewrite `this` using `[map_pow, ZMod.pow_card, map_one]`. Rewrite using `[map_sub, this, map_one, sub_self]`.

Rewrite `hm` using `[← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Take `⟨b, hb⟩` from `hm`. Establish `hu' : u = 1 + l * b` using `by rw [← hb]; ring`. Establish `hs : ∑ i ∈ Finset.range l, u ^ i = 0`. Use `mul_geom_sum u l` as an intermediate fact.

Rewrite `this` using `[hu, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)`. Establish `hd` using `odd_sq_dvd_geom_sum₂_sub (1 : ℤ_[l]) b (hl.out.odd_of_ne_two h2)`. Simplify using `only [one_pow, mul_one, ← hu', hs, zero_sub, dvd_neg] at hd`. Establish `hl0 : (l : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hl.out.ne_zero`.

Establish `hd' : (l : ℤ_[l]) * l ∣ l * 1` using `by rwa [mul_one, ← sq]`. Conclude with `PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hl0).1 hd'))`.
-/
private theorem no_tors (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (u : ℤ_[l]) (hu : u ^ l = 1) : u = 1 := by
  by_contra h1
  have hm : PadicInt.toZMod (u - 1) = 0 := by
    have := congrArg PadicInt.toZMod hu
    rw [map_pow, ZMod.pow_card, map_one] at this
    rw [map_sub, this, map_one, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  obtain ⟨b, hb⟩ := hm
  have hu' : u = 1 + l * b := by rw [← hb]; ring
  have hs : ∑ i ∈ Finset.range l, u ^ i = 0 := by
    have := mul_geom_sum u l
    rw [hu, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  have hd := odd_sq_dvd_geom_sum₂_sub (1 : ℤ_[l]) b (hl.out.odd_of_ne_two h2)
  simp only [one_pow, mul_one, ← hu', hs, zero_sub, dvd_neg] at hd
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hd' : (l : ℤ_[l]) * l ∣ l * 1 := by rwa [mul_one, ← sq]
  exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hl0).1 hd'))

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l hl h2 A hA s ⟨h1, a, h3⟩`. Use `⟨Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a) (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h3), ?_⟩` and prove the remaining obligations. Establish `h4 : s ^ l ^ a ∈ (cycZ F Ω l).ker`. Use `Subgroup.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage (continuous_cycZ F Ω l)) h3` and prove the remaining obligations. Rewrite using `[Subgroup.commutator_le]`.

Introduce `g _ h _`. Rewrite using `[MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]`. Rewrite `h4` using `[MonoidHom.mem_ker, map_pow]`. Establish `: ∀ (b : ℕ) (u : ℤ_[l]), u ^ l ^ b = 1 → u = 1`. Introduce `b`.

Proceed by induction on `b with`. Consider the case `zero => simp`. Consider the case `succ b ih => intro u hu; exact ih u (no_tors l h2 _ (by rw [← pow_mul, ← pow_succ, hu]))`. Conclude with `Units.ext (this a _ (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]))`.
-/
theorem UpperTheory.inertia_acts_trivially_on_roots_of_unity :
    UpperTheory.V.Sd.S3.MuIne := by
  intro F Ω _ _ _ _ _ l hl h2 A hA s ⟨h1, a, h3⟩
  refine ⟨Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a)
    (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h3), ?_⟩
  have h4 : s ^ l ^ a ∈ (cycZ F Ω l).ker := by
    refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage (continuous_cycZ F Ω l)) h3
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  rw [MonoidHom.mem_ker, map_pow] at h4
  have : ∀ (b : ℕ) (u : ℤ_[l]), u ^ l ^ b = 1 → u = 1 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih => intro u hu; exact ih u (no_tors l h2 _ (by rw [← pow_mul, ← pow_succ, hu]))
  exact Units.ext (this a _ (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]))
