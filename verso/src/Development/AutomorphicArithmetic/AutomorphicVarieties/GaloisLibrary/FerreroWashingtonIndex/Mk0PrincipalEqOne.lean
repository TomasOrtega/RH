import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ClassGroupDivMemOfMulConjEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.LocFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.LocInf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormEqMulCE

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE K y`.
-/
private theorem norm_eq_mul_cE (K : Type) [Field K] [NumberField K] [IsCMField K] (y : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) y) = y * cE K y :=
  _root_.UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE K y

private def prI {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨Ideal.span {b}, mem_nonZeroDivisors_of_ne_zero (by simpa using hb)⟩

/- English proof (translation)
The claim follows from `(ClassGroup.mk0_eq_one_iff _).2 ⟨⟨b, rfl⟩⟩`.
-/
private theorem mk0_principal_eq_one {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ClassGroup.mk0 (prI b hb) = 1 :=
  (ClassGroup.mk0_eq_one_iff _).2 ⟨⟨b, rfl⟩⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Ideal.span {b} * (Ideal.span {b}).map (RingOfIntegers.mapRingEquiv τ) = _`. Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]`.
-/
private theorem prI_mul {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (b : 𝓞 K) (hb : b ≠ 0) :
    (prI b hb * idMap τ (prI b hb)).1 = Ideal.span {b * RingOfIntegers.mapRingEquiv τ b} := by
  change Ideal.span {b} * (Ideal.span {b}).map (RingOfIntegers.mapRingEquiv τ) = _
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]

/- English proof (translation)
Introduce `K _ _ _ a I hU ha hpos hI`. Establish `ha0 : a ≠ 0`. Introduce `h`. Use `nonZeroDivisors.ne_zero (I * idMap (cE K) I).2` as an intermediate fact. Rewrite `this` using `[hI, h]`.

Simplify using `at this`. Establish `ha0' : (a : K) ≠ 0` using `by simpa using ha0`. Establish `hmem : (a : K) ∈ maximalRealSubfield K` using `(IsCMField.complexConj_eq_self_iff K _).1 ha`. Establish `hx0 : (⟨a, hmem⟩ : maximalRealSubfield K) ≠ 0` using `fun h => ha0' (congrArg Subtype.val h)`. Establish `hax : (a : K) = algebraMap (maximalRealSubfield K) K (Units.mk0 _ hx0 : (maximalRealSubfield K)ˣ)` using `rfl`.

Take `⟨β, hβ⟩` from `(GroundTheory.Global.mem_range_norm_iff_forall_local_of_finrank_eq_two (L := K) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (Units.mk0 _ hx0)).2 ⟨locFin K _ a I hU hax hI, locInf K _ fun φ => hax ▸ hpos φ⟩`. Establish `hβ' : (β : K) * cE K β = a`. Rewrite using `[← norm_eq_mul_cE, hax, ← hβ]`. Both sides reduce to the same expression. Take `⟨b, d, hd, hbd⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) (β : K)`.

Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Establish `hd0' : (d : K) ≠ 0` using `by simpa using hd0`. Establish `hb : (b : K) = d * β`. Rewrite using `[← hbd]`. Conclude with `(mul_div_cancel₀ _ hd0').symm`.

Establish `hb0 : b ≠ 0`. Introduce `h`. Rewrite `hb` using `[h]`. Conclude with `mul_ne_zero hd0' β.ne_zero (by simpa using hb.symm)`. Establish `key : d * RingOfIntegers.mapRingEquiv (cE K) d * a = b * RingOfIntegers.mapRingEquiv (cE K) b`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(d : K) * cE K d * a = (b : K) * cE K b`. Rewrite using `[hb, map_mul, ← hβ']`. Expand and normalize the polynomial expressions, which then agree. Use `classGroup_div_mem_of_mul_conj_eq K (cE K) (prI d hd0 * I) (prI b hb0) (IsCMField.complexConj_apply_apply K) (by` as an intermediate fact.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[map_mul, mul_mul_mul_comm, Submonoid.coe_mul, hI, prI_mul, prI_mul, Ideal.span_singleton_mul_span_singleton, key])`. Rewrite `this` using `[map_mul, mk0_principal_eq_one, mk0_principal_eq_one, one_mul, div_one]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.FW.hasse :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (a : 𝓞 K) (I : (Ideal (𝓞 K))⁰), UnrFin K → cE K (a : K) = a → (∀ φ : K →+* ℂ, 0 < (φ (a : K)).re) → (I * idMap (cE K) I).1 = Ideal.span {a} → ClassGroup.mk0 I ∈ difR (clMap (cE K)) := by
  intro K _ _ _ a I hU ha hpos hI
  have ha0 : a ≠ 0 := by
    intro h
    have := nonZeroDivisors.ne_zero (I * idMap (cE K) I).2
    rw [hI, h] at this
    simp at this
  have ha0' : (a : K) ≠ 0 := by simpa using ha0
  have hmem : (a : K) ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K _).1 ha
  have hx0 : (⟨a, hmem⟩ : maximalRealSubfield K) ≠ 0 := fun h => ha0' (congrArg Subtype.val h)
  have hax : (a : K) = algebraMap (maximalRealSubfield K) K (Units.mk0 _ hx0 : (maximalRealSubfield K)ˣ) := rfl
  obtain ⟨β, hβ⟩ := (GroundTheory.Global.mem_range_norm_iff_forall_local_of_finrank_eq_two (L := K)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (Units.mk0 _ hx0)).2
    ⟨locFin K _ a I hU hax hI, locInf K _ fun φ => hax ▸ hpos φ⟩
  have hβ' : (β : K) * cE K β = a := by
    rw [← norm_eq_mul_cE, hax, ← hβ]
    rfl
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (β : K)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : (d : K) ≠ 0 := by simpa using hd0
  have hb : (b : K) = d * β := by
    rw [← hbd]
    exact (mul_div_cancel₀ _ hd0').symm
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb
    exact mul_ne_zero hd0' β.ne_zero (by simpa using hb.symm)
  have key : d * RingOfIntegers.mapRingEquiv (cE K) d * a = b * RingOfIntegers.mapRingEquiv (cE K) b := by
    apply Subtype.ext
    change (d : K) * cE K d * a = (b : K) * cE K b
    rw [hb, map_mul, ← hβ']
    ring
  have := classGroup_div_mem_of_mul_conj_eq K (cE K) (prI d hd0 * I) (prI b hb0) (IsCMField.complexConj_apply_apply K) (by
    apply Subtype.ext
    rw [map_mul, mul_mul_mul_comm, Submonoid.coe_mul, hI, prI_mul, prI_mul,
      Ideal.span_singleton_mul_span_singleton, key])
  rwa [map_mul, mk0_principal_eq_one, mk0_principal_eq_one, one_mul, div_one] at this
