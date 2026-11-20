import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Rewrite using `[← mem_perfectClosure_iff_pow_mem q, mem_perfectClosure_iff_natSepDegree_eq_one]`. Establish `hint : IsIntegral K x` using `Algebra.IsIntegral.isIntegral x`. Establish `hspl : ((minpoly K x).map (algebraMap K L)).Splits` using `Normal.splits inferInstance x`. Rewrite using `[Polynomial.natSepDegree_eq_of_splits _ hspl, Finset.card_eq_one]`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Use extensionality with `y`. Simplify using `only [Multiset.mem_toFinset, Polynomial.mem_aroots, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hy⟩`. Take `⟨σ, hσ⟩` from `minpoly.exists_algEquiv_of_root' hint.isAlgebraic hy`.

Rewrite using `[← hσ, hx σ]`. Introduce `h`. Rewrite using `[h]`. Conclude with `⟨minpoly.ne_zero hint, minpoly.aeval K x⟩`.
-/
private lemma exists_pow_mem_of_fixed (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Normal K L] (q : ℕ) [ExpChar K q] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ n, x ^ q ^ n ∈ (algebraMap K L).range := by
  classical
  rw [← mem_perfectClosure_iff_pow_mem q, mem_perfectClosure_iff_natSepDegree_eq_one]
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hspl : ((minpoly K x).map (algebraMap K L)).Splits := Normal.splits inferInstance x
  rw [Polynomial.natSepDegree_eq_of_splits _ hspl, Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [Multiset.mem_toFinset, Polynomial.mem_aroots, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hy⟩
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic hy
    rw [← hσ, hx σ]
  · intro h
    rw [h]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval K x⟩

/- English proof (translation)
Establish `hx : ∀ σ : L ≃ₐ[FractionRing A] L, σ (b : L) = b` using `fun σ => by`. Establish `h` using `algebraMap_galRestrict_apply A (K := FractionRing A) (L := L) (B := integralClosure A L) σ b`. Rewrite `h` using `[hb]`. Conclude with `h.symm`. Take `⟨n, k, hk⟩` from `exists_pow_mem_of_fixed (FractionRing A) L q (b : L) hx`.

Establish `hint : IsIntegral A (algebraMap (FractionRing A) L k)`. Rewrite using `[hk]`. Conclude with `(b ^ q ^ n).2`. Establish `hk' : IsIntegral A k` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom A (FractionRing A) L) (algebraMap (FractionRing A) L).injective).mp hint`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hk'`.

Use `⟨n, a, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[SubmonoidClass.coe_pow, ← hk, ← ha, ← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression.
-/
private lemma fixed_pow_mem (A L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Normal (FractionRing A) L] (q : ℕ) [ExpChar (FractionRing A) q] (b : integralClosure A L)
    (hb : ∀ g : integralClosure A L ≃ₐ[A] integralClosure A L, g b = b) :
    ∃ (n : ℕ) (a : A), b ^ q ^ n = algebraMap A (integralClosure A L) a := by
  have hx : ∀ σ : L ≃ₐ[FractionRing A] L, σ (b : L) = b := fun σ => by
    have h := algebraMap_galRestrict_apply A (K := FractionRing A) (L := L)
      (B := integralClosure A L) σ b
    rw [hb] at h
    exact h.symm
  obtain ⟨n, k, hk⟩ := exists_pow_mem_of_fixed (FractionRing A) L q (b : L) hx
  have hint : IsIntegral A (algebraMap (FractionRing A) L k) := by
    rw [hk]
    exact (b ^ q ^ n).2
  have hk' : IsIntegral A k :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (FractionRing A) L)
      (algebraMap (FractionRing A) L).injective).mp hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk'
  refine ⟨n, a, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, ← hk, ← ha, ← IsScalarTower.algebraMap_apply]
  rfl

/- English proof (translation)
Take `⟨q, hq⟩` from `ExpChar.exists (FractionRing A)`. Take `⟨n, a, ha⟩` from `fixed_pow_mem A L q b hb`. Establish `h1 : φ b ^ q ^ n = φ' b ^ q ^ n`. Rewrite using `[← map_pow, ← map_pow, ha]`. Conclude with `congrArg (fun f : A →+* Ω => f a) h`.

Consider the cases of `hq with`. Consider the case `zero => simpa using h1`. Consider the case `prime hp`. Establish `hA : (q : A) = 0`. Apply `IsFractionRing.injective A (FractionRing A)` to reduce the goal to its premises.

Rewrite using `[map_natCast, map_zero, CharP.cast_eq_zero]`. Establish `hΩ : (q : Ω) = 0`. Use `congrArg (fun f : A →+* Ω => f q) h` as an intermediate fact. Simplify using `only [RingHom.comp_apply, map_natCast] at this`. Rewrite using `[← map_natCast (φ.comp (algebraMap A _)) q, hA, map_zero]`.

Use `haveI : CharP Ω q := (CharP.charP_iff_prime_eq_zero hp).mpr hΩ`. Use `haveI : ExpChar Ω q := ExpChar.prime hp`. Conclude with `iterateFrobenius_inj Ω q n h1`.
-/
private lemma eq_of_fixed (A L Ω : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Normal (FractionRing A) L] [Field Ω] (φ φ' : integralClosure A L →+* Ω)
    (h : φ.comp (algebraMap A _) = φ'.comp (algebraMap A _)) (b : integralClosure A L)
    (hb : ∀ g : integralClosure A L ≃ₐ[A] integralClosure A L, g b = b) : φ b = φ' b := by
  obtain ⟨q, hq⟩ := ExpChar.exists (FractionRing A)
  obtain ⟨n, a, ha⟩ := fixed_pow_mem A L q b hb
  have h1 : φ b ^ q ^ n = φ' b ^ q ^ n := by
    rw [← map_pow, ← map_pow, ha]
    exact congrArg (fun f : A →+* Ω => f a) h
  cases hq with
  | zero => simpa using h1
  | prime hp =>
    have hA : (q : A) = 0 := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_natCast, map_zero, CharP.cast_eq_zero]
    have hΩ : (q : Ω) = 0 := by
      have := congrArg (fun f : A →+* Ω => f q) h
      simp only [RingHom.comp_apply, map_natCast] at this
      rw [← map_natCast (φ.comp (algebraMap A _)) q, hA, map_zero]
    haveI : CharP Ω q := (CharP.charP_iff_prime_eq_zero hp).mpr hΩ
    haveI : ExpChar Ω q := ExpChar.prime hp
    exact iterateFrobenius_inj Ω q n h1

/- English proof (translation)
Introduce `hInv A L Ω _ _ _ _ _ _ _ _ _ _ φ φ' h`. Set `G` to `integralClosure A L ≃ₐ[A] integralClosure A L`. Use `haveI : Finite G := Finite.of_equiv _ (galRestrict A (FractionRing A) L (integralClosure A L)).toEquiv`. Set `A'` to `FixedPoints.subring (integralClosure A L) G`. Use `haveI : SMulCommClass G A' (integralClosure A L) := ⟨fun g a b => by`.

Express the relevant statement in the definitionally equal form `g • ((a : integralClosure A L) * b) = (a : integralClosure A L) * (g • b)`. Rewrite using `[smul_mul', show g • (a : integralClosure A L) = a from a.2 g]⟩`. Use `haveI : Algebra.IsInvariant A' (integralClosure A L) G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩`. Take `⟨g, hg⟩` from `hInv A' (integralClosure A L) G Ω φ φ' (by`. Use extensionality with `a`.

Conclude with `eq_of_fixed A L Ω φ φ' h a fun g => a.2 g)`. Conclude with `⟨g, hg⟩`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.galTrans_of : InvTrans → GalTrans := by
  intro hInv A L Ω _ _ _ _ _ _ _ _ _ _ φ φ' h
  let G := integralClosure A L ≃ₐ[A] integralClosure A L
  haveI : Finite G :=
    Finite.of_equiv _ (galRestrict A (FractionRing A) L (integralClosure A L)).toEquiv
  let A' := FixedPoints.subring (integralClosure A L) G
  haveI : SMulCommClass G A' (integralClosure A L) := ⟨fun g a b => by
    change g • ((a : integralClosure A L) * b) = (a : integralClosure A L) * (g • b)
    rw [smul_mul', show g • (a : integralClosure A L) = a from a.2 g]⟩
  haveI : Algebra.IsInvariant A' (integralClosure A L) G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  obtain ⟨g, hg⟩ := hInv A' (integralClosure A L) G Ω φ φ' (by
    ext a
    exact eq_of_fixed A L Ω φ φ' h a fun g => a.2 g)
  exact ⟨g, hg⟩
