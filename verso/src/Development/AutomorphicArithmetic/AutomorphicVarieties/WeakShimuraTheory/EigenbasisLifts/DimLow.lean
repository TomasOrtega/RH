import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLeOfInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `l _ c N B _ _ _ f J hfin hreg x p _ hpx hJp`. Take `⟨P, hP, hPp⟩` from `Ideal.exists_minimalPrimes_le hJp`. Use `haveI hPprime : P.IsPrime := hP.1.1`. Establish `hJP : J ≤ P` using `hP.1.2`. Use `haveI : IsCO c.O (B ⧸ P) := co_quot c.O B (B ⧸ P) (Ideal.Quotient.mkₐ c.O P) Ideal.Quotient.mk_surjective`.

Use `set g : MvPowerSeries (Fin N) c.O →ₐ[c.O] B ⧸ P := (Ideal.Quotient.mkₐ c.O P).comp f with hg`. Establish `hinj : Function.Injective g`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `hne`.

Establish `hmem : f a ∈ P`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `ha`. Take `⟨y, hyJ, hy⟩` from `Ideal.exists_mul_mem_of_mem_minimalPrimes hP hmem`. Conclude with `hyJ (hreg a hne y hy)`.

Establish `hfinP : (g : MvPowerSeries (Fin N) c.O →+* B ⧸ P).Finite`. Establish `h2` using `(RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJP)).comp hfin`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext fun a => rfl`. Establish `hxP : ∀ a ∈ P, x a = 0` using `fun a ha => by`.

Establish `h3 : a ∈ RingHom.ker x` using `hpx ▸ hPp ha`. Conclude with `h3`. Use `set xb : B ⧸ P →ₐ[c.O] PadicAlgCl l := Ideal.Quotient.liftₐ P x hxP with hxb`. Establish `hxbmk : ∀ b, xb (Ideal.Quotient.mk P b) = x b` using `fun b => rfl`. Establish `hht` using `htLow c N (B ⧸ P) g hinj hfinP xb`.

Use `set q : Ideal (B ⧸ P) := RingHom.ker xb with hq`. Use `haveI : q.IsPrime := RingHom.ker_isPrime _`. Establish `hpq : p = Ideal.comap (Ideal.Quotient.mk P) q`. Use extensionality with `b`. Rewrite using `[hpx, Ideal.mem_comap, hq, RingHom.mem_ker, RingHom.mem_ker, hxbmk]`.

Set `φ` to `Localization.localRingHom p q (Ideal.Quotient.mk P) hpq`. Establish `hφ : Function.Surjective φ`. Introduce `z`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective q.primeCompl z`. Take `⟨r', rfl⟩` from `Ideal.Quotient.mk_surjective r`.

Take `⟨s', hs'⟩` from `Ideal.Quotient.mk_surjective (s : B ⧸ P)`. Establish `hs'p : s' ∈ p.primeCompl`. Introduce `h`. Apply `s.2` to reduce the goal to its premises. Rewrite `h` using `[hpq]`.

Rewrite using `[← hs']`. Conclude with `h`. Use `⟨IsLocalization.mk' (Localization.AtPrime p) r' ⟨s', hs'p⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Localization.localRingHom_mk']`. Use `congr 1`.

Conclude with `Subtype.ext hs'`. Establish `hker : ∀ a ∈ J.map (algebraMap B (Localization.AtPrime p)), φ a = 0`. Introduce `a ha`. Establish `hle : J.map (algebraMap B (Localization.AtPrime p)) ≤ RingHom.ker φ`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `b hb`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Rewrite using `[Localization.localRingHom_to_map]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr (hJP hb), map_zero]`. Conclude with `hle ha`.

Establish `hψ` using `Ideal.Quotient.lift_surjective_of_surjective _ hker hφ`. Establish `hdim` using `ringKrullDim_le_of_surjective _ hψ`. Rewrite `hdim` using `[IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Ws.Eb.dimLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] B) (J : Ideal B), ((Ideal.Quotient.mk J).comp (f : MvPowerSeries (Fin N) c.O →+* B)).Finite → (∀ a, a ≠ 0 → ∀ b, f a * b ∈ J → b ∈ J) →
        ∀ (x : B →ₐ[c.O] PadicAlgCl l) (p : Ideal B) [p.IsPrime], p = RingHom.ker x → J ≤ p → (N : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p ⧸ J.map (algebraMap B (Localization.AtPrime p))) := by
  intro l _ c N B _ _ _ f J hfin hreg x p _ hpx hJp
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_minimalPrimes_le hJp
  haveI hPprime : P.IsPrime := hP.1.1
  have hJP : J ≤ P := hP.1.2
  haveI : IsCO c.O (B ⧸ P) :=
    co_quot c.O B (B ⧸ P) (Ideal.Quotient.mkₐ c.O P) Ideal.Quotient.mk_surjective
  set g : MvPowerSeries (Fin N) c.O →ₐ[c.O] B ⧸ P := (Ideal.Quotient.mkₐ c.O P).comp f with hg
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    have hmem : f a ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    obtain ⟨y, hyJ, hy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hmem
    exact hyJ (hreg a hne y hy)
  have hfinP : (g : MvPowerSeries (Fin N) c.O →+* B ⧸ P).Finite := by
    have h2 := (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJP)).comp hfin
    convert h2 using 1
    exact RingHom.ext fun a => rfl
  have hxP : ∀ a ∈ P, x a = 0 := fun a ha => by
    have h3 : a ∈ RingHom.ker x := hpx ▸ hPp ha
    exact h3
  set xb : B ⧸ P →ₐ[c.O] PadicAlgCl l := Ideal.Quotient.liftₐ P x hxP with hxb
  have hxbmk : ∀ b, xb (Ideal.Quotient.mk P b) = x b := fun b => rfl
  have hht := htLow c N (B ⧸ P) g hinj hfinP xb
  set q : Ideal (B ⧸ P) := RingHom.ker xb with hq
  haveI : q.IsPrime := RingHom.ker_isPrime _
  have hpq : p = Ideal.comap (Ideal.Quotient.mk P) q := by
    ext b
    rw [hpx, Ideal.mem_comap, hq, RingHom.mem_ker, RingHom.mem_ker, hxbmk]
  let φ := Localization.localRingHom p q (Ideal.Quotient.mk P) hpq
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : B ⧸ P)
    have hs'p : s' ∈ p.primeCompl := by
      intro h
      apply s.2
      rw [hpq] at h
      rw [← hs']
      exact h
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) r' ⟨s', hs'p⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  have hker : ∀ a ∈ J.map (algebraMap B (Localization.AtPrime p)), φ a = 0 := by
    intro a ha
    have hle : J.map (algebraMap B (Localization.AtPrime p)) ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [Localization.localRingHom_to_map]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJP hb), map_zero]
    exact hle ha
  have hψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  have hdim := ringKrullDim_le_of_surjective _ hψ
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at hdim
  calc (N : WithBot ℕ∞) ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ ≤ _ := hdim
