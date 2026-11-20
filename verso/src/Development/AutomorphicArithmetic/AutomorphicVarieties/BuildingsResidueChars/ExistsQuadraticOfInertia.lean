import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

/- English proof (translation)
Establish `hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A` using `fun x => by`. Establish `h : IsIntegral A (algebraMap L Ω (x : L))` using `(x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.

Set `f : 𝓞 L →+* A` to `((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint`. Set `P : Ideal (𝓞 L)` to `(IsLocalRing.maximalIdeal A).comap f`. Establish `hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P` using `fun x => (A.valuation_lt_one_iff (f x)).symm`. Establish `hu : v.asIdeal = P.under (𝓞 K)`. Use extensionality with `x`.

Rewrite using `[← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]`. Both sides reduce to the same expression. Establish `hne : P ≠ ⊥`. Introduce `h`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[hu, h]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Conclude with `⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩`.
-/
private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

/- English proof (translation)
Introduce `hQ hI hR F Ω _ _ _ _ _ _ l _ h2 S hS`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : IsScalarTower ℚ F Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Use `haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic`. Use `haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩`.

Establish `hT : {v | ¬ S v}.Finite` using `Filter.eventually_cofinite.1 hS`. Establish `h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, v ∉ (fun w : HeightOneSpectrum (𝓞 F) => w.under (𝓞 ℚ)) '' {v | ¬ S v}` using `(hT.image _).eventually_cofinite_notMem`. Take `⟨K₀, _, _, _, _, _, _, hK₀, hl, v₀, A, ⟨hv1, hv2⟩, hA, s, hs, hsn⟩` from `Cq.exQuad Ω l h2 _ (h1.and (hR ℚ F Ω))`. Take `⟨d, y₀, hd, hy₀, hgen⟩` from `hI K₀ hK₀`. Take `⟨K, i1, i2, i3, i4, i5, i6, i7, hK, y, hy, hgenK⟩` from `hQ F Ω (d : F) (algebraMap K₀ Ω y₀) (by rw [← map_pow, hy₀, map_ratCast, map_ratCast]) (fun φ => by rw [map_ratCast]; exact_mod_cast hd)`.

Take `⟨w, hw, hwv⟩` from `place_between (L := F) hA`. Take `⟨t, rfl⟩` from `hv2 A hA hs`. Use `⟨K, i1, i2, i3, i4, i5, i6, i7, hK, fun j L hL x => ?_, w, A, ?_, hw, t, hs, ?_⟩` and prove the remaining obligations. Take `⟨a, b, rfl⟩` from `hgenK x`. Take `⟨z, hz⟩` from `Cq.embPadic K₀ hK₀ l hl (j.comp (algebraMap K₀ Ω)) y₀`.

Rewrite using `[map_add, map_mul, hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add, map_mul]`. Use `add_mem (hL a) (mul_mem (hL b) ?_)` and prove the remaining obligations. Rewrite `hz` using `[RingHom.comp_apply]`. Rewrite using `[← hz]`. Conclude with `L.1.algebraMap_mem z`.

Assume the negation of the conclusion as `h`. Conclude with `hv1 ⟨w, h, hwv⟩`. Introduce and unpack `⟨u, rfl⟩`. Establish `hu : u (algebraMap K₀ Ω y₀) = algebraMap K₀ Ω y₀` using `by rw [← hy]; exact u.commutes y`. Use `hsn ⟨{ u.toRingEquiv with commutes' := fun x => ?_ }, AlgEquiv.ext fun _ => rfl⟩` and prove the remaining obligations.

Take `⟨a, b, rfl⟩` from `hgen x`. Use `show u _ = _`. Simplify using `only [map_add, map_mul, map_ratCast, hu]`.
-/
theorem UpperTheory.exists_quadratic_of_inertia :
    UpperTheory.V.Af.Cr.QuadCM → UpperTheory.V.Af.Cr.ImagGen → UpperTheory.V.Af.Cr.IneRes → UpperTheory.V.Af.Cr.ExQuadR := by
  intro hQ hI hR F Ω _ _ _ _ _ _ l _ h2 S hS
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsScalarTower ℚ F Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hT : {v | ¬ S v}.Finite := Filter.eventually_cofinite.1 hS
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      v ∉ (fun w : HeightOneSpectrum (𝓞 F) => w.under (𝓞 ℚ)) '' {v | ¬ S v} :=
    (hT.image _).eventually_cofinite_notMem
  obtain ⟨K₀, _, _, _, _, _, _, hK₀, hl, v₀, A, ⟨hv1, hv2⟩, hA, s, hs, hsn⟩ :=
    Cq.exQuad Ω l h2 _ (h1.and (hR ℚ F Ω))
  obtain ⟨d, y₀, hd, hy₀, hgen⟩ := hI K₀ hK₀
  obtain ⟨K, i1, i2, i3, i4, i5, i6, i7, hK, y, hy, hgenK⟩ := hQ F Ω (d : F) (algebraMap K₀ Ω y₀)
    (by rw [← map_pow, hy₀, map_ratCast, map_ratCast]) (fun φ => by rw [map_ratCast]; exact_mod_cast hd)
  obtain ⟨w, hw, hwv⟩ := place_between (L := F) hA
  obtain ⟨t, rfl⟩ := hv2 A hA hs
  refine ⟨K, i1, i2, i3, i4, i5, i6, i7, hK, fun j L hL x => ?_, w, A, ?_, hw, t, hs, ?_⟩
  · obtain ⟨a, b, rfl⟩ := hgenK x
    obtain ⟨z, hz⟩ := Cq.embPadic K₀ hK₀ l hl (j.comp (algebraMap K₀ Ω)) y₀
    rw [map_add, map_mul, hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add, map_mul]
    refine add_mem (hL a) (mul_mem (hL b) ?_)
    rw [RingHom.comp_apply] at hz
    rw [← hz]
    exact L.1.algebraMap_mem z
  · by_contra h
    exact hv1 ⟨w, h, hwv⟩
  · rintro ⟨u, rfl⟩
    have hu : u (algebraMap K₀ Ω y₀) = algebraMap K₀ Ω y₀ := by rw [← hy]; exact u.commutes y
    refine hsn ⟨{ u.toRingEquiv with commutes' := fun x => ?_ }, AlgEquiv.ext fun _ => rfl⟩
    obtain ⟨a, b, rfl⟩ := hgen x
    show u _ = _
    simp only [map_add, map_mul, map_ratCast, hu]
