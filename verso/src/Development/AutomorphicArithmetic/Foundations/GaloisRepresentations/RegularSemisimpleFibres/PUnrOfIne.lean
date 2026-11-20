import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `K M Ω _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hI`. Establish `hunder : HeightOneSpectrum.under (𝓞 K) w = v`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Use `show algebraMap (𝓞 K) (𝓞 M) x ∈ w.asIdeal ↔ x ∈ v.asIdeal`.

Rewrite using `[← hw, ← hv]`. Establish `hx : algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) = algebraMap K Ω (x : K)`. Rewrite using `[IsScalarTower.algebraMap_apply K M Ω]`. Both sides reduce to the same expression. Rewrite using `[hx]`.

Establish `hlies : w.asIdeal.LiesOver v.asIdeal` using `⟨congrArg HeightOneSpectrum.asIdeal hunder.symm⟩`. Establish `hinert : Ideal.inertia Gal(M/K) w.asIdeal = ⊥`. Rewrite using `[← UpperTheory.V.CF.ineAbs K M Ω A w hw, Subgroup.map_eq_bot_iff]`. Introduce `t ht`. Rewrite using `[MonoidHom.mem_ker]`.

Use extensionality with `x`. Apply `(algebraMap M Ω).injective` to reduce the goal to its premises. Use `show algebraMap M Ω ((t.restrictNormal M) x) = algebraMap M Ω x`. Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Conclude with `hI t ht x`.

Establish `he : w.asIdeal.ramificationIdx (𝓞 K) = 1`. Rewrite using `[← (UpperTheory.V.CF.ineCard).1 K M w, hinert]`. Simplify using the standard rewrite rules. Use `⟨hunder, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨w', hw'⟩`.

Rewrite using `[Algebra.isUnramifiedAt_iff_of_isDedekindDomain, ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w'.asIdeal Gal(M/K), Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(M/K)]`. Conclude with `he`. Introduce `x hx hmem`. Establish `hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 M)) w.asIdeal = v.asIdeal` using `congrArg HeightOneSpectrum.asIdeal hunder`. Establish `hv1 : v.asIdeal.ramificationIdx' w.asIdeal = 1`.

Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]`. Conclude with `he`. Establish `hle : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal` using `Ideal.map_le_iff_le_comap.2 hcomap.ge`. Establish `hnot : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal ^ 2` using `fun h => ((Ideal.ramificationIdx'_ne_one_iff hle).2 h) hv1`. Distinguish the cases in `hxv : x ∈ v.asIdeal`.

Take `⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {x}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxv)`. Establish `hJv : ¬ J ≤ v.asIdeal`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← Ideal.span_singleton_le_iff_mem, hJ, pow_two]`.

Conclude with `Ideal.mul_mono_right h`. Establish `hJw : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ≤ w.asIdeal`. Introduce `h`. Rewrite `h` using `[Ideal.map_le_iff_le_comap, hcomap]`. Conclude with `hJv h`.

Establish `hsup : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal = ⊤`. Assume the negation of the conclusion as `hne`. Conclude with `hJw (le_sup_left.trans ((w.isMaximal.eq_of_le hne le_sup_right).symm.le))`. Establish `hsup2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2 = ⊤`. Establish `hc : IsCoprime (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J) w.asIdeal` using `Ideal.isCoprime_iff_sup_eq.2 hsup`.

Conclude with `Ideal.isCoprime_iff_sup_eq.1 hc.pow_right`. Apply `hnot` to reduce the goal to its premises. Establish `hx2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ≤ w.asIdeal ^ 2`. Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]`. Conclude with `hmem`.

Establish `hr : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 ≤ w.asIdeal ^ 2` using `Ideal.mul_le_right`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Ideal.mul_sup, hJ, Ideal.map_mul]`. Use `_ ≤ w.asIdeal ^ 2 := sup_le hx2 hr`. Apply `hxv` to reduce the goal to its premises.

Rewrite using `[← hcomap, Ideal.mem_comap]`. Conclude with `Ideal.pow_le_self two_ne_zero hmem`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.unrOfIne :
    UnrOfIne := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hI
  have hunder : HeightOneSpectrum.under (𝓞 K) w = v := by
    apply HeightOneSpectrum.ext
    ext x
    show algebraMap (𝓞 K) (𝓞 M) x ∈ w.asIdeal ↔ x ∈ v.asIdeal
    rw [← hw, ← hv]
    have hx : algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) = algebraMap K Ω (x : K) := by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      rfl
    rw [hx]
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hunder.symm⟩
  have hinert : Ideal.inertia Gal(M/K) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs K M Ω A w hw, Subgroup.map_eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker]
    ext x
    apply (algebraMap M Ω).injective
    show algebraMap M Ω ((t.restrictNormal M) x) = algebraMap M Ω x
    rw [AlgEquiv.restrictNormal_commutes]
    exact hI t ht x
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← (UpperTheory.V.CF.ineCard).1 K M w, hinert]
    simp
  refine ⟨hunder, ?_, ?_⟩
  · rintro ⟨w', hw'⟩
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w'.asIdeal Gal(M/K),
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(M/K)]
    exact he
  · intro x hx hmem
    have hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 M)) w.asIdeal = v.asIdeal :=
      congrArg HeightOneSpectrum.asIdeal hunder
    have hv1 : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
      exact he
    have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal :=
      Ideal.map_le_iff_le_comap.2 hcomap.ge
    have hnot : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal ^ 2 :=
      fun h => ((Ideal.ramificationIdx'_ne_one_iff hle).2 h) hv1
    by_cases hxv : x ∈ v.asIdeal
    · obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {x} :=
        Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxv)
      have hJv : ¬ J ≤ v.asIdeal := by
        intro h
        apply hx
        rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]
        exact Ideal.mul_mono_right h
      have hJw : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ≤ w.asIdeal := by
        intro h
        rw [Ideal.map_le_iff_le_comap, hcomap] at h
        exact hJv h
      have hsup : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal = ⊤ := by
        by_contra hne
        exact hJw (le_sup_left.trans ((w.isMaximal.eq_of_le hne le_sup_right).symm.le))
      have hsup2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2 = ⊤ := by
        have hc : IsCoprime (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J) w.asIdeal :=
          Ideal.isCoprime_iff_sup_eq.2 hsup
        exact Ideal.isCoprime_iff_sup_eq.1 hc.pow_right
      apply hnot
      have hx2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ≤ w.asIdeal ^ 2 := by
        rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
        exact hmem
      have hr : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 ≤ w.asIdeal ^ 2 :=
        Ideal.mul_le_right
      calc Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal
          = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal *
              (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2) := by rw [hsup2, Ideal.mul_top]
        _ = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ⊔
              Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 := by
            rw [Ideal.mul_sup, hJ, Ideal.map_mul]
        _ ≤ w.asIdeal ^ 2 := sup_le hx2 hr
    · apply hxv
      rw [← hcomap, Ideal.mem_comap]
      exact Ideal.pow_le_self two_ne_zero hmem
