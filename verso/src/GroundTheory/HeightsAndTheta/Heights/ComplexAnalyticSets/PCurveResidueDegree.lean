import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

/- English proof (translation)
Introduce `n I q _ hdim P`. Use `P.isMaximal` as an intermediate fact. Set `_ : Field (curveNormalisation I q ⧸ P.asIdeal)` to `Ideal.Quotient.field _`. Establish `hO : Nontrivial (curveLocalRing I q)`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Rewrite `hdim` using `[ringKrullDim_eq_bot_of_subsingleton]`. Conclude with `absurd hdim (by decide)`. Establish `hIq : ∀ g ∈ I, eval q g = 0`. Introduce `g hg`.

Assume the negation of the conclusion as `hgq`. Establish `hu` using `isUnit_algebraMap_curveLocalRing I q g hgq`. Establish `h0 : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)`. Rewrite `hu` using `[h0]`. Conclude with `not_isUnit_zero hu`.

Set `evL : Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) →+* ℂ` to `IsLocalization.lift (M := (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl) (g := eval q) (fun s ↦ isUnit_iff_ne_zero.2 fun h ↦ s.2 (RingHom.mem_ker.2 h))`. Establish `hJ : ∀ a ∈ I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))), evL a = 0`. Introduce `a ha`. Establish `hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))) ≤ RingHom.ker evL`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `g hg`. Simplify using `[evL, IsLocalization.lift_eq, hIq g hg]`. Conclude with `hle ha`. Set `ε : curveLocalRing I q →+* ℂ` to `Ideal.Quotient.lift _ evL hJ`. Set `K` to `curveNormalisation I q ⧸ P.asIdeal`.

Set `π : curveLocalRing I q →+* K` to `algebraMap (curveLocalRing I q) K`. Set `ι : ℂ →+* K` to `π.comp ((algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)).comp C)`. Establish `: Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q)` using `inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q) ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))`. Establish `hmax : (P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal`. Establish `hmax'` using `Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))))) Ideal.Quotient.mk_surjective (K := P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisati …`.

Establish `hloc` using `IsLocalRing.eq_maximalIdeal hmax'`. Establish `hker : ∀ a ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ), π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) a) = 0`. Introduce `a ha`. Rewrite `ha` using `[← Localization.AtPrime.under_maximalIdeal (I := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)), Ideal.under, Ideal.mem_comap, ← hloc]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 ha`.

Establish `hcomp : π = ι.comp ε`. Use `Ideal.Quotient.ringHom_ext ?_` and prove the remaining obligations. Use `IsLocalization.ringHom_ext (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl ?_` and prove the remaining obligations. Use `MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)` and prove the remaining obligations. Use `show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) = ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)))`.

Establish `he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) = c` using `by show evL (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (C c)) = c`. Simplify using `[evL, IsLocalization.lift_eq]`. Rewrite using `[he]`. Both sides reduce to the same expression. Establish `h1 : (X i - C (q i) : MvPolynomial (Fin n) ℂ) ∈ RingHom.ker (eval q)` using `by simp`.

Establish `h2` using `hker _ h1`. Rewrite `h2` using `[map_sub, map_sub, sub_eq_zero]`. Use `show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) = ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)))`. Establish `he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) = q i` using `by show evL (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (X i)) = q i`. Simplify using `[evL, IsLocalization.lift_eq]`.

Rewrite using `[he]`. Conclude with `h2`. Establish `hint : ι.IsIntegral`. Introduce `z`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective z`.

Establish `hb : IsIntegral (curveLocalRing I q) b` using `Algebra.IsIntegral.isIntegral b`. Take `⟨p, hp, he⟩` from `hb.map (Ideal.Quotient.mkₐ (curveLocalRing I q) P.asIdeal)`. Use `⟨p.map ε, hp.map ε, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, ← hcomp]`. Conclude with `he`.

Establish `hsurj : Function.Surjective ι` using `(IsAlgClosed.ringHom_bijective_of_isIntegral ι hint).2`. Establish `hπ : Function.Surjective π` using `fun y ↦ by`. Take `⟨c, hc⟩` from `hsurj y`. Conclude with `⟨_, hc⟩`. Rewrite using `[Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]`.

Use `⟨inferInstance, fun x hx y ↦ ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `hπ (y * x⁻¹)`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toSpanSingleton_apply, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `π r * x = y`.

Rewrite using `[hr, mul_assoc, inv_mul_cancel₀ hx, mul_one]`.
-/
theorem CurveResidueDegree.proof : CurveResidueDegree.Statement := by
  intro n I q _ hdim P
  have := P.isMaximal
  let _ : Field (curveNormalisation I q ⧸ P.asIdeal) := Ideal.Quotient.field _

  have hO : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)

  have hIq : ∀ g ∈ I, eval q g = 0 := by
    intro g hg
    by_contra hgq
    have hu := isUnit_algebraMap_curveLocalRing I q g hgq
    have h0 : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
    rw [h0] at hu
    exact not_isUnit_zero hu

  let evL : Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) →+* ℂ :=
    IsLocalization.lift (M := (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl) (g := eval q)
      (fun s ↦ isUnit_iff_ne_zero.2 fun h ↦ s.2 (RingHom.mem_ker.2 h))
  have hJ : ∀ a ∈ I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))), evL a = 0 := by
    intro a ha
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ)
        (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))) ≤ RingHom.ker evL := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp [evL, IsLocalization.lift_eq, hIq g hg]
    exact hle ha
  let ε : curveLocalRing I q →+* ℂ := Ideal.Quotient.lift _ evL hJ
  let K := curveNormalisation I q ⧸ P.asIdeal
  let π : curveLocalRing I q →+* K := algebraMap (curveLocalRing I q) K
  let ι : ℂ →+* K := π.comp ((algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)).comp C)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  have hmax : (P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
  have hmax' := Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))))
    Ideal.Quotient.mk_surjective (K := P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)))
    (H := hmax)
  have hloc := IsLocalRing.eq_maximalIdeal hmax'
  have hker : ∀ a ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ),
      π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) a) = 0 := by
    intro a ha
    rw [← Localization.AtPrime.under_maximalIdeal (I := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)),
      Ideal.under, Ideal.mem_comap, ← hloc] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

  have hcomp : π = ι.comp ε := by
    refine Ideal.Quotient.ringHom_ext ?_
    refine IsLocalization.ringHom_ext (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl ?_
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) = c := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (C c)) = c
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      rfl
    · have h1 : (X i - C (q i) : MvPolynomial (Fin n) ℂ) ∈ RingHom.ker (eval q) := by simp
      have h2 := hker _ h1
      rw [map_sub, map_sub, sub_eq_zero] at h2
      show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) = q i := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (X i)) = q i
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      exact h2

  have hint : ι.IsIntegral := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : IsIntegral (curveLocalRing I q) b := Algebra.IsIntegral.isIntegral b
    obtain ⟨p, hp, he⟩ := hb.map (Ideal.Quotient.mkₐ (curveLocalRing I q) P.asIdeal)
    refine ⟨p.map ε, hp.map ε, ?_⟩
    rw [Polynomial.eval₂_map, ← hcomp]
    exact he
  have hsurj : Function.Surjective ι := (IsAlgClosed.ringHom_bijective_of_isIntegral ι hint).2
  have hπ : Function.Surjective π := fun y ↦ by
    obtain ⟨c, hc⟩ := hsurj y
    exact ⟨_, hc⟩

  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun x hx y ↦ ?_⟩
  obtain ⟨r, hr⟩ := hπ (y * x⁻¹)
  refine ⟨r, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  change π r * x = y
  rw [hr, mul_assoc, inv_mul_cancel₀ hx, mul_one]

end

end GroundTheory.Heights₂.Heights
