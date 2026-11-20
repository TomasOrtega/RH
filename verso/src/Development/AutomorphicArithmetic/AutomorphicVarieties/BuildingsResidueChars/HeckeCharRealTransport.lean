import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open ReciprocityTheory.Neutral.Bridge.HCFR

/- English proof (translation)
Use `⟨v'.comap j.symm.toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Use `show v' (j.symm (j x)) = v' x`. Rewrite using `[RingEquiv.symm_apply_apply]`.
-/
private theorem comap_surj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (v' : InfinitePlace E) :
    ∃ v : InfinitePlace L, v.comap j.toRingHom = v' := by
  refine ⟨v'.comap j.symm.toRingHom, ?_⟩
  ext x
  show v' (j.symm (j x)) = v' x
  rw [RingEquiv.symm_apply_apply]

/- English proof (translation)
Use extensionality with `x`. Establish `h1 : (u.comap j.toRingHom) (j.symm x) = (v.comap j.toRingHom) (j.symm x)` using `by rw [h]`. Express the relevant statement in the definitionally equal form `u (j (j.symm x)) = v (j (j.symm x)) at h1`. Rewrite `h1` using `[RingEquiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
private theorem comap_inj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (u v : InfinitePlace L)
    (h : u.comap j.toRingHom = v.comap j.toRingHom) : u = v := by
  ext x
  have h1 : (u.comap j.toRingHom) (j.symm x) = (v.comap j.toRingHom) (j.symm x) := by rw [h]
  change u (j (j.symm x)) = v (j (j.symm x)) at h1
  rwa [RingEquiv.apply_symm_apply] at h1

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `u show CT.infEquiv j u (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) (v.comap j.toRingHom) (-1) (u.comap j.toRingHom)) = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) v (-1) u`. Distinguish the cases in `h : u = v`. Substitute `h` using the available equality.

Rewrite using `[Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]`. Establish `h' : u.comap j.toRingHom ≠ v.comap j.toRingHom` using `fun e => h (comap_inj j u v e)`. Rewrite using `[Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, map_one]`. Use `show CT.finMap j 1 = 1`. Conclude with `map_one _`.
-/
private theorem idMap_infIdele {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (j : E ≃+* L)
    (v : InfinitePlace L) :
    CT.idMap j (infIdele E (v.comap j.toRingHom) (-1)) = infIdele L v (-1) := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext u
    show CT.infEquiv j u (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) (v.comap j.toRingHom) (-1)
      (u.comap j.toRingHom)) = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) v (-1) u
    by_cases h : u = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]
    · have h' : u.comap j.toRingHom ≠ v.comap j.toRingHom := fun e => h (comap_inj j u v e)
      rw [Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, map_one]
  · show CT.finMap j 1 = 1
    exact map_one _

/- English proof (translation)
Introduce `F K _ _ _ _ _ _ _ h2 χ`. Use `haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := h2 }`. Set `j : maximalRealSubfield K ≃+* F` to `(CMExtension.equivMaximalRealSubfield F K).symm`. Use `⟨CT.transport j χ, fun v' => ?_, fun w => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl⟩` from `comap_surj j v'`.

Use `⟨v, ?_⟩` and prove the remaining obligations. Use `show χ.1 (CT.idMap j (infIdele _ (v.comap j.toRingHom) (-1))) = χ.1 (infIdele F v (-1))`. Rewrite using `[idMap_infIdele]`. Establish `hp : CT.plMap j (w.under (𝓞 (maximalRealSubfield K))) = w.under (𝓞 F)`. Use extensionality with `x`.

Use `show algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal`. Establish `e : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) = algebraMap (𝓞 F) (𝓞 K) x` using `RingOfIntegers.ext rfl`. Rewrite using `[e]`. Use `⟨?_, fun hu => ?_⟩` and prove the remaining obligations. Establish `h` using `CT.absNorm_plMap j (w.under (𝓞 (maximalRealSubfield K)))`.

Rewrite `h` using `[hp, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `h.symm`. Rewrite `hu` using `[← hp]`. Use `⟨(CT.transport_unrAt_iff j χ _).mpr hu, ?_⟩` and prove the remaining obligations. Rewrite using `[CT.transport_val j χ _ hu, hp]`.
-/
theorem UpperTheory.heckeChar_realTransport :
    UpperTheory.V.Af.Cr.RealTransport := by
  intro F K _ _ _ _ _ _ _ h2 χ
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := h2 }
  let j : maximalRealSubfield K ≃+* F := (CMExtension.equivMaximalRealSubfield F K).symm
  refine ⟨CT.transport j χ, fun v' => ?_, fun w => ?_⟩
  · obtain ⟨v, rfl⟩ := comap_surj j v'
    refine ⟨v, ?_⟩
    show χ.1 (CT.idMap j (infIdele _ (v.comap j.toRingHom) (-1))) = χ.1 (infIdele F v (-1))
    rw [idMap_infIdele]
  · have hp : CT.plMap j (w.under (𝓞 (maximalRealSubfield K))) = w.under (𝓞 F) := by
      ext x
      show algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) ∈ w.asIdeal ↔
        algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
      have e : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) =
          algebraMap (𝓞 F) (𝓞 K) x := RingOfIntegers.ext rfl
      rw [e]
    refine ⟨?_, fun hu => ?_⟩
    · have h := CT.absNorm_plMap j (w.under (𝓞 (maximalRealSubfield K)))
      rw [hp, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
      exact h.symm
    · rw [← hp] at hu
      refine ⟨(CT.transport_unrAt_iff j χ _).mpr hu, ?_⟩
      rw [CT.transport_val j χ _ hu, hp]
