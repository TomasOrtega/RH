import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open ReciprocityTheory.Neutral.Bridge.HCFR

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem comap_surj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (v' : InfinitePlace E) :
    ∃ v : InfinitePlace L, v.comap j.toRingHom = v' := by
  refine ⟨v'.comap j.symm.toRingHom, ?_⟩
  ext x
  show v' (j.symm (j x)) = v' x
  rw [RingEquiv.symm_apply_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
private theorem comap_inj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (u v : InfinitePlace L)
    (h : u.comap j.toRingHom = v.comap j.toRingHom) : u = v := by
  ext x
  have h1 : (u.comap j.toRingHom) (j.symm x) = (v.comap j.toRingHom) (j.symm x) := by rw [h]
  change u (j (j.symm x)) = v (j (j.symm x)) at h1
  rwa [RingEquiv.apply_symm_apply] at h1

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
