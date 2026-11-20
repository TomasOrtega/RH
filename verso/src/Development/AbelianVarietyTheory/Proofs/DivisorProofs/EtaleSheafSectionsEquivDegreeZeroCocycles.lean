import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCZero

noncomputable def clHom (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    Cocycle ((chains R).obj E) (res R F) 0 →+ H R E F 0 :=
  AddMonoidHom.mk' (fun c => CohomologyClass.mk c) (fun a b => CohomologyClass.mk_add a b)

/- English proof (translation)
Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : 0 < p`. Conclude with `(GlobalTheory.EtC.HCElements.chains_X_isZero R E p hp).eq_of_src _ _`. Conclude with `(GlobalTheory.EtC.HCElements.res_X_isZero R F q (by omega)).eq_of_tgt _ _`.
-/
theorem cochain_neg_one_eq_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (β : Cochain ((chains R).obj E) (res R F) (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · exact (GlobalTheory.EtC.HCElements.chains_X_isZero R E p hp).eq_of_src _ _
  · exact (GlobalTheory.EtC.HCElements.res_X_isZero R F q (by omega)).eq_of_tgt _ _

/- English proof (translation)
Use `⟨fun a b hab => ?_, fun x => ?_⟩` and prove the remaining obligations. Establish `h0 : CohomologyClass.mk (a - b) = 0`. Rewrite using `[CohomologyClass.mk_sub]`. Conclude with `sub_eq_zero.2 hab`. Rewrite `h0` using `[CohomologyClass.mk_eq_zero_iff]`.

Take `⟨m, hm, β, hβ⟩` from `h0`. Take `rfl : m = -1` from `by omega`. Rewrite `hβ` using `[cochain_neg_one_eq_zero R F E β, δ_zero]`. Rewrite using `[← sub_eq_zero]`. Conclude with `Cocycle.ext (by simpa using hβ.symm)`.

Take `⟨c, rfl⟩` from `x.mk_surjective`. Conclude with `⟨c, rfl⟩`.
-/
theorem clHom_bijective (R : Type) [CommRing R] (F : Shv R) (E : Spc) : Function.Bijective (clHom R F E) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : CohomologyClass.mk (a - b) = 0 := by
      rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 hab
    rw [CohomologyClass.mk_eq_zero_iff] at h0
    obtain ⟨m, hm, β, hβ⟩ := h0
    obtain rfl : m = -1 := by omega
    rw [cochain_neg_one_eq_zero R F E β, δ_zero] at hβ
    rw [← sub_eq_zero]
    exact Cocycle.ext (by simpa using hβ.symm)
  · obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c, rfl⟩

/- English proof (translation)
Introduce `R _ F`. Take `⟨-, e, he, -⟩` from `GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F`. Set `cE : ∀ X : Scheme.{0}, Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 ≃+ H R (sch.obj X) F 0` to `fun X => AddEquiv.ofBijective (clHom R F (sch.obj X)) (clHom_bijective R F (sch.obj X))`. Set `φ : ∀ X : Scheme.{0}, Sec F X →+ Cochain ((chains R).obj (sch.obj X)) (res R F) 0` to `fun X => (AddMonoidHom.mk' (fun c : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 => c.1) (fun _ _ => rfl)).comp ((cE X).symm.toAddMonoidHom.comp (e X).toAddMonoidHom)`. Establish `hφ : ∀ X s, φ X s = ((cE X).symm (e X s)).1` using `fun _ _ => rfl`.

Use `⟨{ app := fun U => AddCommGrpCat.ofHom (φ U.unop), naturality := ?_ }, fun U => ⟨?_, fun z => ⟨?_, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `U V f`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `φ V.unop ((F.obj.map f).hom x) = ((HC R F).map (sch.map f.unop).op).f 0 (φ U.unop x)`. Use `set c := (cE U.unop).symm (e U.unop x) with hc`.

Establish `key : (cE V.unop) (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) = e V.unop ((F.obj.map f).hom x)`. Establish `h1` using `he f.unop x`. Establish `h2 : pull R (sch.map f.unop) F 0 (cE U.unop c) = CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0))` using `rfl`. Rewrite `h2` using `[hc, AddEquiv.apply_symm_apply]`. Rewrite `h1` using `[h2]`.

Conclude with `h1`. Rewrite using `[hφ, hφ, ← key, AddEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Introduce `a b hab`. Express the relevant statement in the definitionally equal form `φ U.unop a = φ U.unop b at hab`.

Rewrite `hab` using `[hφ, hφ]`. Conclude with `(e U.unop).injective ((cE U.unop).symm.injective (Subtype.ext hab))`. Introduce `hz`. Use `⟨(e U.unop).symm (cE U.unop (Cocycle.mk z (0 + 1) rfl hz)), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ U.unop _ = z`.

Rewrite using `[hφ, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Introduce and unpack `⟨x, rfl⟩`. Express the relevant statement in the definitionally equal form `δ 0 (0 + 1) (φ U.unop x) = 0`. Rewrite using `[hφ]`.

Conclude with `((cE U.unop).symm (e U.unop x)).2`.
-/
theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  intro R _ F
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  let cE : ∀ X : Scheme.{0}, Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 ≃+ H R (sch.obj X) F 0 :=
    fun X => AddEquiv.ofBijective (clHom R F (sch.obj X)) (clHom_bijective R F (sch.obj X))
  let φ : ∀ X : Scheme.{0}, Sec F X →+ Cochain ((chains R).obj (sch.obj X)) (res R F) 0 :=
    fun X => (AddMonoidHom.mk' (fun c : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 => c.1) (fun _ _ => rfl)).comp
      ((cE X).symm.toAddMonoidHom.comp (e X).toAddMonoidHom)
  have hφ : ∀ X s, φ X s = ((cE X).symm (e X s)).1 := fun _ _ => rfl
  refine ⟨{ app := fun U => AddCommGrpCat.ofHom (φ U.unop), naturality := ?_ }, fun U => ⟨?_, fun z => ⟨?_, ?_⟩⟩⟩
  · intro U V f
    ext x
    change φ V.unop ((F.obj.map f).hom x) = ((HC R F).map (sch.map f.unop).op).f 0 (φ U.unop x)
    set c := (cE U.unop).symm (e U.unop x) with hc
    have key : (cE V.unop) (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) =
        e V.unop ((F.obj.map f).hom x) := by
      have h1 := he f.unop x
      have h2 : pull R (sch.map f.unop) F 0 (cE U.unop c) =
          CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) := rfl
      rw [hc, AddEquiv.apply_symm_apply] at h2
      rw [h2] at h1
      exact h1
    rw [hφ, hφ, ← key, AddEquiv.symm_apply_apply]
    rfl
  · intro a b hab
    change φ U.unop a = φ U.unop b at hab
    rw [hφ, hφ] at hab
    exact (e U.unop).injective ((cE U.unop).symm.injective (Subtype.ext hab))
  · intro hz
    refine ⟨(e U.unop).symm (cE U.unop (Cocycle.mk z (0 + 1) rfl hz)), ?_⟩
    change φ U.unop _ = z
    rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, rfl⟩
    change δ 0 (0 + 1) (φ U.unop x) = 0
    rw [hφ]
    exact ((cE U.unop).symm (e U.unop x)).2

end GlobalTheory.EtC.HCZero
