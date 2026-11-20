import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCommMonObjTors
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.MuConst GlobalTheory.HTSheaf GlobalTheory.LieVB
open GlobalTheory.Conormal

namespace GlobalTheory.TorsionChart

/- English proof (translation)
Use `set I := Ideal.map f.hom (RingHom.ker g.hom) with hIdef`. Establish `hw : ∀ a, i.hom (f.hom a) = j.hom (g.hom a)` using `fun a => congr($(po.w).hom a)`. Establish `hI : I ≤ RingHom.ker i.hom`. Rewrite using `[hIdef, Ideal.map_le_iff_le_comap]`. Introduce `a ha`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hw, (RingHom.mem_ker).1 ha, map_zero]`. Set `mk : B ⟶ CommRingCat.of (B ⧸ I)` to `CommRingCat.ofHom (Ideal.Quotient.mk I)`. Establish `hker : RingHom.ker g.hom ≤ RingHom.ker ((Ideal.Quotient.mk I).comp f.hom)`. Introduce `a ha`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_map_of_mem _ ha`. Set `φ : {g' : A →+* B ⧸ I // RingHom.ker g.hom ≤ RingHom.ker g'}` to `⟨(Ideal.Quotient.mk I).comp f.hom, hker⟩`. Set `ψ : C ⟶ CommRingCat.of (B ⧸ I)` to `CommRingCat.ofHom (g.hom.liftOfSurjective hg φ)`. Establish `hψ : f ≫ mk = g ≫ ψ`. Use extensionality with `a`.

Conclude with `(RingHom.liftOfSurjective_comp_apply g.hom hg φ a).symm`. Set `lift : CommRingCat.of (B ⧸ I) ⟶ D` to `CommRingCat.ofHom (Ideal.Quotient.lift I i.hom hI)`. Establish `h1 : i ≫ po.desc mk ψ hψ = mk` using `po.inl_desc _ _ _`. Establish `h2 : po.desc mk ψ hψ ≫ lift = 𝟙 D`. Use `po.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, h1, Category.comp_id]`. Use extensionality with `b`. Both sides reduce to the same expression. Rewrite using `[← Category.assoc, po.inr_desc, Category.comp_id]`. Use extensionality with `c`.

Take `⟨a, rfl⟩` from `hg c`. Express the relevant statement in the definitionally equal form `lift.hom (ψ.hom (g.hom a)) = j.hom (g.hom a)`. Rewrite using `[show ψ.hom (g.hom a) = mk.hom (f.hom a) from (RingHom.liftOfSurjective_comp_apply g.hom hg φ a), ← hw]`. Both sides reduce to the same expression. Use `⟨fun d => ?_, le_antisymm (fun b hb => ?_) hI⟩` and prove the remaining obligations.

Take `⟨b, hb⟩` from `Ideal.Quotient.mk_surjective ((po.desc mk ψ hψ).hom d)`. Use `⟨b, ?_⟩` and prove the remaining obligations. Use `congr($(h2).hom d)` as an intermediate fact. Express the relevant statement in the definitionally equal form `lift.hom ((po.desc mk ψ hψ).hom d) = d at this`. Rewrite `this` using `[← hb]`.

Conclude with `this`. Use `congr($(h1).hom b)` as an intermediate fact. Express the relevant statement in the definitionally equal form `(po.desc mk ψ hψ).hom (i.hom b) = Ideal.Quotient.mk I b at this`. Rewrite `this` using `[(RingHom.mem_ker).1 hb, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this.symm`.
-/
theorem pushout_inl_surjective_and_ker {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ D} {j : C ⟶ D} (po : IsPushout f g i j) (hg : Function.Surjective g.hom) :
    Function.Surjective i.hom ∧ RingHom.ker i.hom = Ideal.map f.hom (RingHom.ker g.hom) := by
  set I := Ideal.map f.hom (RingHom.ker g.hom) with hIdef
  have hw : ∀ a, i.hom (f.hom a) = j.hom (g.hom a) := fun a => congr($(po.w).hom a)
  have hI : I ≤ RingHom.ker i.hom := by
    rw [hIdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hw, (RingHom.mem_ker).1 ha, map_zero]
  let mk : B ⟶ CommRingCat.of (B ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hker : RingHom.ker g.hom ≤ RingHom.ker ((Ideal.Quotient.mk I).comp f.hom) := by
    intro a ha
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let φ : {g' : A →+* B ⧸ I // RingHom.ker g.hom ≤ RingHom.ker g'} :=
    ⟨(Ideal.Quotient.mk I).comp f.hom, hker⟩
  let ψ : C ⟶ CommRingCat.of (B ⧸ I) := CommRingCat.ofHom (g.hom.liftOfSurjective hg φ)
  have hψ : f ≫ mk = g ≫ ψ := by
    ext a
    exact (RingHom.liftOfSurjective_comp_apply g.hom hg φ a).symm
  let lift : CommRingCat.of (B ⧸ I) ⟶ D := CommRingCat.ofHom (Ideal.Quotient.lift I i.hom hI)
  have h1 : i ≫ po.desc mk ψ hψ = mk := po.inl_desc _ _ _
  have h2 : po.desc mk ψ hψ ≫ lift = 𝟙 D := by
    refine po.hom_ext ?_ ?_
    · rw [← Category.assoc, h1, Category.comp_id]
      ext b
      rfl
    · rw [← Category.assoc, po.inr_desc, Category.comp_id]
      ext c
      obtain ⟨a, rfl⟩ := hg c
      change lift.hom (ψ.hom (g.hom a)) = j.hom (g.hom a)
      rw [show ψ.hom (g.hom a) = mk.hom (f.hom a) from
        (RingHom.liftOfSurjective_comp_apply g.hom hg φ a), ← hw]
      rfl
  refine ⟨fun d => ?_, le_antisymm (fun b hb => ?_) hI⟩
  · obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((po.desc mk ψ hψ).hom d)
    refine ⟨b, ?_⟩
    have := congr($(h2).hom d)
    change lift.hom ((po.desc mk ψ hψ).hom d) = d at this
    rw [← hb] at this
    exact this
  · have := congr($(h1).hom b)
    change (po.desc mk ψ hψ).hom (i.hom b) = Ideal.Quotient.mk I b at this
    rw [(RingHom.mem_ker).1 hb, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

end GlobalTheory.TorsionChart
