import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFnDegAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FnDegAdjoin

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {σ : Type}

def quotEquiv (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) :
    (MvPolynomial σ F ⧸ I) ≃ₐ[F] Algebra.adjoin F (Set.range g) :=
  let e1 := Ideal.quotientEquivAlgOfEq F h
  let e2 := Ideal.quotientKerEquivRange (aeval g : MvPolynomial σ F →ₐ[F] Ω)
  let e3 := Subalgebra.equivOfEq _ _ (aeval_range (R := F) g)
  (e1.trans e2).trans e3

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotEquiv_mk (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) (p : MvPolynomial σ F) :
    (quotEquiv g I h (Ideal.Quotient.mk I p) : Ω) = aeval g p :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incl_apply {S T : Subalgebra F Ω} (h : S ≤ T) (x : S) :
    ((Subalgebra.inclusion h).toRingHom x : Ω) = x :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toRingHom_apply {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (a : A) :
    f.toRingHom a = f a :=
  rfl

end FnDegAdjoin

/- English proof (translation)
Introduce `F Ω _ _ _ K _ ι _ K' _ ι' _ v x' i' hx hV`. Establish `hker : chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i' = RingHom.ker (aeval (fun q => x' q / x' ⟨q.1, i' q.1⟩) : MRingOver F ι' →ₐ[F] Ω)` using `ChartRankAdjoin.chartIdeal_eq_ker hx hV`. Establish `hcomap : (chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').comap (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom = RingHom.ker (aeval ((fun q => x' q / x' ⟨q.1, i' q.1⟩) ∘ v) : MRingOver F ι →ₐ[F] Ω)`. Rewrite using `[hker]`. Use extensionality with `p`.

Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename]`. Set `_` to `adjoinInclAlgebra F (Set.range_comp_subset_range v fun q => x' q / x' ⟨q.1, i' q.1⟩)`. Unfold `fnDeg`. Set `_` to `(chartMap v (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').toAlgebra`. Establish `key` using `Algebra.finrank_eq_of_equiv_equiv (FnDegAdjoin.quotEquiv _ _ hcomap).toRingEquiv (FnDegAdjoin.quotEquiv _ _ hker).toRingEquiv`.

Use `key ?_` and prove the remaining obligations. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]`.

Rewrite using `[RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, chartMap, Ideal.quotientMap_mk]`. Rewrite using `[FnDegAdjoin.incl_apply, FnDegAdjoin.toRingHom_apply, FnDegAdjoin.quotEquiv_mk, FnDegAdjoin.quotEquiv_mk, aeval_rename]`.
-/
theorem FnDegAdjoin.proof : FnDegAdjoin.Statement := by
  classical
  intro F Ω _ _ _ K _ ι _ K' _ ι' _ v x' i' hx hV
  have hker : chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i' =
      RingHom.ker (aeval (fun q => x' q / x' ⟨q.1, i' q.1⟩) : MRingOver F ι' →ₐ[F] Ω) :=
    ChartRankAdjoin.chartIdeal_eq_ker hx hV
  have hcomap : (chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').comap
      (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom =
      RingHom.ker (aeval ((fun q => x' q / x' ⟨q.1, i' q.1⟩) ∘ v) : MRingOver F ι →ₐ[F] Ω) := by
    rw [hker]
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename]
  let _ := adjoinInclAlgebra F (Set.range_comp_subset_range v fun q => x' q / x' ⟨q.1, i' q.1⟩)
  unfold fnDeg
  let _ := (chartMap v (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').toAlgebra
  have key := Algebra.finrank_eq_of_equiv_equiv (FnDegAdjoin.quotEquiv _ _ hcomap).toRingEquiv
    (FnDegAdjoin.quotEquiv _ _ hker).toRingEquiv
  refine key ?_
  refine RingHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Subtype.ext
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, chartMap, Ideal.quotientMap_mk]
  rw [FnDegAdjoin.incl_apply, FnDegAdjoin.toRingHom_apply, FnDegAdjoin.quotEquiv_mk, FnDegAdjoin.quotEquiv_mk,
    aeval_rename]

end GroundTheory.Heights₂.Heights.Inter
