import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjField
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjField

open GlobalTheory.AbelianProjective

section BaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

abbrev bcProj (X : Over S) : ((Over.pullback f).obj X).left ⟶ X.left := pullback.fst X.hom f

/- English proof (translation)
Simplify using `only [Over.pullback_map_left]`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem map_left_bcProj {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ bcProj f Y = bcProj f X ≫ g.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Use `IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f) ?_ (map_left_bcProj f g).symm (IsPullback.of_hasPullback Y.hom f)` and prove the remaining obligations. Establish `e : ((Over.pullback f).map g).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f`. Simplify using `only [Over.pullback_map_left]`. Conclude with `pullback.lift_snd _ _ _`. Rewrite using `[e, Over.w]`.

Conclude with `IsPullback.of_hasPullback X.hom f`.
-/
theorem isPullback_bcProj {X Y : Over S} (g : X ⟶ Y) :
    IsPullback (bcProj f X) ((Over.pullback f).map g).left g.left (bcProj f Y) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f) ?_ (map_left_bcProj f g).symm
    (IsPullback.of_hasPullback Y.hom f)
  have e : ((Over.pullback f).map g).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  rw [e, Over.w]
  exact IsPullback.of_hasPullback X.hom f

def bcProd (X Y : Over S) : ((Over.pullback f).obj X ⊗ (Over.pullback f).obj Y).left ⟶ (X ⊗ Y).left :=
  (Functor.LaxMonoidal.μ (Over.pullback f) X Y).left ≫ bcProj f (X ⊗ Y)

/- English proof (translation)
Rewrite using `[bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_fst]`.
-/
theorem bcProd_fst (X Y : Over S) :
    bcProd f X Y ≫ (fst X Y).left = (fst ((Over.pullback f).obj X) ((Over.pullback f).obj Y)).left ≫ bcProj f X := by
  rw [bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_fst]

/- English proof (translation)
Rewrite using `[bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_snd]`.
-/
theorem bcProd_snd (X Y : Over S) :
    bcProd f X Y ≫ (snd X Y).left = (snd ((Over.pullback f).obj X) ((Over.pullback f).obj Y)).left ≫ bcProj f Y := by
  rw [bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_snd]

/- English proof (translation)
Rewrite using `[bcProd, bcProd, ← Category.assoc, ← Over.comp_left, Functor.LaxMonoidal.μ_natural_left, Over.comp_left, Category.assoc, map_left_bcProj, Category.assoc]`.
-/
theorem bcProd_whiskerRight {W V : Over S} (π : W ⟶ V) (X : Over S) :
    ((Over.pullback f).map π ▷ (Over.pullback f).obj X).left ≫ bcProd f V X = bcProd f W X ≫ (π ▷ X).left := by
  rw [bcProd, bcProd, ← Category.assoc, ← Over.comp_left, Functor.LaxMonoidal.μ_natural_left, Over.comp_left,
    Category.assoc, map_left_bcProj, Category.assoc]

end BaseChange

section Group

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

/- English proof (translation)
Rewrite using `[Hom.mul_def, Hom.mul_def, Functor.map_comp, Functor.obj.μ_def, ← Functor.Monoidal.lift_μ]`. Simplify using `only [← Category.assoc]`. Use `congr 2`. Rewrite using `[comp_lift, Functor.map_comp, Functor.Monoidal.μ_fst_assoc, Functor.Monoidal.μ_snd]`.
-/
theorem bcSum_eq {W X : Over S} [GrpObj X] (a : W ⟶ X) :
    (fst ((Over.pullback f).obj W) ((Over.pullback f).obj X) ≫ (Over.pullback f).map a) *
        snd ((Over.pullback f).obj W) ((Over.pullback f).obj X) =
      Functor.LaxMonoidal.μ (Over.pullback f) W X ≫ (Over.pullback f).map ((fst W X ≫ a) * snd W X) := by
  rw [Hom.mul_def, Hom.mul_def, Functor.map_comp, Functor.obj.μ_def, ← Functor.Monoidal.lift_μ]
  simp only [← Category.assoc]
  congr 2
  rw [comp_lift, Functor.map_comp, Functor.Monoidal.μ_fst_assoc, Functor.Monoidal.μ_snd]

/- English proof (translation)
Rewrite using `[bcSum_eq, Over.comp_left, Category.assoc, map_left_bcProj, bcProd, Category.assoc]`.
-/
theorem bcSum_left {W X : Over S} [GrpObj X] (a : W ⟶ X) :
    ((fst ((Over.pullback f).obj W) ((Over.pullback f).obj X) ≫ (Over.pullback f).map a) *
        snd ((Over.pullback f).obj W) ((Over.pullback f).obj X)).left ≫ bcProj f X =
      bcProd f W X ≫ ((fst W X ≫ a) * snd W X).left := by
  rw [bcSum_eq, Over.comp_left, Category.assoc, map_left_bcProj, bcProd, Category.assoc]

end Group

/- English proof (translation)
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `: Subsingleton (Sp K)` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Establish `: Nonempty (Sp Ω)` using `inferInstanceAs (Nonempty (PrimeSpectrum Ω))`. Conclude with `⟨Classical.arbitrary _, Subsingleton.elim _ _⟩`.
-/
theorem surjective_spMap (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] : Surjective (spMap (algebraMap K Ω)) := by
  refine ⟨fun x => ?_⟩
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Sp Ω) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  exact ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

/- English proof (translation)
Introduce `K Ω _ _ _ A _ _ N₀ _ ⟨W, V, π, a, U, N, n, hπ, ha, hW, hWt, hU, hUne, hN, H, hloc⟩`. Establish `hf` using `surjective_spMap K Ω`. Use `set f := spMap (algebraMap K Ω)`. Establish `hsurj : ∀ X : Over (Sp K), Function.Surjective (bcProj f X)` using `fun X => (MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback X.hom f).flip hf).surj`. Establish `sq` using `bcProd_whiskerRight f π A`.

Establish `pb : IsPullback (bcProd f W A) ((Over.pullback f).map π ▷ (Over.pullback f).obj A).left (π ▷ A).left (bcProd f V A)`. Use `IsPullback.of_right (h₁₂ := (fst W A).left) (v₁₃ := π.left) (h₂₂ := (fst V A).left) ?_ sq.symm (isPullback_whiskerRight π A)` and prove the remaining obligations. Rewrite using `[bcProd_fst, bcProd_fst]`. Conclude with `(isPullback_whiskerRight _ _).paste_horiz (isPullback_bcProj f π)`. Use `⟨(Over.pullback f).obj W, (Over.pullback f).obj V, (Over.pullback f).map π, (Over.pullback f).map a, bcProj f A ⁻¹ᵁ U, N.pull (bcProd f V A), GlobalTheory.secPull n (bcProd f V A), MorphismProperty.of_isPullback (isPullback_bcProj f π) hπ, MorphismProperty.of_isPullback (isPullba …` and prove the remaining obligations.

Take `⟨w⟩` from `hW`. Take `⟨w', -⟩` from `hsurj W w`. Conclude with `⟨w'⟩`. Conclude with `MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback W.hom f) hWt`. Establish `: IsAffineHom (bcProj f A)` using `MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback A.hom f).flip inferInstance`.

Conclude with `hU.preimage _`. Take `⟨u, hu⟩` from `hUne`. Take `⟨u', rfl⟩` from `hsurj A u`. Conclude with `⟨u', hu⟩`. Establish `e : (snd ((Over.pullback f).obj V) ((Over.pullback f).obj A)).left ≫ bcProj f A = bcProd f V A ≫ (snd V A).left` using `(bcProd_snd f V A).symm`.

Conclude with `LBIso.chartPull (GlobalTheory.chartPullPull N (bcProd f V A)) (chartPullLinComb N₀ (bcProj f A) (fun _ : PUnit => _) (fun _ => (snd V A).left) (fun _ => 1) _ fun _ => e) H`. Introduce `x'`. Rewrite using `[GlobalTheory.nonzeroLocus_secPull]`. Express the relevant statement in the definitionally equal form `bcProd f V A x' ∈ Out.nonzeroLocus n ↔ _`. Rewrite using `[hloc]`.

Prove the components needed by the constructor for the conclusion. Introduce `h z' hz'`. Express the relevant statement in the definitionally equal form `bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U`. Rewrite using `[← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply]`. Use `h _ ?_` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, ← sq, Scheme.Hom.comp_apply, hz']`. Introduce `h z hz`. Take `⟨z', rfl, hz'⟩` from `Scheme.exists_preimage_of_isPullback pb z x' hz`. Establish `h'` using `h z' hz'`. Express the relevant statement in the definitionally equal form `bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U at h'`.

Rewrite `h'` using `[← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply]`. Conclude with `h'`.
-/
theorem normChart_baseChange : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A],
    IsAbelianScheme A → ∀ N₀ : LB A.left, N₀.IsLB → NormChart A N₀ →
      NormChart ((Over.pullback (spMap (algebraMap K Ω))).obj A)
        (N₀.pull (pullback.fst A.hom (spMap (algebraMap K Ω)))) := by
  intro K Ω _ _ _ A _ _ N₀ _ ⟨W, V, π, a, U, N, n, hπ, ha, hW, hWt, hU, hUne, hN, H, hloc⟩
  have hf := surjective_spMap K Ω
  set f := spMap (algebraMap K Ω)
  have hsurj : ∀ X : Over (Sp K), Function.Surjective (bcProj f X) := fun X =>
    (MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback X.hom f).flip hf).surj
  have sq := bcProd_whiskerRight f π A
  have pb : IsPullback (bcProd f W A) ((Over.pullback f).map π ▷ (Over.pullback f).obj A).left (π ▷ A).left
      (bcProd f V A) := by
    refine IsPullback.of_right (h₁₂ := (fst W A).left) (v₁₃ := π.left) (h₂₂ := (fst V A).left) ?_ sq.symm
      (isPullback_whiskerRight π A)
    rw [bcProd_fst, bcProd_fst]
    exact (isPullback_whiskerRight _ _).paste_horiz (isPullback_bcProj f π)
  refine ⟨(Over.pullback f).obj W, (Over.pullback f).obj V, (Over.pullback f).map π, (Over.pullback f).map a,
    bcProj f A ⁻¹ᵁ U, N.pull (bcProd f V A), GlobalTheory.secPull n (bcProd f V A),
    MorphismProperty.of_isPullback (isPullback_bcProj f π) hπ,
    MorphismProperty.of_isPullback (isPullback_bcProj f a) ha, ?_, ?_, ?_, ?_, pull_isLB hN _, ?_, ?_⟩
  · obtain ⟨w⟩ := hW
    obtain ⟨w', -⟩ := hsurj W w
    exact ⟨w'⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback W.hom f) hWt
  · have : IsAffineHom (bcProj f A) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback A.hom f).flip inferInstance
    exact hU.preimage _
  · obtain ⟨u, hu⟩ := hUne
    obtain ⟨u', rfl⟩ := hsurj A u
    exact ⟨u', hu⟩
  · have e : (snd ((Over.pullback f).obj V) ((Over.pullback f).obj A)).left ≫ bcProj f A =
        bcProd f V A ≫ (snd V A).left := (bcProd_snd f V A).symm
    exact LBIso.chartPull (GlobalTheory.chartPullPull N (bcProd f V A))
      (chartPullLinComb N₀ (bcProj f A) (fun _ : PUnit => _) (fun _ => (snd V A).left) (fun _ => 1) _
        fun _ => e) H
  · intro x'
    rw [GlobalTheory.nonzeroLocus_secPull]
    change bcProd f V A x' ∈ Out.nonzeroLocus n ↔ _
    rw [hloc]
    constructor
    · intro h z' hz'
      change bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U
      rw [← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply]
      refine h _ ?_
      rw [← Scheme.Hom.comp_apply, ← sq, Scheme.Hom.comp_apply, hz']
    · intro h z hz
      obtain ⟨z', rfl, hz'⟩ := Scheme.exists_preimage_of_isPullback pb z x' hz
      have h' := h z' hz'
      change bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U at h'
      rw [← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply] at h'
      exact h'

end GlobalTheory.ProjField
