import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

/- English proof (translation)
The claim follows from `(GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r ↦ by simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c).trans (Subtype.ext (IsMor.pullCohomologyOne_id _ _))`.
-/
theorem red_constPull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c :=
  (GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀))
    (fun r ↦ by simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c).trans
    (Subtype.ext (IsMor.pullCohomologyOne_id _ _))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H c`. Use `H ((GlobalTheory.FODef.constMorV k V A₀).pull c)` as an intermediate fact. Rewrite `this` using `[red_constPull]`. Conclude with `this`.

Introduce `H c'`. Establish `hm` using `GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)`. Take `⟨z, rfl⟩` from `hm.2 c'`. Proceed by induction on `z with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `add x x' hx hx' => simp only [map_add, hx, hx']`. Consider the case `tmul r c`. Rewrite using `[liftSemi_tmul]`. Establish `h1` using `(GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull.map_smulₛₗ r ((GlobalTheory.FODef.constMorV k V A₀).pull c)`. Use `(congrArg y h1).trans ?_` and prove the remaining obligations.

Rewrite using `[red_constPull, map_smul, H c]`. Establish `h2` using `e.map_smul r ((GlobalTheory.FODef.constMorV k V A₀).pull c)`. Rewrite using `[h2]`. Conclude with `(TrivSqZeroExt.fst_mul r _).symm`.
-/
theorem corr_crysRedMor_iff (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) (y : HdR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y ↔
      ∀ c, y c = TrivSqZeroExt.fst (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)) := by
  constructor
  · intro H c
    have := H ((GlobalTheory.FODef.constMorV k V A₀).pull c)
    rw [red_constPull] at this
    exact this
  · intro H c'
    have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)
    obtain ⟨z, rfl⟩ := hm.2 c'
    induction z with
    | zero => simp only [map_zero]
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | tmul r c =>
      rw [liftSemi_tmul]
      have h1 := (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull.map_smulₛₗ r
        ((GlobalTheory.FODef.constMorV k V A₀).pull c)
      refine (congrArg y h1).trans ?_
      rw [red_constPull, map_smul, H c]
      have h2 := e.map_smul r ((GlobalTheory.FODef.constMorV k V A₀).pull c)
      rw [h2]
      exact (TrivSqZeroExt.fst_mul r _).symm

/- English proof (translation)
Introduce `p _ D R _ b N k _ _ tk s o₀ _ d f y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨e, he, hc⟩` from `exists_mem_glueFil o₀.A o₀.ab f hy`. Use `⟨e, he, (corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).2 fun c ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[hc c]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨e, ⟨x, hx, z, -, he⟩, hc⟩`. Establish `hxy : y = x` using `LinearMap.ext fun c ↦ by`. Rewrite using `[(corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).1 hc c, he c]`.

Simplify using the standard rewrite rules. Conclude with `hxy ▸ hx`.
-/
theorem mem_fil_iff_exists_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, (corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).2 fun c ↦ ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, -, he⟩, hc⟩
    have hxy : y = x := LinearMap.ext fun c ↦ by
      rw [(corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).1 hc c, he c]
      simp
    exact hxy ▸ hx

end GlobalTheory.HTGlue
