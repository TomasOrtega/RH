import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨E0, i0, m0, ⟨M0⟩⟩` from `lieModel_exists (Sp R) C.A R (𝟙 (Sp R))`. Take `⟨b0, hb0⟩` from `basis_of_lieBasis v hv M0`. Take `⟨E1, i1, m1, ⟨M1⟩⟩` from `lieModel_exists (Sp R) C.A V (spMap f ≫ 𝟙 (Sp R))`. Take `⟨j, hj, -⟩` from `GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) C.A R V f (𝟙 _) E0 E1 M0 M1`. Use `letI : Algebra R V := f.toAlgebra`.

Use `letI : Module R E1 := Module.compHom E1 f`. Use `haveI : IsScalarTower R V E1 := ⟨fun r x e => by show (f r * x) • e = f r • (x • e)`. Rewrite using `[mul_smul]⟩`. Set `jR : E0 →ₗ[R] E1` to `{ toFun := j map_add' := j.map_add map_smul' := fun r e => by show j (r • e) = f r • j e`. Conclude with `j.map_smulₛₗ r e }`.

Use `haveI : SmoothOfRelativeDimension C.g C.A.hom := C.smoothDim`. Use `haveI : Smooth C.A.hom := by first`. Consider the case `exact SmoothOfRelativeDimension.smooth C.g C.A.hom`. Consider the case `exact SmoothOfRelativeDimension.smooth C.g`. Consider the case `exact SmoothOfRelativeDimension.smooth (n := C.g)`.

Establish `hbc : IsBaseChange V jR` using `GlobalTheory.T.lie_model_isBaseChange (Sp R) C.A R V (𝟙 _) E0 E1 M0 M1 jR (fun e => hj e)`. Use `⟨E1, i1, m1, M1, hbc.basis b0, ?_⟩` and prove the remaining obligations. Rewrite using `[IsBaseChange.basis_apply]`. Establish `h` using `hj (b0 0)`. Unfold `LieModel.Lifts at h`.

Establish `h'` using `(Category.comp_id (M1.pt (j (b0 0))).left).symm.trans h`. Use `show (M1.pt (j (b0 0))).left = _`. Rewrite using `[h', hb0]`.
-/
theorem lc (C : Out.PolAV (Sp R)) (v : epsR R ⟶ C.A) (hv : IsLieBasis ![v]) (V : Type) [CommRing V] (f : R →+* V) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module V E) (M : LieModel C.A (spMap f ≫ 𝟙 (Sp R)) E)
      (b : Module.Basis (Fin 1) V E), (M.pt (b 0)).left = spMap (dualMap f) ≫ v.left := by
  obtain ⟨E0, i0, m0, ⟨M0⟩⟩ := lieModel_exists (Sp R) C.A R (𝟙 (Sp R))
  obtain ⟨b0, hb0⟩ := basis_of_lieBasis v hv M0
  obtain ⟨E1, i1, m1, ⟨M1⟩⟩ := lieModel_exists (Sp R) C.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) C.A R V f (𝟙 _) E0 E1 M0 M1
  letI : Algebra R V := f.toAlgebra
  letI : Module R E1 := Module.compHom E1 f
  haveI : IsScalarTower R V E1 := ⟨fun r x e => by
    show (f r * x) • e = f r • (x • e)
    rw [mul_smul]⟩
  let jR : E0 →ₗ[R] E1 :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => by
        show j (r • e) = f r • j e
        exact j.map_smulₛₗ r e }
  haveI : SmoothOfRelativeDimension C.g C.A.hom := C.smoothDim
  haveI : Smooth C.A.hom := by
    first
    | exact SmoothOfRelativeDimension.smooth C.g C.A.hom
    | exact SmoothOfRelativeDimension.smooth C.g
    | exact SmoothOfRelativeDimension.smooth (n := C.g)
  have hbc : IsBaseChange V jR := GlobalTheory.T.lie_model_isBaseChange (Sp R) C.A R V (𝟙 _) E0 E1 M0 M1 jR (fun e => hj e)
  refine ⟨E1, i1, m1, M1, hbc.basis b0, ?_⟩
  rw [IsBaseChange.basis_apply]
  have h := hj (b0 0)
  unfold LieModel.Lifts at h
  have h' := (Category.comp_id (M1.pt (j (b0 0))).left).symm.trans h
  show (M1.pt (j (b0 0))).left = _
  rw [h', hb0]

end PositivityTheory.Xgf.isogeny_decomposition_product

end
