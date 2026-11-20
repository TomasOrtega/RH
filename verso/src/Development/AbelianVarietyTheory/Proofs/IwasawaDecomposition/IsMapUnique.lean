import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.LocM.MapUniq

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ _ _ Z₁ Z₂ f f' hf hf'`. Use `Z₁.normal` as an intermediate fact. Establish `: IsReduced Z₁.X` using `GlobalTheory.IsNormalScheme.isReduced`. Use `isProper_str (Z₂.i.c.V W) Z₂.n` as an intermediate fact. Establish `: IsProper Z₂.s`.

Unfold `Pre.s`. Use `infer_instance`. Establish `: IsSeparated (Z₂.s ≫ terminal.from _)` using `inferInstance`. Use `ext_of_fromSpecResidueField_eq _ _ (Z₂.s ≫ terminal.from _) Z₁.opn Z₁.dense (fun x hx => ?_) (terminal.hom_ext _ _)` and prove the remaining obligations. Establish `hr : Set.range (Z₁.X.fromSpecResidueField x) ⊆ Z₁.opn`.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `(Scheme.fromSpecResidueField_apply x a).symm ▸ hx`. Conclude with `CommonMod.natImg_unique hf.1 (hf.2 _ _ hr) (hf'.2 _ _ hr)`.
-/
theorem isMap_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime →
    (p : ℂ) ∈ W.nonunits → ∀ (Z₁ Z₂ : Mdl Y i₀) (f f' : Z₁.X ⟶ Z₂.X), IsMap Z₁ Z₂ f → IsMap Z₁ Z₂ f' → f = f' := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ Z₁ Z₂ f f' hf hf'
  have := Z₁.normal
  have : IsReduced Z₁.X := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_str (Z₂.i.c.V W) Z₂.n
  have : IsProper Z₂.s := by
    unfold Pre.s
    infer_instance
  have : IsSeparated (Z₂.s ≫ terminal.from _) := inferInstance
  refine ext_of_fromSpecResidueField_eq _ _ (Z₂.s ≫ terminal.from _) Z₁.opn Z₁.dense (fun x hx => ?_)
    (terminal.hom_ext _ _)
  have hr : Set.range (Z₁.X.fromSpecResidueField x) ⊆ Z₁.opn := by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply x a).symm ▸ hx
  exact CommonMod.natImg_unique hf.1 (hf.2 _ _ hr) (hf'.2 _ _ hr)

end GlobalTheory.LocM.MapUniq
