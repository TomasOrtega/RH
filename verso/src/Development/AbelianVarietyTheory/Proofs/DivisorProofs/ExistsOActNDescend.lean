import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GaloisActDesc

/- English proof (translation)
Introduce `O _ X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act hπ _ _ hp hφ _ hcomm`. Establish `: Flat π` using `by have := hπ.etale; infer_instance`. Establish `: Surjective π` using `hπ.onto`. Establish `eφ : Epi φ` using `GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hφ`. Establish `hi : ∀ c, ∃ f : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ f.left`.

Introduce `c`. Take `⟨g, hg, -⟩` from `hφ.existsUnique_desc ((act.act c).left ≫ φ) (fun a ↦ by`. Rewrite using `[← Category.assoc, ← hcomm, Category.assoc, hφ.inv])`. Establish `hw : g ≫ A₀.hom = A₀.hom`. Rewrite using `[← cancel_epi φ, reassoc_of% hg, hp.1.w, Over.w_assoc]`.

Conclude with `⟨Over.homMk g hw, hg.symm⟩`. Use `choose f hf using hi`. Use `⟨⟨f, fun x ↦ ?_, ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩, hf⟩` and prove the remaining obligations. Use `act.hom x` as an intermediate fact. Conclude with `GlobalTheory.ActDescent.isMonHom_descend hp hp (act.act x) (f x) (hf x)`.

Use `GlobalTheory.ActDescent.over_hom_ext hp.1 ?_` and prove the remaining obligations. Rewrite using `[← hf, act.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]`. Use `GlobalTheory.ActDescent.over_hom_ext hp.1 ?_` and prove the remaining obligations. Rewrite using `[← hf, act.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]`. Use `GlobalTheory.ActDescent.over_hom_ext hp.1 ?_` and prove the remaining obligations.

Set `φ₀ : Over.mk (A.hom ≫ π) ⟶ A₀` to `Over.homMk φ hp.1.w`. Establish `h` using `hp.2 A (act.act x) (act.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm`. Rewrite `h` using `[← MonObj.comp_mul]`. Rewrite using `[← hf, act.add, ← h]`. Both sides reduce to the same expression.
-/
theorem exists_oActN_descend : ∀ (O : Type) [Ring O] (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → (∀ a c, (act.act c).left ≫ ν a = ν a ≫ (act.act c).left) → ∃ act₀ : OActN O A₀, ∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left := by
  intro O _ X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act hπ _ _ hp hφ _ hcomm
  have : Flat π := by have := hπ.etale; infer_instance
  have : Surjective π := hπ.onto
  have eφ : Epi φ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hφ
  have hi : ∀ c, ∃ f : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ f.left := by
    intro c
    obtain ⟨g, hg, -⟩ := hφ.existsUnique_desc ((act.act c).left ≫ φ) (fun a ↦ by
      rw [← Category.assoc, ← hcomm, Category.assoc, hφ.inv])
    have hw : g ≫ A₀.hom = A₀.hom := by
      rw [← cancel_epi φ, reassoc_of% hg, hp.1.w, Over.w_assoc]
    exact ⟨Over.homMk g hw, hg.symm⟩
  choose f hf using hi
  refine ⟨⟨f, fun x ↦ ?_, ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩, hf⟩
  · have := act.hom x
    exact GlobalTheory.ActDescent.isMonHom_descend hp hp (act.act x) (f x) (hf x)
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    let φ₀ : Over.mk (A.hom ≫ π) ⟶ A₀ := Over.homMk φ hp.1.w
    have h := hp.2 A (act.act x) (act.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, act.add, ← h]
    rfl

end GlobalTheory.GaloisActDesc
