import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivity

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

/- English proof (translation)
Take `⟨e, c, g, d, bs, gv, hp, rfl⟩` from `h`. Conclude with `Submodule.subset_span ⟨_, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, rfl⟩`.
-/
theorem monoFock (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : Mx D V.rank n → ℂ) (h : IsMonoFock θ V l s φ) :
    φ ∈ fockA θ V n l s := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  exact Submodule.subset_span ⟨_, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, rfl⟩

def MonoSchPos : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ τ, l τ ≠ 0) → (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

/- English proof (translation)
Introduce `D n V θ l s hl hs φ h`. Use `⟨?_, monoFock D n V θ l s φ h⟩` and prove the remaining obligations. Take `⟨e, c, g, d, bs, gv, hp, rfl⟩` from `h`. Take `⟨f, hf⟩` from `GlobalTheory.CompanionTheory.WhitAdd.exists_schwartz_polyGauss V l hl s hs (MvPolynomial.monomial e c)`. Use `Submodule.subset_span ⟨f, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Rewrite using `[hf]`. Both sides reduce to the same expression.
-/
theorem monoSchPos : MonoSchPos := by
  intro D n V θ l s hl hs φ h
  refine ⟨?_, monoFock D n V θ l s φ h⟩
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.WhitAdd.exists_schwartz_polyGauss V l hl s hs (MvPolynomial.monomial e c)
  refine Submodule.subset_span ⟨f, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, ?_⟩
  funext x
  rw [hf]
  rfl

def MonoSchStd : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ →
    ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

/- English proof (translation)
Introduce `D n V _ _ θ _ _ _ l s _ _ hS φ h` and use `monoSchPos D n V θ l s (GlobalTheory.CompanionTheory.WhitAdd.par_ne_zero hS) hS.hs φ h`.
-/
theorem monoSchStd : MonoSchStd := fun D n V _ _ θ _ _ _ l s _ _ hS φ h =>
  monoSchPos D n V θ l s (GlobalTheory.CompanionTheory.WhitAdd.par_ne_zero hS) hS.hs φ h

end PositivityTheory.PfSWUS.SwMatch

end
