import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.VacReal

open GlobalTheory.ChainFr GlobalTheory.Size

/- English proof (translation)
Establish `hd : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z 0 = 0`. Introduce `τ z`. Use function extensionality and compare the values at `w`. Simplify using `[Formalism.IndefR.Datum.dRho, heisO]`. Establish `: pureTensorO ψ θ V W A.cart B.cart A.onb B.onb 0 = 0`.

Unfold `pureTensorO pureTensorL`. Use `(MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.constr_basis]`. Use `show opPow _ k 0 = 0`. Unfold `opPow`.

Proceed by induction on `Multiset.toList (Finsupp.toMultiset k) with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => rw [List.foldr_cons, ih]`. Simplify using `[aPlusAll, aPlus, crea, hd]`. Unfold `ptF`.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem ptF_zero {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (P : PolF D W.rank V.rank) : ptF ψ θ A B 0 P = 0 := by
  have hd : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z 0 = 0 := by
    intro τ z
    funext w
    simp [Formalism.IndefR.Datum.dRho, heisO]
  have : pureTensorO ψ θ V W A.cart B.cart A.onb B.onb 0 = 0 := by
    unfold pureTensorO pureTensorL
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [Module.Basis.constr_basis]
    show opPow _ k 0 = 0
    unfold opPow
    induction Multiset.toList (Finsupp.toMultiset k) with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, ih]; simp [aPlusAll, aPlus, crea, hd]
  unfold ptF
  rw [this]
  rfl

/- English proof (translation)
Introduce `D V W A B θ ψ hψ hθ f hf hf0`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Take `⟨i1, i2, i3, i4, i5, K, hK, hKc⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D W V`. Establish `i6 : BorelSpace (WO V W)` using `⟨rfl⟩`.

Take `⟨μ, 𝓕, hμ, h𝓕, h1⟩` from `(GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO V W) (ratL W V) K hK hKc).1`. Take `⟨U, -, -, hd⟩` from `GlobalTheory.T.fockVectors_overVacua_dense_thetaFunctions D V W A B θ ψ hψ hθ μ 𝓕 ⟨hμ, h𝓕, h1⟩ f hf`. Establish `hspan : fockSpan ψ θ A B U = ⊥`. Unfold `fockSpan`. Rewrite using `[Submodule.span_eq_bot]`.

Introduce and unpack `g ⟨f₀, P, hv, -, rfl⟩`. Rewrite using `[hno f₀ hv]`. Conclude with `ptF_zero ψ θ A B P`. Establish `hl : l2O μ 𝓕 f = 0`. Assume the negation of the conclusion as `hne`.

Take `⟨g, hg, -, hlt⟩` from `hd 0 (l2O μ 𝓕 f) (pos_iff_ne_zero.2 hne)`. Rewrite `hg` using `[hspan, Submodule.mem_bot]`. Rewrite `hlt` using `[hg, sub_zero]`. Establish `e : sobO ψ θ μ 𝓕 0 f = l2O μ 𝓕 f` using `wordSum_zero _ _ _`. Rewrite `hlt` using `[e]`.

Conclude with `lt_irrefl _ hlt`. Establish `h0 : ∀ᵐ x ∂μ.restrict 𝓕, f x = 0` using `(eLpNorm_eq_zero_iff hf.cont.aestronglyMeasurable two_ne_zero).1 hl`. Conclude with `hf0 (GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL W V) μ 𝓕 h𝓕 f hf.cont (GlobalTheory.WeilVacMove.norm_periodic hψ hf) h0)`.
-/
theorem exists_isVacF_ne_zero : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → f ≠ 0 →
      ∃ f₀, GlobalTheory.ChainFr.IsVacF ψ θ A B f₀ ∧ f₀ ≠ 0 := by
  intro D V W A B θ ψ hψ hθ f hf hf0
  by_contra hno
  push_neg at hno
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have i6 : BorelSpace (WO V W) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO V W) (ratL W V) K hK hKc).1
  obtain ⟨U, -, -, hd⟩ := GlobalTheory.T.fockVectors_overVacua_dense_thetaFunctions D V W A B θ ψ hψ hθ μ 𝓕 ⟨hμ, h𝓕, h1⟩ f hf
  have hspan : fockSpan ψ θ A B U = ⊥ := by
    unfold fockSpan
    rw [Submodule.span_eq_bot]
    rintro g ⟨f₀, P, hv, -, rfl⟩
    rw [hno f₀ hv]
    exact ptF_zero ψ θ A B P
  have hl : l2O μ 𝓕 f = 0 := by
    by_contra hne
    obtain ⟨g, hg, -, hlt⟩ := hd 0 (l2O μ 𝓕 f) (pos_iff_ne_zero.2 hne)
    rw [hspan, Submodule.mem_bot] at hg
    rw [hg, sub_zero] at hlt
    have e : sobO ψ θ μ 𝓕 0 f = l2O μ 𝓕 f := wordSum_zero _ _ _
    rw [e] at hlt
    exact lt_irrefl _ hlt
  have h0 : ∀ᵐ x ∂μ.restrict 𝓕, f x = 0 :=
    (eLpNorm_eq_zero_iff hf.cont.aestronglyMeasurable two_ne_zero).1 hl
  exact hf0 (GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL W V) μ 𝓕 h𝓕 f hf.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hf) h0)

end GlobalTheory.Mem.VacReal

end
