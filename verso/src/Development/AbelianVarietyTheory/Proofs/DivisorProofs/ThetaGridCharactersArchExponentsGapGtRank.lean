import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiGridVertexRankAddLtTwoExponentAddCentreStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SquareExps

open GlobalTheory.Chain.StepVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simp, h, fun θ _ x _ _ => by simp⟩`.
-/
theorem hasInfExp_one_of (τ : D.what₂.Tau) (h : ∃ θ, IsInfFam (D := D) θ) : HasInfExp D (1 : (AE D)ˣ →* Circle) τ 0 :=
  ⟨0, by simp, h, fun θ _ x _ _ => by simp⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Take `⟨_, _, hθ, _⟩` from `h`. Simplify using `using hasInfExp_one_of τ hθ`. Consider the case `succ n ih`.

Rewrite using `[pow_succ]`. Use `hasInfExp_mul ih h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasInfExp_pow {η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {b : ℚ} (h : HasInfExp D η τ b) (n : ℕ) :
    HasInfExp D (η ^ n) τ (n * b) := by
  induction n with
  | zero =>
    obtain ⟨_, _, hθ, _⟩ := h
    simpa using hasInfExp_one_of τ hθ
  | succ n ih =>
    rw [pow_succ]
    have := hasInfExp_mul ih h
    convert this using 1
    push_cast; ring

/- English proof (translation)
The claim follows from `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ`.
-/
theorem eta_exp {μ₀ : T} (hL : L.Is μ₀) (τ : D.what₂.Tau) : HasInfExp D L.eta τ (1 / 2) :=
  GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `hL.xi_fin t`. Establish `h0` using `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ`. Take `⟨θ, hθ⟩ : ∃ θ, IsInfFam (D` from `D) θ := by`. Take `⟨_, _, hθ, _⟩` from `h0`. Conclude with `hθ`.

Establish `h1 : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩)`. Use `hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)` as an intermediate fact. Rewrite `this` using `[add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]`. Conclude with `this`. Conclude with `hasInfExp_mul h1 (hasInfExp_pow (eta_exp hL τ) _)`.
-/
theorem alpha_exp {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (alpha G t i j) τ (-(D.hc τ).e ⟨j, hj⟩ + (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j : ℚ) * (1 / 2)) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have h1 : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
    have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
    rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
    exact this
  exact hasInfExp_mul h1 (hasInfExp_pow (eta_exp hL τ) _)

/- English proof (translation)
Establish `hm1 : 1 ≤ D.R.m - i` using `by omega`. Establish `hm2 : D.R.m - i ≤ D.R.m` using `by omega`. Establish `h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ)` using `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2) ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ`. Conclude with `hasInfExp_mul h0 (hasInfExp_pow (eta_exp hL τ) _)`.
-/
theorem beta_exp {μ₀ : T} (hL : L.Is μ₀) (i j : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (beta G i j) τ ((cen D sc.cGap τ (D.R.m - i) : ℚ) + (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j : ℚ) * (1 / 2)) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  exact hasInfExp_mul h0 (hasInfExp_pow (eta_exp hL τ) _)

/- English proof (translation)
Introduce `D T L sc G μ₀ hL t i j _ τf hτf`. Take `⟨mα, hα, eα⟩` from `GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => alpha_exp (G := G) hL t i j j.2 τ) τf hτf`. Take `⟨mβ, hβ, eβ⟩` from `GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => beta_exp (G := G) hL i j i.2 τ) τf hτf`. Use `⟨mα, mβ, hα, hβ, fun w => ?_⟩` and prove the remaining obligations. Establish `hr : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b` using `fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank`.

Establish `key` using `GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap (τf w) i j i.2 j.2`. Establish `e1 : (spW G i j).rank = rankV D (i + 1) (j + 1)` using `hr _ _ (by omega) (by omega)`. Establish `e2 : (spW₁ G i j).rank = rankV D i j` using `hr _ _ (by omega) (by omega)`. Rewrite using `[e1, e2]`. Establish `h1` using `eα w`.

Establish `h2` using `eβ w`. Establish `: (((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ)`. Move the coercions through the operations in `at h1 h2 key ⊢`. Rewrite using `[h1, h2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `this` after adjusting the coercions.
-/
theorem exps : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, (((spW G i j).rank + (spW₁ G i j).rank : ℕ) : ℤ) < mα w - mβ w := by
  intro D T L sc G μ₀ hL t i j _ τf hτf
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => alpha_exp (G := G) hL t i j j.2 τ) τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => beta_exp (G := G) hL i j i.2 τ) τf hτf
  refine ⟨mα, mβ, hα, hβ, fun w => ?_⟩
  have hr : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap (τf w) i j i.2 j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := hr _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := hr _ _ (by omega) (by omega)
  rw [e1, e2]
  have h1 := eα w
  have h2 := eβ w
  have : (((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
    push_cast at h1 h2 key ⊢
    rw [h1, h2]
    linarith
  exact_mod_cast this

end GlobalTheory.SquareExps

end
