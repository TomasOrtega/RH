import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzLinear
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConnectionLinear

section Helpers
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

/- English proof (translation)
Establish `i1` using `GlobalTheory.ContractionLocal.integrable_contr hψ l S vL hX hZ u v`. Establish `i2` using `GlobalTheory.ContractionLocal.integrable_contr hψ l S vL hY hZ u v`. Unfold `GlobalTheory.Unf.contr`. Rewrite using `[← integral_const_mul, ← integral_add (i1.const_mul c) i2]`. Use `congr 1`.

Use function extensionality and compare the values at `w`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem contr_comb_left (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : Unf.BesLev D ρ} {B' : Unf.BesLev D σ}
    (l : Unf.Link B B'.L B'.ζ) (S : HSp D) (vL : Unf.VolM D B'.L.rank S.rank) (c : ℂ) {X Y : WO B.V₀ S → ℂ}
    {Z : WO S B'.V₀ → ℂ} (hX : IsThetaFunO ψ B.V₀ S X) (hY : IsThetaFunO ψ B.V₀ S Y) (hZ : IsThetaFunO ψ S B'.V₀ Z)
    (u : WO B.A S) (v : WO S B'.A) :
    Unf.contr l S vL (c • X + Y) Z u v = c * Unf.contr l S vL X Z u v + Unf.contr l S vL Y Z u v := by
  have i1 := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL hX hZ u v
  have i2 := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL hY hZ u v
  unfold GlobalTheory.Unf.contr
  rw [← integral_const_mul, ← integral_add (i1.const_mul c) i2]
  congr 1
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hF` using `GlobalTheory.Unf.Flat.flatLaw D`. Establish `fX` using `(GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hF ψ).1 ρ B J s X hX`. Establish `fY` using `(GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hF ψ).1 ρ B J s Y hY`. Establish `hcX` using `GlobalTheory.OrientedHeis.theta_smul c hX`. Rewrite using `[(GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J s (c • X) Y c hcX hY).1, (GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J s X Y c hX hY).2]`.

Conclude with `contr_comb_left hψ l J.W₀ vL c fX fY hZ u v`.
-/
private theorem contr_flatBF_smul_add (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : Unf.BesLev D ρ} {J : Unf.JacLev D ρ}
    {B' : Unf.BesLev D σ} (s : Unf.StepBF ψ B J) (l : Unf.Link B B'.L B'.ζ) (vL : Unf.VolM D B'.L.rank J.W₀.rank)
    (c : ℂ) {X Y : WO B.V J.W → ℂ} {Z : WO J.W₀ B'.V₀ → ℂ} (hX : IsThetaFunO ψ B.V J.W X)
    (hY : IsThetaFunO ψ B.V J.W Y) (hZ : IsThetaFunO ψ J.W₀ B'.V₀ Z) (u : WO B.A J.W₀) (v : WO J.W₀ B'.A) :
    Unf.contr l J.W₀ vL (Unf.flatBF s (c • X + Y)) Z u v =
      c * Unf.contr l J.W₀ vL (Unf.flatBF s X) Z u v + Unf.contr l J.W₀ vL (Unf.flatBF s Y) Z u v := by
  have hF := GlobalTheory.Unf.Flat.flatLaw D
  have fX := (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hF ψ).1 ρ B J s X hX
  have fY := (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hF ψ).1 ρ B J s Y hY
  have hcX := GlobalTheory.OrientedHeis.theta_smul c hX
  rw [(GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J s (c • X) Y c hcX hY).1,
    (GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J s X Y c hX hY).2]
  exact contr_comb_left hψ l J.W₀ vL c fX fY hZ u v

end Helpers

section Grid
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Unfold `GridData.Weil.fock`. Conclude with `GlobalTheory.FockFiniteHeis.pureTensorO_lin W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ c hf hg Q`.
-/
theorem fock_comb (W : G.Weil) (p : Pair T) (c : ℂ) {f g : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (hg : IsThetaFunO W.ψ _ _ g) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • f + g) Q = c • W.fock p f Q + W.fock p g Q := by
  unfold GridData.Weil.fock
  exact GlobalTheory.FockFiniteHeis.pureTensorO_lin W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ c hf hg Q

/- English proof (translation)
Unfold `GridData.Weil.fock`. Conclude with `GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf Q`.
-/
theorem fock_theta (W : G.Weil) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (Q : PolF D (G.pT p).rank (G.pS p).rank) : IsThetaFunO W.ψ _ _ (W.fock p f Q) := by
  unfold GridData.Weil.fock
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf Q

end Grid

/- English proof (translation)
Use `⟨0, fun ε CF _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Introduce `D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _`. Introduce `j hj hjm hm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v`. Take `⟨a, ha'⟩` from `a`. Simplify using `only [add_zero] at ha`.

Substitute `ha` using the available equality. Establish `h1 : ¬ (a + 2 * 0 + 2 = D.R.m)` using `by omega`. Establish `h2 : a + 2 * ((D.R.m - 4 - a) / 2 + 1) + 2 = D.R.m`. Take `⟨k, hk⟩` from `hj`. Take `⟨n, hn⟩` from `hm`.

Use linear arithmetic over natural numbers and integers. Establish `hin : (Pair.mu t D.R.m a : Pair T).InRange D.R.m` using `show D.R.m ≤ D.R.m ∧ a + 1 ≤ D.R.m from ⟨le_rfl, by omega⟩`. Establish `hin' : (Pair.mu t D.R.m (a + 1) : Pair T).InRange D.R.m` using `show D.R.m ≤ D.R.m ∧ a + 1 + 1 ≤ D.R.m from ⟨le_rfl, by omega⟩`. Simplify using `only [conAt, dif_neg h1, fockD]`. Simplify using `(disch := simp) only [Function.update_self, Function.update_of_ne]`.

Simplify using `only [h2, ↓reduceDIte]`. Rewrite using `[fock_comb ch.W (Pair.mu t D.R.m a) c hφ hφ' (P ⟨a, ha'⟩), map_add, map_smul]`. Use `contr_flatBF_smul_add ch.W.ψ_std (B := besAt ch.G hM a ((D.R.m - 4 - a) / 2 + 1) h2 _) (J := jacAt ch.G hM (a + 1) ((D.R.m - 4 - a) / 2 + 1) (by omega)) _ _ _ c ?_ ?_ ?_ _ _` and prove the remaining obligations. Conclude with `(ch.W.om_is _ hin).om_pres _ _ (fock_theta ch.W _ hφ _)`. Conclude with `(ch.W.om_is _ hin).om_pres _ _ (fock_theta ch.W _ hφ' _)`.

Conclude with `(GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.Unf.Flat.flatLaw D) _).2 _ _ _ _ _ ((ch.W.om_is _ hin').om_pres _ _ (fock_theta ch.W _ (hΦ ⟨a + 1, by omega⟩) _))`.
-/
theorem contrLin_left : Big fun ch => ContrLin ch 0 := by

  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _
  intro j hj hjm hm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  obtain ⟨a, ha'⟩ := a
  simp only [add_zero] at ha
  subst ha

  have h1 : ¬ (a + 2 * 0 + 2 = D.R.m) := by omega
  have h2 : a + 2 * ((D.R.m - 4 - a) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨k, hk⟩ := hj
    obtain ⟨n, hn⟩ := hm
    omega
  have hin : (Pair.mu t D.R.m a : Pair T).InRange D.R.m := show D.R.m ≤ D.R.m ∧ a + 1 ≤ D.R.m from ⟨le_rfl, by omega⟩
  have hin' : (Pair.mu t D.R.m (a + 1) : Pair T).InRange D.R.m :=
    show D.R.m ≤ D.R.m ∧ a + 1 + 1 ≤ D.R.m from ⟨le_rfl, by omega⟩
  simp only [conAt, dif_neg h1, fockD]
  simp (disch := simp) only [Function.update_self, Function.update_of_ne]
  simp only [h2, ↓reduceDIte]
  · rw [fock_comb ch.W (Pair.mu t D.R.m a) c hφ hφ' (P ⟨a, ha'⟩), map_add, map_smul]
    refine contr_flatBF_smul_add ch.W.ψ_std (B := besAt ch.G hM a ((D.R.m - 4 - a) / 2 + 1) h2 _)
      (J := jacAt ch.G hM (a + 1) ((D.R.m - 4 - a) / 2 + 1) (by omega)) _ _ _ c ?_ ?_ ?_ _ _
    · exact (ch.W.om_is _ hin).om_pres _ _ (fock_theta ch.W _ hφ _)
    · exact (ch.W.om_is _ hin).om_pres _ _ (fock_theta ch.W _ hφ' _)
    · exact (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.Unf.Flat.flatLaw D) _).2 _ _ _ _ _
        ((ch.W.om_is _ hin').om_pres _ _ (fock_theta ch.W _ (hΦ ⟨a + 1, by omega⟩) _))

end GlobalTheory.ConnectionLinear
