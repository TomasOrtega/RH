import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoeffDeriv

open GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def coefL (R : Rep k r) (x : R.H) (X : V) : R.H →L[ℝ] V :=
  ((innerSL ℂ x).smulRight X).restrictScalars ℝ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coefL_apply (x w : R.H) (X : V) : coefL R x X w = ⟪x, w⟫_ℂ • X := rfl

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `nil => exact hy`. Consider the case `cons Y b ih`. Conclude with `dsig_smooth hR.2 (hb Y (by simp)) (ih fun Z hZ => hb Z (by simp [hZ]))`.
-/
theorem dsigW_smooth (hR : R.IsDG ε mu) {y : R.H} (hy : y ∈ R.sm) (b : List (Mx k r))
    (hb : ∀ Y ∈ b, B.inLie k r Y) : PI.UpqRep.dsigW (k := k) (r := r) R.σ b y ∈ R.sm := by
  induction b with
  | nil => exact hy
  | cons Y b ih =>
    exact dsig_smooth hR.2 (hb Y (by simp)) (ih fun Z hZ => hb Z (by simp [hZ]))

/- English proof (translation)
Take `⟨hmul, -⟩` from `rep_basic_of_isDS hK k r ε mu R hR`. Establish `h` using `(coefL R x X).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_apply (σ := R.σ) hY hy (R.σ g))`. Rewrite using `[← coefL_apply, ← h.deriv]`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Establish `he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r` using `exp_mem hY t`. Rewrite using `[hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg he), hmul g hg _ he]`. Both sides reduce to the same expression.
-/
theorem right_step (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (X : V) (F : Mx k r → V) (x : R.H) {y : R.H}
    (hy : y ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    deriv (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      ⟪x, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ Y y)⟫_ℂ • X := by
  obtain ⟨hmul, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  have h := (coefL R x X).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_apply (σ := R.σ) hY hy (R.σ g))
  rw [← coefL_apply, ← h.deriv]
  congr 1
  funext t
  have he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := exp_mem hY t
  rw [hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg he), hmul g hg _ he]
  rfl

/- English proof (translation)
Take `⟨hmul, hone, hinner, -⟩` from `rep_basic_of_isDS hK k r ε mu R hR`. Establish `h1` using `(hasDerivAt_dsig (σ := R.σ) hY hx).inner ℂ (hasDerivAt_const (0 : ℝ) (R.σ g y))`. Simplify using `only [inner_zero_right, zero_add] at h1`. Establish `h` using `h1.smul_const X`. Unfold `B.LdV`.

Rewrite using `[← h.deriv]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Establish `he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r` using `exp_mem hY t`. Establish `he' : NormedSpace.exp (-((t : ℂ) • Y)) ∈ GG k r`.

Use `exp_mem hY (-t)` as an intermediate fact. Rewrite `this` using `[Complex.ofReal_neg, neg_smul]`. Then use the resulting hypothesis. Establish `hee : NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp (-((t : ℂ) • Y)) = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Y)).neg_right, add_neg_cancel, NormedSpace.exp_zero]`. Rewrite using `[hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul he' hg), hmul _ he' g hg, ← hinner _ he, ← hmul _ he _ he', hee, hone]`.
-/
theorem left_step (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (X : V) (F : Mx k r → V) {x : R.H} (y : R.H)
    (hx : x ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    B.LdV Y F g = ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ Y x, R.σ g y⟫_ℂ • X := by
  obtain ⟨hmul, hone, hinner, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  have h1 := (hasDerivAt_dsig (σ := R.σ) hY hx).inner ℂ (hasDerivAt_const (0 : ℝ) (R.σ g y))
  simp only [inner_zero_right, zero_add] at h1
  have h := h1.smul_const X
  unfold B.LdV
  rw [← h.deriv]
  congr 1
  funext t
  have he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := exp_mem hY t
  have he' : NormedSpace.exp (-((t : ℂ) • Y)) ∈ GG k r := by
    have := exp_mem hY (-t)
    rwa [Complex.ofReal_neg, neg_smul] at this
  have hee : NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp (-((t : ℂ) • Y)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Y)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  rw [hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul he' hg), hmul _ he' g hg, ← hinner _ he, ← hmul _ he _ he', hee, hone]

/- English proof (translation)
Introduce `hK k r ε mu R V _ _ X F hR x hx y hy hF`. Use `⟨fun g₀ hg₀ => ?_, fun a b ha hb => ?_⟩` and prove the remaining obligations. Take `⟨U, G, hU, hgU, hG, hfG⟩` from `hy g₀ hg₀`. Use `⟨U, fun g => coefL R x X (G g), hU, hgU, (coefL R x X).contDiff.comp_contDiffOn hG, ?_⟩` and prove the remaining obligations. Introduce `g hg hgG`.

Establish `e : R.σ g y = G g` using `hfG g hg hgG`. Rewrite using `[hF g hgG, e]`. Both sides reduce to the same expression. Establish `hRw : ∀ g ∈ GG k r, B.Rw b F g = ⟪x, R.σ g (PI.UpqRep.dsigW (k` using `k) (r := r) R.σ b y)⟫_ℂ • X := by`. Proceed by induction on `b with`.

Consider the case `nil => exact hF`. Consider the case `cons Y b ih`. Establish `hb' : ∀ Z ∈ b, B.inLie k r Z` using `fun Z hZ => hb Z (by simp [hZ])`. Introduce `g hg`. Conclude with `right_step hK hR X _ x (dsigW_smooth hR hy b hb') (ih hb') (hb Y (by simp)) g hg`.

Proceed by induction on `a with`. Consider the case `nil => exact hRw`. Consider the case `cons Y a ih`. Establish `ha' : ∀ Z ∈ a, B.inLie k r Z` using `fun Z hZ => ha Z (by simp [hZ])`. Introduce `g hg`.

Conclude with `left_step hK hR X _ _ (dsigW_smooth hR hx a ha') (ih ha') (ha Y (by simp)) g hg`.
-/
theorem coeff_dLR : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : V) (F : Mx k r → V), R.IsDG ε mu → ∀ x ∈ R.sm, ∀ y ∈ R.sm, (∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) → B.CkOn ⊤ (B.GV k r) F ∧ ∀ a b : List (Mx k r), (∀ Y ∈ a, B.inLie k r Y) → (∀ Y ∈ b, B.inLie k r Y) → ∀ g ∈ GG k r, B.dLR a b F g = ⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
  intro hK k r ε mu R V _ _ X F hR x hx y hy hF
  refine ⟨fun g₀ hg₀ => ?_, fun a b ha hb => ?_⟩
  · obtain ⟨U, G, hU, hgU, hG, hfG⟩ := hy g₀ hg₀
    refine ⟨U, fun g => coefL R x X (G g), hU, hgU, (coefL R x X).contDiff.comp_contDiffOn hG, ?_⟩
    intro g hg hgG
    have e : R.σ g y = G g := hfG g hg hgG
    rw [hF g hgG, e]
    rfl
  · have hRw : ∀ g ∈ GG k r, B.Rw b F g = ⟪x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
      induction b with
      | nil => exact hF
      | cons Y b ih =>
        have hb' : ∀ Z ∈ b, B.inLie k r Z := fun Z hZ => hb Z (by simp [hZ])
        intro g hg
        exact right_step hK hR X _ x (dsigW_smooth hR hy b hb') (ih hb') (hb Y (by simp)) g hg
    induction a with
    | nil => exact hRw
    | cons Y a ih =>
      have ha' : ∀ Z ∈ a, B.inLie k r Z := fun Z hZ => ha Z (by simp [hZ])
      intro g hg
      exact left_step hK hR X _ _ (dsigW_smooth hR hx a ha') (ih ha') (ha Y (by simp)) g hg

end GlobalTheory.CoeffDeriv
