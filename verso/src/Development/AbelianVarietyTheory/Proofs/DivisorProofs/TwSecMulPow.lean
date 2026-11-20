import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw.TwSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Take `⟨-, -, h2, -, h3⟩` from `const_spec (x := x) s.pts (1 : c.F) one_ne_zero`. Use `⟨(const x s.pts 1 one_ne_zero).copy (zero_nsmul G₀).symm, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w show (const x s.pts 1 one_ne_zero).lo w = _`.

Rewrite using `[h2 w]`. Simplify using `[vAdd]`. Use `show (const x s.pts 1 one_ne_zero).degLo = _`. Rewrite using `[h3]`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Take `⟨u, hl, hd⟩` from `ih`. Use `⟨(u.mul s).copy (succ_nsmul G₀ n).symm, ?_, ?_⟩` and prove the remaining obligations. Use `show u.lo + s.lo = _`. Rewrite using `[hl, succ_nsmul]`.

Use `show (u.mul s).degLo = _`. Rewrite using `[degLo_mul, hd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pow {G₀ : WTZ E} (s : TwSec U x Z G₀) (n : ℕ) :
    ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  induction n with
  | zero =>
    obtain ⟨-, -, h2, -, h3⟩ := const_spec (x := x) s.pts (1 : c.F) one_ne_zero
    refine ⟨(const x s.pts 1 one_ne_zero).copy (zero_nsmul G₀).symm, ?_, ?_⟩
    · funext w
      show (const x s.pts 1 one_ne_zero).lo w = _
      rw [h2 w]
      simp [vAdd]
    · show (const x s.pts 1 one_ne_zero).degLo = _
      rw [h3]; simp
  | succ n ih =>
    obtain ⟨u, hl, hd⟩ := ih
    refine ⟨(u.mul s).copy (succ_nsmul G₀ n).symm, ?_, ?_⟩
    · show u.lo + s.lo = _
      rw [hl, succ_nsmul]
    · show (u.mul s).degLo = _
      rw [degLo_mul, hd]; push_cast; ring

end GlobalTheory.FlatTw.TwSec

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x Z`. Conclude with `⟨fun G₀ G₁ s t => ⟨s.mul t, rfl, rfl, rfl, TwSec.degLo_mul s t⟩, fun G₀ s n => s.exists_pow n⟩`.
-/
theorem GlobalTheory.FlatTw.twSec_mul_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c), (∀ (G₀ G₁ : WTZ E) (s : TwSec U x Z G₀) (t : TwSec U x Z G₁), ∃ u : TwSec U x Z (G₀ + G₁), u.sig = s.sig * t.sig ∧ u.cInf = s.cInf * t.cInf ∧ u.lo = s.lo + t.lo ∧ u.degLo = s.degLo + t.degLo) ∧ ∀ (G₀ : WTZ E) (s : TwSec U x Z G₀) (n : ℕ), ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  intro E _ _ _ H Dw l Xo c r U x Z
  exact ⟨fun G₀ G₁ s t => ⟨s.mul t, rfl, rfl, rfl, TwSec.degLo_mul s t⟩, fun G₀ s n => s.exists_pow n⟩
