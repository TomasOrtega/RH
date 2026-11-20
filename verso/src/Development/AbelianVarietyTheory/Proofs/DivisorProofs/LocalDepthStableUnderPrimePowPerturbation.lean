import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.DescentPf
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PertDepth

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Rewrite using `[neg_zero]`. Rewrite using `[nval_of_ne (neg_ne_zero.2 hx), nval_of_ne hx]`. Simplify using `only [vV, Valuation.map_neg]`.
-/
theorem nval_neg_eq (T : CDVR) (e : ℕ) (x : T.Fr) : nval T.V e (-x) = nval T.V e x := by
  by_cases hx : x = 0
  · subst hx; rw [neg_zero]
  · rw [nval_of_ne (neg_ne_zero.2 hx), nval_of_ne hx]
    simp only [vV, Valuation.map_neg]

/- English proof (translation)
Use `set Y := ⨅ (i) (_ : Q i), nval T.V e (A i) with hY`. Use `set X := ⨅ (i) (_ : Q i), nval T.V e (A i + D i) with hX`. Establish `hge : min Y M ≤ X` using `le_iInf₂ fun i hi => le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) (nval_add e (A i) (D i))`. Establish `hle : min X M ≤ Y` using `le_iInf₂ fun i hi => by`. Establish `h1` using `nval_add (V := T.V) e (A i + D i) (-D i)`.

Rewrite `h1` using `[add_neg_cancel_right, nval_neg_eq]`. Conclude with `le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) h1`. Establish `h1 : Y ≤ X` using `by rwa [min_eq_left hA.le] at hge`. Establish `h2 : X ≤ Y`. Break down `le_total X M with h | h` into its components or cases.

Rewrite `hle` using `[min_eq_left h]`. Then use the resulting hypothesis. Rewrite `hle` using `[min_eq_right h]`. Conclude with `absurd (lt_of_le_of_lt hle hA) (lt_irrefl _)`. Conclude with `le_antisymm h2 h1`.
-/
theorem iInf_nval_add_eq (T : CDVR) (e : ℕ) {ι : Type*} (Q : ι → Prop) (A D : ι → T.Fr) (M : EReal)
    (hD : ∀ i, Q i → M ≤ nval T.V e (D i)) (hA : ⨅ (i) (_ : Q i), nval T.V e (A i) < M) :
    ⨅ (i) (_ : Q i), nval T.V e (A i + D i) = ⨅ (i) (_ : Q i), nval T.V e (A i) := by
  set Y := ⨅ (i) (_ : Q i), nval T.V e (A i) with hY
  set X := ⨅ (i) (_ : Q i), nval T.V e (A i + D i) with hX
  have hge : min Y M ≤ X := le_iInf₂ fun i hi =>
    le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) (nval_add e (A i) (D i))
  have hle : min X M ≤ Y := le_iInf₂ fun i hi => by
    have h1 := nval_add (V := T.V) e (A i + D i) (-D i)
    rw [add_neg_cancel_right, nval_neg_eq] at h1
    exact le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) h1
  have h1 : Y ≤ X := by rwa [min_eq_left hA.le] at hge
  have h2 : X ≤ Y := by
    rcases le_total X M with h | h
    · rwa [min_eq_left h] at hle
    · rw [min_eq_right h] at hle; exact absurd (lt_of_le_of_lt hle hA) (lt_irrefl _)
  exact le_antisymm h2 h1

/- English proof (translation)
Establish `hp0 : (p : T.Fr) ≠ 0`. Introduce `h0`. Rewrite `hp` using `[h0]`. Simplify using `[vV] at hp`. Use linear arithmetic over natural numbers and integers.

Establish `h1 : nval T.V e (p : T.Fr) = ((1 : ℝ) : EReal)`. Rewrite using `[nval_of_ne hp0, hp]`. Use `congr 1`. Establish `: (e : ℝ) ≠ 0` using `by exact_mod_cast he.ne'`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Proceed by induction on `N with`. Consider the case `zero`. Rewrite using `[pow_zero, nval_of_ne one_ne_zero]`. Simplify using `[vV]`.

Consider the case `succ N ih`. Rewrite using `[pow_succ, nval_mul, ih, h1, ← EReal.coe_add]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem nval_pow_p (T : CDVR) (p e : ℕ) (he : 0 < e) (hp : vV T.V (p : T.Fr) = e) (N : ℕ) :
    nval T.V e ((p : T.Fr) ^ N) = ((N : ℝ) : EReal) := by
  have hp0 : (p : T.Fr) ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp [vV] at hp
    omega
  have h1 : nval T.V e (p : T.Fr) = ((1 : ℝ) : EReal) := by
    rw [nval_of_ne hp0, hp]
    congr 1
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    push_cast
    field_simp
  induction N with
  | zero =>
    rw [pow_zero, nval_of_ne one_ne_zero]
    simp [vV]
  | succ N ih =>
    rw [pow_succ, nval_mul, ih, h1, ← EReal.coe_add]
    push_cast
    rfl

end GlobalTheory.PertDepth

open GlobalTheory.PertDepth in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c`. Use `letI := H.starRing`. Introduce `p T io y Ch e he hp a n N k ρ B P₀ R hCh hR hP₀ hBN`. Use `letI := io.toAlgebra`. Establish `hRv : ∀ f : PS T.Fr n Ch.ch.d, IsIntPS T f → ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) R)`.

Introduce `f hf`. Establish `h1` using `hCh k`. Rewrite `h1` using `[nuLocC_eq_iInf]`. Conclude with `le_trans h1 (le_trans (iInf₂_le R hR) (iInf₂_le f hf))`. Unfold `nuLocOf`.

Simplify using `only [Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_addP, Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_smulP]`. Use `iInf_nval_add_eq T e _ _ _ (((N : ℝ) - ρ : ℝ) : EReal) (fun f hf => ?_) ?_` and prove the remaining obligations. Rewrite using `[nval_mul, nval_pow_p T p e he hp N]`. Use `add_le_add (le_refl ((N : ℝ) : EReal)) (hRv f hf)` as an intermediate fact. Rewrite `this` using `[← EReal.coe_add]`.

Simplify `this` using `[sub_eq_add_neg]`. Use `lt_of_le_of_lt hP₀ ?_` and prove the remaining obligations. Conclude with `EReal.coe_lt_coe_iff.2 (by linarith)`.
-/
theorem GlobalTheory.nuLocOf_pert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → vV T.V (p : T.Fr) = e → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N k : ℕ) (ρ B : ℝ) (P₀ R : MvPolynomial (LtN Dw n) T.Fr), ChBound Ch e ρ a n → R ∈ FFV (Dw := Dw) T a n → nuLocOf Ch e k P₀ ≤ (B : EReal) → B + ρ < N → nuLocOf Ch e k (P₀ + ((p : T.Fr) ^ N) • R) = nuLocOf Ch e k P₀ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p T io y Ch e he hp a n N k ρ B P₀ R hCh hR hP₀ hBN
  letI := io.toAlgebra
  have hRv : ∀ f : PS T.Fr n Ch.ch.d, IsIntPS T f →
      ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ => ℓ.2.2)
        (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) R) := by
    intro f hf
    have h1 := hCh k
    rw [nuLocC_eq_iInf] at h1
    exact le_trans h1 (le_trans (iInf₂_le R hR) (iInf₂_le f hf))
  unfold nuLocOf
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_addP, Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_smulP]
  refine iInf_nval_add_eq T e _ _ _ (((N : ℝ) - ρ : ℝ) : EReal) (fun f hf => ?_) ?_
  · rw [nval_mul, nval_pow_p T p e he hp N]
    have := add_le_add (le_refl ((N : ℝ) : EReal)) (hRv f hf)
    rw [← EReal.coe_add] at this
    simpa [sub_eq_add_neg] using this
  · refine lt_of_le_of_lt hP₀ ?_
    exact EReal.coe_lt_coe_iff.2 (by linarith)
