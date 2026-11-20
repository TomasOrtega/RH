import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

/- English proof (translation)
Proceed by induction on `c using ENat.recTopCoe with`. Consider the case `top => simp at h`. Consider the case `coe n => exact ⟨n, rfl, by exact_mod_cast h⟩`.
-/
theorem enat_add_natCast_eq_natCast_exists {c : ℕ∞} {a b : ℕ} (h : c + (a : ℕ∞) = (b : ℕ∞)) : ∃ n : ℕ, c = n ∧ n + a = b := by
  induction c using ENat.recTopCoe with
  | top => simp at h
  | coe n => exact ⟨n, rfl, by exact_mod_cast h⟩

/- English proof (translation)
Introduce `k _ Y _ q hq e hY`. Establish `hB` using `GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq`. Establish `hC` using `GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k Y q hq (e + 1) hY`. Establish `h1 : ∀ z : Y, Order.coheight z = 1 ↔ HasDim z e`. Introduce `z`.

Take `⟨m, hm⟩` from `hB.1`. Take `⟨d, -, hd⟩` from `hm z`. Take `⟨n, hn, hnd⟩` from `enat_add_natCast_eq_natCast_exists (hC z d hd)`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Rewrite `hn` using `[hz]`. Establish `: n = 1` using `by exact_mod_cast hn.symm`. Substitute `this` using the available equality. Establish `: d = e` using `by omega`. Conclude with `this ▸ hd`.

Introduce `hz`. Use `hB.2.1 z d e hd hz` as an intermediate fact. Substitute `this` using the available equality. Rewrite using `[hn]`. Establish `: n = 1` using `by omega`.

Simplify using `[this]`. Use `⟨h1, fun z w hz => ?_⟩` and prove the remaining obligations. Establish `hze : HasDim z e` using `(h1 z).1 hz`. Establish `hgen : HasDim (genericPoint (clo z)) e`. Rewrite using `[← hB.2.2.2.2.1 (clo z) (cloι z) (genericPoint (clo z)) e, cloι_genericPoint]`.

Conclude with `hze`. Establish `hdim : topologicalKrullDim (clo z) = e` using `(hB.2.2.2.2.2 (clo z) e).1 hgen`. Use `⟨hdim, ?_⟩` and prove the remaining obligations. Establish `hq' : IsAmb (cloι z ≫ q)` using `hq.sub (cloι z)`. Establish `hB'` using `GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k (clo z) (cloι z ≫ q) hq'`.

Take `⟨m, hm⟩` from `hB'.1`. Take `⟨d, -, hd⟩` from `hm w`. Establish `hd' : HasDim (cloι z w) d` using `(hB.2.2.2.2.1 (clo z) (cloι z) w d).2 hd`. Take `⟨n, hn, hnd⟩` from `enat_add_natCast_eq_natCast_exists (GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k (clo z) (cloι z ≫ q) hq' e hdim w d hd)`. Take `⟨n', hn', hnd'⟩` from `enat_add_natCast_eq_natCast_exists (hC (cloι z w) d hd')`.

Establish `: n' = n + 1` using `by omega`. Rewrite using `[hn, hn', this]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: n = 1` using `by exact_mod_cast h`.

Simplify using `[this]`. Introduce `h`. Establish `: n + 1 = 2` using `by exact_mod_cast h`. Establish `: n = 1` using `by omega`. Simplify using `[this]`.
-/
theorem dimOne : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ,
    topologicalKrullDim Y = (e + 1 : ℕ) → (∀ z : Y, Order.coheight z = 1 ↔ HasDim z e) ∧
    ∀ (z : Y) (w : clo z), Order.coheight z = 1 →
      (topologicalKrullDim (clo z) = e ∧ (Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2)) := by
  intro k _ Y _ q hq e hY
  have hB := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  have hC := GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k Y q hq (e + 1) hY
  have h1 : ∀ z : Y, Order.coheight z = 1 ↔ HasDim z e := by
    intro z
    obtain ⟨m, hm⟩ := hB.1
    obtain ⟨d, -, hd⟩ := hm z
    obtain ⟨n, hn, hnd⟩ := enat_add_natCast_eq_natCast_exists (hC z d hd)
    constructor
    · intro hz
      rw [hz] at hn
      have : n = 1 := by exact_mod_cast hn.symm
      subst this
      have : d = e := by omega
      exact this ▸ hd
    · intro hz
      have := hB.2.1 z d e hd hz
      subst this
      rw [hn]
      have : n = 1 := by omega
      simp [this]
  refine ⟨h1, fun z w hz => ?_⟩
  have hze : HasDim z e := (h1 z).1 hz
  have hgen : HasDim (genericPoint (clo z)) e := by
    rw [← hB.2.2.2.2.1 (clo z) (cloι z) (genericPoint (clo z)) e, cloι_genericPoint]
    exact hze
  have hdim : topologicalKrullDim (clo z) = e := (hB.2.2.2.2.2 (clo z) e).1 hgen
  refine ⟨hdim, ?_⟩
  have hq' : IsAmb (cloι z ≫ q) := hq.sub (cloι z)
  have hB' := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k (clo z) (cloι z ≫ q) hq'
  obtain ⟨m, hm⟩ := hB'.1
  obtain ⟨d, -, hd⟩ := hm w
  have hd' : HasDim (cloι z w) d := (hB.2.2.2.2.1 (clo z) (cloι z) w d).2 hd
  obtain ⟨n, hn, hnd⟩ := enat_add_natCast_eq_natCast_exists (GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k (clo z) (cloι z ≫ q) hq' e hdim w d hd)
  obtain ⟨n', hn', hnd'⟩ := enat_add_natCast_eq_natCast_exists (hC (cloι z w) d hd')
  have : n' = n + 1 := by omega
  rw [hn, hn', this]
  constructor
  · intro h
    have : n = 1 := by exact_mod_cast h
    simp [this]
  · intro h
    have : n + 1 = 2 := by exact_mod_cast h
    have : n = 1 := by omega
    simp [this]

end GlobalTheory.MixHt
