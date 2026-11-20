import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOnPts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOnLineGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierRatioLocalNorm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ShFam.Pad GlobalTheory.FlatSecCover

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatSecCover

/- English proof (translation)
Take `⟨g, hg, hu⟩` from `h`. Use `⟨g⁻¹, hg.neg, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val, ← mul_inv]`. Conclude with `hu.inv`.
-/
theorem generatesAt_neg_inv {X : Scheme.{0}} [IsIntegral X] {Δ : CartierDiv X} {x : X} {f : X.functionField}
    (h : Δ.GeneratesAt x f) : (-Δ).GeneratesAt x f⁻¹ := by
  obtain ⟨g, hg, hu⟩ := h
  refine ⟨g⁻¹, hg.neg, ?_⟩
  rw [Units.val_inv_eq_inv_val, ← mul_inv]
  exact hu.inv

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (CartierDiv.generatesAt_zero_iff (x := x) (f := (1 : X.functionField))).2 (unitAt_one x)`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.prod_insert hj]`. Conclude with `(h j (Finset.mem_insert_self j s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem generatesAt_prod {X : Scheme.{0}} [IsIntegral X] {ι : Type} (s : Finset ι) {Δ : ι → CartierDiv X} {x : X}
    {f : ι → X.functionField} (h : ∀ i ∈ s, (Δ i).GeneratesAt x (f i)) :
    (∑ i ∈ s, Δ i).GeneratesAt x (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CartierDiv.generatesAt_zero_iff (x := x) (f := (1 : X.functionField))).2 (unitAt_one x)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self j s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {D : D7}

/- English proof (translation)
Establish `hp` using `O.S.p_eq`. Establish `hr` using `O.S.rank_eq`. Establish `hi'` using `i.isLt`. Unfold `rootFn rootSym`. Distinguish the cases in `hi : (i : ℕ) < O.j`.

Rewrite using `[if_pos hi, if_pos (by omega)]`. Establish `e : expo O.S.Dw (Finsupp.single ((fun _ => false : ℕ → Bool), (none : Option ℝ), (Sum.inl (DV.tauEmb D τ, (i : ℕ)) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)) 1) = expo O.S.Dw (Finsupp.single (ArIn.ind (FlagAr.setB O.Y B), (none : Option ℝ), (Sum.inl (DV.tauEmb D τ, (i : ℕ)) : ((D.host.E →+* …`. Use function extensionality and compare the values at `x`. Rewrite using `[expo_single, expo_single]`. Rewrite using `[e]`.

Conclude with `generatesAt_genAt _ z`. Rewrite using `[if_neg hi, if_neg (by omega)]`. Establish `e : expo O.S.Dw (Finsupp.single ((fun _ => false : ℕ → Bool), (none : Option ℝ), (Sum.inl (conjEmb (DV.tauEmb D τ), O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ)) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)) (-1)) = -expo O.S.Dw (Finsupp.single (ArIn.ind (FlagAr.setB O.Y B), (none : Option ℝ), (Sum.inl (c …`. Use function extensionality and compare the values at `x`. Establish `hs : O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ) = O.N - 1 - (i : ℕ)` using `by omega`.

Rewrite using `[Pi.neg_apply, expo_single, expo_single, hs]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e, GlobalTheory.OmCx.divOf_neg O c]`. Conclude with `generatesAt_neg_inv (generatesAt_genAt _ z)`.
-/
theorem generatesAt_rootFn (O : Setup D) (c : O.s.Comp) (B : ℝ) (τ : D.what₂.Tau) (i : Fin O.N) (z : (O.var c).X) :
    (divOf (O.Φ.C c) (expo O.S.Dw (rootSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ) i))).GeneratesAt z
      (rootFn O c B (τ, i) z) := by
  have hp := O.S.p_eq
  have hr := O.S.rank_eq
  have hi' := i.isLt
  unfold rootFn rootSym
  by_cases hi : (i : ℕ) < O.j
  · rw [if_pos hi, if_pos (by omega)]
    have e : expo O.S.Dw (Finsupp.single ((fun _ => false : ℕ → Bool), (none : Option ℝ),
        (Sum.inl (DV.tauEmb D τ, (i : ℕ)) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)) 1) =
        expo O.S.Dw (Finsupp.single (ArIn.ind (FlagAr.setB O.Y B), (none : Option ℝ),
        (Sum.inl (DV.tauEmb D τ, (i : ℕ)) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)) 1) := by
      funext x
      rw [expo_single, expo_single]
    rw [e]
    exact generatesAt_genAt _ z
  · rw [if_neg hi, if_neg (by omega)]
    have e : expo O.S.Dw (Finsupp.single ((fun _ => false : ℕ → Bool), (none : Option ℝ),
        (Sum.inl (conjEmb (DV.tauEmb D τ), O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ)) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)) (-1)) =
        -expo O.S.Dw (Finsupp.single (ArIn.ind (FlagAr.setB O.Y B), (none : Option ℝ),
        (Sum.inl (conjEmb (DV.tauEmb D τ), O.N - 1 - (i : ℕ)) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)) 1) := by
      funext x
      have hs : O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ) = O.N - 1 - (i : ℕ) := by omega
      rw [Pi.neg_apply, expo_single, expo_single, hs]
      split_ifs <;> simp
    rw [e, GlobalTheory.OmCx.divOf_neg O c]
    exact generatesAt_neg_inv (generatesAt_genAt _ z)

/- English proof (translation)
Rewrite using `[detSym, GlobalTheory.OmCx.expo_finset_sum, GlobalTheory.OmCx.divOf_sum, O.S.rank_eq, Finset.sum_range]`. Conclude with `generatesAt_prod Finset.univ fun i _ => generatesAt_rootFn O c B τ i z`.
-/
theorem generatesAt_detFn (O : Setup D) (c : O.s.Comp) (B : ℝ) (τ : D.what₂.Tau) (z : (O.var c).X) :
    (divOf (O.Φ.C c) (expo O.S.Dw (detSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ)))).GeneratesAt z
      (detFn O c B τ z) := by
  rw [detSym, GlobalTheory.OmCx.expo_finset_sum, GlobalTheory.OmCx.divOf_sum, O.S.rank_eq, Finset.sum_range]
  exact generatesAt_prod Finset.univ fun i _ => generatesAt_rootFn O c B τ i z

/- English proof (translation)
Introduce `D O c B τ z`. Rewrite using `[div_eq_mul_inv]`. Conclude with `GlobalTheory.ChernWeilLine.unitAt_mul_inv_of_generatesAt (GlobalTheory.ShFam.Hor.isFlat_flatSec D O.A O.N O.j O.S O.κ O.s O.Φ c τ z) (generatesAt_detFn O c B τ z)`.
-/
theorem unitAt_flatSec_div_detFn : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (B : ℝ) (τ : D.what₂.Tau) (z : (O.var c).X),
    UnitAt z (flatSec O.s O.Φ c τ / detFn O c B τ z) := by
  intro D O c B τ z
  rw [div_eq_mul_inv]
  exact GlobalTheory.ChernWeilLine.unitAt_mul_inv_of_generatesAt
    (GlobalTheory.ShFam.Hor.isFlat_flatSec D O.A O.N O.j O.S O.κ O.s O.Φ c τ z) (generatesAt_detFn O c B τ z)

end GlobalTheory.FlatSecCover
