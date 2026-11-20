import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinPol2P

/- English proof (translation)
Assemble the required witnesses or components as `⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl, fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩`.
-/
theorem isLevel_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.LFun.KGL w n) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl, fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩

end PositivityTheory.Rg.BcB.G3.FinPol2P

open PositivityTheory.Rg.BcB.G3.FinPol2P in
/- English proof (translation)
Introduce `E _ _ _ hU a b S hS φ hφc hφ1`. Establish `hC₁ : ∀ w, IsCompact (Prod.fst '' tsupport (φ w))` using `fun w => (hφc w).image continuous_fst`. Establish `hC₂ : ∀ w, IsCompact (Prod.snd '' tsupport (φ w))` using `fun w => (hφc w).image continuous_snd`. Use `choose γ₁ hγ₁0 hγ₁ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E a w _ (hC₁ w)`. Use `choose γ₂ hγ₂0 hγ₂ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E b w _ (hC₂ w)`.

Set `good : Pl E → Prop` to `fun w => φ w = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set (GLw a w × GLw b w)).indicator 1`. Set `g₁ : Pl E → WithZero (Multiplicative ℤ)` to `fun w => if good w then 1 else γ₁ w`. Set `g₂ : Pl E → WithZero (Multiplicative ℤ)` to `fun w => if good w then 1 else γ₂ w`. Apply the tactic sequence `have hfin₁ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E a S hS g₁ (fun w => by by_cases h : good w <;> simp [g₁, h, hγ₁0]) (hφ1.mono fun w h => by simp [g₁, good, h])`. Apply the tactic sequence `have hfin₂ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E b S hS g₂ (fun w => by by_cases h : good w <;> simp [g₂, h, hγ₂0]) (hφ1.mono fun w h => by simp [g₂, good, h])`.

Use `(hfin₁.prod hfin₂).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨h₁, h₂, hp⟩`. Establish `key : ∀ w ∈ S, ((∀ i, Valued.v ((atPl w p.1).coeff i) ≤ g₁ w) ∧ (g₁ w)⁻¹ ≤ Valued.v ((atPl w p.1).coeff 0)) ∧ ((∀ i, Valued.v ((atPl w p.2).coeff i) ≤ g₂ w) ∧ (g₂ w)⁻¹ ≤ Valued.v ((atPl w p.2).coeff 0))`. Introduce `w hw`. Take `⟨y, hy, e₁, e₂⟩` from `hp w hw`.

Rewrite using `[← e₁, ← e₂]`. Distinguish the cases in `hg : good w`. Simplify using `only [g₁, g₂, if_pos hg, inv_one]`. Establish `hy' : y ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)`. Establish `hy2` using `hy`.

Rewrite `hy2` using `[show φ w = _ from hg]`. Assume the negation of the conclusion as `hc`. Conclude with `hy2 (Set.indicator_of_notMem hc _)`. Conclude with `⟨GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E a w (isLevel_KGL hU a w) y.1 hy'.1, GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E b w (isLevel_KGL hU b w) y.2 hy'.2⟩`. Simplify using `only [g₁, g₂, if_neg hg]`.

Establish `hyt : y ∈ tsupport (φ w)` using `subset_tsupport _ hy`. Conclude with `⟨hγ₁ w y.1 ⟨y, hyt, rfl⟩, hγ₂ w y.2 ⟨y, hyt, rfl⟩⟩`. Conclude with `⟨⟨h₁, fun w hw => (key w hw).1⟩, ⟨h₂, fun w hw => (key w hw).2⟩⟩`.
-/
theorem PositivityTheory.Rg.BcB.G3.finPol2_pf : FinPol2 := by
  intro E _ _ _ hU a b S hS φ hφc hφ1
  have hC₁ : ∀ w, IsCompact (Prod.fst '' tsupport (φ w)) := fun w => (hφc w).image continuous_fst
  have hC₂ : ∀ w, IsCompact (Prod.snd '' tsupport (φ w)) := fun w => (hφc w).image continuous_snd
  choose γ₁ hγ₁0 hγ₁ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E a w _ (hC₁ w)
  choose γ₂ hγ₂0 hγ₂ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E b w _ (hC₂ w)
  let good : Pl E → Prop := fun w => φ w = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) :
    Set (GLw a w × GLw b w)).indicator 1
  let g₁ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₁ w
  let g₂ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₂ w
  have hfin₁ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E a S hS g₁
    (fun w => by by_cases h : good w <;> simp [g₁, h, hγ₁0]) (hφ1.mono fun w h => by simp [g₁, good, h])
  have hfin₂ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E b S hS g₂
    (fun w => by by_cases h : good w <;> simp [g₂, h, hγ₂0]) (hφ1.mono fun w h => by simp [g₂, good, h])
  refine (hfin₁.prod hfin₂).subset ?_
  rintro p ⟨h₁, h₂, hp⟩
  have key : ∀ w ∈ S, ((∀ i, Valued.v ((atPl w p.1).coeff i) ≤ g₁ w) ∧ (g₁ w)⁻¹ ≤ Valued.v ((atPl w p.1).coeff 0)) ∧
      ((∀ i, Valued.v ((atPl w p.2).coeff i) ≤ g₂ w) ∧ (g₂ w)⁻¹ ≤ Valued.v ((atPl w p.2).coeff 0)) := by
    intro w hw
    obtain ⟨y, hy, e₁, e₂⟩ := hp w hw
    rw [← e₁, ← e₂]
    by_cases hg : good w
    · simp only [g₁, g₂, if_pos hg, inv_one]
      have hy' : y ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
        have hy2 := hy
        rw [show φ w = _ from hg] at hy2
        by_contra hc
        exact hy2 (Set.indicator_of_notMem hc _)
      exact ⟨GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E a w (isLevel_KGL hU a w) y.1 hy'.1,
        GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E b w (isLevel_KGL hU b w) y.2 hy'.2⟩
    · simp only [g₁, g₂, if_neg hg]
      have hyt : y ∈ tsupport (φ w) := subset_tsupport _ hy
      exact ⟨hγ₁ w y.1 ⟨y, hyt, rfl⟩, hγ₂ w y.2 ⟨y, hyt, rfl⟩⟩
  exact ⟨⟨h₁, fun w hw => (key w hw).1⟩, ⟨h₂, fun w hw => (key w hw).2⟩⟩

end
