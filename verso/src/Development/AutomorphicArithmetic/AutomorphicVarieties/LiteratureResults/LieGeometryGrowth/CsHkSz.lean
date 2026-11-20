import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsFlowSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
import Mathlib.Analysis.Normed.Module.Alternating.Curry
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

/- English proof (translation)
Introduce `V F _ _ _ _ _ _ q k c`. Take `⟨hA, C₁, hC₁⟩` from `altSz V F q k (1 + c)`. Take `⟨C₂, h₂, hC₂⟩` from `compSz V (V →L[ℝ] V) ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)`. Take `⟨C₃, h₃, hC₃⟩` from `compSz V V (V [⋀^Fin (q + 1)]→L[ℝ] F) k (1 + c)`. Set `L : (V [⋀^Fin (q + 1)]→L[ℝ] F) →L[ℝ] (V →L[ℝ] V [⋀^Fin q]→L[ℝ] F)` to `(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap`.

Use `⟨2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|), by positivity, ?_⟩` and prove the remaining obligations. Introduce `W t w p b ht hW hWs hw hws`. Take `⟨f1, f2, f3, f4⟩` from `flowSz V k c W t p ht hW hWs`. Establish `a1 : Sz k (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p (C₃ * b)` using `hC₃ w _ p b f1 hw (fun i h1 h2 => f4 i h1 (h2.trans (Nat.le_succ k))) hws`. Establish `s1 : ContDiffAt ℝ ∞ (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p` using `hw.comp p f1`.

Establish `a2` using `(appSz V _ _ k p).2.1 L _ _ s1 a1`. Establish `s2 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y))) p` using `L.contDiff.contDiffAt.comp p s1`. Establish `a3` using `(appSz V _ _ k p).1 _ W _ _ s2 hW a2 ((hWs.of_le (Nat.le_succ k)).mono (le_abs_self c))`. Establish `s3 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y)) (W y)) p` using `s2.clm_apply hW`. Establish `a4` using `hC₂ _ _ p _ f2 hA.contDiffAt (fun i _ h2 => f3 i h2) ((hC₁ _ f3.norm_le).mono (le_abs_self C₁))`.

Establish `s4` using `hA.contDiffAt.comp p f2`. Establish `a5` using `(appSz V _ _ k p).1 _ _ _ _ s4 s3 a4 a3`. Establish `e : 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|) * b = 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * (C₃ * b)) * |c|)` using `by ring`. Rewrite using `[e]`. Conclude with `a5`.
-/
theorem UpperTheory.V.Lit.Geo.Cs.hkSz :
    HkSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hA, C₁, hC₁⟩ := altSz V F q k (1 + c)
  obtain ⟨C₂, h₂, hC₂⟩ := compSz V (V →L[ℝ] V) ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  obtain ⟨C₃, h₃, hC₃⟩ := compSz V V (V [⋀^Fin (q + 1)]→L[ℝ] F) k (1 + c)
  let L : (V [⋀^Fin (q + 1)]→L[ℝ] F) →L[ℝ] (V →L[ℝ] V [⋀^Fin q]→L[ℝ] F) :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
  refine ⟨2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|), by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨f1, f2, f3, f4⟩ := flowSz V k c W t p ht hW hWs
  have a1 : Sz k (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p (C₃ * b) :=
    hC₃ w _ p b f1 hw (fun i h1 h2 => f4 i h1 (h2.trans (Nat.le_succ k))) hws
  have s1 : ContDiffAt ℝ ∞ (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p := hw.comp p f1
  have a2 := (appSz V _ _ k p).2.1 L _ _ s1 a1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y))) p := L.contDiff.contDiffAt.comp p s1
  have a3 := (appSz V _ _ k p).1 _ W _ _ s2 hW a2 ((hWs.of_le (Nat.le_succ k)).mono (le_abs_self c))
  have s3 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y)) (W y)) p := s2.clm_apply hW
  have a4 := hC₂ _ _ p _ f2 hA.contDiffAt (fun i _ h2 => f3 i h2) ((hC₁ _ f3.norm_le).mono (le_abs_self C₁))
  have s4 := hA.contDiffAt.comp p f2
  have a5 := (appSz V _ _ k p).1 _ _ _ _ s4 s3 a4 a3
  have e : 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|) * b =
      2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * (C₃ * b)) * |c|) := by ring
  rw [e]
  exact a5
