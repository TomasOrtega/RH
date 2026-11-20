import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PoinPt

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Introduce `V F _ _ _ _ _ _ Y hYo hYc p hp q w hw`. Establish `hseg : ∀ x ∈ Y, ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (x - p) ∈ Y`. Introduce `x hx t ht`. Establish `h` using `hYc hp hx (sub_nonneg.2 ht.2) ht.1 (by ring)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_sub, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Set `g : V × ℝ → V` to `fun z => p + z.2 • (z.1 - p)`. Establish `hg : ContDiff ℝ ⊤ g`. Conclude with `contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))`.

Set `W : Set (V × ℝ)` to `g ⁻¹' Y`. Establish `hW : IsOpen W` using `hYo.preimage hg.continuous`. Set `Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F` to `fun z => z.2 ^ q • (w (p + z.2 • (z.1 - p))).curryLeft (z.1 - p)`. Establish `hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ W`. Establish `h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => w (g z)) W` using `hw.comp (hg.of_le le_top).contDiffOn (fun z hz => hz)`.

Set `L` to `(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap`. Establish `hfst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.1 - p)` using `contDiff_fst.sub contDiff_const`. Establish `h2` using `(L.contDiff.comp_contDiffOn h1).clm_apply (hfst.contDiffOn (s := W))`. Establish `hsnd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.2 ^ q)` using `contDiff_snd.pow q`. Conclude with `hsnd.contDiffOn.smul h2`.

Establish `hsub : Y ×ˢ Set.Icc (0:ℝ) 1 ⊆ W` using `fun z hz => hseg z.1 hz.1 z.2 hz.2`. Use `⟨UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y W Φ hYo hW hsub hΦ, ?_⟩` and prove the remaining obligations. Introduce `hcl x hx`. Establish `hd` using `UpperTheory.V.Lit.Dr.paramDeriv V (V [⋀^Fin q]→L[ℝ] F) x W Φ hW (fun t ht => hseg x hx t ht) hΦ`. Establish `hI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1` using `Set.uIcc_of_le zero_le_one`.

Set `A` to `ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V F (n := q)`. Establish `hint : IntervalIntegrable (fun t => fderiv ℝ (fun y => Φ (y, t)) x) MeasureTheory.volume 0 1` using `(hI ▸ hd.1).intervalIntegrable`. Establish `hcont' : ContinuousOn (fun t => A (fderiv ℝ (fun y => Φ (y, t)) x)) (Set.uIcc 0 1)` using `hI ▸ (A.continuous.comp_continuousOn hd.1)`. Establish `hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p + r • (x - p))) (A (fderiv ℝ (fun y => Φ (y, t)) x)) t`. Introduce `t ht`.

Rewrite `ht` using `[hI]`. Establish `hm` using `hseg x hx t ht`. Establish `hdiff : DifferentiableAt ℝ w (p + t • (x - p))` using `(hw.contDiffAt (hYo.mem_nhds hm)).differentiableAt (by simp)`. Conclude with `UpperTheory.V.Lit.Dr.poinPt V F q w p x t hdiff (hcl _ hm)`. Establish `hfd : fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x = ∫ t in (0:ℝ)..1, fderiv ℝ (fun y => Φ (y, t)) x` using `hd.2.fderiv`.

Establish `key : extDeriv (UpperTheory.V.Cj.H.coneOp p w) x = A (fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x)` using `rfl`. Rewrite using `[key, hfd, ← A.intervalIntegral_comp_comm hint, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont'.intervalIntegrable)]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Cj.H.coneD :
    UpperTheory.V.Cj.H.ConeD := by
  intro V F _ _ _ _ _ _ Y hYo hYc p hp q w hw
  have hseg : ∀ x ∈ Y, ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (x - p) ∈ Y := by
    intro x hx t ht
    have h := hYc hp hx (sub_nonneg.2 ht.2) ht.1 (by ring)
    convert h using 1
    rw [smul_sub, sub_smul, one_smul]
    abel
  let g : V × ℝ → V := fun z => p + z.2 • (z.1 - p)
  have hg : ContDiff ℝ ⊤ g := by
    exact contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))
  let W : Set (V × ℝ) := g ⁻¹' Y
  have hW : IsOpen W := hYo.preimage hg.continuous
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p + z.2 • (z.1 - p))).curryLeft (z.1 - p)
  have hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ W := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => w (g z)) W :=
      hw.comp (hg.of_le le_top).contDiffOn (fun z hz => hz)
    let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
    have hfst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.1 - p) :=
      contDiff_fst.sub contDiff_const
    have h2 := (L.contDiff.comp_contDiffOn h1).clm_apply (hfst.contDiffOn (s := W))
    have hsnd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.2 ^ q) :=
      contDiff_snd.pow q
    exact hsnd.contDiffOn.smul h2
  have hsub : Y ×ˢ Set.Icc (0:ℝ) 1 ⊆ W := fun z hz => hseg z.1 hz.1 z.2 hz.2
  refine ⟨UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y W Φ hYo hW hsub hΦ, ?_⟩
  intro hcl x hx
  have hd := UpperTheory.V.Lit.Dr.paramDeriv V (V [⋀^Fin q]→L[ℝ] F) x W Φ hW (fun t ht => hseg x hx t ht) hΦ
  have hI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V F (n := q)
  have hint : IntervalIntegrable (fun t => fderiv ℝ (fun y => Φ (y, t)) x) MeasureTheory.volume 0 1 :=
    (hI ▸ hd.1).intervalIntegrable
  have hcont' : ContinuousOn (fun t => A (fderiv ℝ (fun y => Φ (y, t)) x)) (Set.uIcc 0 1) :=
    hI ▸ (A.continuous.comp_continuousOn hd.1)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p + r • (x - p))) (A (fderiv ℝ (fun y => Φ (y, t)) x)) t := by
    intro t ht
    rw [hI] at ht
    have hm := hseg x hx t ht
    have hdiff : DifferentiableAt ℝ w (p + t • (x - p)) :=
      (hw.contDiffAt (hYo.mem_nhds hm)).differentiableAt (by simp)
    exact UpperTheory.V.Lit.Dr.poinPt V F q w p x t hdiff (hcl _ hm)
  have hfd : fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x = ∫ t in (0:ℝ)..1, fderiv ℝ (fun y => Φ (y, t)) x :=
    hd.2.fderiv
  have key : extDeriv (UpperTheory.V.Cj.H.coneOp p w) x = A (fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x) := rfl
  rw [key, hfd, ← A.intervalIntegral_comp_comm hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont'.intervalIntegrable)]
  simp
