import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamSmooth

noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `V F _ _ _ _ _ _ Y hY W hW q w hw`. Establish `hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞`. Conclude with `le_top` after adjusting the coercions. Establish `hWat : ∀ p ∈ Y, ContDiffAt ℝ ∞ W p` using `fun p hp => hW.1.contDiffAt (hY.mem_nhds hp)`. Establish `hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w p` using `fun p hp => hw.contDiffAt (hY.mem_nhds hp)`.

Establish `hfd : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p = ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p`. Introduce `p hp t`. Establish `hd : DifferentiableAt ℝ W p` using `(hWat p hp).differentiableAt (by simp)`. Conclude with `((hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)).fderiv`. Establish `hflowc : ∀ z : V × ℝ, z.1 ∈ Y → ContDiffAt ℝ ∞ (fun y : V × ℝ => flow W y.2 y.1) z`.

Introduce `z hz`. Conclude with `contDiffAt_fst.add (contDiffAt_snd.smul ((hWat z.1 hz).comp z contDiffAt_fst))`. Establish `hSo : IsOpen {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y}`. Establish `h` using `ContinuousOn.isOpen_inter_preimage (f := fun y : V × ℝ => flow W y.2 y.1) (s := Prod.fst ⁻¹' Y) (t := Y) ?_ (hY.preimage continuous_fst) hY`. Conclude with `h`.

Introduce `z hz`. Conclude with `(hflowc z hz).continuousAt.continuousWithinAt`. Establish `hsm : ContDiffOn ℝ ∞ (fun z : V × ℝ => hk W z.2 w z.1) {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y}`. Introduce `z hz`. Apply `ContDiffAt.contDiffWithinAt` to reduce the goal to its premises.

Apply `UpperTheory.V.Lit.Dr.altSmooth (V × ℝ) V F q` to reduce the goal to its premises. Introduce `v`. Establish `hf : ContDiffAt ℝ ∞ (fun y : V × ℝ => w (flow W y.2 y.1)) z` using `(hwat _ hz.2).comp z (hflowc z hz.1)`. Establish `hu : ∀ i : Fin (q + 1), ContDiffAt ℝ ∞ ((Fin.cons (fun y : V × ℝ => W y.1) (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) i) z`. Introduce `i`.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`. Conclude with `(hWat z.1 hz.1).comp z contDiffAt_fst`. Simplify using `only [Fin.cons_succ]`. Conclude with `contDiffAt_const.add (contDiffAt_snd.smul ((((hWat z.1 hz.1).fderiv_right hinf).comp z contDiffAt_fst).clm_apply contDiffAt_const))`.

Establish `h3` using `UpperTheory.V.Lit.Dr.applySmooth (V × ℝ) V F (q + 1) (fun y : V × ℝ => w (flow W y.2 y.1)) (Fin.cons (fun y : V × ℝ => W y.1) (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) z hf hu`. Apply `h3.congr_of_eventuallyEq` to reduce the goal to its premises. Establish `hnb : {y : V × ℝ | y.1 ∈ Y} ∈ 𝓝 z` using `(hY.preimage continuous_fst).mem_nhds hz.1`. Use `filter_upwards [hnb] with y hy`. Simplify using `only [hk, ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.curryLeft_apply_apply, hfd y.1 hy y.2]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish `hmaps : ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y}` using `fun p hp t ht => ⟨hp, hW.2 p hp t ht⟩`. Use `⟨hSo, hsm, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Establish `hc : ContinuousOn ((fun z : V × ℝ => hk W z.2 w z.1) ∘ (fun t : ℝ => (p, t))) (Set.Icc 0 1)` using `hsm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => hmaps p hp t ht)`. Simplify `hc` using `[Function.comp_def]`.

Establish `h4` using `UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} (fun z => hk W z.2 w z.1) hY hSo (fun z hz => hmaps z.1 hz.1 z.2 hz.2) hsm`. Conclude with `h4`.
-/
theorem hkSmooth : HkSmooth := by
  intro V F _ _ _ _ _ _ Y hY W hW q w hw
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  have hWat : ∀ p ∈ Y, ContDiffAt ℝ ∞ W p := fun p hp => hW.1.contDiffAt (hY.mem_nhds hp)
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w p := fun p hp => hw.contDiffAt (hY.mem_nhds hp)
  have hfd : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p = ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p := by
    intro p hp t
    have hd : DifferentiableAt ℝ W p := (hWat p hp).differentiableAt (by simp)
    exact ((hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)).fderiv
  have hflowc : ∀ z : V × ℝ, z.1 ∈ Y → ContDiffAt ℝ ∞ (fun y : V × ℝ => flow W y.2 y.1) z := by
    intro z hz
    exact contDiffAt_fst.add (contDiffAt_snd.smul ((hWat z.1 hz).comp z contDiffAt_fst))
  have hSo : IsOpen {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} := by
    have h := ContinuousOn.isOpen_inter_preimage (f := fun y : V × ℝ => flow W y.2 y.1)
      (s := Prod.fst ⁻¹' Y) (t := Y) ?_ (hY.preimage continuous_fst) hY
    · exact h
    · intro z hz
      exact (hflowc z hz).continuousAt.continuousWithinAt
  have hsm : ContDiffOn ℝ ∞ (fun z : V × ℝ => hk W z.2 w z.1) {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    apply UpperTheory.V.Lit.Dr.altSmooth (V × ℝ) V F q
    intro v
    have hf : ContDiffAt ℝ ∞ (fun y : V × ℝ => w (flow W y.2 y.1)) z := (hwat _ hz.2).comp z (hflowc z hz.1)
    have hu : ∀ i : Fin (q + 1), ContDiffAt ℝ ∞ ((Fin.cons (fun y : V × ℝ => W y.1)
        (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) i) z := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (hWat z.1 hz.1).comp z contDiffAt_fst
      · simp only [Fin.cons_succ]
        exact contDiffAt_const.add (contDiffAt_snd.smul
          ((((hWat z.1 hz.1).fderiv_right hinf).comp z contDiffAt_fst).clm_apply contDiffAt_const))
    have h3 := UpperTheory.V.Lit.Dr.applySmooth (V × ℝ) V F (q + 1) (fun y : V × ℝ => w (flow W y.2 y.1))
      (Fin.cons (fun y : V × ℝ => W y.1)
        (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) z hf hu
    apply h3.congr_of_eventuallyEq
    have hnb : {y : V × ℝ | y.1 ∈ Y} ∈ 𝓝 z := (hY.preimage continuous_fst).mem_nhds hz.1
    filter_upwards [hnb] with y hy
    simp only [hk, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, hfd y.1 hy y.2]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  have hmaps : ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} :=
    fun p hp t ht => ⟨hp, hW.2 p hp t ht⟩
  refine ⟨hSo, hsm, ?_, ?_⟩
  · intro p hp
    have hc : ContinuousOn ((fun z : V × ℝ => hk W z.2 w z.1) ∘ (fun t : ℝ => (p, t))) (Set.Icc 0 1) :=
      hsm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => hmaps p hp t ht)
    simpa [Function.comp_def] using hc
  · have h4 := UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y}
      (fun z => hk W z.2 w z.1) hY hSo (fun z hz => hmaps z.1 hz.1 z.2 hz.2) hsm
    exact h4

end UpperTheory.V.Lit.Geo
