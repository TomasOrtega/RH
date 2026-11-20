import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact

noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep
open scoped Pointwise
open PositivityTheory.RgTw (G)

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

section Gen

variable {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [TopologicalSpace U] [CompactSpace U] [T2Space U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
  (ν : Measure U) [IsFiniteMeasure ν]
  (K : Subgroup G) (hK : IsCompact (K : Set G)) (ι : U → G) (hι : Continuous ι) (hιK : ∀ u, ι u ∈ K)

include hK in
/- English proof (translation)
Establish `e : Measure.map (⇑(MeasurableEquiv.mulRight k)) μ = μ` using `GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact μ K hK k hk`. Use `conv_rhs => rw [← e]`. Rewrite using `[(MeasurableEquiv.mulRight k).measurableEmbedding.integral_map]`. Both sides reduce to the same expression.
-/
theorem integral_mul_mem (k : G) (hk : k ∈ K) (F : G → ℂ) : ∫ y, F (y * k) ∂μ = ∫ y, F y ∂μ := by
  have e : Measure.map (⇑(MeasurableEquiv.mulRight k)) μ = μ :=
    GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact μ K hK k hk
  conv_rhs => rw [← e]
  rw [(MeasurableEquiv.mulRight k).measurableEmbedding.integral_map]
  rfl

include hK hι hιK in
/- English proof (translation)
Establish `hKK : IsCompact (Kc * (K : Set G))` using `hKc.mul hK`. Establish `i1 : Integrable (Function.uncurry fun y u => c y u * h (y * ι u)) (μ.prod ν)`. Apply `Continuous.integrable_of_hasCompactSupport` to reduce the goal to its premises. Conclude with `hc.mul (hh.comp (continuous_fst.mul (hι.comp continuous_snd)))`. Use `HasCompactSupport.intro (hKc.prod isCompact_univ) fun p hp => ?_` and prove the remaining obligations.

Establish `: p.1 ∉ Kc` using `fun h1 => hp ⟨h1, Set.mem_univ _⟩`. Simplify using `[Function.uncurry, hcK _ _ this]`. Establish `i2 : Integrable (Function.uncurry fun y u => c (y * (ι u)⁻¹) u * h y) (μ.prod ν)`. Apply `Continuous.integrable_of_hasCompactSupport` to reduce the goal to its premises. Conclude with `(hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)).mul (hh.comp continuous_fst)`.

Use `HasCompactSupport.intro (hKK.prod isCompact_univ) fun p hp => ?_` and prove the remaining obligations. Establish `: p.1 * (ι p.2)⁻¹ ∉ Kc` using `fun h1 => hp ⟨⟨p.1 * (ι p.2)⁻¹, h1, ι p.2, hιK p.2, by simp⟩, Set.mem_univ _⟩`. Simplify using `[Function.uncurry, hcK _ _ this]`. Rewrite using `[integral_integral_swap i1]`. Establish `e : ∀ u, ∫ y, c y u * h (y * ι u) ∂μ = ∫ y, c (y * (ι u)⁻¹) u * h y ∂μ`.

Introduce `u`. Use `integral_mul_mem μ K hK (ι u) (hιK u) (fun y => c (y * (ι u)⁻¹) u * h y)` as an intermediate fact. Simplify using `using this`. Repeatedly rewrite using `[e]`. Rewrite using `[← integral_integral_swap i2]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[integral_mul_const]`.
-/
theorem swap_right (c : G → U → ℂ) (hc : Continuous (Function.uncurry c)) (Kc : Set G) (hKc : IsCompact Kc)
    (hcK : ∀ y u, y ∉ Kc → c y u = 0) (h : G → ℂ) (hh : Continuous h) :
    ∫ y, (∫ u, c y u * h (y * ι u) ∂ν) ∂μ = ∫ y, (∫ u, c (y * (ι u)⁻¹) u ∂ν) * h y ∂μ := by
  have hKK : IsCompact (Kc * (K : Set G)) := hKc.mul hK
  have i1 : Integrable (Function.uncurry fun y u => c y u * h (y * ι u)) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hc.mul (hh.comp (continuous_fst.mul (hι.comp continuous_snd)))
    · refine HasCompactSupport.intro (hKc.prod isCompact_univ) fun p hp => ?_
      have : p.1 ∉ Kc := fun h1 => hp ⟨h1, Set.mem_univ _⟩
      simp [Function.uncurry, hcK _ _ this]
  have i2 : Integrable (Function.uncurry fun y u => c (y * (ι u)⁻¹) u * h y) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)).mul
        (hh.comp continuous_fst)
    · refine HasCompactSupport.intro (hKK.prod isCompact_univ) fun p hp => ?_
      have : p.1 * (ι p.2)⁻¹ ∉ Kc := fun h1 =>
        hp ⟨⟨p.1 * (ι p.2)⁻¹, h1, ι p.2, hιK p.2, by simp⟩, Set.mem_univ _⟩
      simp [Function.uncurry, hcK _ _ this]
  rw [integral_integral_swap i1]
  have e : ∀ u, ∫ y, c y u * h (y * ι u) ∂μ = ∫ y, c (y * (ι u)⁻¹) u * h y ∂μ := by
    intro u
    have := integral_mul_mem μ K hK (ι u) (hιK u) (fun y => c (y * (ι u)⁻¹) u * h y)
    simpa using this
  simp_rw [e]
  rw [← integral_integral_swap i2]
  congr 1
  funext y
  rw [integral_mul_const]

include hK hι hιK in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `continuous_parametric_integral_of_continuous (μ := ν) (f := fun y u => c (y * (ι u)⁻¹) u) (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)) isCompact_univ` as an intermediate fact. Simplify `this` using `[Measure.restrict_univ]`. Use `HasCompactSupport.intro (hKc.mul hK) fun y hy => ?_` and prove the remaining obligations. Establish `: ∀ u, c (y * (ι u)⁻¹) u = 0` using `fun u => hcK _ _ fun h1 => hy ⟨_, h1, ι u, hιK u, by simp⟩`.

Simplify using `[this]`.
-/
theorem avg_cont_supp (c : G → U → ℂ) (hc : Continuous (Function.uncurry c)) (Kc : Set G) (hKc : IsCompact Kc)
    (hcK : ∀ y u, y ∉ Kc → c y u = 0) :
    Continuous (fun y => ∫ u, c (y * (ι u)⁻¹) u ∂ν) ∧ HasCompactSupport (fun y => ∫ u, c (y * (ι u)⁻¹) u ∂ν) := by
  constructor
  · have := continuous_parametric_integral_of_continuous (μ := ν) (f := fun y u => c (y * (ι u)⁻¹) u)
      (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)) isCompact_univ
    simpa [Measure.restrict_univ] using this
  · refine HasCompactSupport.intro (hKc.mul hK) fun y hy => ?_
    have : ∀ u, c (y * (ι u)⁻¹) u = 0 := fun u => hcK _ _ fun h1 => hy ⟨_, h1, ι u, hιK u, by simp⟩
    simp [this]

end Gen

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `continuous_subtype_val`. Conclude with `continuous_star.comp continuous_subtype_val`.
-/
theorem continuous_toUnitsU (N : ℕ) :
    Continuous (fun u : Matrix.unitaryGroup (Fin N) ℂ => (Unitary.toUnits u : G N)) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_subtype_val
  · exact continuous_star.comp continuous_subtype_val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

/- English proof (translation)
Set `Mt : (InfinitePlace E → G N) → GL (Fin N) (Cinf E)` to `fun y => Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom (MulEquiv.piUnits.symm y)`. Establish `hM : Continuous Mt`. Use `Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E => Matrix (Fin N) (Fin N) ℂ)).symm.continuous` and prove the remaining obligations. Conclude with `continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j`. Establish `hL : Continuous fun x : Matrix (Fin N) (Fin N) (Cinf E) => (toL x : Lie E N)` using `continuous_id`.

Establish `e : (fun t : G N => φ (g * infP N (Pi.mulSingle v t))) = fun t => chart φ g (toL (Mt (Pi.mulSingle v t)).val)`. Use function extensionality and compare the values at `t`. Rewrite using `[chart_val]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `(hs g).continuousOn.comp_continuous (hL.comp ((Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp (hM.comp (continuous_mulSingle (A := fun _ : InfinitePlace E => G N) v)))) fun t => val_mem_invSet _`.
-/
theorem continuous_along_infP (v : InfinitePlace E) (g : GA E N) (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) :
    Continuous fun t : G N => φ (g * infP N (Pi.mulSingle v t)) := by
  let Mt : (InfinitePlace E → G N) → GL (Fin N) (Cinf E) := fun y =>
    Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
      (MulEquiv.piUnits.symm y)
  have hM : Continuous Mt := by
    refine Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E =>
      Matrix (Fin N) (Fin N) ℂ)).symm.continuous
    exact continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  have hL : Continuous fun x : Matrix (Fin N) (Fin N) (Cinf E) => (toL x : Lie E N) := continuous_id
  have e : (fun t : G N => φ (g * infP N (Pi.mulSingle v t))) =
      fun t => chart φ g (toL (Mt (Pi.mulSingle v t)).val) := by
    funext t
    rw [chart_val]
    rfl
  rw [e]
  exact (hs g).continuousOn.comp_continuous
    (hL.comp ((Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp (hM.comp (continuous_mulSingle (A := fun _ : InfinitePlace E => G N) v))))
    fun t => val_mem_invSet _

end PositivityTheory.Rg.BcB.CG.ReproL
