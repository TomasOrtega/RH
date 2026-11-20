import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Introduce `F _ _ _`. Take `⟨w₀⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Use `set s : TR.Rinf F := fun w => if w = w₀ then -1 else 1 with hs`. Establish `hss : s * s = 1`. Use function extensionality and compare the values at `w`.

Apply the tactic sequence `by_cases h : w = w₀ <;> simp [hs, h]`. Establish `hx : ((TR.infEq F s, 1) : A F) * (TR.infEq F s, 1) = 1`. Establish `h1 : TR.infEq F s * TR.infEq F s = 1` using `by rw [← map_mul, hss, map_one]`. Conclude with `Prod.ext h1 (mul_one _)`. Set `a : (A F)ˣ` to `⟨(TR.infEq F s, 1), (TR.infEq F s, 1), hx, hx⟩`.

Establish `haa : a * a = 1` using `Units.ext hx`. Use `⟨a, ⟨rfl, w₀, fun w => ?_⟩, haa, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(TR.infEq F).symm (TR.infEq F s) w = _`. Rewrite using `[RingEquiv.symm_apply_apply]`. Establish `h1 : IdeleGroup.ideleModule F (a * a) = 1` using `by rw [haa, map_one]`.

Rewrite `h1` using `[map_mul]`. Establish `h2 : ab a * ab a = 1`. Use `congrArg (fun r : {r : ℝ // 0 < r} => (r : ℝ)) h1` as an intermediate fact. Simplify `this` using `[ab]`. Establish `h3 : 0 < ab a` using `(IdeleGroup.ideleModule F a).2`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.sgnEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ a : (A F)ˣ, IsSgn a ∧ a * a = 1 ∧ ab a = 1 := by
  intro F _ _ _
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set s : TR.Rinf F := fun w => if w = w₀ then -1 else 1 with hs
  have hss : s * s = 1 := by
    funext w
    by_cases h : w = w₀ <;> simp [hs, h]
  have hx : ((TR.infEq F s, 1) : A F) * (TR.infEq F s, 1) = 1 := by
    have h1 : TR.infEq F s * TR.infEq F s = 1 := by rw [← map_mul, hss, map_one]
    exact Prod.ext h1 (mul_one _)
  let a : (A F)ˣ := ⟨(TR.infEq F s, 1), (TR.infEq F s, 1), hx, hx⟩
  have haa : a * a = 1 := Units.ext hx
  refine ⟨a, ⟨rfl, w₀, fun w => ?_⟩, haa, ?_⟩
  · change (TR.infEq F).symm (TR.infEq F s) w = _
    rw [RingEquiv.symm_apply_apply]
  · have h1 : IdeleGroup.ideleModule F (a * a) = 1 := by rw [haa, map_one]
    rw [map_mul] at h1
    have h2 : ab a * ab a = 1 := by
      have := congrArg (fun r : {r : ℝ // 0 < r} => (r : ℝ)) h1
      simpa [ab] using this
    have h3 : 0 < ab a := (IdeleGroup.ideleModule F a).2
    nlinarith
