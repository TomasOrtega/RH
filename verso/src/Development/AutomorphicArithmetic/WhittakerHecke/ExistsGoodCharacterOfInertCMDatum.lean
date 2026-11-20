import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Introduce `E _ _ D v w hG hI`. Take `⟨e, h1, h2, h3, -⟩` from `hI.coord`. Take `⟨sa, sm, sc, -⟩` from `H.sgLaws ℚ v`. Take `⟨-, tm, tc, -⟩` from `H.sgLaws E w`. Take `⟨ga, gi, gm⟩` from `hG.psi`.

Establish `hs : ∀ u, -(H.sg v u) = H.sg v (-u)` using `fun u => by`. Rewrite using `[← neg_one_mul, sm, map_neg, map_one, neg_one_mul]`. Establish `s0 : H.sg v (0 : H.Kv v) = 0` using `by simpa using (sm 0 0).symm`. Establish `h4 : ∀ c u t, e (0, c) * e (u, t) = e (H.cp v (rt D.δ) * (c * t), c * u)` using `fun c u t => by`. Establish `a1 : ∀ x y, H.sg v (x * y) = H.sg v x * H.sg v y` using `fun x y => by rw [sm, sc]`.

Establish `a2 : ∀ x, H.sg v (H.cp v (rt D.δ) * x) = rt D.δ * H.sg v x` using `fun x => (sm (rt D.δ) x).symm`. Establish `a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap ℚ E (rt D.δ)`. Rewrite using `[← map_pow, D.sq]`. Conclude with `(AdeleBaseChange.adeleMap_algebraMap _).symm`. Establish `: H.sg w (e (0, c) * e (u, t)) = H.sg w (e (H.cp v (rt D.δ) * (c * t), c * u))`.

Rewrite using `[← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]`. Simplify using `only [Dat.mkE, map_mul, map_zero, ← a3]`. Expand and normalize the polynomial expressions, which then agree. Simplify `congrArg (H.cp w) this` using `only [tc]`. Establish `key : ∀ y : H.Kv v, (∀ c, H.IsInt c → ψ (H.sg v (-(c * y))) = 1) → H.IsInt y` using `fun y hy => by`.

Establish `: Valued.v (-y) ≤ 1` using `gm _ fun c hc => by`. Use `hy c hc` as an intermediate fact. Rewrite `this` using `[show -(c * y) = c * -y by ring]`. Then use the resulting hypothesis. Rewrite `this` using `[Valuation.map_neg]`. Then use the resulting hypothesis. Use `⟨fun x => ψ (H.sg v (-(e.symm x).2)), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[map_add, Prod.snd_add, neg_add]`. Conclude with `ga _ _`. Take `⟨⟨u, t⟩, rfl⟩` from `e.surjective x`. Establish `ht : Valued.v t ≤ 1` using `(le_max_right _ _).trans ((h2 u t).symm.le.trans hx)`.

Use `beta_reduce`. Rewrite using `[e.symm_apply_apply]`. Use `gi _ ?_` and prove the remaining obligations. Use `show Valued.v _ ≤ 1`. Rewrite using `[Valuation.map_neg]` and apply the resulting hypothesis.

Take `⟨⟨u, t⟩, rfl⟩` from `e.surjective x`. Establish `ht : H.IsInt t` using `key t fun c hc => by`. Use `hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))` as an intermediate fact. Use `beta_reduce at this`. Rewrite `this` using `[h3, e.symm_apply_apply]`. Then use the resulting hypothesis.

Establish `hu : H.IsInt u` using `key u fun c hc => by`. Use `hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))` as an intermediate fact. Use `beta_reduce at this`. Rewrite `this` using `[h4, e.symm_apply_apply]`. Then use the resulting hypothesis. Conclude with `(h2 u t).le.trans (max_le hu ht)`.

Take `⟨⟨u, t⟩, rfl⟩` from `e.surjective x`. Conclude with `⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩`.
-/
theorem UpperTheory.exists_good_character_of_inert_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w : H.P E), H.Gd D.δ v → H.Inert D v w →
          ∃ χ : H.Kv w → ℂ, H.Good χ ∧ ∀ x, ∃ u t, H.sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  intro E _ _ D v w hG hI
  obtain ⟨e, h1, h2, h3, -⟩ := hI.coord
  obtain ⟨sa, sm, sc, -⟩ := H.sgLaws ℚ v
  obtain ⟨-, tm, tc, -⟩ := H.sgLaws E w
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have hs : ∀ u, -(H.sg v u) = H.sg v (-u) := fun u => by
    rw [← neg_one_mul, sm, map_neg, map_one, neg_one_mul]
  have s0 : H.sg v (0 : H.Kv v) = 0 := by simpa using (sm 0 0).symm
  have h4 : ∀ c u t, e (0, c) * e (u, t) = e (H.cp v (rt D.δ) * (c * t), c * u) := fun c u t => by
    have a1 : ∀ x y, H.sg v (x * y) = H.sg v x * H.sg v y := fun x y => by rw [sm, sc]
    have a2 : ∀ x, H.sg v (H.cp v (rt D.δ) * x) = rt D.δ * H.sg v x := fun x => (sm (rt D.δ) x).symm
    have a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap ℚ E (rt D.δ) := by
      rw [← map_pow, D.sq]
      exact (AdeleBaseChange.adeleMap_algebraMap _).symm
    have : H.sg w (e (0, c) * e (u, t)) = H.sg w (e (H.cp v (rt D.δ) * (c * t), c * u)) := by
      rw [← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]
      simp only [Dat.mkE, map_mul, map_zero, ← a3]
      ring
    simpa only [tc] using congrArg (H.cp w) this
  have key : ∀ y : H.Kv v, (∀ c, H.IsInt c → ψ (H.sg v (-(c * y))) = 1) → H.IsInt y := fun y hy => by
    have : Valued.v (-y) ≤ 1 := gm _ fun c hc => by
      have := hy c hc
      rwa [show -(c * y) = c * -y by ring] at this
    rwa [Valuation.map_neg] at this
  refine ⟨fun x => ψ (H.sg v (-(e.symm x).2)), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩
  · beta_reduce
    rw [map_add, Prod.snd_add, neg_add]
    exact ga _ _
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : Valued.v t ≤ 1 := (le_max_right _ _).trans ((h2 u t).symm.le.trans hx)
    beta_reduce
    rw [e.symm_apply_apply]
    refine gi _ ?_
    show Valued.v _ ≤ 1
    rwa [Valuation.map_neg]
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : H.IsInt t := key t fun c hc => by
      have := hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))
      beta_reduce at this
      rwa [h3, e.symm_apply_apply] at this
    have hu : H.IsInt u := key u fun c hc => by
      have := hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))
      beta_reduce at this
      rwa [h4, e.symm_apply_apply] at this
    exact (h2 u t).le.trans (max_le hu ht)
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    exact ⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩
