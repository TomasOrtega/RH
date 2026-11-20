import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Introduce `E _ _ D M d hd c hc`. Establish `hk : ∀ u t : A ℚ, D.mkE u t = AdeleBaseChange.adeleMap ℚ E u + AdeleBaseChange.adeleMap ℚ E t * rt D.θ` using `fun _ _ => rfl`. Establish `h0 : (0 : A E) ∈ Oh E` using `⟨rfl, fun w => by`. Express the relevant statement in the definitionally equal form `Valued.v (0 : H.Kv w) ≤ 1`. Use the proof step `simp⟩`.

Establish `hneg : ∀ s : A E, s ∈ Oh E → -s ∈ Oh E` using `fun s hs => ⟨by`. Express the relevant statement in the definitionally equal form `-s.1 = 0`. Rewrite using `[hs.1, neg_zero], fun w => by`. Establish `e : (-s).2 w = -(s.2 w)` using `rfl`. Rewrite using `[e, Valuation.map_neg]`.

Conclude with `hs.2 w⟩`. Establish `hfst : (AdeleBaseChange.adeleMap ℚ E c).1 = 0`. Take `⟨c1, c2⟩` from `c`. Take `rfl : c1 = 0` from `hc.1`. Conclude with `map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))`.

Establish `hb : AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ) ∈ Oh E`. Use `⟨?_, fun w => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(AdeleBaseChange.adeleMap ℚ E c).1 * _ = 0`. Rewrite using `[hfst, zero_mul]`. Establish `h1 : Valued.v ((AdeleBaseChange.adeleMap ℚ E c).2 w) ≤ 1` using `GroundTheory.Global.AdeleBaseChange.mapsTo_completionMap _ w (hc.2 _)`.

Establish `e : (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)).2 w = (AdeleBaseChange.adeleMap ℚ E c).2 w * H.cp w (rt ((d : E) * D.θ))` using `rfl`. Rewrite using `[e, map_mul]`. Conclude with `mul_le_one' h1 (hd w)`. Establish `hx : D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c) = (M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ))`. Establish `hr : rt ((d : E) * D.θ) = (d : A E) * rt D.θ`.

Express the relevant statement in the definitionally equal form `algebraMap E (A E) ((d : E) * D.θ) = _`. Rewrite using `[map_mul, map_natCast]`. Rewrite using `[hk, map_zero, zero_add, map_mul, map_mul, map_natCast, map_natCast, hr]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ s : A E, s ∈ Oh E → ∀ i j, ∃ c ∈ Oh E, (!![1, (M : A E) * s; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (M : A E) * c`.

Introduce `s hs i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `⟨0, h0, by simp⟩`. Conclude with `⟨s, hs, by simp⟩`. Conclude with `⟨0, h0, by simp⟩`.

Conclude with `⟨0, h0, by simp⟩`. Establish `hinv : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q))`. Introduce `q`. Use `inv_eq_of_mul_eq_one_right (Units.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(!![1, q; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) * !![1, -q; 0, 1] = 1`.

Simplify using `[Matrix.mul_fin_two, Matrix.one_fin_two]`. Establish `hn : nu D ((M : A ℚ) * (d : A ℚ) * c) = gl (nU ((M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ))))`. Express the relevant statement in the definitionally equal form `gl (nU (D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c))) = _`. Rewrite using `[hx]`. Introduce `i j`.

Rewrite using `[hn, hinv, ← mul_neg]`. Conclude with `⟨key _ hb i j, key _ (hneg _ hb) i j⟩`.
-/
theorem UpperTheory.unipotentTheta_mem_congruence_of_integral :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (M d : ℕ), (∀ w : H.P E, Valued.v (H.cp w (rt ((d : E) * D.θ))) ≤ 1) → ∀ c ∈ Oh ℚ, CongE M (nu D ((M : A ℚ) * (d : A ℚ) * c)) := by
  intro E _ _ D M d hd c hc
  have hk : ∀ u t : A ℚ, D.mkE u t = AdeleBaseChange.adeleMap ℚ E u + AdeleBaseChange.adeleMap ℚ E t * rt D.θ := fun _ _ => rfl
  have h0 : (0 : A E) ∈ Oh E := ⟨rfl, fun w => by
    change Valued.v (0 : H.Kv w) ≤ 1
    simp⟩
  have hneg : ∀ s : A E, s ∈ Oh E → -s ∈ Oh E := fun s hs => ⟨by
    change -s.1 = 0
    rw [hs.1, neg_zero], fun w => by
    have e : (-s).2 w = -(s.2 w) := rfl
    rw [e, Valuation.map_neg]
    exact hs.2 w⟩
  have hfst : (AdeleBaseChange.adeleMap ℚ E c).1 = 0 := by
    obtain ⟨c1, c2⟩ := c
    obtain rfl : c1 = 0 := hc.1
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have hb : AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ) ∈ Oh E := by
    refine ⟨?_, fun w => ?_⟩
    · change (AdeleBaseChange.adeleMap ℚ E c).1 * _ = 0
      rw [hfst, zero_mul]
    · have h1 : Valued.v ((AdeleBaseChange.adeleMap ℚ E c).2 w) ≤ 1 :=
        GroundTheory.Global.AdeleBaseChange.mapsTo_completionMap _ w (hc.2 _)
      have e : (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)).2 w =
          (AdeleBaseChange.adeleMap ℚ E c).2 w * H.cp w (rt ((d : E) * D.θ)) := rfl
      rw [e, map_mul]
      exact mul_le_one' h1 (hd w)
  have hx : D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c) = (M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)) := by
    have hr : rt ((d : E) * D.θ) = (d : A E) * rt D.θ := by
      change algebraMap E (A E) ((d : E) * D.θ) = _
      rw [map_mul, map_natCast]
    rw [hk, map_zero, zero_add, map_mul, map_mul, map_natCast, map_natCast, hr]
    ring
  have key : ∀ s : A E, s ∈ Oh E → ∀ i j, ∃ c ∈ Oh E,
      (!![1, (M : A E) * s; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (M : A E) * c := by
    intro s hs i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, h0, by simp⟩
    · exact ⟨s, hs, by simp⟩
    · exact ⟨0, h0, by simp⟩
    · exact ⟨0, h0, by simp⟩
  have hinv : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := by
    intro q
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    change (!![1, q; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) * !![1, -q; 0, 1] = 1
    simp [Matrix.mul_fin_two, Matrix.one_fin_two]
  have hn : nu D ((M : A ℚ) * (d : A ℚ) * c) = gl (nU ((M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)))) := by
    change gl (nU (D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c))) = _
    rw [hx]
  intro i j
  rw [hn, hinv, ← mul_neg]
  exact ⟨key _ hb i j, key _ (hneg _ hb) i j⟩
