import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsExtra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology

namespace GlobalTheory.OrbitArchSlope

/- English proof (translation)
Use `haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField`. Set `W : Set (κ → FiniteAdeleRing (𝓞 F) F)` to `Set.univ.pi fun _ => (Formalism.UG.intAd F : Set _)`. Establish `hc : IsCompact W` using `isCompact_univ_pi fun _ => Formalism.MainNotions.Gaps.LevGap.isCompact_intAd`. Establish `ho : IsOpen W` using `isOpen_set_pi Set.finite_univ fun _ _ => Formalism.MainNotions.Gaps.LevGap.isOpen_intAd`. Establish `h0 : (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ W` using `fun i _ => (Formalism.UG.intAd F).zero_mem`.

Use `⟨W.indicator 1, GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB hc ⟨hc.isClosed, ho⟩, 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem h0]`. Conclude with `one_ne_zero`.
-/
theorem exists_sb_ne_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ y, g y ≠ 0 := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  let W : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => (Formalism.UG.intAd F : Set _)
  have hc : IsCompact W := isCompact_univ_pi fun _ => Formalism.MainNotions.Gaps.LevGap.isCompact_intAd
  have ho : IsOpen W := isOpen_set_pi Set.finite_univ fun _ _ => Formalism.MainNotions.Gaps.LevGap.isOpen_intAd
  have h0 : (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ W := fun i _ => (Formalism.UG.intAd F).zero_mem
  refine ⟨W.indicator 1, GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB hc ⟨hc.isClosed, ho⟩, 0, ?_⟩
  rw [Set.indicator_of_mem h0]
  exact one_ne_zero

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ f u hu`. Take `⟨c, c', hc0, hlim, hacts⟩` from `GlobalTheory.WeilArchSmooth.exists_orbit hK.base G.M' B.ψ X.α (X.α / X.β) om' hM.triple.base.cm hM.triple.base.std hM.triple.weil' γ hγ f`. Take `⟨g, hg, y, hy⟩` from `exists_sb_ne_zero F (Fin a' × Fin (a + a'))`. Set `r : (Fin a' × Fin (a + a') → AF F) → ℂ` to `fun x => g (fun i => (x i).2)`. Establish `hpure : ∀ h : SInf F (Fin a' × Fin (a + a')), pureA F (⇑h) g = tens (evI F) (⇑h) r` using `fun h => rfl`.

Establish `hRest : Rest (evI F) (⇑f) r`. Use `⟨fun x z hz => ?_, ?_⟩` and prove the remaining obligations. Set `e : AF F` to `(show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))`. Establish `he : evI F e = 0` using `by show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0`. Conclude with `map_zero _`.

Establish `hz2 : ∀ i, (z i).2 = 0`. Introduce `i`. Establish `h1` using `congrFun (hz e he) i`. Establish `h2 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0` using `congrArg Prod.snd h1`. Simplify using `using h2`.

Use `show g (fun i => (x i + z i).2) = g (fun i => (x i).2)`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `show (x i).2 + (z i).2 = (x i).2`. Rewrite using `[hz2 i, add_zero]`.

Rewrite using `[← hpure]`. Conclude with `Submodule.subset_span ⟨f, g, hg, rfl⟩`. Establish `heq : ∀ t, u t = c t`. Introduce `t`. Establish `h1 : pureA F (⇑(u t)) g = pureA F (⇑(c t)) g`.

Rewrite using `[← hu t g hg, hpure, hpure]`. Conclude with `hacts t r hRest`. Use `DFunLike.ext _ _ fun x => ?_` and prove the remaining obligations. Establish `e` using `congrFun h1 (fun i => (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)))`. Simplify using `only [pureA] at e`.

Establish `hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i))) = x`. Use function extensionality and compare the values at `fun i => RingEquiv.apply_symm_apply _ _`. Rewrite `e` using `[hx]`. Conclude with `mul_right_cancel₀ hy e`. Establish `hc : u = c` using `funext heq`.

Substitute `hc` using the available equality. Use `⟨c', ?_⟩` and prove the remaining obligations. Rewrite using `[hc0]`. Conclude with `hlim`.
-/
theorem orbit_slope_tendsto : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ γ ∈ Lines σ G.W, ∀ (f : SInf F (Fin a' × Fin (a + a'))) (u : ℝ → SInf F (Fin a' × Fin (a + a'))), (∀ t : ℝ, ∀ g ∈ SB (Fin a' × Fin (a + a') → Af F), om' (1, γ (Multiplicative.ofAdd t)) (pureA F f g) = pureA F (u t) g) → ∃ u₁ : SInf F (Fin a' × Fin (a + a')), Tendsto (fun t : ℝ => t⁻¹ • (u t - u 0)) (𝓝[≠] 0) (𝓝 u₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ f u hu
  obtain ⟨c, c', hc0, hlim, hacts⟩ := GlobalTheory.WeilArchSmooth.exists_orbit hK.base G.M' B.ψ X.α (X.α / X.β) om'
    hM.triple.base.cm hM.triple.base.std hM.triple.weil' γ hγ f
  obtain ⟨g, hg, y, hy⟩ := exists_sb_ne_zero F (Fin a' × Fin (a + a'))
  let r : (Fin a' × Fin (a + a') → AF F) → ℂ := fun x => g (fun i => (x i).2)
  have hpure : ∀ h : SInf F (Fin a' × Fin (a + a')), pureA F (⇑h) g = tens (evI F) (⇑h) r := fun h => rfl
  have hRest : Rest (evI F) (⇑f) r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · let e : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
      have he : evI F e = 0 := by
        show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
        exact map_zero _
      have hz2 : ∀ i, (z i).2 = 0 := by
        intro i
        have h1 := congrFun (hz e he) i
        have h2 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd h1
        simpa using h2
      show g (fun i => (x i + z i).2) = g (fun i => (x i).2)
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [hz2 i, add_zero]
    · rw [← hpure]
      exact Submodule.subset_span ⟨f, g, hg, rfl⟩
  have heq : ∀ t, u t = c t := by
    intro t
    have h1 : pureA F (⇑(u t)) g = pureA F (⇑(c t)) g := by
      rw [← hu t g hg, hpure, hpure]
      exact hacts t r hRest
    refine DFunLike.ext _ _ fun x => ?_
    have e := congrFun h1 (fun i => (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)))
    simp only [pureA] at e
    have hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i))) = x :=
      funext fun i => RingEquiv.apply_symm_apply _ _
    rw [hx] at e
    exact mul_right_cancel₀ hy e
  have hc : u = c := funext heq
  subst hc
  refine ⟨c', ?_⟩
  rw [hc0]
  exact hlim

end GlobalTheory.OrbitArchSlope
