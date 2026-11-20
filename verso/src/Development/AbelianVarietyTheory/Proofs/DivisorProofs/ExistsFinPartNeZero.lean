import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.EvZeroInf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finPart (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ :=
  ∏ᶠ v, φ v fun i => evFin F v (x i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pure_eq_tens (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure f φ = tens (evI F) (⇑f) (finPart φ) := rfl

/- English proof (translation)
Establish `h0 : evI F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 1) = 0` using `by show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0`. Conclude with `map_zero _`. Establish `h` using `congrArg Prod.snd (congrFun (hz _ h0) i)`. Express the relevant statement in the definitionally equal form `(1 : Af F) * (z i).2 = 0 at h`. Rewrite `h` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem snd_eq_zero_of_at (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h0 : evI F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
    exact map_zero _
  have h := congrArg Prod.snd (congrFun (hz _ h0) i)
  change (1 : Af F) * (z i).2 = 0 at h
  rwa [one_mul] at h

/- English proof (translation)
Unfold `finPart`. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `h : evFin F v (z i) = 0` using `by show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0`.

Rewrite using `[snd_eq_zero_of_at z hz i, map_zero]`. Rewrite using `[Pi.add_apply, map_add, h, add_zero]`.
-/
theorem finPart_add (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    finPart φ (x + z) = finPart φ x := by
  unfold finPart
  refine finprod_congr fun v => ?_
  congr 1
  funext i
  have h : evFin F v (z i) = 0 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
    rw [snd_eq_zero_of_at z hz i, map_zero]
  rw [Pi.add_apply, map_add, h, add_zero]

/- English proof (translation)
Establish `hfin` using `Filter.eventually_cofinite.1 hstd`. Use `set S := hfin.toFinset with hS`. Establish `hy : ∀ v, ∃ y, φ v y ≠ 0` using `fun v => by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `h0 v (funext h)`. Use `choose y hy using hy`. Use `⟨fun i => ∑ v ∈ S, singleFin v (y v i), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hev : ∀ w, (fun i => evFin F w (x i)) = if w ∈ S then y w else 0`. Introduce `w`.

Use function extensionality and compare the values at `i`. Use `show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (x i).2 = _`. Rewrite using `[hx i, map_sum]`. Distinguish the cases in `hw : w ∈ S`. Rewrite using `[Finset.sum_eq_single w (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hw h), evalV_singleFin_self, if_pos hw]`.

Rewrite using `[Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (fun h => hw (by rw [h]; exact hv)) _), if_neg hw]`. Both sides reduce to the same expression. Establish `hne : ∀ w, φ w (fun i => evFin F w (x i)) ≠ 0`. Introduce `w`. Distinguish the cases in `hw : w ∈ S`.

Rewrite using `[hev w, if_pos hw]`. Conclude with `hy w`. Rewrite using `[hev w, if_neg hw]`. Establish `hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1`. Assume the negation of the conclusion as `h`.

Conclude with `hw (by rw [hS, Set.Finite.mem_toFinset]; exact h)`. Rewrite using `[hw', Set.indicator_of_mem (show (0 : κ → Fv F w) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from fun i => zero_mem _)]`. Conclude with `one_ne_zero`. Unfold `finPart`. Rewrite using `[finprod_def]`.

Use `split_ifs`. Conclude with `Finset.prod_ne_zero_iff.2 fun w _ => hne w`. Conclude with `one_ne_zero`.
-/
theorem exists_finPart_ne_zero (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ x₀ : κ → Af F, ∀ x : κ → AF F, (∀ i, (x i).2 = x₀ i) → finPart φ x ≠ 0 := by
  classical
  have hfin := Filter.eventually_cofinite.1 hstd
  set S := hfin.toFinset with hS
  have hy : ∀ v, ∃ y, φ v y ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact h0 v (funext h)
  choose y hy using hy
  refine ⟨fun i => ∑ v ∈ S, singleFin v (y v i), fun x hx => ?_⟩
  have hev : ∀ w, (fun i => evFin F w (x i)) = if w ∈ S then y w else 0 := by
    intro w
    funext i
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (x i).2 = _
    rw [hx i, map_sum]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hw h),
        evalV_singleFin_self, if_pos hw]
    · rw [Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (fun h => hw (by rw [h]; exact hv)) _), if_neg hw]
      rfl
  have hne : ∀ w, φ w (fun i => evFin F w (x i)) ≠ 0 := by
    intro w
    by_cases hw : w ∈ S
    · rw [hev w, if_pos hw]; exact hy w
    · rw [hev w, if_neg hw]
      have hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hw (by rw [hS, Set.Finite.mem_toFinset]; exact h)
      rw [hw', Set.indicator_of_mem (show (0 : κ → Fv F w) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from
        fun i => zero_mem _)]
      exact one_ne_zero
  unfold finPart
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_ne_zero_iff.2 fun w _ => hne w
  · exact one_ne_zero

/- English proof (translation)
Take `⟨x₀, hx₀⟩` from `exists_finPart_ne_zero φ h0 hstd`. Use `DFunLike.ext g g' fun y => ?_` and prove the remaining obligations. Set `x : κ → AF F` to `fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (x₀ i)`. Establish `hI : (fun i => evI F (x i)) = y`. Use function extensionality and compare the values at `fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)`.

Establish `e` using `congrFun h x`. Express the relevant statement in the definitionally equal form `g (fun i => evI F (x i)) * finPart φ x = g' (fun i => evI F (x i)) * finPart φ x at e`. Rewrite `e` using `[hI]`. Conclude with `mul_right_cancel₀ (hx₀ x fun i => rfl) e`.
-/
theorem eq_of_pure_eq (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (g g' : SInf F κ) (h : pure g φ = pure g' φ) : g = g' := by
  obtain ⟨x₀, hx₀⟩ := exists_finPart_ne_zero φ h0 hstd
  refine DFunLike.ext g g' fun y => ?_
  let x : κ → AF F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (x₀ i)
  have hI : (fun i => evI F (x i)) = y :=
    funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)
  have e := congrFun h x
  change g (fun i => evI F (x i)) * finPart φ x = g' (fun i => evI F (x i)) * finPart φ x at e
  rw [hI] at e
  exact mul_right_cancel₀ (hx₀ x fun i => rfl) e

end GlobalTheory.EvZeroInf
