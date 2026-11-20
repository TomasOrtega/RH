import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Establish `h : ∀ x : Af E, ∀ᶠ w in Filter.cofinite, pLoc E w x ∈ Formalism.UG.Ov E w` using `fun x => x.2`. Establish `h1 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w (k.val i j) ∈ Formalism.UG.Ov E w`. Simplify using `only [Filter.eventually_all]`. Conclude with `fun i j => h _`. Establish `h2 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w ((k⁻¹).val i j) ∈ Formalism.UG.Ov E w`.

Simplify using `only [Filter.eventually_all]`. Conclude with `fun i j => h _`. Establish `h3 : ∀ᶠ w in Filter.cofinite, cmp w k ∈ GlobalTheory.LFun.KGL w n` using `by filter_upwards [h1, h2] with w a b`. Rewrite using `[GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv]`. Conclude with `⟨a, b⟩`.

Conclude with `h3`.
-/
private theorem fin_bad {E : Type} [Field E] [NumberField E] {n : ℕ} (k : GL (Fin n) (Af E)) :
    {w | cmp w k ∉ GlobalTheory.LFun.KGL w n}.Finite := by
  have h : ∀ x : Af E, ∀ᶠ w in Filter.cofinite, pLoc E w x ∈ Formalism.UG.Ov E w := fun x => x.2
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w (k.val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w ((k⁻¹).val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h3 : ∀ᶠ w in Filter.cofinite, cmp w k ∈ GlobalTheory.LFun.KGL w n := by
    filter_upwards [h1, h2] with w a b
    rw [GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv]
    exact ⟨a, b⟩
  exact h3

/- English proof (translation)
Introduce `E _ _ n S P h0 h1`. It suffices to establish `H : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k, Away S k → (∀ w ∉ T, cmp w k ∈ GlobalTheory.LFun.KGL w n) → P k by`. Introduce `k hk`. Use `H (fin_bad k).toFinset k hk fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hw ((Set.Finite.mem_toFinset _).2 h)`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact fun k hk h => h0 k ⟨hk, fun w => h w (Finset.notMem_empty w)⟩`. Consider the case `insert w T hw ih`.

Introduce `k hk h`. Distinguish the cases in `hS : w ∈ S`. Use `ih k hk fun v hv => ?_` and prove the remaining obligations. Distinguish the cases in `e : v = w`. Substitute `e` using the available equality.

Rewrite using `[hk v hS]`. Conclude with `one_mem _`. Conclude with `h v (by simp [e, hv])`. Establish `e1 : cmp w (k * (locGL E n w (cmp w k))⁻¹) = 1`. Rewrite using `[map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL, mul_inv_cancel]`.

Establish `e2 : ∀ v, v ≠ w → cmp v (k * (locGL E n w (cmp w k))⁻¹) = cmp v k` using `fun v e => by`. Rewrite using `[map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL_of_ne e, inv_one, mul_one]`. Establish `a : Away S (k * (locGL E n w (cmp w k))⁻¹)` using `fun v hv => by`. Rewrite using `[e2 v (fun e => hS (e ▸ hv)), hk v hv]`. Establish `p` using `ih _ a fun v hv => by`.

Distinguish the cases in `e : v = w`. Substitute `e` using the available equality. Rewrite using `[e1]`. Conclude with `one_mem _`. Rewrite using `[e2 v e]; exact h v (by simp [e, hv])`.

Establish `q` using `h1 w hS _ a e1 p (cmp w k)`. Rewrite `q` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Af.Smo.awayInd :
    UpperTheory.V.Af.Smo.AwayInd := by
  intro E _ _ n S P h0 h1
  classical
  suffices H : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k, Away S k → (∀ w ∉ T, cmp w k ∈ GlobalTheory.LFun.KGL w n) → P k by
    intro k hk
    refine H (fin_bad k).toFinset k hk fun w hw => ?_
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).2 h)
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun k hk h => h0 k ⟨hk, fun w => h w (Finset.notMem_empty w)⟩
  | insert w T hw ih =>
    intro k hk h
    by_cases hS : w ∈ S
    · refine ih k hk fun v hv => ?_
      by_cases e : v = w
      · subst e; rw [hk v hS]; exact one_mem _
      · exact h v (by simp [e, hv])
    · have e1 : cmp w (k * (locGL E n w (cmp w k))⁻¹) = 1 := by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL, mul_inv_cancel]
      have e2 : ∀ v, v ≠ w → cmp v (k * (locGL E n w (cmp w k))⁻¹) = cmp v k := fun v e => by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL_of_ne e, inv_one, mul_one]
      have a : Away S (k * (locGL E n w (cmp w k))⁻¹) := fun v hv => by
        rw [e2 v (fun e => hS (e ▸ hv)), hk v hv]
      have p := ih _ a fun v hv => by
        by_cases e : v = w
        · subst e; rw [e1]; exact one_mem _
        · rw [e2 v e]; exact h v (by simp [e, hv])
      have q := h1 w hS _ a e1 p (cmp w k)
      rwa [inv_mul_cancel_right] at q
