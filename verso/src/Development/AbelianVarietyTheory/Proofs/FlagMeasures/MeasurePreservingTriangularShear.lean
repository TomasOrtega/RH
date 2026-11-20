import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

/- English proof (translation)
Use `set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p with he`. Establish `he_mp : MeasurePreserving e volume volume` using `volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p`. Set `G : (Subtype p → ℝ) → ({i // ¬ p i} → ℝ)` to `fun a i => f (e.symm (a, 0)) i`. Establish `hG : Measurable G`. Use `measurable_pi_lambda _ (fun i => ?_)` and prove the remaining obligations.

Conclude with `(measurable_pi_apply (i : Fin d)).comp (hf.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))`. Establish `hΨ : MeasurePreserving (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1)) (volume.prod volume) (volume.prod volume)` using `MeasurePreserving.skew_product (f := id) (g := fun a b => b + G a) (MeasurePreserving.id volume) (measurable_snd.add (hG.comp measurable_fst)) (Filter.Eventually.of_forall fun a => (measurePreserving_add_right volume (G a)).map_eq)`. Establish `key : (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i) = e.symm ∘ (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1)) ∘ e`. Use function extensionality and compare the values at `x i`. Establish `hx : ∀ k, p k → x k = e.symm ((e x).1, 0) k` using `fun k hk => by simp [e, hk]`.

Distinguish the cases in `hi : p i`. Simplify using `[e, hi]`. Simplify using `[e, G, hi, h x _ i hi hx]`. Rewrite using `[key]`. Conclude with `(MeasurePreserving.symm e he_mp).comp (hΨ.comp he_mp)`.
-/
theorem measurePreserving_layer_shear (d : ℕ) (p : Fin d → Prop) [DecidablePred p]
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, ¬ p i → (∀ k, p k → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i)
      (volume : Measure (Fin d → ℝ)) volume := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p with he
  have he_mp : MeasurePreserving e volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p

  let G : (Subtype p → ℝ) → ({i // ¬ p i} → ℝ) := fun a i => f (e.symm (a, 0)) i
  have hG : Measurable G := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact (measurable_pi_apply (i : Fin d)).comp
      (hf.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))

  have hΨ : MeasurePreserving
      (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (f := id) (g := fun a b => b + G a)
      (MeasurePreserving.id volume) (measurable_snd.add (hG.comp measurable_fst))
      (Filter.Eventually.of_forall fun a => (measurePreserving_add_right volume (G a)).map_eq)
  have key : (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i) =
      e.symm ∘ (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1)) ∘ e := by
    funext x i
    have hx : ∀ k, p k → x k = e.symm ((e x).1, 0) k := fun k hk => by simp [e, hk]
    by_cases hi : p i
    · simp [e, hi]
    · simp [e, G, hi, h x _ i hi hx]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΨ.comp he_mp)

/- English proof (translation)
Set `U : ℕ → (Fin d → ℝ) → (Fin d → ℝ)` to `fun n x i => if n ≤ deg i then x i + f x i else x i`. Establish `hS : ∀ n, MeasurePreserving (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) volume volume` using `fun n => measurePreserving_layer_shear d (fun i => deg i ≠ n) f hf (fun x y i hi hxy => h x y i (fun k hk => hxy k (by omega)))`. Establish `hstep : ∀ n, U n = (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) ∘ U (n + 1)`. Introduce `n`. Use function extensionality and compare the values at `x i`.

Distinguish the cases in `hin : deg i = n`. Establish `hfx : f (U (n + 1) x) i = f x i` using `h _ _ i (fun k hk => by simp only [U]; rw [if_neg (by omega)])`. Simplify using `only [Function.comp_apply, hfx]`. Simplify using `only [U]`. Rewrite using `[if_pos (by omega), if_neg (by omega), if_neg (by omega)]`.

Simplify using `only [Function.comp_apply, U]`. Rewrite using `[if_pos hin]`. Distinguish the cases in `h2 : n ≤ deg i`. Rewrite using `[if_pos h2, if_pos (by omega)]`. Rewrite using `[if_neg h2, if_neg (by omega)]`.

Establish `hN : ∀ n, Finset.univ.sup deg < n → U n = id`. Introduce `n hn`. Use function extensionality and compare the values at `x i`. Establish `hi : deg i ≤ Finset.univ.sup deg` using `Finset.le_sup (Finset.mem_univ i)`. Simplify using `only [U, id]`.

Rewrite using `[if_neg (by omega)]`. Establish `hU : ∀ k n, Finset.univ.sup deg < n + k → MeasurePreserving (U n) volume volume`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `n hn`. Rewrite using `[hN n (by omega)]`. Conclude with `MeasurePreserving.id _`. Consider the case `succ k ih`. Introduce `n hn`.

Rewrite using `[hstep n]`. Conclude with `(hS n).comp (ih (n + 1) (by omega))`. Establish `h0 : U 0 = fun x => x + f x`. Use function extensionality and compare the values at `x i`. Simplify using `[U]`.

Rewrite using `[← h0]`. Conclude with `hU (Finset.univ.sup deg + 1) 0 (by omega)`.
-/
theorem measurePreserving_triangular_shear (d : ℕ) (deg : Fin d → ℕ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, (∀ k, deg k < deg i → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun x => x + f x) (volume : Measure (Fin d → ℝ)) volume := by

  let U : ℕ → (Fin d → ℝ) → (Fin d → ℝ) := fun n x i => if n ≤ deg i then x i + f x i else x i
  have hS : ∀ n, MeasurePreserving
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) volume volume :=
    fun n => measurePreserving_layer_shear d (fun i => deg i ≠ n) f hf
      (fun x y i hi hxy => h x y i (fun k hk => hxy k (by omega)))
  have hstep : ∀ n, U n =
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) ∘ U (n + 1) := by
    intro n
    funext x i
    by_cases hin : deg i = n
    · have hfx : f (U (n + 1) x) i = f x i :=
        h _ _ i (fun k hk => by simp only [U]; rw [if_neg (by omega)])
      simp only [Function.comp_apply, hfx]
      simp only [U]
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    · simp only [Function.comp_apply, U]
      rw [if_pos hin]
      by_cases h2 : n ≤ deg i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have hN : ∀ n, Finset.univ.sup deg < n → U n = id := by
    intro n hn
    funext x i
    have hi : deg i ≤ Finset.univ.sup deg := Finset.le_sup (Finset.mem_univ i)
    simp only [U, id]
    rw [if_neg (by omega)]
  have hU : ∀ k n, Finset.univ.sup deg < n + k → MeasurePreserving (U n) volume volume := by
    intro k
    induction k with
    | zero =>
      intro n hn
      rw [hN n (by omega)]
      exact MeasurePreserving.id _
    | succ k ih =>
      intro n hn
      rw [hstep n]
      exact (hS n).comp (ih (n + 1) (by omega))
  have h0 : U 0 = fun x => x + f x := by
    funext x i
    simp [U]
  rw [← h0]
  exact hU (Finset.univ.sup deg + 1) 0 (by omega)

end GlobalTheory
