import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Use `show Multiset.bind S (fun a => {(a : ℂ)}) = _`. Conclude with `Multiset.bind_singleton _ _`.
-/
private theorem multiset_bind_pure_coe_eq_map (S : Multiset ℂˣ) :
    (do let a ← S; Pure.pure (a : ℂ) : Multiset ℂ) = Multiset.map (fun a : ℂˣ => (a : ℂ)) S := by
  show Multiset.bind S (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton _ _

/- English proof (translation)
Rewrite using `[Fin.univ_val_map, List.ofFn_eq_map]`. Establish `h : List.map (fun i : Fin t => f i) (List.finRange t) = List.map f (List.range t)`. Rewrite using `[← List.map_coe_finRange_eq_range, List.map_map]`. Both sides reduce to the same expression. Rewrite using `[h, ← Multiset.map_coe]`.

Both sides reduce to the same expression.
-/
private theorem multiset_map_fin_eq_map_range (t : ℕ) (f : ℕ → ℂ) :
    Multiset.map (fun i : Fin t => f i) Finset.univ.val = Multiset.map f (Finset.range t).val := by
  rw [Fin.univ_val_map, List.ofFn_eq_map]
  have h : List.map (fun i : Fin t => f i) (List.finRange t) = List.map f (List.range t) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [h, ← Multiset.map_coe]
  rfl

/- English proof (translation)
Introduce `E _ _ w n t B x y k c hk hc`. Establish `hq0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `w.ne_bot`. Establish `hs : ∀ m : ℕ, (((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ)) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((m : ℂ) - 1) / 2)`.

Introduce `m`. Rewrite using `[Complex.ofReal_cpow (by positivity)]`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [algSat, GlobalTheory.LFun.seg, hs]`.

Rewrite using `[multiset_bind_pure_coe_eq_map, multiset_bind_pure_coe_eq_map]`. Simplify using `only [Multiset.map_add, Multiset.map_map]`. Establish `hR` using `multiset_map_fin_eq_map_range t (fun j : ℕ => (x : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ)))`. Establish `hc' : c = fun i : Fin t => (fun j : ℕ => (x : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ))) (i : ℕ)` using `funext hc`. Rewrite using `[hc', hR]`.

Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `b _`. Simplify using `only [Function.comp, Units.val_mul, Units.val_inv_eq_inv_val, hk]`. Establish `hsplit : (((n + t : ℕ) : ℂ) - 1) / 2 = ((n : ℂ) - 1) / 2 + (t : ℂ) / 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, Complex.cpow_add _ _ hq0, Complex.cpow_neg, mul_inv, mul_inv, inv_inv, inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Apply `Multiset.map_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Simplify using `only [Function.comp, Units.val_mul, GlobalTheory.LFun.npowU, Units.val_mk0, GlobalTheory.LFun.npow]`. Rewrite using `[mul_left_comm, ← Complex.cpow_add _ _ hq0]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.TP.Sub.satId_holds :
    SatId := by
  intro E _ _ w n t B x y k c hk hc
  have hq0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hs : ∀ m : ℕ, (((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ)) : ℂ) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((m : ℂ) - 1) / 2) := by
    intro m
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  simp only [algSat, GlobalTheory.LFun.seg, hs]
  rw [multiset_bind_pure_coe_eq_map, multiset_bind_pure_coe_eq_map]
  simp only [Multiset.map_add, Multiset.map_map]
  have hR := multiset_map_fin_eq_map_range t (fun j : ℕ => (x : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ)))
  have hc' : c = fun i : Fin t => (fun j : ℕ => (x : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ))) (i : ℕ) := funext hc
  rw [hc', hR]
  congr 1
  · apply Multiset.map_congr rfl
    intro b _
    simp only [Function.comp, Units.val_mul, Units.val_inv_eq_inv_val, hk]
    have hsplit : (((n + t : ℕ) : ℂ) - 1) / 2 = ((n : ℂ) - 1) / 2 + (t : ℂ) / 2 := by
      push_cast
      ring
    rw [hsplit, Complex.cpow_add _ _ hq0, Complex.cpow_neg, mul_inv, mul_inv, inv_inv, inv_inv]
    ring
  · apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp, Units.val_mul, GlobalTheory.LFun.npowU, Units.val_mk0, GlobalTheory.LFun.npow]
    rw [mul_left_comm, ← Complex.cpow_add _ _ hq0]
    congr 2
    push_cast
    ring
