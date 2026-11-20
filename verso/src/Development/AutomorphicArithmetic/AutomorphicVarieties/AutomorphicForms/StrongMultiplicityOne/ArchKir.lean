import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toL (a * (b * Matrix.of x)) = toL (a * b * Matrix.of x)`. Rewrite using `[Matrix.mul_assoc]`.
-/
private theorem lmul_lmul {E : Type} [Field E] [NumberField E] {n : ℕ} (a b : Matrix (Fin n) (Fin n) (Cinf E))
    (x : Lie E n) : lmul (toL a) (lmul (toL b) x) = lmul (toL (a * b)) x := by
  change toL (a * (b * Matrix.of x)) = toL (a * b * Matrix.of x)
  rw [Matrix.mul_assoc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [rowM, Matrix.of_apply]`. Use `split_ifs with h`. Rewrite using `[h.1]`. Both sides reduce to the same expression.
-/
private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

/- English proof (translation)
Introduce `hC hR hA hL E _ _ n m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `_`. Use `⟨fun p => psiR E (supN p.val), ?_, fun α => ⟨α, fun w _ _ hw p hp => ?_⟩⟩` and prove the remaining obligations.

Establish `: supN (1 : GL (Fin n) (Cinf E)).val = 0`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `Matrix.one_apply_ne (fun e => by subst e; omega)`. Both sides reduce to the same expression.

Simplify using `only [this]`. Simplify using `[psiR]`. Simplify using `only [hw p hp, mul_assoc]`. Conclude with `integral_const_mul _ _`. Consider the case `succ m ih`.

Introduce `hm`. Take `⟨H, H1, hH⟩` from `ih (by omega)`. Set `m' : Fin n` to `⟨m, by omega⟩`. Take `⟨h, h1, hu, hh⟩` from `hA E n m' hm`. Take `⟨c, c1, hc⟩` from `hL E n`.

Use `⟨fun p => if hs : IsUnit (rowM m' (p.val m')) then h (p.val m') * (c hs.unit * H (p * hs.unit⁻¹)) else 0, ?_, fun α => ?_⟩` and prove the remaining obligations. Establish `hs : IsUnit (rowM m' ((1 : GL (Fin n) (Cinf E)).val m'))`. Rewrite using `[Units.val_one, rowM_one]`. Conclude with `isUnit_one`. Establish `e : hs.unit = 1` using `Units.ext (by rw [hs.unit_spec, Units.val_one, rowM_one])`.

Simplify using `only [dif_pos hs, e]`. Simplify using `[h1, c1, H1]`. Take `⟨β₀, hβ₀⟩` from `hH α`. Take `⟨β, hβ⟩` from `hh β₀`. Use `⟨β, fun w wm wb hw p hp => ?_⟩` and prove the remaining obligations.

Take `⟨C, hCb⟩` from `wb`. Establish `key` using `hβ (fun x => w (lmul (toL p.val) x)) (p.val m') (wm.comp (lmul (toL p.val)).continuous.measurable) ⟨C, fun x => hCb _⟩ (fun u x => by`. Take `⟨ν, hν, hs, e⟩` from `hC (Cinf E) n m' hm p hp u`. Simplify using `only [lmul_lmul]`. Rewrite using `[e, ← lmul_lmul, hw ν hν, hs])`.

Rewrite using `[key]`. Distinguish the cases in `h0 : h (p.val m') = 0`. Simplify using `[h0]`. Establish `hs` using `hu _ h0`. Simplify using `only [dif_pos hs]`.

Establish `hy` using `hR (Cinf E) n m' p hs.unit hp hs.unit_spec`. Establish `e1` using `hβ₀ w wm ⟨C, hCb⟩ hw _ hy`. Establish `e2` using `hc hs.unit (fun y => w (lmul (toL (p * hs.unit⁻¹).val) y) * β₀ y)`. Establish `e3 : (p * hs.unit⁻¹).val * hs.unit.val = p.val`. Rewrite using `[← Units.val_mul, inv_mul_cancel_right]`.

Simplify using `only [lmul_lmul, e3] at e2`. Rewrite `e2` using `[hs.unit_spec]`. Rewrite using `[e2, e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Af.StrongMultiplicityOne.archKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.StrongMultiplicityOne.ArchStep → UpperTheory.V.Af.StrongMultiplicityOne.LinChange → UpperTheory.V.Af.StrongMultiplicityOne.ArchKir := by
  classical
  intro hC hR hA hL E _ _ n m
  induction m with
  | zero =>
    intro _
    refine ⟨fun p => psiR E (supN p.val), ?_, fun α => ⟨α, fun w _ _ hw p hp => ?_⟩⟩
    · have : supN (1 : GL (Fin n) (Cinf E)).val = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with h
        · exact Matrix.one_apply_ne (fun e => by subst e; omega)
        · rfl
      simp only [this]
      simp [psiR]
    · simp only [hw p hp, mul_assoc]
      exact integral_const_mul _ _
  | succ m ih =>
    intro hm
    obtain ⟨H, H1, hH⟩ := ih (by omega)
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨h, h1, hu, hh⟩ := hA E n m' hm
    obtain ⟨c, c1, hc⟩ := hL E n
    refine ⟨fun p => if hs : IsUnit (rowM m' (p.val m')) then h (p.val m') * (c hs.unit * H (p * hs.unit⁻¹)) else 0, ?_,
      fun α => ?_⟩
    · have hs : IsUnit (rowM m' ((1 : GL (Fin n) (Cinf E)).val m')) := by
        rw [Units.val_one, rowM_one]; exact isUnit_one
      have e : hs.unit = 1 := Units.ext (by rw [hs.unit_spec, Units.val_one, rowM_one])
      simp only [dif_pos hs, e]
      simp [h1, c1, H1]
    · obtain ⟨β₀, hβ₀⟩ := hH α
      obtain ⟨β, hβ⟩ := hh β₀
      refine ⟨β, fun w wm wb hw p hp => ?_⟩
      obtain ⟨C, hCb⟩ := wb
      have key := hβ (fun x => w (lmul (toL p.val) x)) (p.val m')
        (wm.comp (lmul (toL p.val)).continuous.measurable) ⟨C, fun x => hCb _⟩ (fun u x => by
          obtain ⟨ν, hν, hs, e⟩ := hC (Cinf E) n m' hm p hp u
          simp only [lmul_lmul]
          rw [e, ← lmul_lmul, hw ν hν, hs])
      rw [key]
      by_cases h0 : h (p.val m') = 0
      · simp [h0]
      have hs := hu _ h0
      simp only [dif_pos hs]
      have hy := hR (Cinf E) n m' p hs.unit hp hs.unit_spec
      have e1 := hβ₀ w wm ⟨C, hCb⟩ hw _ hy
      have e2 := hc hs.unit (fun y => w (lmul (toL (p * hs.unit⁻¹).val) y) * β₀ y)
      have e3 : (p * hs.unit⁻¹).val * hs.unit.val = p.val := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      simp only [lmul_lmul, e3] at e2
      rw [hs.unit_spec] at e2
      rw [e2, e1]
      ring
