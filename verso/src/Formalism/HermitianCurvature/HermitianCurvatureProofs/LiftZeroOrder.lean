import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.TLB
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs κ i j c Pol E a`. Introduce `cf hPol hE hcomm ha`. Take `⟨q, hqdeg, hq⟩` from `id hPol`. Set `fib : Fin 1 → B.Mat P.k P.r → C6.EndH Wp Wq` to `fun _ => E`. Set `t : MinorPolynomials.CT P.k P.r 1` to `⟨q, fun l => if l = Fin.last (P.r + 1) then i else 0, fun l => if l = Fin.last (P.r + 1) then j else 0, c, [((0 : Fin 1), [])]⟩`.

Set `T0 : B.DTerm P.k P.r Wp Wq` to `MinorPolynomials.mkTerm Bs fib (t, [])`. Establish `hcoef : ∀ g, T0.coef g = cf g`. Introduce `g`. Simplify using `only [T0, MinorPolynomials.mkTerm, MinorPolynomials.cv, MinorPolynomials.cvs, C6.Epart, C6.monoM, t, fib, cf]`. Rewrite using `[Finset.prod_eq_single (Fin.last (P.r + 1)) (fun l _ hl => by simp [hl]) (fun h => absurd (Finset.mem_univ _) h)]`.

Simplify using `only [↓reduceIte, pow_zero, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]`. Rewrite using `[hq g]`. Simplify using `only [PI.UnitaryGroupMassFormula.UsCompose.vars]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hfib : ∀ j : Fin 1, C6.FibBound Bs (fib j)` using `fun _ => hE`. Establish `hgood : MinorPolynomials.Good (∅ : Finset (Fin (P.r + 2))) (t, ([] : List (B.Mat P.k P.r)))`. Use `⟨fun l hl => ?_, by simp [t], by simp⟩` and prove the remaining obligations. Use `right`. Assume the negation of the conclusion as `h`.

Simplify using `[t, h] at hl`. Establish `hadj : ∀ {S : Set (B.Mat P.k P.r)} {f : B.Mat P.k P.r → C6.EndH Wp Wq}, B.CkOn ⊤ S f → B.CkOn ⊤ S (fun x => HilbertSchmidtVectorization.adjH (f x))`. Introduce `S f hf g0 hg0`. Take `⟨U, f', hU, hgU, hf', heq⟩` from `hf g0 hg0`. Use `⟨U, fun x => HilbertSchmidtVectorization.adjR (f' x), hU, hgU, (HilbertSchmidtVectorization.adjR (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn hf', ?_⟩` and prove the remaining obligations.

Introduce `g hg hgv`. Use `show HilbertSchmidtVectorization.adjH (f g) = HilbertSchmidtVectorization.adjH (f' g)`. Rewrite using `[heq g hg hgv]`. Establish `hsmooth : B.SmoothCoef (C6.domL Bs ∅) [T0]`. Introduce `T hT`.

Rewrite `hT` using `[List.mem_singleton]`. Substitute `hT` using the available equality. Conclude with `⟨MinorPolynomials.ckOn_cv Bs fib (fun j => (hfib j).1) hgood, hadj (MinorPolynomials.ckOn_cv Bs fib (fun j => (hfib j).1) hgood)⟩`. Establish `hop : ∀ (F : B.Mat P.k P.r → Wq →L[ℂ] Wp) g, B.opApply [T0] F g = cf g (F g)`. Introduce `F g`.

Simplify using `only [B.opApply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]`. Rewrite using `[hcoef]`. Simplify using `[T0, MinorPolynomials.mkTerm, B.Rw]`. Establish `hord : B.opOrder [T0] = 0`. Simplify using `[B.opOrder, T0, MinorPolynomials.mkTerm]`.

Establish `hcomD : B.Commutes Bs (C6.domL Bs ∅) [T0]`. Introduce `p hp f _ g hg`. Rewrite using `[hop]`. Simplify using `only [B.rho]`. Rewrite using `[hop]`.

Conclude with `hcomm p hp g hg (f (B.sgs p g))`. Establish `hDD : C6.InDDPlus Bs fib ∅ 0 κ [T0]`. Use `⟨hsmooth, hcomD, fun T hT => ?_⟩` and prove the remaining obligations. Rewrite `hT` using `[List.mem_singleton]`. Substitute `hT` using the available equality.

Use `⟨Pol, t.a, t.b, c, [((0 : Fin 1), [])], hPol, fun l _ hl => by simp [t, hl], ?_, by simp, ?_⟩` and prove the remaining obligations. Simplify using `[T0, MinorPolynomials.mkTerm]`. Introduce `g _`. Simplify using `only [T0, MinorPolynomials.mkTerm, MinorPolynomials.cv, MinorPolynomials.cvs, t]`. Rewrite using `[hq g]`.

Both sides reduce to the same expression. Use `⟨1, fib, [T0], hfib, hDD, ?_⟩` and prove the remaining obligations. Introduce `F hF Φ hΦ x hx`. Rewrite using `[ha Φ x hx, hΦ x hx]`. Take `⟨ε, _, hnice⟩` from `TLB.nice_of_cpt hF`.

Establish `hcomO : B.Commutes Bs (JF.Om P.k P.r Bs.z Bs.z') [T0]`. Introduce `p hp f hf g hg`. Conclude with `hcomD p hp f hf g ⟨hg.1, hg.2.2, by simp⟩`. Establish `hJ` using `orbital_commutes_on_open_set P.k P.r Wp Wq Bs (12 * ((P.r : ℝ) + 1) ^ 2 * (((0 : ℕ) : ℝ) + (P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1)) 0 F [T0] (JF.Om P.k P.r Bs.z Bs.z') subset_rfl hord.le (OrbitalIntegralIdentities.thrW_of P.k P.r 0 _ le_rfl) (hnice.2.1 _ 0) hcomO _ (TLB.wC …`. Rewrite `hJ` using `[hop]`.

Simplify using `only [Q.resG, map_smul]`. Rewrite using `[hJ]`.
-/
theorem lift_zero_order : TL.LiftZero := by
  intro Wp Wq _ _ _ _ _ _ P Bs κ i j c Pol E a
  intro cf hPol hE hcomm ha
  obtain ⟨q, hqdeg, hq⟩ := id hPol
  let fib : Fin 1 → B.Mat P.k P.r → C6.EndH Wp Wq := fun _ => E
  let t : MinorPolynomials.CT P.k P.r 1 :=
    ⟨q, fun l => if l = Fin.last (P.r + 1) then i else 0,
      fun l => if l = Fin.last (P.r + 1) then j else 0, c, [((0 : Fin 1), [])]⟩
  let T0 : B.DTerm P.k P.r Wp Wq := MinorPolynomials.mkTerm Bs fib (t, [])
  have hcoef : ∀ g, T0.coef g = cf g := by
    intro g
    simp only [T0, MinorPolynomials.mkTerm, MinorPolynomials.cv, MinorPolynomials.cvs, C6.Epart, C6.monoM, t, fib, cf]
    rw [Finset.prod_eq_single (Fin.last (P.r + 1)) (fun l _ hl => by simp [hl])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, pow_zero, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hq g]
    simp only [PI.UnitaryGroupMassFormula.UsCompose.vars]
    congr 1
    ring

  have hfib : ∀ j : Fin 1, C6.FibBound Bs (fib j) := fun _ => hE
  have hgood : MinorPolynomials.Good (∅ : Finset (Fin (P.r + 2))) (t, ([] : List (B.Mat P.k P.r))) := by
    refine ⟨fun l hl => ?_, by simp [t], by simp⟩
    right
    by_contra h
    simp [t, h] at hl
  have hadj : ∀ {S : Set (B.Mat P.k P.r)} {f : B.Mat P.k P.r → C6.EndH Wp Wq},
      B.CkOn ⊤ S f → B.CkOn ⊤ S (fun x => HilbertSchmidtVectorization.adjH (f x)) := by
    intro S f hf g0 hg0
    obtain ⟨U, f', hU, hgU, hf', heq⟩ := hf g0 hg0
    refine ⟨U, fun x => HilbertSchmidtVectorization.adjR (f' x), hU, hgU, (HilbertSchmidtVectorization.adjR (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn hf', ?_⟩
    intro g hg hgv
    show HilbertSchmidtVectorization.adjH (f g) = HilbertSchmidtVectorization.adjH (f' g)
    rw [heq g hg hgv]
  have hsmooth : B.SmoothCoef (C6.domL Bs ∅) [T0] := by
    intro T hT
    rw [List.mem_singleton] at hT
    subst hT
    exact ⟨MinorPolynomials.ckOn_cv Bs fib (fun j => (hfib j).1) hgood,
      hadj (MinorPolynomials.ckOn_cv Bs fib (fun j => (hfib j).1) hgood)⟩
  have hop : ∀ (F : B.Mat P.k P.r → Wq →L[ℂ] Wp) g, B.opApply [T0] F g = cf g (F g) := by
    intro F g
    simp only [B.opApply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hcoef]
    simp [T0, MinorPolynomials.mkTerm, B.Rw]
  have hord : B.opOrder [T0] = 0 := by
    simp [B.opOrder, T0, MinorPolynomials.mkTerm]
  have hcomD : B.Commutes Bs (C6.domL Bs ∅) [T0] := by
    intro p hp f _ g hg
    rw [hop]
    simp only [B.rho]
    rw [hop]
    exact hcomm p hp g hg (f (B.sgs p g))
  have hDD : C6.InDDPlus Bs fib ∅ 0 κ [T0] := by
    refine ⟨hsmooth, hcomD, fun T hT => ?_⟩
    rw [List.mem_singleton] at hT
    subst hT
    refine ⟨Pol, t.a, t.b, c, [((0 : Fin 1), [])], hPol, fun l _ hl => by simp [t, hl], ?_, by simp, ?_⟩
    · simp [T0, MinorPolynomials.mkTerm]
    · intro g _
      simp only [T0, MinorPolynomials.mkTerm, MinorPolynomials.cv, MinorPolynomials.cvs, t]
      rw [hq g]
      rfl
  refine ⟨1, fib, [T0], hfib, hDD, ?_⟩
  intro F hF Φ hΦ x hx
  rw [ha Φ x hx, hΦ x hx]
  obtain ⟨ε, _, hnice⟩ := TLB.nice_of_cpt hF
  have hcomO : B.Commutes Bs (JF.Om P.k P.r Bs.z Bs.z') [T0] := by
    intro p hp f hf g hg
    exact hcomD p hp f hf g ⟨hg.1, hg.2.2, by simp⟩
  have hJ := orbital_commutes_on_open_set P.k P.r Wp Wq Bs
    (12 * ((P.r : ℝ) + 1) ^ 2 * (((0 : ℕ) : ℝ) + (P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1)) 0 F [T0]
    (JF.Om P.k P.r Bs.z Bs.z') subset_rfl hord.le (OrbitalIntegralIdentities.thrW_of P.k P.r 0 _ le_rfl) (hnice.2.1 _ 0) hcomO
    _ (TLB.wCell_om Bs hx)
  rw [hop] at hJ
  simp only [Q.resG, map_smul]
  rw [hJ]

end

end Formalism.FourierDecayAlt.P
