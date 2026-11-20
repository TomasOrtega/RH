import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

/- English proof (translation)
Substitute `h` using the available equality. Establish `hp : ((pos.symm (posJ X D pos i ⟨v, s⟩)).2 : ℕ) = s.val`. Apply the tactic sequence `cases i <;> exact congrArg (fun x => (x.2 : ℕ)) (pos.symm_apply_apply _)`. Establish `ho : IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 ↔ ¬ Even s.val`. Unfold `IsOddPos`.

Rewrite using `[hp, Nat.not_even_iff_odd, Nat.odd_iff]`. Unfold `zAt zT reM`. Distinguish the cases in `hs : Even s.val`. Establish `: ¬ IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2` using `fun h' => (ho.1 h') hs`. Simplify using `[hs, this]`.

Establish `: IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2` using `ho.2 hs`. Simplify using `[hs, this]`.
-/
theorem zAt_eq_zT {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ)
    {n : ℕ} (h : (X.Pj i).m + 1 = n) (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (v : Fin (X.Pj i).nV) (s : Fin ((X.Pj i).n' v)) :
    zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f v s =
      (zT X D pos f (posJ X D pos i ⟨v, s⟩)).submatrix (finCongr h) (finCongr h) := by
  subst h
  have hp : ((pos.symm (posJ X D pos i ⟨v, s⟩)).2 : ℕ) = s.val := by
    cases i <;> exact congrArg (fun x => (x.2 : ℕ)) (pos.symm_apply_apply _)
  have ho : IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 ↔ ¬ Even s.val := by
    unfold IsOddPos; rw [hp, Nat.not_even_iff_odd, Nat.odd_iff]
  unfold zAt zT reM
  by_cases hs : Even s.val
  · have : ¬ IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 := fun h' => (ho.1 h') hs
    simp [hs, this]
  · have : IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 := ho.2 hs
    simp [hs, this]

/- English proof (translation)
Introduce `p _ X D pos i n h R f`. Use `show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f.1 v s).det ^ (eAt (X.Pj i) v s)) * MvPolynomial.eval (fun x : Var (X.Pj i) => zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f.1 x.1 x.2.1 x.2.2.1 x.2.2.2) R = _`. Use `congr 1`. Repeatedly rewrite using `[zAt_eq_zT, Matrix.det_submatrix_equiv_self]`. Rewrite using `[← Equiv.prod_comp (posJ X D pos i), Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Unfold `eT`. Rewrite using `[Equiv.symm_apply_apply]`. Unfold `valZ`. Use `congr 2`.

Use function extensionality and compare the values at `x`. Rewrite using `[zAt_eq_zT]`. Both sides reduce to the same expression.
-/
theorem ev1_eq_prod_det_pow_mul_valZ : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : Fr1 D n), ev1 X D pos i h R f = (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R f.1 := by
  intro p _ X D pos i n h R f
  show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f.1 v s).det ^ (eAt (X.Pj i) v s)) *
      MvPolynomial.eval (fun x : Var (X.Pj i) => zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f.1 x.1 x.2.1 x.2.2.1 x.2.2.2) R = _
  congr 1
  · simp_rw [zAt_eq_zT, Matrix.det_submatrix_equiv_self]
    rw [← Equiv.prod_comp (posJ X D pos i), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    unfold eT
    rw [Equiv.symm_apply_apply]
  · unfold valZ
    congr 2
    funext x
    rw [zAt_eq_zT]
    rfl

end GlobalTheory.TwV.DelA
end
