import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

/- English proof (translation)
Introduce `p k _ d e G H c c' f`. Establish `hone` using `(GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.2`. Establish `hcomp : ∀ j n, G.res n (f.app (n + 1) (c'.x (n + 1) j)) = f.app n (c'.x n j)` using `fun j n => by`. Rewrite using `[res_app, c'.res]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `choose φ hφ _ using fun j => hone (fun n => f.app n (c'.x n j)) (hcomp j)`. Use `⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => ?_⟩` and prove the remaining obligations. Take `⟨g, -, hg⟩` from `hone (fun n => f.app n (c'.x n j)) (hcomp j)`. Conclude with `(hg (ψ j) fun n => hψ n j).trans (hg (φ j) fun n => hφ j n).symm`. Introduce `φ hφ`.

Establish `hconst : ∀ j, constantCoeff (φ j) = 0` using `fun j => by`. Establish `h1` using `(GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d (G.A 0) (c.x 0) (c.nil 0) (c.aug 0) (φ j)).1`. Express the relevant statement in the definitionally equal form `Coalgebra.counit (R := k) (c.ev 0 (φ j)) = _ at h1`. Rewrite using `[← h1, hφ 0 j, CoalgHomClass.counit_comp_apply, c'.aug]`. Use `⟨hconst, fun n => ⟨fun g => ?_, fun s => ?_⟩⟩` and prove the remaining obligations.

Establish `hy : ∀ j, IsNilpotent (f.app n (c'.x n j))` using `fun j => (c'.nil n j).map (f.app n)`. Establish `h1` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (G.A n)).1 (Fin d) (c.ev n) (fun t => by`. Express the relevant statement in the definitionally equal form `IsNilpotent (evA k (c.x n) (c.nil n) (X t))`. Rewrite using `[evA_X]`. Conclude with `c.nil n t) φ hconst _ hy (fun j => hφ n j) g`.

Rewrite using `[h1]`. Conclude with `((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (H.A n)).2 (G.A n) (f.app n : H.A n →ₐ[k] G.A n) (c'.x n) (c'.nil n) _ hy (fun _ => rfl) g).symm`. Set `F : H.A n ⊗[k] H.A n →ₐ[k] G.A n ⊗[k] G.A n` to `Algebra.TensorProduct.map (f.app n : H.A n →ₐ[k] G.A n) (f.app n : H.A n →ₐ[k] G.A n)`. Establish `hy : ∀ i, IsNilpotent (F (c'.x₂ n i))` using `fun i => (c'.nil₂ n i).map F`. Establish `hev` using `GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n`.

Establish `ha : ∀ i, constantCoeff ((Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k) i) = 0`. Introduce `i`. Establish `hc` using `hev.2.2.2`. Consider the cases of `i with`. Consider the case `inl j`.

Rewrite using `[Sum.elim_inl, ← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]`. Express the relevant statement in the definitionally equal form `Coalgebra.counit (R := k) (c.ev n (φ j)) = 0`. Rewrite using `[hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]`. Consider the case `inr j`. Rewrite using `[Sum.elim_inr, ← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]`.

Express the relevant statement in the definitionally equal form `Coalgebra.counit (R := k) (c.ev n (φ j)) = 0`. Rewrite using `[hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]`. Establish `h1` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) (fun t => by`. Express the relevant statement in the definitionally equal form `IsNilpotent (evA k (c.x₂ n) (c.nil₂ n) (X t))`. Rewrite using `[evA_X]`.

Conclude with `c.nil₂ n t) _ ha _ hy`. Use the proof step `(fun i => by`. Consider the cases of `i with`. Consider the case `inl j`. Simplify using `only [Sum.elim_inl]`.

Rewrite using `[hev.1, hφ n j]`. Use `show _ = F (c'.x n j ⊗ₜ 1)`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Consider the case `inr j`.

Simplify using `only [Sum.elim_inr]`. Rewrite using `[hev.2.1, hφ n j]`. Use `show _ = F (1 ⊗ₜ c'.x n j)`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Use the proof step `rfl) s`.

Establish `h2` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n ⊗[k] G.A n) F (c'.x₂ n) (c'.nil₂ n) _ hy (fun _ => rfl) s`. Establish `h3 : pullbackTwo (f.app n) (c'.ev₂ n s) = F (c'.ev₂ n s)`. Proceed by induction on `(c'.ev₂ n s) with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Consider the case `tmul a b => rfl`. Unfold `pull2 at2`. Rewrite using `[h1, h3]`. Conclude with `h2.symm`.
-/
theorem isMapOf_existsUnique_and : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ f : G ⟶ H, (∃! φ, c.IsMapOf c' f φ) ∧ ∀ (φ : Fin e → MvPowerSeries (Fin d) k), c.IsMapOf c' f φ → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n, (∀ g, c.ev n (subst φ g) = f.app n (c'.ev n g)) ∧ ∀ s, c.ev₂ n (pull2 φ s) = pullbackTwo (f.app n) (c'.ev₂ n s) := by
  intro p k _ d e G H c c' f
  have hone := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.2
  have hcomp : ∀ j n, G.res n (f.app (n + 1) (c'.x (n + 1) j)) = f.app n (c'.x n j) := fun j n => by
    rw [res_app, c'.res]
  refine ⟨?_, ?_⟩
  · choose φ hφ _ using fun j => hone (fun n => f.app n (c'.x n j)) (hcomp j)
    refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => ?_⟩
    obtain ⟨g, -, hg⟩ := hone (fun n => f.app n (c'.x n j)) (hcomp j)
    exact (hg (ψ j) fun n => hψ n j).trans (hg (φ j) fun n => hφ j n).symm
  intro φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d (G.A 0) (c.x 0) (c.nil 0) (c.aug 0) (φ j)).1
    change Coalgebra.counit (R := k) (c.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, CoalgHomClass.counit_comp_apply, c'.aug]
  refine ⟨hconst, fun n => ⟨fun g => ?_, fun s => ?_⟩⟩
  · have hy : ∀ j, IsNilpotent (f.app n (c'.x n j)) := fun j => (c'.nil n j).map (f.app n)
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (G.A n)).1 (Fin d) (c.ev n)
      (fun t => by
        change IsNilpotent (evA k (c.x n) (c.nil n) (X t))
        rw [evA_X]; exact c.nil n t) φ hconst _ hy (fun j => hφ n j) g
    rw [h1]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (H.A n)).2 (G.A n) (f.app n : H.A n →ₐ[k] G.A n) (c'.x n)
      (c'.nil n) _ hy (fun _ => rfl) g).symm
  · let F : H.A n ⊗[k] H.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      Algebra.TensorProduct.map (f.app n : H.A n →ₐ[k] G.A n) (f.app n : H.A n →ₐ[k] G.A n)
    have hy : ∀ i, IsNilpotent (F (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map F
    have hev := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n
    have ha : ∀ i, constantCoeff ((Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) :
        Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k) i) = 0 := by
      intro i
      have hc := hev.2.2.2
      cases i with
      | inl j =>
        rw [Sum.elim_inl, ← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
      | inr j =>
        rw [Sum.elim_inr, ← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n)
      (fun t => by
        change IsNilpotent (evA k (c.x₂ n) (c.nil₂ n) (X t))
        rw [evA_X]; exact c.nil₂ n t) _ ha _ hy
      (fun i => by
        cases i with
        | inl j =>
          simp only [Sum.elim_inl]
          rw [hev.1, hφ n j]
          show _ = F (c'.x n j ⊗ₜ 1)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
        | inr j =>
          simp only [Sum.elim_inr]
          rw [hev.2.1, hφ n j]
          show _ = F (1 ⊗ₜ c'.x n j)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl) s
    have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n ⊗[k] G.A n) F
      (c'.x₂ n) (c'.nil₂ n) _ hy (fun _ => rfl) s
    have h3 : pullbackTwo (f.app n) (c'.ev₂ n s) = F (c'.ev₂ n s) := by
      induction (c'.ev₂ n s) with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b => rfl
    unfold pull2 at2
    rw [h1, h3]
    exact h2.symm

end GlobalTheory.Katz
