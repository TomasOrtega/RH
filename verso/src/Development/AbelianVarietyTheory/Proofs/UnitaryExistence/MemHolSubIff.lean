import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

noncomputable section

namespace GlobalTheory.CuspProduct

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

/- English proof (translation)
Use `⟨fun h => ?_, holCusp_mem_holSub X la⟩` and prove the remaining obligations. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1`. Consider the case `add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)`.

Consider the case `smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)`.
-/
theorem mem_holSub_iff {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (P : FDSec X) : P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

open Classical in

/- English proof (translation)
Use function extensionality and compare the values at `k x`. Use `show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) = (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) * (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)`. Use `split_ifs with h`. Conclude with `evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)`. Simplify using the standard rewrite rules.
-/
theorem rdU_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) =
    (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) *
      (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp

/- English proof (translation)
Take `⟨m, rfl⟩` from `hn`. Take `⟨m', rfl⟩` from `hn'`. Establish `h1 : (m + m) / 2 = m` using `by omega`. Establish `h2 : (m' + m') / 2 = m'` using `by omega`. Establish `h3 : (m + m + (m' + m')) / 2 = m + m'` using `by omega`.

Use function extensionality and compare the values at `τ j`. Simplify using `only [laU, Pi.add_apply, h1, h2, h3]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem laU_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  funext τ j
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U a a' n n' f g hd hd' hf hg`. Rewrite `hf`, `hg`, the goal using `[mem_cusp]`. Use `⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩` and prove the remaining obligations. Use `show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))`. Rewrite using `[rdU_mul, mem_holSub_iff]`.

Introduce `k`. Rewrite using `[laU_add (U σ) a a' n n' hd.2 hd'.2 k]`. Conclude with `(siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_iff _ _ _).1 (hf.2 σ hσ) k) _ ((mem_holSub_iff _ _ _).1 (hg.2 σ hσ) k).1`.
-/
theorem cuspMul_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.CuspMul Xo c U := by
  intro E _ _ _ H Dw l Xo c r U a a' n n' f g hd hd' hf hg
  rw [mem_cusp] at hf hg ⊢
  refine ⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩
  show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))
  rw [rdU_mul, mem_holSub_iff]
  intro k
  rw [laU_add (U σ) a a' n n' hd.2 hd'.2 k]
  exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_iff _ _ _).1 (hf.2 σ hσ) k) _
    ((mem_holSub_iff _ _ _).1 (hg.2 σ hσ) k).1

end GlobalTheory.CuspProduct
