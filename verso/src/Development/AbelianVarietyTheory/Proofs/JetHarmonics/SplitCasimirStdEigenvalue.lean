import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimirStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorStdRelAdjointSplitCasimir
open Formalism.REAL

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ n E Et Om m hE hadj hq hEt hOm lam x hx hlam`. Take `⟨K, hK, -⟩` from `GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir V n E Om m hE hq hOm`. Take `⟨-, -, -, hc⟩` from `tensorStd_rel_adjoint_splitCasimir V n E Et Om hE hadj hEt hOm`. Assume the negation of the conclusion as `hne`. Establish `hprod : (∏ j, (-lam + m j)) ≠ 0`.

Use `Finset.prod_ne_zero_iff.2 fun j _ h => hne ⟨j, ?_⟩` and prove the remaining obligations. Take the linear combination `-h`. Establish `hlast : ∀ y, Om y = lam • y → y (Fin.last n) = 0`. Introduce `y hy`. Establish `h` using `hK (-lam) y`.

Rewrite `h` using `[hy, sub_zero, neg_smul, neg_add_cancel, map_zero]`. Conclude with `(smul_eq_zero.1 h.symm).resolve_left hprod`. Apply `hx` to reduce the goal to its premises. Use `PiLp.ext fun c => ?_` and prove the remaining obligations. Establish `h1 : Om (Et (Fin.last n) c x) = lam • Et (Fin.last n) c x`.

Establish `h` using `LinearMap.congr_fun (hc (Fin.last n) c) x`. Simplify using `only [Module.End.mul_apply] at h`. Rewrite using `[h, hlam, map_smul]`. Establish `h2` using `hlast _ h1`. Rewrite `h2` using `[hEt, hlast x hlam]`.

Simplify using `using h2`.
-/
theorem splitCasimirStd_eigenvalue : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + 0 := by
  intro V _ _ _ n E Et Om m hE hadj hq hEt hOm lam x hx hlam
  obtain ⟨K, hK, -⟩ := GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir V n E Om m hE hq hOm
  obtain ⟨-, -, -, hc⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hE hadj hEt hOm
  by_contra hne
  have hprod : (∏ j, (-lam + m j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j _ h => hne ⟨j, ?_⟩
    linear_combination -h
  have hlast : ∀ y, Om y = lam • y → y (Fin.last n) = 0 := by
    intro y hy
    have h := hK (-lam) y
    rw [hy, sub_zero, neg_smul, neg_add_cancel, map_zero] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hprod
  apply hx
  refine PiLp.ext fun c => ?_
  have h1 : Om (Et (Fin.last n) c x) = lam • Et (Fin.last n) c x := by
    have h := LinearMap.congr_fun (hc (Fin.last n) c) x
    simp only [Module.End.mul_apply] at h
    rw [h, hlam, map_smul]
  have h2 := hlast _ h1
  rw [hEt, hlast x hlam] at h2
  simpa using h2

end GlobalTheory
