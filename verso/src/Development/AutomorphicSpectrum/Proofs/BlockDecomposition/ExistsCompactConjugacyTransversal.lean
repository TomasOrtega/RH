import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

/- English proof (translation)
Introduce `H _ _ _ K N hK hfin C hC`. Use `⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) | ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}, (fun k => Quotient.out q * k) '' (K : Set H), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hfin C hC).isCompact_biUnion fun q _ => hK.image (continuous_const.mul continuous_id)`. Introduce `x hx`. Take `⟨h, k, hh, hk, hout⟩` from `DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) N) K x`.

Establish `hcomm : h * N = N * h` using `hh`. Establish `hconj : (h * x)⁻¹ * N * (h * x) = x⁻¹ * N * x`. Establish `: h⁻¹ * N * h = N`. Rewrite using `[mul_assoc, ← hcomm, inv_mul_cancel_left]`. Combine the equalities or inequalities in the displayed calculation.

Use `set q := DoubleCoset.mk (twCent (MonoidHom.id H) N) K x with hq`. Establish `hd : Quotient.out q * k⁻¹ = h * x`. Rewrite using `[hout]`. Use `group`. Use `⟨h⁻¹, inv_mem hh, Quotient.out q * k⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Use `Set.mem_biUnion (x := q) ?_ ⟨k⁻¹, inv_mem hk, rfl⟩` and prove the remaining obligations. Use `⟨k⁻¹, inv_mem hk, ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.id_apply, hd, hconj]`. Conclude with `hx`. Rewrite using `[hd, inv_mul_cancel_left]`.
-/
theorem exists_compact_reps_of_finite_doubleCosets :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H),
      IsCompact (K : Set H) →
      (∀ C : Set H, IsCompact C →
        {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
          ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
      ∀ C : Set H, IsCompact C →
        ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
          ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  intro H _ _ _ K N hK hfin C hC
  refine ⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
      ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C},
      (fun k => Quotient.out q * k) '' (K : Set H), ?_, ?_⟩
  · exact (hfin C hC).isCompact_biUnion fun q _ =>
      hK.image (continuous_const.mul continuous_id)
  · intro x hx
    obtain ⟨h, k, hh, hk, hout⟩ :=
      DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) N) K x
    have hcomm : h * N = N * h := hh
    have hconj : (h * x)⁻¹ * N * (h * x) = x⁻¹ * N * x := by
      have : h⁻¹ * N * h = N := by
        rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
      calc (h * x)⁻¹ * N * (h * x) = x⁻¹ * (h⁻¹ * N * h) * x := by group
        _ = x⁻¹ * N * x := by rw [this]
    set q := DoubleCoset.mk (twCent (MonoidHom.id H) N) K x with hq
    have hd : Quotient.out q * k⁻¹ = h * x := by
      rw [hout]; group
    refine ⟨h⁻¹, inv_mem hh, Quotient.out q * k⁻¹, ?_, ?_⟩
    · refine Set.mem_biUnion (x := q) ?_ ⟨k⁻¹, inv_mem hk, rfl⟩
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [MonoidHom.id_apply, hd, hconj]
      exact hx
    · rw [hd, inv_mul_cancel_left]

end GlobalTheory.CompanionTheory.OrbitalCount
