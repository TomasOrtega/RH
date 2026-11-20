import Mathlib
import Formalism.SobolevGaussianKernels.StatementSB
import Formalism.SobolevGaussianKernels.StatementLF

namespace Formalism.SL.P

open MeasureTheory Formalism.SL.SB
open scoped ContDiff

namespace SphereChartDerivatives

variable {n : ℕ}

def sn (t : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) y t

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
@[simp] lemma sn_last (t : ℝ) (y : Fin n → ℝ) : sn t y (Fin.last n) = t := by simp [sn]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
@[simp] lemma sn_cast (t : ℝ) (y : Fin n → ℝ) (k : Fin n) : sn t y (Fin.castSucc k) = y k := by
  simp [sn]

noncomputable def snocL (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun j => if h : j = Fin.last n then 0
    else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (j.castPred h))

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma sum_split (f : Finset (Fin (n + 1)) → ℝ) :
    ∑ α : Finset (Fin (n + 1)), f α =
      ∑ β : Finset (Fin n), f (β.map Fin.castSuccEmb) +
        ∑ β : Finset (Fin n), f (insert (Fin.last n) (β.map Fin.castSuccEmb)) := by
  have hnot : Fin.last n ∉ (Finset.univ : Finset (Fin n)).map Fin.castSuccEmb := by
    simp [Fin.castSucc_ne_last]
  have hu : (Finset.univ : Finset (Finset (Fin (n + 1)))) =
      (insert (Fin.last n) ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb)).powerset := by
    rw [← Finset.cons_eq_insert _ _ hnot, ← Fin.univ_castSuccEmb, Finset.powerset_univ]
  rw [hu, Finset.sum_powerset_insert hnot]
  have key : ∀ h : Finset (Fin (n + 1)) → ℝ,
      ∑ t ∈ ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb).powerset, h t =
        ∑ β : Finset (Fin n), h (β.map Fin.castSuccEmb) := by
    intro h
    symm
    apply Finset.sum_nbij' (fun β => β.map Fin.castSuccEmb)
      (fun α => Finset.univ.filter (fun k => Fin.castSucc k ∈ α))
    · intro β _
      simp [Finset.map_subset_map]
    · intro α _
      simp
    · intro β _
      ext k
      simp
    · intro α hα
      rw [Finset.mem_powerset] at hα
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSuccEmb]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hk
      · intro hx
        obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 (hα hx)
        exact ⟨k, hx, rfl⟩
    · intro β _
      rfl
  rw [key, key (fun t => f (insert (Fin.last n) t))]

noncomputable def SS {m : ℕ} (δ : ℝ) (g : (Fin m → ℝ) → ℂ) (y : Fin m → ℝ) : ℝ :=
  ∑ α : Finset (Fin m), δ ^ (2 * α.card) * ‖mixed α g y‖ ^ 2

end SphereChartDerivatives

end Formalism.SL.P
