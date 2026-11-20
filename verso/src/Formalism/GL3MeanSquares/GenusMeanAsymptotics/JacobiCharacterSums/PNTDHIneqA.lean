import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

def dhFam (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : Multiset ℂ :=
  Z.val.bind (fun ρ => Multiset.replicate (m ρ) (s - ρ))

/- English proof (translation)
Unfold `dhFam`. Rewrite using `[Multiset.mem_bind]`. Conclude with `⟨ρ, h, Multiset.mem_replicate.2 ⟨by omega, rfl⟩⟩`.
-/
theorem dhFam_mem (Z : Finset ℂ) (m : ℂ → ℕ) (s ρ : ℂ) (h : ρ ∈ Z) (hm : 1 ≤ m ρ) :
    s - ρ ∈ dhFam Z m s := by
  unfold dhFam
  rw [Multiset.mem_bind]
  exact ⟨ρ, h, Multiset.mem_replicate.2 ⟨by omega, rfl⟩⟩

/- English proof (translation)
Use `⟨S.toList.length, S.toList.get, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]`.
-/
theorem dhFlat (S : Multiset ℂ) : ∃ (N : ℕ) (w : Fin N → ℂ), Finset.univ.val.map w = S := by
  refine ⟨S.toList.length, S.toList.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]

/- English proof (translation)
Rewrite using `[← h, Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem dhFlat_sum {β : Type*} [AddCommMonoid β] {N : ℕ} (w : Fin N → ℂ) (S : Multiset ℂ)
    (h : Finset.univ.val.map w = S) (g : ℂ → β) : ∑ i, g (w i) = (S.map g).sum := by
  rw [← h, Multiset.map_map]
  rfl

end Formalism.HermitianLattices.Ext.PrimesInProgressions
