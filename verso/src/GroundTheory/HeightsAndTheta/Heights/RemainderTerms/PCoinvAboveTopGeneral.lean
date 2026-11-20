import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

/- English proof (translation)
Introduce `K _ _ β ι _ _ _ _ d H hH hd`. Use `set eβ := Fintype.equivFin β`. Use `set eι := Fintype.equivFin ι`. Use `set ψ : β × ι ≃ Fin (Fintype.card β) × Fin (Fintype.card ι) := eβ.prodCongr eι with hψ`. Take `⟨Q', hQ'h, hQ'⟩` from `h1 K (Fintype.card β) (Fintype.card ι) d (rename ψ H) hH.rename_isHomogeneous hd`.

Use `⟨fun m b => rename ψ.symm (Q' m (eβ b)), fun m b => (hQ'h m (eβ b)).rename_isHomogeneous, ?_⟩` and prove the remaining obligations. Establish `hback : H = rename ψ.symm (rename ψ H)`. Rewrite using `[rename_rename, Equiv.symm_comp_self, rename_id_apply]`. Rewrite using `[hback, hQ', map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum, ← Equiv.sum_comp eβ.symm]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Simplify using `only [Equiv.apply_symm_apply]`. Use `congr 1`.

Rewrite using `[bps, map_sum, ← Equiv.sum_comp eι.symm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[hψ]`.
-/
theorem CoinvAboveTopGeneral.proof (h1 : CoinvAboveTop.Statement) :
    CoinvAboveTopGeneral.Statement := by
  intro K _ _ β ι _ _ _ _ d H hH hd
  set eβ := Fintype.equivFin β
  set eι := Fintype.equivFin ι
  set ψ : β × ι ≃ Fin (Fintype.card β) × Fin (Fintype.card ι) := eβ.prodCongr eι with hψ
  obtain ⟨Q', hQ'h, hQ'⟩ := h1 K (Fintype.card β) (Fintype.card ι) d (rename ψ H)
    hH.rename_isHomogeneous hd
  refine ⟨fun m b => rename ψ.symm (Q' m (eβ b)),
    fun m b => (hQ'h m (eβ b)).rename_isHomogeneous, ?_⟩
  have hback : H = rename ψ.symm (rename ψ H) := by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
  rw [hback, hQ', map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_sum, ← Equiv.sum_comp eβ.symm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [map_mul]
  simp only [Equiv.apply_symm_apply]
  congr 1
  rw [bps, map_sum, ← Equiv.sum_comp eι.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hψ]

end

end GroundTheory.Heights₂.Heights.RestTerms
