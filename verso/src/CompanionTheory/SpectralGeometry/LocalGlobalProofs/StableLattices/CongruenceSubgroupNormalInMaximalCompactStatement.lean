import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FCongruenceSubgroupNormalInMaximalCompact.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L), c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl → x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 → c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK | exact GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK <;> assumption)
