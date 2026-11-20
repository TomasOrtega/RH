import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmallCompactOpenBetween
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsSmallCompactOpenBetween.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_small_compact_open_between : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)),
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small <;> assumption)
