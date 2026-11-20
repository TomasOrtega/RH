import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricUnipotentTimesKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriLeviUnipotentFactorStatement

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

/- English proof (translation)
Introduce `k _ _ _ _ n s d e g hg`. Take `⟨u, hu, h, hh, rfl⟩` from `GlobalTheory.T.parahoric_unipotent_times_kernel k n s d e g hg`. Take `⟨m, hLm, x, hx, c, hc, hdec⟩` from `GlobalTheory.T.iwahori_levi_unipotent_factor k n s d e h hh`. Establish `hm : GlobalTheory.SmGL.leviEmb k e m ∈ PositivityTheory.LowerBoundConstant.Gx k e`. Unfold `PositivityTheory.LowerBoundConstant.Gx`.

Conclude with `Subgroup.mem_sup_left hLm`. Establish `hconj : (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m ∈ GlobalTheory.SmGL.unipRad k e`. Establish `hn` using `GlobalTheory.SmGL.leviEmb_mem_normalizer k e m⁻¹`. Rewrite `hn` using `[map_inv]`. Establish `h'` using `(Subgroup.mem_normalizer_iff.mp hn u).mp hu.1`.

Rewrite `h'` using `[inv_inv]`. Then use the resulting hypothesis. Use `⟨m, Subgroup.mem_comap.mpr hm, (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m * x, mul_mem hconj hx.1, c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hdec]`. Use `group`.
-/
theorem factor_Gx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ m ∈ (Gx k e).comap (leviEmb k e), ∃ x ∈ unipRad k e, ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  intro k _ _ _ _ n s d e g hg
  obtain ⟨u, hu, h, hh, rfl⟩ := GlobalTheory.T.parahoric_unipotent_times_kernel k n s d e g hg
  obtain ⟨m, hLm, x, hx, c, hc, hdec⟩ := GlobalTheory.T.iwahori_levi_unipotent_factor k n s d e h hh
  have hm : GlobalTheory.SmGL.leviEmb k e m ∈ PositivityTheory.LowerBoundConstant.Gx k e := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact Subgroup.mem_sup_left hLm
  have hconj : (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m
      ∈ GlobalTheory.SmGL.unipRad k e := by
    have hn := GlobalTheory.SmGL.leviEmb_mem_normalizer k e m⁻¹
    rw [map_inv] at hn
    have h' := (Subgroup.mem_normalizer_iff.mp hn u).mp hu.1
    rwa [inv_inv] at h'
  refine ⟨m, Subgroup.mem_comap.mpr hm,
    (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m * x,
    mul_mem hconj hx.1, c, hc, ?_⟩
  rw [hdec]; group

end GlobalTheory.CompanionTheory.MoyPrasad
