import Development.EtaleCohomology.EtaleSheaves.BijOfIso
import Development.EtaleCohomology.EtaleSheaves.TruncKerPf
import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

/- English proof (translation)
Introduce `hH q _ i n A Y φ hq P hpush het hlow _ D d hPD hpts Y' w φ' hpo`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨z, rfl⟩` from `relExact _ _ _ n x hx`. Take `⟨E, e, Z, u, ψ, h, he, hs, h0⟩` from `relKill hH.2.2.2.2.2.2.1 hC q i n φ hq d hpts w φ' hpo z hx`.

Establish `hz : z = 0` using `(injective_iff_map_eq_zero _).1 (hD hH q i n φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Z u ψ he hs (het d e hPD he) h) z h0`. Rewrite using `[hz, map_zero]`.
-/
theorem KerLoc_of (hC : Coprod) (hD : LateralTheory.E.TruncationKernel.RelDesc) : KerLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow _ D d hPD hpts Y' w φ' hpo
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := relExact _ _ _ n x hx
  obtain ⟨E, e, Z, u, ψ, h, he, hs, h0⟩ := relKill hH.2.2.2.2.2.2.1 hC q i n φ hq d hpts w φ' hpo z hx
  have hz : z = 0 := (injective_iff_map_eq_zero _).1
    (hD hH q i n φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Z u ψ he hs (het d e hPD he) h) z h0
  rw [hz, map_zero]

end LateralTheory.E.KernelLocalization
