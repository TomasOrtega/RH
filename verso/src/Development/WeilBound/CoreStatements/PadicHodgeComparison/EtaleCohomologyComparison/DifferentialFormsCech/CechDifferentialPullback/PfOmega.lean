import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

/- English proof (translation)
Introduce `K _ X Y q p u hu a j y`. Apply `(GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective` to reduce the goal to its premises. Rewrite using `[AddEquiv.apply_symm_apply]`. Take `⟨w, rfl⟩` from `(GlobalTheory.SiteCoh.terminalEquiv ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j isTerminalTop).surjective y`. Take `⟨z, rfl⟩` from `(GlobalTheory.cohOn.toH' (GlobalTheory.HodgeCoh.Omega p a) ⊤ j).surjective w`.

Establish `hz : (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)) = z` using `(GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm_apply_apply z`. Rewrite using `[hz]`. Express the relevant statement in the definitionally equal form `GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.SheafPull.pull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j (homOfLE le_top) ((GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop).symm (GlobalTheory.SiteCoh.terminalEquiv _ j isT …`. Rewrite using `[AddEquiv.symm_apply_apply]`. Use `congr 1`.
-/
theorem hPull_omega_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) (a j : ℕ)
    (y : Sheaf.H.{0} ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j),
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm (hPull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j y) =
      pullC u hu a j ((GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm y) := by
  intro K _ X Y q p u hu a j y
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  rw [AddEquiv.apply_symm_apply]
  obtain ⟨w, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j
    isTerminalTop).surjective y
  obtain ⟨z, rfl⟩ := (GlobalTheory.cohOn.toH' (GlobalTheory.HodgeCoh.Omega p a) ⊤ j).surjective w
  have hz : (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm
      (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)) = z :=
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm_apply_apply z
  rw [hz]
  change GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop
      (GlobalTheory.SheafPull.pull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j (homOfLE le_top)
        ((GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop).symm
          (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)))) =
    GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ _ j (GlobalTheory.HodgeCoh.hodgePull hu a j z))
  rw [AddEquiv.symm_apply_apply]
  congr 1

end CrystallineSemistableComparison.Om.Cech
