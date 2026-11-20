import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GLColumnsIsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFlagCellFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelSubbundleIsVBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFlagLastInclIsIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFlagFrameSpecialize

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.FlagZ

namespace GlobalTheory.FlagZ.TautCell

open GlobalTheory.VB

variable (ι : Type) [Fintype ι] (N : ℕ)

/- English proof (translation)
Take `⟨w, x, hx⟩` from `GlobalTheory.FlagZ.exists_mem_range_cell _ _ _ (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd y`. Conclude with `⟨w, ⟨x, trivial, hx⟩⟩`.
-/
theorem mem_cellU_exists (y : Fl ι N) : ∃ w : ι → Equiv.Perm (Fin N), y ∈ cellU w := by
  obtain ⟨w, x, hx⟩ := GlobalTheory.FlagZ.exists_mem_range_cell _ _ _ (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd y
  exact ⟨w, ⟨x, trivial, hx⟩⟩

/- English proof (translation)
Introduce `y` and use `by obtain ⟨w, hw⟩ := mem_cellU_exists ι N y obtain ⟨e, he, -⟩ := GlobalTheory.T.universal_flag_cell_frame ι N w τ l exact ⟨_, e, hw, he⟩`.
-/
theorem isVB_F (τ : ι) (l : Fin (N + 1)) : IsVB (Univ.F ι N τ l) l := fun y => by
  obtain ⟨w, hw⟩ := mem_cellU_exists ι N y
  obtain ⟨e, he, -⟩ := GlobalTheory.T.universal_flag_cell_frame ι N w τ l
  exact ⟨_, e, hw, he⟩

/- English proof (translation)
Establish `hc` using `GlobalTheory.T.cokernel_subbundle_isVB (Fl ι N) _ _ (Univ.sub ι N τ l).incl N l l.is_le inferInstance fun y => by`. Take `⟨w, hw⟩` from `mem_cellU_exists ι N y`. Take `⟨e, he, hi⟩` from `GlobalTheory.T.universal_flag_cell_frame ι N w τ l`. Conclude with `⟨cellU w, colU w τ, e, hw, GlobalTheory.T.GL_columns_isFrame N _ _ (cellMat w τ), he, hi⟩`. Conclude with `⟨inferInstanceAs (Mono ((Univ.sub ι N τ l).incl ≫ (Univ.freeIso ι N).inv)), N - l, hc.of_iso (cokernelCompIsIso _ _).symm⟩`.
-/
theorem isSubbundle_incl (τ : ι) (l : Fin (N + 1)) : IsSubbundle (Univ.incl ι N τ l) := by
  have hc := GlobalTheory.T.cokernel_subbundle_isVB (Fl ι N) _ _ (Univ.sub ι N τ l).incl N l l.is_le inferInstance fun y => by
    obtain ⟨w, hw⟩ := mem_cellU_exists ι N y
    obtain ⟨e, he, hi⟩ := GlobalTheory.T.universal_flag_cell_frame ι N w τ l
    exact ⟨cellU w, colU w τ, e, hw, GlobalTheory.T.GL_columns_isFrame N _ _ (cellMat w τ), he, hi⟩
  exact ⟨inferInstanceAs (Mono ((Univ.sub ι N τ l).incl ≫ (Univ.freeIso ι N).inv)), N - l,
    hc.of_iso (cokernelCompIsIso _ _).symm⟩

def tautFlag (τ : ι) : Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N where
  F := Univ.F ι N τ
  ι := Univ.incl ι N τ
  isSubbundle := isSubbundle_incl ι N τ
  isVB := isVB_F ι N τ
  step := Univ.step ι N τ
  step_ι := Univ.step_incl ι N τ
  isIso_last := GlobalTheory.T.universal_flag_last_incl_isIso ι N τ

/- English proof (translation)
Introduce `A _ g a l` and use `GlobalTheory.T.universal_flag_frame_specialize ι N a l (fun w => GlobalTheory.T.universal_flag_cell_frame ι N w a l) (isVB_F ι N a l) A g`.
-/
theorem isTaut_tautFlag : GlobalTheory.FlagZ.Taut.IsTaut ι N (tautFlag ι N) := fun A _ g a l =>
  GlobalTheory.T.universal_flag_frame_specialize ι N a l (fun w => GlobalTheory.T.universal_flag_cell_frame ι N w a l) (isVB_F ι N a l) A g

end GlobalTheory.FlagZ.TautCell

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

/- English proof (translation)
Introduce `ι _ N` and use `⟨GlobalTheory.FlagZ.TautCell.tautFlag ι N, GlobalTheory.FlagZ.TautCell.isTaut_tautFlag ι N⟩`.
-/
theorem GlobalTheory.FlagZ.exists_isTaut : ∀ (ι : Type) [Fintype ι] (N : ℕ), ∃ fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N, GlobalTheory.FlagZ.Taut.IsTaut ι N fl :=
  fun ι _ N => ⟨GlobalTheory.FlagZ.TautCell.tautFlag ι N, GlobalTheory.FlagZ.TautCell.isTaut_tautFlag ι N⟩
