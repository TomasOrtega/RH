import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiWachLatticeClosedWeak
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JDANEqRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisOrbitWittTensorLatticeWeakTopoloStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOneTmulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactSpaceATopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousWittCbInclusionSmulWeakTopologyStatement

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology

namespace GlobalTheory.WeakClosedX

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/- English proof (translation)
Take `⟨S, hS⟩` from `W.N_fg T`. Set `n : Fin S.card → W.DD T` to `fun i => (S.equivFin.symm i : W.DD T)`. Establish `hrange : Set.range n = (S : Set (W.DD T))`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `(S.equivFin.symm i).2`. Introduce `hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩`. Establish `hspan : W.N T = Submodule.span (AA K LL) (Set.range n)` using `by rw [hrange, hS]`. Use `⟨S.card, fun i => E.tie.jD T (a • n i), ?_⟩` and prove the remaining obligations.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨m, hm, rfl⟩` from `Submodule.mem_map.1 hx`. Rewrite `hm` using `[hspan]`.

Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm`. Use `⟨c, ?_⟩` and prove the remaining obligations. Simplify using `only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.NL.WkRange.jD_smul_letter]`.

Conclude with `smul_comm _ _ _`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨∑ i, c i • (a • n i), ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hspan]`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩`. Simplify using `only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => smul_comm _ _ _`. Simplify using `only [map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => GlobalTheory.NL.WkRange.jD_smul_letter E T _ _`.
-/
theorem jD_aN_eq_range_gen {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}
    {s : ℕ} {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (T : Lt K LL) (a : AA K LL) :
    ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T a : Set (W.DD T)) =
      Set.range fun c : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (c i)) • y i := by
  obtain ⟨S, hS⟩ := W.N_fg T
  let n : Fin S.card → W.DD T := fun i => (S.equivFin.symm i : W.DD T)
  have hrange : Set.range n = (S : Set (W.DD T)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2
    · intro hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩
  have hspan : W.N T = Submodule.span (AA K LL) (Set.range n) := by rw [hrange, hS]
  refine ⟨S.card, fun i => E.tie.jD T (a • n i), ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    rw [hspan] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm
    refine ⟨c, ?_⟩
    simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [GlobalTheory.NL.WkRange.jD_smul_letter]
    exact smul_comm _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨∑ i, c i • (a • n i), ?_, ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩
      · rw [hspan]
        exact (Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩
      · simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    · simp only [map_sum]
      exact Finset.sum_congr rfl fun i _ => GlobalTheory.NL.WkRange.jD_smul_letter E T _ _

/- English proof (translation)
Introduce `D HW F l _ K s LL h T _`. Use `haveI := LL.2`. Use `haveI : Module.Free ℤ_[l] ↥(OL LL) := (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1`. Use `haveI : Module.Finite ℤ_[l] ↥(OL LL) := (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1`. Take `⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d)` from `GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T`.

Set `bO` to `Module.finBasis ℤ_[l] ↥(OL LL)`. Use `letI τ := twTop T b`. Use `letI tW : TopologicalSpace (WCb l) := wTop l`. Use `letI := cbTop l`. Use `haveI := hausdorff_tilt_witt (l := l)`.

Use `haveI := ring_cb (l := l)`. Use `haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product`. Use `haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt`. Use `letI := zlMod T`. Use `haveI := zlTower T`.

Establish `hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)` using `continuous_induced_dom`. Use `haveI hT2 : T2Space (TW (RW LL) T) := T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc`. Use `haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) := Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩`. Use `⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩` and prove the remaining obligations. Take `⟨r, y, hy⟩` from `jD_aN_eq_range_gen ((F l).E K s LL h) T ((HW l).W K s LL h).X`.

Rewrite using `[hy]`. Use `letI := aTop (K := K) bO`. Use `haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO`. Use `(isCompact_range ?_).isClosed` and prove the remaining obligations. Use `continuous_finsetSum _ fun i _ => ?_` and prove the remaining obligations.

Conclude with `(GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)`.
-/
theorem jD_XN_closed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T))) := by
  intro D HW F l _ K s LL h T _
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d) := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  let bO := Module.finBasis ℤ_[l] ↥(OL LL)
  letI τ := twTop T b
  letI tW : TopologicalSpace (WCb l) := wTop l
  letI := cbTop l
  haveI := hausdorff_tilt_witt (l := l)
  haveI := ring_cb (l := l)
  haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  letI := zlMod T
  haveI := zlTower T
  have hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) := continuous_induced_dom
  haveI hT2 : T2Space (TW (RW LL) T) :=
    T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc
  haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) :=
    Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩
  refine ⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩
  obtain ⟨r, y, hy⟩ := jD_aN_eq_range_gen ((F l).E K s LL h) T ((HW l).W K s LL h).X
  rw [hy]
  letI := aTop (K := K) bO
  haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO
  refine (isCompact_range ?_).isClosed
  refine continuous_finsetSum _ fun i _ => ?_
  exact (GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)

end GlobalTheory.WeakClosedX
