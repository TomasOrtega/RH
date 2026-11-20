import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.NL.WkRange

/- English proof (translation)
Rewrite using `[← algebraMap_smul W.EE a x, E.tie.jD_smul, E.tie.ioE_ext]`.
-/
theorem jD_smul_letter {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
    {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (T : Lt K LL) (a : AA K LL) (x : W.DD T) :
    E.tie.jD T (a • x) = inclR LL (E.tie.io a) • E.tie.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.tie.jD_smul, E.tie.ioE_ext]

/- English proof (translation)
Introduce `l _ P AI K s LL h W E T`. Take `⟨S, hS⟩` from `W.N_fg T`. Set `n : Fin S.card → W.DD T` to `fun i => (S.equivFin.symm i : W.DD T)`. Establish `hrange : Set.range n = (S : Set (W.DD T))`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(S.equivFin.symm i).2`. Introduce `hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩`. Establish `hspan : W.N T = Submodule.span (AA K LL) (Set.range n)` using `by rw [hrange, hS]`.

Use `⟨S.card, fun i => E.tie.jD T ((letπ : AA K LL) • n i), ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨m, hm, rfl⟩` from `Submodule.mem_map.1 hx`.

Rewrite `hm` using `[hspan]`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm`. Use `⟨c, ?_⟩` and prove the remaining obligations. Simplify using `only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [jD_smul_letter]`. Conclude with `smul_comm _ _ _`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨∑ i, c i • ((letπ : AA K LL) • n i), ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hspan]`. Conclude with `(Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩`. Simplify using `only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => smul_comm _ _ _`. Simplify using `only [map_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => jD_smul_letter E T _ _`.
-/
theorem jD_aN_eq_range : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL), ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T letπ : Set (W.DD T)) = Set.range fun a : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (a i)) • y i := by
  intro l _ P AI K s LL h W E T
  obtain ⟨S, hS⟩ := W.N_fg T
  let n : Fin S.card → W.DD T := fun i => (S.equivFin.symm i : W.DD T)
  have hrange : Set.range n = (S : Set (W.DD T)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2
    · intro hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩
  have hspan : W.N T = Submodule.span (AA K LL) (Set.range n) := by rw [hrange, hS]
  refine ⟨S.card, fun i => E.tie.jD T ((letπ : AA K LL) • n i), ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    rw [hspan] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm
    refine ⟨c, ?_⟩
    simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [jD_smul_letter]
    exact smul_comm _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨∑ i, c i • ((letπ : AA K LL) • n i), ?_, ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩
      · rw [hspan]
        exact (Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩
      · simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    · simp only [map_sum]
      exact Finset.sum_congr rfl fun i _ => jD_smul_letter E T _ _

end GlobalTheory.NL.WkRange
