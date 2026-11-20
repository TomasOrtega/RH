import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulPhiMemMM

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK

namespace PhiMod

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NeZero a]

/- English proof (translation)
Establish `hc : ∀ p : ZMod a × ι, ∃ n : ℕ, (l : K⟦X⟧) ^ n * (P.mxInv p.1 *ᵥ v p.1) p.2 ∈ S O K e`. Introduce `p`. Take `⟨n, hn⟩` from `mem_away.1 (mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 hv p.1)) p.2)`. Conclude with `⟨n, by simpa using hn⟩`. Use `choose n hn using hc`.

Use `⟨Finset.univ.sup n, mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => ?_)⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))`. Rewrite using `[Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, hc, smul_eq_C_mul, map_pow, map_natCast, pow_add, mul_assoc]`. Conclude with `mul_mem (pow_mem (natCast_mem _ l) c) (hn (τ, i))`.
-/
theorem exists_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {v : Vec K a ι} (hv : v ∈ P.MMl) :
    ∃ N : ℕ, (l : K) ^ N • v ∈ P.MM := by
  have hc : ∀ p : ZMod a × ι, ∃ n : ℕ,
      (l : K⟦X⟧) ^ n * (P.mxInv p.1 *ᵥ v p.1) p.2 ∈ S O K e := by
    intro p
    obtain ⟨n, hn⟩ := mem_away.1 (mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 hv p.1)) p.2)
    exact ⟨n, by simpa using hn⟩
  choose n hn using hc
  refine ⟨Finset.univ.sup n, mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => ?_)⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, hc, smul_eq_C_mul, map_pow, map_natCast,
    pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem _ l) c) (hn (τ, i))

/- English proof (translation)
Use `mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => mem_away.2 ⟨N, ?_⟩)` and prove the remaining obligations. Establish `h1` using `mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 h τ)) i`. Rewrite `h1` using `[Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_C_mul, map_pow, map_natCast]`. Simplify using `using h1`.
-/
theorem mem_MMl_of_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {w : Vec K a ι} (N : ℕ)
    (h : (l : K) ^ N • w ∈ P.MM) : w ∈ P.MMl := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => mem_away.2 ⟨N, ?_⟩)
  have h1 := mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 h τ)) i
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_C_mul, map_pow, map_natCast] at h1
  simpa using h1

end PhiMod

/- English proof (translation)
Introduce `O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D v hv`. Take `⟨N, hN⟩` from `D.toPhiMod.exists_lpow_smul_mem_MM hv`. Establish `h` using `PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper _ hN`. Rewrite `h` using `[map_smul, smul_smul, ← pow_add]`. Conclude with `D.toPhiMod.mem_MMl_of_lpow_smul_mem_MM _ h`.
-/
theorem BKDat.phi_mem_MMl : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ v ∈ D.MMl, D.phi v ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D v hv
  obtain ⟨N, hN⟩ := D.toPhiMod.exists_lpow_smul_mem_MM hv
  have h := PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper _ hN
  rw [map_smul, smul_smul, ← pow_add] at h
  exact D.toPhiMod.mem_MMl_of_lpow_smul_mem_MM _ h

end GlobalTheory.BK
