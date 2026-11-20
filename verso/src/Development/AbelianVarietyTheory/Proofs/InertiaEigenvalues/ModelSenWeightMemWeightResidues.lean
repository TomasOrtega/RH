import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicitySubquotientLatticeLeStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

/- English proof (translation)
Introduce `k G _ _ l n _ _ _ R F r Dt M A N hN i x hx`. Take `⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩` from `hN`. Establish `hle` using `GlobalTheory.T.senMultiplicity_subquotient_lattice_le F B A₁ A j p Dt.w Dt.wst Nb (M.base_obj B Nb hB) hj hji hp hps (M.base_abc B Nb hB) i x`. Take `⟨μ, -, hs⟩` from `M.base_sen B Nb hB`. Rewrite `hle` using `[hs i x]`.

Establish `h0 : resCount (Dt.Ut i) (Dt.w i) x ≠ 0`. Introduce `h`. Rewrite `hle` using `[h]`. Apply `hx` to reduce the goal to its premises. Simplify using `using hle`.

Unfold `resCount at h0`. Take `⟨u, hu⟩` from `Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero h0)`. Rewrite `hu` using `[Multiset.mem_filter]`. Conclude with `⟨u, hu.1, hu.2⟩`.
-/
theorem model_sen_mem : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.Ut i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M A N hN i x hx
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F B A₁ A j p Dt.w Dt.wst Nb (M.base_obj B Nb hB) hj hji hp hps
    (M.base_abc B Nb hB) i x
  obtain ⟨μ, -, hs⟩ := M.base_sen B Nb hB
  rw [hs i x] at hle
  have h0 : resCount (Dt.Ut i) (Dt.w i) x ≠ 0 := by
    intro h
    rw [h] at hle
    apply hx
    simpa using hle
  unfold resCount at h0
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero h0)
  classical
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

end GlobalTheory.Models
