import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH

namespace GlobalTheory.LatticeSumMembership

open Formalism.MainNotions.TaylorLogMetric

/- English proof (translation)
Introduce `D T N N' L L' y hy`. Unfold `Formalism.MainNotions.TaylorLogMetric.La at hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, A, hA, rfl⟩` from `hx`.

Conclude with `⟨1, fun _ => A, fun _ => w, fun _ => hA, fun _ => hw, by simp⟩`. Consider the case `zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩`. Consider the case `add x z _ _ ihx ihz`. Take `⟨r₁, b₁, w₁, hb₁, hw₁, rfl⟩` from `ihx`. Take `⟨r₂, b₂, w₂, hb₂, hw₂, rfl⟩` from `ihz`.

Use `⟨r₁ + r₂, Fin.append b₁ b₂, Fin.append w₁ w₂, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Simplify using `using hb₁ i`. Simplify using `using hb₂ i`.

Introduce `j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Simplify using `using hw₁ i`. Simplify using `using hw₂ i`. Rewrite using `[Fin.sum_univ_add]`.

Simplify using the standard rewrite rules. Consider the case `neg x _ ihx`. Take `⟨r, b, w, hb, hw, rfl⟩` from `ihx`. Use `⟨r, b, fun j => -w j, hb, fun j => T.abelian₂.neg_mem (hw j), ?_⟩` and prove the remaining obligations. Simplify using `[neg_smul, Finset.sum_neg_distrib]`.
-/
theorem La_mem_sum :
    ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) {N N' : ℕ}
      (L : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E))
      (L' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)),
      ∀ y ∈ Formalism.MainNotions.TaylorLogMetric.La D T L L', ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (w : Fin r → ℂ),
        (∀ (j : Fin r), b j ∈ Formalism.MainNotions.TaylorLogMetric.YYl D L L') ∧ (∀ (j : Fin r), w j ∈ Formalism.MainNotions.TaylorLogMetric.Tor.abelian₂ T) ∧
          y = ∑ j : Fin r, w j • Formalism.MainNotions.TaylorLogMetric.embV D T (b j) := by
  intro D T N N' L L' y hy
  unfold Formalism.MainNotions.TaylorLogMetric.La at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    exact ⟨1, fun _ => A, fun _ => w, fun _ => hA, fun _ => hw, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩
  | add x z _ _ ihx ihz =>
    obtain ⟨r₁, b₁, w₁, hb₁, hw₁, rfl⟩ := ihx
    obtain ⟨r₂, b₂, w₂, hb₂, hw₂, rfl⟩ := ihz
    refine ⟨r₁ + r₂, Fin.append b₁ b₂, Fin.append w₁ w₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hb₁ i
      · simpa using hb₂ i
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hw₁ i
      · simpa using hw₂ i
    · rw [Fin.sum_univ_add]
      simp
  | neg x _ ihx =>
    obtain ⟨r, b, w, hb, hw, rfl⟩ := ihx
    refine ⟨r, b, fun j => -w j, hb, fun j => T.abelian₂.neg_mem (hw j), ?_⟩
    simp [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LatticeSumMembership
