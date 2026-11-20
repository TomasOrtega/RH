import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfB

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

/- English proof (translation)
Distinguish the cases in `ha : -(h' : ℤ) ≤ a`. Conclude with `u3upPf_FilC_anti (PD := PD) T τ ha`. Establish `hc : ∀ j : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - j) = FildR PD T.ρ τ (-(h' : ℤ))`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - (j + 1 : ℕ))`. Introduce `hj`. Use `(hJ _ hj).1` as an intermediate fact.

Move the coercions through the operations in `at this`. Use linear arithmetic over natural numbers and integers. Unfold `IsJumpV at hnj`. Use `push_neg at hnj`. Rewrite using `[← ih, ← hnj]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨j, hj⟩ : ∃ j : ℕ, a = -(h' : ℤ) - j` from `⟨(-(h' : ℤ) - a).toNat, by omega⟩`. Unfold `Formalism.MainNotions.DeltaInvariantLattices.FilC`.

Rewrite using `[hj, hc j]`.
-/
theorem filC_le_bot (τ : K →ₐ[Qp] LL) (h' : ℕ)
    (hJ : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (a : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  by_cases ha : -(h' : ℤ) ≤ a
  · exact u3upPf_FilC_anti (PD := PD) T τ ha
  · have hc : ∀ j : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - j) = FildR PD T.ρ τ (-(h' : ℤ)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - (j + 1 : ℕ)) := by
          intro hj
          have := (hJ _ hj).1
          push_cast at this
          omega
        unfold IsJumpV at hnj
        push_neg at hnj
        rw [← ih, ← hnj]
        congr 1
        push_cast
        ring
    obtain ⟨j, hj⟩ : ∃ j : ℕ, a = -(h' : ℤ) - j := ⟨(-(h' : ℤ) - a).toNat, by omega⟩
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [hj, hc j]

/- English proof (translation)
Establish `hφ : W.φA (letE (O` using `O) i) = letE (i + 1) := by`. Use function extensionality and compare the values at `j`. Simplify using `only [LocWach.φA, letφ]`. Distinguish the cases in `h : j = i + 1`. Substitute `h` using the available equality.

Simplify using `[letE]`. Establish `h' : j - 1 ≠ i` using `fun h'' => h (by rw [← h'']; ring)`. Simplify using `[letE, h, h']`. Rewrite using `[← hφ, ← algebraMap_smul W.EE (W.φA (letE i)) (W.φD T x)]`. Establish `h : algebraMap (LetA O n) W.EE (W.φA (letE (O` using `O) i)) = W.φE (algebraMap (LetA O n) W.EE (letE i)) := (W.φE_ext _).symm`.

Rewrite using `[h, ← W.φD_smul, algebraMap_smul, hx]`.
-/
theorem φD_letter' {i : ZMod n} {x : W.DD T} (hx : (letE (O := O) i : LetA O n) • x = x) :
    (letE (O := O) (i + 1) : LetA O n) • W.φD T x = W.φD T x := by
  have hφ : W.φA (letE (O := O) i) = letE (i + 1) := by
    funext j
    simp only [LocWach.φA, letφ]
    by_cases h : j = i + 1
    · subst h
      simp [letE]
    · have h' : j - 1 ≠ i := fun h'' => h (by rw [← h'']; ring)
      simp [letE, h, h']
  rw [← hφ, ← algebraMap_smul W.EE (W.φA (letE i)) (W.φD T x)]
  have h : algebraMap (LetA O n) W.EE (W.φA (letE (O := O) i)) =
      W.φE (algebraMap (LetA O n) W.EE (letE i)) := (W.φE_ext _).symm
  rw [h, ← W.φD_smul, algebraMap_smul, hx]

end Generic

end Formalism.MainNotions.N.Ln34.MLC

end
