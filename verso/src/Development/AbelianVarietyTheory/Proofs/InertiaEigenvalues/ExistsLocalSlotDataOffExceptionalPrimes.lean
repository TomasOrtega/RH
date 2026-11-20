import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntPts
import Formalism.PadicSubsetSums.StableGradedCounts.TOPSgLe
import Formalism.PadicSubsetSums.StableGradedCounts.TOPSgRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShiftedJumpUpperBoundLeTwistBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpSlotConditionsAtLetterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimeThresholdNumericsAlongFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowJumpsAndCloudInWindowsAlongFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParametersBaseSizeBoundsAlongFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorPrimesLtSpecialPrimeThresholdEventuallyStatement

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.LocalPositionData

/- English proof (translation)
Introduce `eps Fm`. Take `⟨x0, hx0⟩` from `GlobalTheory.T.conductorPrimes_lt_specialPrimeThreshold_eventually Fm`. Use `⟨x0, fun x hx hx1 a _ l hl hlS => ?_⟩` and prove the remaining obligations. Take `⟨hqS, hdS, hsS⟩` from `hx0 x hx hx1 a`. Take `⟨htη, hη, hB, hSc, hls1, hls2, hH⟩` from `GlobalTheory.T.specialPrimeThreshold_numerics_along_family Fm x hx1 a`.

Establish `ht1 : 1 ≤ (Fm.D x a).R.t`. Use `(Fm.D x a).R.rank_add_five_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `htR : (0 : ℝ) ≤ (Fm.D x a).R.t` using `by positivity`. Use `⟨⟨?_, ?_, ?_, ?_, fun h => absurd (hsS l h) (not_lt.2 hlS.le)⟩, ?_⟩` and prove the remaining obligations.

Establish `: (7 : ℝ) < l` using `by linarith`. Conclude with `(show 5 ≤ l by exact_mod_cast (show (5 : ℝ) ≤ l by linarith))` after adjusting the coercions. Establish `: ((Fm.D x a).R.t : ℝ) + 1 < l` using `by linarith`. Conclude with `this` after adjusting the coercions. Introduce `h`.

Rewrite `hlS` using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`. Rewrite `hlS` using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `hexc j hj1 hjm n _ up τ`. Establish `hfinL : ∀ c, (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)).Finite`. Introduce `c`. Establish `h0 : (AdmissibleParameterJ.lowJ (Fm.D x a) j (τ c)).Finite` using `(Set.finite_range (fun i : Fin (Fm.D x a).R.m => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) - ((Fm.D x a).hc (τ c)).b i + AdmissibleParameterJ.c0 (Fm.D x a))).subset (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)`. Unfold `AdmissibleParameterJ.lowT`.

Use `split_ifs`. Conclude with `h0`. Conclude with `h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))`. Establish `hfinC : ∀ c, (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)).Finite`. Introduce `c`.

Establish `h0 : (AdmissibleParameterJ.cloudJ (Fm.D x a) j (τ c)).Finite` using `(Set.finite_range (fun i : Fin ((Fm.D x a).R.k - 1) => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) + ((Fm.D x a).hc (τ c)).v i + AdmissibleParameterJ.c0 (Fm.D x a))).subset (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)`. Unfold `AdmissibleParameterJ.cloudT`. Use `split_ifs`. Conclude with `h0`. Conclude with `h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))`.

Use `set Fl : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)) with hFl`. Use `set Fc : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)) with hFc`. Establish `hdat : ∀ c, ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a), (∀ z ∈ Fl c, |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧ 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤ |(z : ℝ) - (((Fm.D …`. Introduce `c`. Take `⟨hlo, W0, hW0, hcl⟩` from `GlobalTheory.T.lowJumps_and_cloud_in_windows_along_family Fm x hx1 a j hj1 hjm (up c) (τ c)`.

Use `⟨W0, hW0, fun z hz => hlo z ((GlobalTheory.PositionData.mem_intPts (hfinL c) z).1 hz), fun z hz => hcl z ((GlobalTheory.PositionData.mem_intPts (hfinC c) z).1 hz)⟩` and prove the remaining obligations. Use `set hh : ZMod n → ℕ := fun c => GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) with hhh`. Establish `hhle : ∀ c, (hh c : ℝ) ≤ (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3`. Introduce `c`. Take `⟨W0, hW0, hlo, hcl⟩` from `hdat c`.

Take `⟨hW1, hW2⟩` from `GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0`. Use `GlobalTheory.T.shiftedJumpUpperBound_le_twist_bound (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 ht1 htη hB hSc hlo hcl hW1` as an intermediate fact. Use `show ((GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) : ℕ) : ℝ) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsg : ∀ c, (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) ≤ 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a))`.

Introduce `c`. Establish `hl2 : 2 ≤ l` using `hl.two_le`. Use `set W := (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 with hW`. Establish `hW0 : 0 ≤ W` using `le_trans (Nat.cast_nonneg _) (hhle c)`. Establish `h1` using `Formalism.IrreducibleCountingLemmas.TOP.carryFloorLeGeom n l hh ⌊W⌋₊ hl2 (fun c' => Nat.le_floor (hhle c')) c`.

Establish `h2 : ((⌊W⌋₊ : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ W / ((l : ℝ) - 1)`. Apply `div_le_div_of_nonneg_right (Nat.floor_le hW0)` to reduce the goal to its premises. Establish `: (2 : ℝ) ≤ l` using `by exact_mod_cast hl2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `Formalism.IrreducibleCountingLemmas.TOP.geomRatioBound l (LevelStarExponents.lStar (Fm.L x a)) (Fm.L x a).sc.b W hW0 hls1 hlS hH`.

Establish `h4 : (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) = (Formalism.IrreducibleCountingLemmas.TOP.sg n l hh c : ℝ)` using `rfl`. Rewrite using `[h4, ← mul_div_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hh, fun c => GlobalTheory.PositionData.wS (up c) (Fl c) (Fc c), fun c => GlobalTheory.PositionData.etaS (Fm.D x a).R.t (Fl c), up, fun c => GlobalTheory.PositionData.US (up c) (Fl c) (Fc c), ?_, ?_⟩` and prove the remaining obligations. Introduce `c`.

Take `⟨W0, hW0, hlo, hcl⟩` from `hdat c`. Take `⟨hW1, -⟩` from `GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0`. Establish `hex : ∀ m : ℤ, W0 + (-(Fm.L x a).etaSz - 2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) - 3) ≤ (m : ℝ) → (m : ℝ) ≤ W0 + ((Fm.L x a).Sc + (Fm.L x a).etaSz + (Fm.L x a).etaSz + 2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : …` using `fun m h1 h2 hd => hexc ⟨hl, hlS, W0, hW0, m, ⟨h1, h2⟩, hd⟩`. Establish `hσP : Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a)`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus`.

Apply `Int.le_floor.mpr` to reduce the goal to its premises. Rewrite using `[mul_div_assoc]`. Conclude with `hsg c`. Establish `hT1 : 2 * (Fm.L x a).etaSz + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < (l : ℝ)` using `by linarith`. Conclude with `GlobalTheory.T.jump_position_conditions_at_letter l (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a)) (Formalism.MainNotions.tableLine …`.

Introduce `c b`. Rewrite using `[GlobalTheory.PositionData.count_US]`. Establish `hm : b ∈ Fl c ∪ Fc c ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)`. Rewrite using `[Finset.mem_union, GlobalTheory.PositionData.mem_intPts (hfinL c), GlobalTheory.PositionData.mem_intPts (hfinC c)]`. Unfold `AdmissibleParameterJ.JW`.

Rewrite using `[Set.mem_union]`. The claim follows by propositional logic. Rewrite using `[← hm]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem position_data_exist : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.conductorPrimes_lt_specialPrimeThreshold_eventually Fm
  refine ⟨x0, fun x hx hx1 a _ l hl hlS => ?_⟩
  obtain ⟨hqS, hdS, hsS⟩ := hx0 x hx hx1 a
  obtain ⟨htη, hη, hB, hSc, hls1, hls2, hH⟩ := GlobalTheory.T.specialPrimeThreshold_numerics_along_family Fm x hx1 a
  have ht1 : 1 ≤ (Fm.D x a).R.t := by
    have := (Fm.D x a).R.rank_add_five_le; omega
  have htR : (0 : ℝ) ≤ (Fm.D x a).R.t := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_, fun h => absurd (hsS l h) (not_lt.2 hlS.le)⟩, ?_⟩
  · have : (7 : ℝ) < l := by linarith
    exact_mod_cast (show 5 ≤ l by exact_mod_cast (show (5 : ℝ) ≤ l by linarith))
  · have : ((Fm.D x a).R.t : ℝ) + 1 < l := by linarith
    exact_mod_cast this
  · intro h; rw [h] at hlS; linarith
  · intro h; rw [h] at hlS; linarith
  intro hexc j hj1 hjm n _ up τ
  have hfinL : ∀ c, (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.lowJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin (Fm.D x a).R.m => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) - ((Fm.D x a).hc (τ c)).b i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.lowT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  have hfinC : ∀ c, (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.cloudJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin ((Fm.D x a).R.k - 1) => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) + ((Fm.D x a).hc (τ c)).v i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.cloudT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  set Fl : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)) with hFl
  set Fc : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)) with hFc
  have hdat : ∀ c, ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
      (∀ z ∈ Fl c, |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
        2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
          |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
      (∀ z ∈ Fc c, W0 ≤ (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
        (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
          W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1) := by
    intro c
    obtain ⟨hlo, W0, hW0, hcl⟩ := GlobalTheory.T.lowJumps_and_cloud_in_windows_along_family Fm x hx1 a j hj1 hjm (up c) (τ c)
    refine ⟨W0, hW0, fun z hz => hlo z ((GlobalTheory.PositionData.mem_intPts (hfinL c) z).1 hz),
      fun z hz => hcl z ((GlobalTheory.PositionData.mem_intPts (hfinC c) z).1 hz)⟩
  set hh : ZMod n → ℕ := fun c => GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) with hhh
  have hhle : ∀ c, (hh c : ℝ) ≤ (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 := by
    intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, hW2⟩ := GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0
    have := GlobalTheory.T.shiftedJumpUpperBound_le_twist_bound (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 ht1 htη hB hSc hlo hcl hW1
    show ((GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) : ℕ) : ℝ) ≤ _
    linarith
  have hsg : ∀ c, (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) ≤ 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) := by
    intro c
    have hl2 : 2 ≤ l := hl.two_le
    set W := (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 with hW
    have hW0 : 0 ≤ W := le_trans (Nat.cast_nonneg _) (hhle c)
    have h1 := Formalism.IrreducibleCountingLemmas.TOP.carryFloorLeGeom n l hh ⌊W⌋₊ hl2 (fun c' => Nat.le_floor (hhle c')) c
    have h2 : ((⌊W⌋₊ : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ W / ((l : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right (Nat.floor_le hW0)
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      linarith
    have h3 := Formalism.IrreducibleCountingLemmas.TOP.geomRatioBound l (LevelStarExponents.lStar (Fm.L x a)) (Fm.L x a).sc.b W hW0 hls1 hlS hH
    have h4 : (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) = (Formalism.IrreducibleCountingLemmas.TOP.sg n l hh c : ℝ) := rfl
    rw [h4, ← mul_div_assoc]
    linarith
  refine ⟨hh, fun c => GlobalTheory.PositionData.wS (up c) (Fl c) (Fc c), fun c => GlobalTheory.PositionData.etaS (Fm.D x a).R.t (Fl c),
    up, fun c => GlobalTheory.PositionData.US (up c) (Fl c) (Fc c), ?_, ?_⟩
  · intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, -⟩ := GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0
    have hex : ∀ m : ℤ, W0 + (-(Fm.L x a).etaSz - 2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) - 3) ≤ (m : ℝ) →
        (m : ℝ) ≤ W0 + ((Fm.L x a).Sc + (Fm.L x a).etaSz + (Fm.L x a).etaSz +
          2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) + 4) → ¬ (l : ℤ) ∣ m :=
      fun m h1 h2 hd => hexc ⟨hl, hlS, W0, hW0, m, ⟨h1, h2⟩, hd⟩
    have hσP : Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus
      apply Int.le_floor.mpr
      rw [mul_div_assoc]; exact hsg c
    have hT1 : 2 * (Fm.L x a).etaSz + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < (l : ℝ) := by linarith
    exact GlobalTheory.T.jump_position_conditions_at_letter l (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a)) (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c)
      ht1 htη hB hSc hlo hcl hW1 hex (hsg c) hσP hT1
  · intro c b
    rw [GlobalTheory.PositionData.count_US]
    have hm : b ∈ Fl c ∪ Fc c ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c) := by
      rw [Finset.mem_union, GlobalTheory.PositionData.mem_intPts (hfinL c), GlobalTheory.PositionData.mem_intPts (hfinC c)]
      unfold AdmissibleParameterJ.JW
      rw [Set.mem_union]; tauto
    rw [← hm]
    split_ifs <;> simp_all

end GlobalTheory.LocalPositionData
