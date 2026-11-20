import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEmbeddedDataWithGivenFixedLattice
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

/- English proof (translation)
Apply `Module.finrank_le_of_rank_le` to reduce the goal to its premises. Apply `rank_le` to reduce the goal to its premises. Introduce `s hs`. Establish `h` using `hs.map' L.subtype (Submodule.ker_subtype L)`. Rewrite `h` using `[LinearIndependent.iff_fractionRing (R := 𝓞 K) (K := K)]`.

Simplify using `using h.fintype_card_le_finrank`.
-/
theorem finrank_sub_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) L ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  apply rank_le
  intro s hs
  have h := hs.map' L.subtype (Submodule.ker_subtype L)
  rw [LinearIndependent.iff_fractionRing (R := 𝓞 K) (K := K)] at h
  simpa using h.fintype_card_le_finrank

/- English proof (translation)
Establish `: Module.Finite (𝓞 K) L` using `Module.Finite.iff_fg.2 hL`. Establish `: Module.IsTorsionFree (𝓞 K) V` using `Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V`. Establish `: Module.Flat (𝓞 K) L` using `inferInstance`. Establish `: Module.FinitePresentation (𝓞 K) L` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective (𝓞 K) L` using `Module.Flat.projective_of_finitePresentation`.

Take `⟨h1, h2⟩` from `Formalism.SLP.Final.submoduleIndexCountO K L x hx`. Establish `hsub : {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x} ⊆ (Submodule.map L.subtype) '' {N : Submodule (𝓞 K) L | N.toAddSubgroup.index = x}`. Introduce and unpack `N ⟨hN, hi⟩`. Use `⟨N.comap L.subtype, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hi`.

Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.2 hN]`. Use `⟨(h1.image _).subset hsub, ?_⟩` and prove the remaining obligations. Establish `h3` using `(Set.ncard_le_ncard hsub (h1.image _)).trans (Set.ncard_image_le h1)`. Establish `hx1 : (1 : ℝ) ≤ x` using `by exact_mod_cast hx`. Establish `hx0 : (0 : ℝ) < x` using `by linarith`.

Establish `h4` using `Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x Module.finrank_pos hx`. Establish `h5 : ((Module.finrank (𝓞 K) L : ℕ) : ℝ) ≤ (Module.finrank K V : ℝ)`. Conclude with `finrank_sub_le L` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Conclude with `h3.trans h2` after adjusting the coercions.

Use `_ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) L := mul_le_mul_of_nonneg_right h4 (by positivity)`. Use `_ = (x : ℝ) ^ (((Module.finrank (𝓞 K) L : ℕ) : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by`. Rewrite using `[Real.rpow_add hx0, Real.rpow_natCast, mul_comm]`. Use `_ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)`.
-/
theorem sublat_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG) (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.Finite ∧
      (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) L := inferInstance
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K L x hx
  have hsub : {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x} ⊆
      (Submodule.map L.subtype) '' {N : Submodule (𝓞 K) L | N.toAddSubgroup.index = x} := by
    rintro N ⟨hN, hi⟩
    refine ⟨N.comap L.subtype, ?_, ?_⟩
    · exact hi
    · rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  refine ⟨(h1.image _).subset hsub, ?_⟩
  have h3 := (Set.ncard_le_ncard hsub (h1.image _)).trans (Set.ncard_image_le h1)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x Module.finrank_pos hx
  have h5 : ((Module.finrank (𝓞 K) L : ℕ) : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast finrank_sub_le L
  calc (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ)
      ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ Module.finrank (𝓞 K) L := by
        exact_mod_cast h3.trans h2
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) L :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ (((Module.finrank (𝓞 K) L : ℕ) : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x hx`. Establish `hfib` using `GlobalTheory.DegCnt.DatCount.main K V H hK hP L₀ g j D₀ hL hD hG hg`. Take `⟨hfin, hcnt⟩` from `sublat_count L₀ hL.1.fg x hx`. Use `set S := {N : Submodule (𝓞 K) V | N ≤ L₀ ∧ idx L₀ N = x} with hS`. Establish `hsub : {d | IsDat H g L₀ j x d} ⊆ ⋃ La ∈ hfin.toFinset, {d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}`.

Introduce `d hd`. Simplify using `only [Set.mem_iUnion, Set.Finite.mem_toFinset]`. Use `⟨fixLat d.2, ⟨?_, hd.2.2.2.1⟩, hd, rfl⟩` and prove the remaining obligations. Introduce `y hy`. Conclude with `(hd.2.2.1.1 hy).2`.

Establish `h1` using `(Set.encard_le_encard hsub).trans (Finset.set_encard_biUnion_le _ _)`. Establish `h2 : ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ∑ La ∈ hfin.toFinset, ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞)`. Use `(ENat.toENNReal_le.2 h1).trans (le_of_eq ?_)` and prove the remaining obligations. Conclude with `map_sum ENat.toENNRealRingHom _ _`. Use `h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun La _ => hfib La x).trans ?_)` and prove the remaining obligations.

Rewrite using `[nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]`. Use `gcongr`. Rewrite using `[← ENNReal.ofReal_natCast, ← Set.ncard_eq_toFinset_card S hfin]`. Conclude with `ENNReal.ofReal_le_ofReal hcnt`.
-/
theorem encard_isDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  intro K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x hx
  have hfib := GlobalTheory.DegCnt.DatCount.main K V H hK hP L₀ g j D₀ hL hD hG hg
  obtain ⟨hfin, hcnt⟩ := sublat_count L₀ hL.1.fg x hx
  set S := {N : Submodule (𝓞 K) V | N ≤ L₀ ∧ idx L₀ N = x} with hS
  have hsub : {d | IsDat H g L₀ j x d} ⊆
      ⋃ La ∈ hfin.toFinset, {d | IsDat H g L₀ j x d ∧ fixLat d.2 = La} := by
    intro d hd
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    refine ⟨fixLat d.2, ⟨?_, hd.2.2.2.1⟩, hd, rfl⟩
    intro y hy
    exact (hd.2.2.1.1 hy).2
  have h1 := (Set.encard_le_encard hsub).trans (Finset.set_encard_biUnion_le _ _)
  have h2 : ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤
      ∑ La ∈ hfin.toFinset, ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) := by
    refine (ENat.toENNReal_le.2 h1).trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun La _ => hfib La x).trans ?_)
  rw [nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  gcongr
  rw [← ENNReal.ofReal_natCast, ← Set.ncard_eq_toFinset_card S hfin]
  exact ENNReal.ofReal_le_ofReal hcnt

end GlobalTheory.DegCnt
