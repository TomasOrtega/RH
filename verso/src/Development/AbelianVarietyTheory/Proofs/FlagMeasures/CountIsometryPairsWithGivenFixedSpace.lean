import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEmbeddedDataWithGivenFixedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedLatticeInfEqAndPairingOfIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantOrderCommonFixedLatticeEmbeddedDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesIndexFixedTraceLeStatement
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.FixedSpaceCount

/- English proof (translation)
Establish `hS : S = ⋃ t : T, {s ∈ S | f s = t}`. Use extensionality with `s`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`. Conclude with `⟨fun h => ⟨⟨f s, hm s h⟩, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hS, ENNReal.tsum_set_one]`. Use `_ ≤ ∑' t : T, ∑' _ : ({s ∈ S | f s = t} : Set α), (1 : ℝ≥0∞) := ENNReal.tsum_iUnion_le_tsum (fun _ => 1) _`. Use `_ ≤ ∑' _ : T, b := ENNReal.tsum_le_tsum fun t => by`. Rewrite using `[ENNReal.tsum_set_one]`. Conclude with `hb t t.2`.

Use `_ = ((T.encard : ℕ∞) : ℝ≥0∞) * b := ENNReal.tsum_set_const _ _`. Use `_ ≤ a * b := by gcongr`.
-/
theorem encard_le_mul {α β : Type*} (S : Set α) (T : Set β) (f : α → β) (a b : ℝ≥0∞)
    (hm : ∀ s ∈ S, f s ∈ T) (hT : ((T.encard : ℕ∞) : ℝ≥0∞) ≤ a)
    (hb : ∀ t ∈ T, ((({s ∈ S | f s = t}).encard : ℕ∞) : ℝ≥0∞) ≤ b) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ a * b := by
  have hS : S = ⋃ t : T, {s ∈ S | f s = t} := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨⟨f s, hm s h⟩, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  calc ((S.encard : ℕ∞) : ℝ≥0∞) = ∑' _ : (⋃ t : T, {s ∈ S | f s = t} : Set α), (1 : ℝ≥0∞) := by
        rw [← hS, ENNReal.tsum_set_one]
    _ ≤ ∑' t : T, ∑' _ : ({s ∈ S | f s = t} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_iUnion_le_tsum (fun _ => 1) _
    _ ≤ ∑' _ : T, b := ENNReal.tsum_le_tsum fun t => by
        rw [ENNReal.tsum_set_one]; exact hb t t.2
    _ = ((T.encard : ℕ∞) : ℝ≥0∞) * b := ENNReal.tsum_set_const _ _
    _ ≤ a * b := by gcongr

section

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] in

/- English proof (translation)
Apply `Module.finrank_le_of_rank_le` to reduce the goal to its premises. Rewrite using `[Module.finrank_eq_rank, IsLocalization.rank_eq K (𝓞 K)⁰ le_rfl]`. Conclude with `Submodule.rank_le N`.
-/
theorem finrank_le [NumberField K] (N : Submodule (𝓞 K) V) : Module.finrank (𝓞 K) N ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  rw [Module.finrank_eq_rank, IsLocalization.rank_eq K (𝓞 K)⁰ le_rfl]
  exact Submodule.rank_le N

/- English proof (translation)
Establish `h : (1 : ℝ) ≤ Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Use `Real.logb_nonneg (b := 2) one_lt_two h` as an intermediate fact. Unfold `cf`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cf_nonneg (K : Type) [Field K] [NumberField K] : 0 ≤ cf K := by
  have h : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have := Real.logb_nonneg (b := 2) one_lt_two h
  unfold cf
  linarith

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.2 hN`. Use `haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V`. Use `haveI : Module.Projective (𝓞 K) N := by haveI : Module.FinitePresentation (𝓞 K) N := Module.finitePresentation_of_finite _ _`. Conclude with `Module.Flat.projective_of_finitePresentation`. Establish `hf : Module.finrank ℚ K = 2 * InfinitePlace.nrComplexPlaces K` using `IsTotallyComplex.finrank K`.

Take `⟨hfin, hc⟩` from `Formalism.HermitianLatticeCounting.P.sublattice_count_alt K N _ y hf hy`. Establish `h1 : ({M : Submodule (𝓞 K) V | M ≤ N ∧ GlobalTheory.Mass.idxN N M = y}).encard ≤ ({M : Submodule (𝓞 K) N | M.toAddSubgroup.index = y}).encard`. Use `Set.encard_le_encard_of_injOn (f := fun M => M.comap N.subtype) ?_ ?_` and prove the remaining obligations. Introduce and unpack `M ⟨-, h⟩`. Conclude with `h`.

Introduce and unpack `M ⟨h, -⟩ M' ⟨h', -⟩ e`. Use `congrArg (Submodule.map N.subtype) e` as an intermediate fact. Simplify `this` using `[Submodule.map_comap_subtype, inf_eq_right.2 h, inf_eq_right.2 h']`. Use `(ENat.toENNReal_le.2 h1).trans ?_` and prove the remaining obligations. Rewrite using `[← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]`.

Use `ENNReal.ofReal_le_ofReal (hc.trans ?_)` and prove the remaining obligations. Establish `e : (1 + Real.logb 2 (2 * (InfinitePlace.nrComplexPlaces K : ℝ))) = cf K`. Unfold `cf`. Rewrite using `[hf]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[e]`. Use `Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hy) ?_` and prove the remaining obligations. Establish `: (Module.finrank (𝓞 K) N : ℝ) ≤ Module.finrank K V` using `by exact_mod_cast finrank_le N`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sub_count [IsTotallyComplex K] (N : Submodule (𝓞 K) V) (hN : N.FG) (y : ℕ) (hy : 1 ≤ y) :
    ((({M : Submodule (𝓞 K) V | M ≤ N ∧ GlobalTheory.Mass.idxN N M = y}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((y : ℝ) ^ ((Module.finrank K V : ℝ) + cf K)) := by
  haveI : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.2 hN
  haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  haveI : Module.Projective (𝓞 K) N := by
    haveI : Module.FinitePresentation (𝓞 K) N := Module.finitePresentation_of_finite _ _
    exact Module.Flat.projective_of_finitePresentation
  have hf : Module.finrank ℚ K = 2 * InfinitePlace.nrComplexPlaces K := IsTotallyComplex.finrank K
  obtain ⟨hfin, hc⟩ := Formalism.HermitianLatticeCounting.P.sublattice_count_alt K N _ y hf hy
  have h1 : ({M : Submodule (𝓞 K) V | M ≤ N ∧ GlobalTheory.Mass.idxN N M = y}).encard ≤
      ({M : Submodule (𝓞 K) N | M.toAddSubgroup.index = y}).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun M => M.comap N.subtype) ?_ ?_
    · rintro M ⟨-, h⟩
      exact h
    · rintro M ⟨h, -⟩ M' ⟨h', -⟩ e
      have := congrArg (Submodule.map N.subtype) e
      simpa [Submodule.map_comap_subtype, inf_eq_right.2 h, inf_eq_right.2 h'] using this
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal (hc.trans ?_)
  have e : (1 + Real.logb 2 (2 * (InfinitePlace.nrComplexPlaces K : ℝ))) = cf K := by
    unfold cf; rw [hf]; push_cast; rfl
  rw [e]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hy) ?_
  have : (Module.finrank (𝓞 K) N : ℝ) ≤ Module.finrank K V := by exact_mod_cast finrank_le N
  linarith

omit [FiniteDimensional K V] in

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL.fg`. Conclude with `Submodule.FG.of_le_of_isNoetherian hM`. Rewrite using `[eq_top_iff, ← hL.span_eq_top, Submodule.span_le]`. Introduce `v hv`.

Establish `h1 : idx L M • v ∈ M` using `AddSubgroup.nsmul_relIndex_mem M.toAddSubgroup (K := L.toAddSubgroup) hv`. Establish `h2 : ((idx L M : K)⁻¹) • (idx L M • v) = v`. Rewrite using `[← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (by exact_mod_cast h), one_smul]`. Rewrite using `[← h2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`.
-/
theorem isLattice_of_idx {L M : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hM : M ≤ L)
    (h : idx L M ≠ 0) : Submodule.IsLattice K M := by
  refine ⟨?_, ?_⟩
  · haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL.fg
    exact Submodule.FG.of_le_of_isNoetherian hM
  · rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro v hv
    have h1 : idx L M • v ∈ M := AddSubgroup.nsmul_relIndex_mem M.toAddSubgroup (K := L.toAddSubgroup) hv
    have h2 : ((idx L M : K)⁻¹) • (idx L M • v) = v := by
      rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (by exact_mod_cast h), one_smul]
    rw [← h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

omit [FiniteDimensional K V] [NumberField K] in

/- English proof (translation)
Establish `e : GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) = (M.toAddSubgroup.comap U.subtype.toAddMonoidHom).relIndex (L.toAddSubgroup.comap U.subtype.toAddMonoidHom)` using `rfl`. Rewrite using `[e, AddSubgroup.relIndex_comap]`. Conclude with `AddSubgroup.relIndex_le_of_le_right (AddSubgroup.map_comap_le _ _) h`.
-/
theorem idx_latIn_le (U : Submodule K V) (L M : Submodule (𝓞 K) V) (h : idx L M ≠ 0) :
    GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ≤ idx L M := by
  have e : GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) =
      (M.toAddSubgroup.comap U.subtype.toAddMonoidHom).relIndex
        (L.toAddSubgroup.comap U.subtype.toAddMonoidHom) := rfl
  rw [e, AddSubgroup.relIndex_comap]
  exact AddSubgroup.relIndex_le_of_le_right (AddSubgroup.map_comap_le _ _) h

omit [FiniteDimensional K V] [NumberField K] in

/- English proof (translation)
Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨v, h2⟩, h1, rfl⟩`. Introduce and unpack `⟨w, hw, rfl⟩`.

Conclude with `⟨hw, w.2⟩`.
-/
theorem inf_eq_map (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    M ⊓ rs (𝓞 K) U = (GlobalTheory.Mass.latIn U M).map (U.subtype.restrictScalars (𝓞 K)) := by
  ext v
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨v, h2⟩, h1, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.2⟩

variable [StarRing K]

omit [FiniteDimensional K V] in

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `key : ∀ x : U, GlobalTheory.Mass.hRes h U x x = 0 → x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Use `hP τ x (fun e => hne (Subtype.ext e))` as an intermediate fact.

Establish `e : h x x = 0` using `hx`. Rewrite `this` using `[e]`. Simplify using `at this`. Conclude with `⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩`.
-/
theorem hRes_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hP : GlobalTheory.Mass.PD h) (U : Submodule K V) :
    (GlobalTheory.Mass.hRes h U).Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x : U, GlobalTheory.Mass.hRes h U x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have := hP τ x (fun e => hne (Subtype.ext e))
    have e : h x x = 0 := hx
    rw [e] at this
    simp at this
  exact ⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩

omit [FiniteDimensional K V] in

/- English proof (translation)
Introduce `_ hv` and use `(hd.2.2.1.1 hv).2`.
-/
theorem fixLat_le {H : HermSpace K V} {g : ℕ} {L₀ : Submodule (𝓞 K) V} {j x : ℕ}
    {d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)} (hd : IsDat H g L₀ j x d) : fixLat d.2 ≤ L₀ :=
  fun _ hv => (hd.2.2.1.1 hv).2

/- English proof (translation)
Establish `hM' : GlobalTheory.Mass.IsIntLat H.B.flip M` using `⟨isLattice_of_idx hL.1 hM h, fun x hx y hy => hL.2 x (hM hx) y (hM hy)⟩`. Establish `hs : (GlobalTheory.Mass.hRes H.B.flip U).IsSymm` using `⟨fun x y => H.herm y x⟩`. Conclude with `(GlobalTheory.Mass.DiscOrder.main K U _ hK hs (hRes_nondeg _ hP U) _ (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hM' U)).2.2.1 _ (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hL U) (Submodule.comap_mono hM)`.
-/
theorem disc_trace (H : HermSpace K V) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hP : GlobalTheory.Mass.PD H.B.flip)
    {L M : Submodule (𝓞 K) V} (hL : GlobalTheory.Mass.IsIntLat H.B.flip L) (hM : M ≤ L) (h : idx L M ≠ 0)
    (U : Submodule K V) :
    GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ≠ 0 ∧
    GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U M) =
      GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L) *
        GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ^ 2 := by
  have hM' : GlobalTheory.Mass.IsIntLat H.B.flip M :=
    ⟨isLattice_of_idx hL.1 hM h, fun x hx y hy => hL.2 x (hM hx) y (hM hy)⟩
  have hs : (GlobalTheory.Mass.hRes H.B.flip U).IsSymm := ⟨fun x y => H.herm y x⟩
  exact (GlobalTheory.Mass.DiscOrder.main K U _ hK hs (hRes_nondeg _ hP U) _
    (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hM' U)).2.2.1 _ (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hL U)
    (Submodule.comap_mono hM)

/- English proof (translation)
Use `haveI : IsTotallyComplex K := hK.1`. Use `encard_le_mul _ _ (fun d => fixLat d.2) _ _ ?_ (GlobalTheory.T.encard_sublattices_index_fixed_trace_le K V L₀ M U x hL.1 hx) ?_` and prove the remaining obligations. Introduce and unpack `d ⟨hd, hM⟩`. Conclude with `⟨fixLat_le hd, hd.2.2.2.1, hM⟩`. Introduce `La _`.

Use `le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) (GlobalTheory.T.card_embeddedData_with_given_fixedLattice K V H hK hP L₀ g j D₀ hL hD hG hg La x)` and prove the remaining obligations. Introduce and unpack `d ⟨⟨hd, -⟩, h⟩`. Conclude with `⟨hd, h⟩`.
-/
theorem dat_count (H : HermSpace K V) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hP : GlobalTheory.Mass.PD H.B.flip)
    (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ) (hL : GlobalTheory.Mass.IsIntLat H.B.flip L₀)
    (hD : GlobalTheory.Mass.discN H.B.flip L₀ = D₀) (hG : GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1) (hg : 2 ≤ g)
    (x : ℕ) (hx : 1 ≤ x) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) *
        ((x : ℝ≥0∞) * D₀) ^ (3 * (2 * j + 1)) := by
  haveI : IsTotallyComplex K := hK.1
  refine encard_le_mul _ _ (fun d => fixLat d.2) _ _ ?_ (GlobalTheory.T.encard_sublattices_index_fixed_trace_le K V L₀ M U x hL.1 hx) ?_
  · rintro d ⟨hd, hM⟩
    exact ⟨fixLat_le hd, hd.2.2.2.1, hM⟩
  · intro La _
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_))
      (GlobalTheory.T.card_embeddedData_with_given_fixedLattice K V H hK hP L₀ g j D₀ hL hD hG hg La x)
    rintro d ⟨⟨hd, -⟩, h⟩
    exact ⟨hd, h⟩

end

/- English proof (translation)
Establish `hy1 : (1 : ℝ) ≤ y` using `by exact_mod_cast hy`. Establish `hn1 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hx1 : (y : ℝ) ≤ x` using `by exact_mod_cast hx`. Establish `hx2 : (1 : ℝ) ≤ x'` using `by exact_mod_cast hx'`. Rewrite using `[Real.rpow_add (by linarith)]`.

Establish `h1 : (y : ℝ) ^ (u : ℝ) ≤ (A / n) ^ ((k : ℝ) / 2)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (A / n) ^ ((k : ℝ) / 2) := by`. Use `Real.rpow_le_rpow (by positivity) ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hn1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : (y : ℝ) ^ c ≤ ((x : ℝ) * x') ^ c` using `Real.rpow_le_rpow (by linarith) (by nlinarith) hc`. Conclude with `mul_le_mul h1 h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (y : ℝ) ^ (u : ℝ)).trans h1)`.
-/
theorem pow_bound (A c : ℝ) (n y x x' u k : ℕ) (hn : 1 ≤ n) (hy : 1 ≤ y) (hx : y ≤ x) (hx' : 1 ≤ x')
    (hu : u ≤ k) (hc : 0 ≤ c) (hA : (n : ℝ) * (y : ℝ) ^ 2 ≤ A) :
    (y : ℝ) ^ ((u : ℝ) + c) ≤ (A / n) ^ ((k : ℝ) / 2) * ((x : ℝ) * x') ^ c := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1 : (y : ℝ) ≤ x := by exact_mod_cast hx
  have hx2 : (1 : ℝ) ≤ x' := by exact_mod_cast hx'
  rw [Real.rpow_add (by linarith)]
  have h1 : (y : ℝ) ^ (u : ℝ) ≤ (A / n) ^ ((k : ℝ) / 2) := by
    calc (y : ℝ) ^ (u : ℝ) ≤ (y : ℝ) ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hy1 (by exact_mod_cast hu)
      _ = ((y : ℝ) ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          congr 1
          push_cast
          ring
      _ ≤ (A / n) ^ ((k : ℝ) / 2) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [le_div_iff₀ hn1]
          linarith
  have h2 : (y : ℝ) ^ c ≤ ((x : ℝ) * x') ^ c :=
    Real.rpow_le_rpow (by linarith) (by nlinarith) hc
  exact mul_le_mul h1 h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (y : ℝ) ^ (u : ℝ)).trans h1)

/- English proof (translation)
Establish `hx1 : (1 : ℝ) ≤ x` using `by exact_mod_cast hx`. Establish `hx2 : (1 : ℝ) ≤ x'` using `by exact_mod_cast hx'`. Establish `e1 : ∀ a : ℕ, ((a : ℝ≥0∞) * D) ^ e = ENNReal.ofReal (((a : ℝ) * D) ^ e)` using `fun a => by`. Rewrite using `[ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]`. Establish `e2 : (C : ℝ≥0∞) ^ C = ENNReal.ofReal ((C : ℝ) ^ C)`.

Rewrite using `[ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]`. Rewrite using `[e1, e1, e2, ← ENNReal.ofReal_natCast x, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `e3 : ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * c + 1) = (x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c * ((x : ℝ) * x')`. Rewrite using `[← Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_add (by positivity), ← Real.rpow_add_one (by positivity)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : ((x : ℝ) * x' * (D : ℝ) ^ 2) ^ e = ((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e`. Rewrite using `[← mul_pow]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, e4]`. Establish `h : (x : ℝ) ≤ x * x'` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_bound (B c : ℝ) (x x' D s e C : ℕ) (hB : 0 ≤ B) (hx : 1 ≤ x) (hx' : 1 ≤ x') :
    (x : ℝ≥0∞) * ENNReal.ofReal (B * ((x : ℝ) * x') ^ c) *
      (ENNReal.ofReal ((x : ℝ) ^ (2 * (s : ℝ) + c)) * ((x : ℝ≥0∞) * D) ^ e *
        (ENNReal.ofReal ((x' : ℝ) ^ (2 * (s : ℝ) + c)) * ((x' : ℝ≥0∞) * D) ^ e * (C : ℝ≥0∞) ^ C)) ≤
    ENNReal.ofReal (B * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * c + 1) * ((x : ℝ) * x' * (D : ℝ) ^ 2) ^ e *
      (C : ℝ) ^ C) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx2 : (1 : ℝ) ≤ x' := by exact_mod_cast hx'
  have e1 : ∀ a : ℕ, ((a : ℝ≥0∞) * D) ^ e = ENNReal.ofReal (((a : ℝ) * D) ^ e) := fun a => by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  have e2 : (C : ℝ≥0∞) ^ C = ENNReal.ofReal ((C : ℝ) ^ C) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  rw [e1, e1, e2, ← ENNReal.ofReal_natCast x, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e3 : ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * c + 1) =
      (x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c * ((x : ℝ) * x') := by
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_add (by positivity),
      ← Real.rpow_add_one (by positivity)]
    congr 1
    ring
  have e4 : ((x : ℝ) * x' * (D : ℝ) ^ 2) ^ e = ((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e := by
    rw [← mul_pow]; congr 1; ring
  rw [e3, e4]
  have h : (x : ℝ) ≤ x * x' := by nlinarith
  calc _ = (B * ((x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c) *
        (((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e) * (C : ℝ) ^ C) * x := by ring
    _ ≤ (B * ((x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c) *
        (((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e) * (C : ℝ) ^ C) * (x * x') := by gcongr
    _ = _ := by ring

/- English proof (translation)
Introduce `hM K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x x' s n U hx hx' hn hs hdisc`. Use `haveI : IsTotallyComplex K := hK.1`. Establish `hsub : Module.finrank K V - Module.finrank K U = s` using `by omega`. Use `set A : ℝ := (2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' with hA`. Use `set N := GlobalTheory.Mass.latIn U L₀ with hN`.

Establish `key : ∀ p ∈ {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U}, GlobalTheory.Mass.latIn U (fixLat p.1.2) ≤ N ∧ 1 ≤ GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) ∧ GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) ≤ x ∧ (n : ℝ) * (GlobalTheory.Mass. …`. Introduce and unpack `p ⟨hp, hU⟩`. Establish `hi : idx L₀ (fixLat p.1.2) = x` using `hp.1.2.2.2.1`. Establish `hi0 : idx L₀ (fixLat p.1.2) ≠ 0` using `by omega`. Take `⟨h1, h2⟩` from `disc_trace H hK hP hL (fixLat_le hp.1) hi0 U`.

Establish `h3` using `GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hP L₀ g j D₀ hL hD hG hg x x' hx hx' p hp`. Rewrite `h3` using `[hU, hsub, h2, hdisc]`. Use `⟨Submodule.comap_mono (fixLat_le hp.1), Nat.one_le_iff_ne_zero.2 h1, hi ▸ idx_latIn_le U _ _ hi0, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at h3`. Conclude with `h3`.

Use `split_ifs with hcase`. Establish `hA0 : 0 ≤ A` using `by positivity`. Use `le_trans ?_ (prod_bound ((A / n) ^ ((Module.finrank K V : ℝ) / 2)) (cf K) x x' D₀ s (3 * (2 * j + 1)) (4 * s * Formalism.HermitianLatticesTheory.fDeg K) (by positivity) hx hx')` and prove the remaining obligations. Use `encard_le_mul _ {M : Submodule (𝓞 K) U | M ≤ N ∧ 1 ≤ GlobalTheory.Mass.idxN N M ∧ GlobalTheory.Mass.idxN N M ≤ x ∧ (n : ℝ) * (GlobalTheory.Mass.idxN N M : ℝ) ^ 2 ≤ A} (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] …` and prove the remaining obligations. Use `encard_le_mul _ {y : ℕ | 1 ≤ y ∧ y ≤ x ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ A} (GlobalTheory.Mass.idxN N) _ _ (fun M h => h.2) ?_ ?_` and prove the remaining obligations.

Establish `h1 : {y : ℕ | 1 ≤ y ∧ y ≤ x ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ A} ⊆ (Finset.Icc 1 x : Finset ℕ)`. Introduce and unpack `y ⟨a, b, -⟩`. Simplify using `[a, b]`. Use `(ENat.toENNReal_le.2 (Set.encard_le_encard h1)).trans ?_` and prove the remaining obligations. Rewrite using `[Set.encard_coe_eq_coe_finsetCard]`.

Simplify using the standard rewrite rules. Introduce and unpack `y ⟨a, b, c⟩`. Establish `hfg : N.FG` using `(GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hL U).1.fg`. Use `le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) ((sub_count N hfg y a).trans (ENNReal.ofReal_le_ofReal (pow_bound A (cf K) n y x x' _ _ hn a b hx' (by omega) (cf_nonneg K) c)))` and prove the remaining obligations. Introduce and unpack `M ⟨h, e⟩`.

Conclude with `⟨h.1, e⟩`. Introduce `M _`. Establish `c1` using `dat_count H hK hP L₀ g j D₀ hL hD hG hg x hx U (M.map (U.subtype.restrictScalars (𝓞 K)))`. Establish `c2` using `dat_count H hK hP L₀ g j D₀ hL hD hG hg x' hx' U (M.map (U.subtype.restrictScalars (𝓞 K)))`. Rewrite `c1`, `c2` using `[hsub]`.

Use `encard_le_mul _ _ (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.1) _ _ ?_ c1 ?_` and prove the remaining obligations. Introduce and unpack `p ⟨⟨hp, -⟩, e⟩`. Conclude with `⟨hp.1, by rw [inf_eq_map, e]⟩`. Introduce `d hd`. Use `encard_le_mul _ _ (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.2.1) _ _ ?_ c2 ?_` and prove the remaining obligations.

Introduce and unpack `p ⟨⟨⟨hp, hU⟩, e⟩, -⟩`. Apply the tactic sequence `have h42 := (GlobalTheory.T.fixedLattice_inf_eq_and_pairing_of_isometry K V H hK hP L₀ g j D₀ hL hD hG hg x x' p hp).1`. Rewrite `h42` using `[hU]`. Conclude with `⟨hp.2.1, by rw [← h42, inf_eq_map, e]⟩`. Introduce `d' hd'`.

Establish `c3` using `GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hP U d'.1 d.1 hd'.1.1.1 hd.1.1.1`. Rewrite `c3` using `[hsub]`. Use `le_trans (ENat.toENNReal_le.2 ?_) c3` and prove the remaining obligations. Use `Set.encard_le_encard_of_injOn (f := fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.2.2) ?_ ?_` and prove the remaining obligations. Introduce and unpack `p ⟨⟨⟨⟨hp, hU⟩, -⟩, e1⟩, e2⟩`.

Use `⟨hp.2.2.1, by rw [← e1, ← e2]; exact hp.2.2.2.1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[← hU]`. Establish `: p.2.2 y - y = 0` using `hy`. Conclude with `sub_eq_zero.1 this`. Introduce and unpack `p ⟨⟨-, e1⟩, e2⟩ q ⟨⟨-, f1⟩, f2⟩ e`.

Conclude with `Prod.ext (e1.trans f1.symm) (Prod.ext (e2.trans f2.symm) e)`. Establish `hempty : {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U} = ∅`. Use `Set.eq_empty_of_forall_notMem fun p hp => hcase ?_` and prove the remaining obligations. Take `⟨-, a, -, c⟩` from `key p hp`. Establish `hg' : (2 : ℝ) ≤ g` using `by exact_mod_cast hg`.

Establish `h1 : (2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) ≤ 1` using `pow_le_one₀ (by positivity) ((div_le_one (by linarith)).2 hg')`. Establish `h2 : A ≤ (D₀ : ℝ) * x * x'`. Combine the equalities or inequalities in the displayed calculation. Establish `a' : (1 : ℝ) ≤ (GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) : ℝ) ^ 2` using `one_le_pow₀ (by exact_mod_cast a)`. Establish `h3 : (0 : ℝ) ≤ n` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hempty]`. Simplify using the standard rewrite rules.
-/
theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' s n : ℕ) (U : Submodule K V), 1 ≤ x → 1 ≤ x' → 1 ≤ n → Module.finrank K U + s = (Module.finrank K V) → GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L₀) = n → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U}).encard : ℕ∞) : ℝ≥0∞) ≤ if (n : ℝ) ≤ (D₀ : ℝ) * x * x' then ENNReal.ofReal (((2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' / n) ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * cf K + 1) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (3 * (2 * j + 1)) * ((4 * s * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * s * (Formalism.HermitianLatticesTheory.fDeg K))) else 0 := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x x' s n U hx hx' hn hs hdisc
  haveI : IsTotallyComplex K := hK.1
  have hsub : Module.finrank K V - Module.finrank K U = s := by omega
  set A : ℝ := (2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' with hA
  set N := GlobalTheory.Mass.latIn U L₀ with hN
  have key : ∀ p ∈ {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U},
      GlobalTheory.Mass.latIn U (fixLat p.1.2) ≤ N ∧ 1 ≤ GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) ∧
      GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) ≤ x ∧
      (n : ℝ) * (GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) : ℝ) ^ 2 ≤ A := by
    rintro p ⟨hp, hU⟩
    have hi : idx L₀ (fixLat p.1.2) = x := hp.1.2.2.2.1
    have hi0 : idx L₀ (fixLat p.1.2) ≠ 0 := by omega
    obtain ⟨h1, h2⟩ := disc_trace H hK hP hL (fixLat_le hp.1) hi0 U
    have h3 := GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hP L₀ g j D₀ hL hD hG hg x x' hx hx' p hp
    rw [hU, hsub, h2, hdisc] at h3
    refine ⟨Submodule.comap_mono (fixLat_le hp.1), Nat.one_le_iff_ne_zero.2 h1,
      hi ▸ idx_latIn_le U _ _ hi0, ?_⟩
    push_cast at h3
    exact h3
  split_ifs with hcase
  · have hA0 : 0 ≤ A := by positivity
    refine le_trans ?_ (prod_bound ((A / n) ^ ((Module.finrank K V : ℝ) / 2)) (cf K) x x' D₀ s (3 * (2 * j + 1))
      (4 * s * Formalism.HermitianLatticesTheory.fDeg K) (by positivity) hx hx')
    refine encard_le_mul _ {M : Submodule (𝓞 K) U | M ≤ N ∧ 1 ≤ GlobalTheory.Mass.idxN N M ∧ GlobalTheory.Mass.idxN N M ≤ x ∧
      (n : ℝ) * (GlobalTheory.Mass.idxN N M : ℝ) ^ 2 ≤ A}
      (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) =>
        GlobalTheory.Mass.latIn U (fixLat p.1.2)) _ _ key ?_ ?_
    · refine encard_le_mul _ {y : ℕ | 1 ≤ y ∧ y ≤ x ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ A} (GlobalTheory.Mass.idxN N) _ _
        (fun M h => h.2) ?_ ?_
      · have h1 : {y : ℕ | 1 ≤ y ∧ y ≤ x ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ A} ⊆ (Finset.Icc 1 x : Finset ℕ) := by
          rintro y ⟨a, b, -⟩
          simp [a, b]
        refine (ENat.toENNReal_le.2 (Set.encard_le_encard h1)).trans ?_
        rw [Set.encard_coe_eq_coe_finsetCard]
        simp
      · rintro y ⟨a, b, c⟩
        have hfg : N.FG := (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hL U).1.fg
        refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) ((sub_count N hfg y a).trans
          (ENNReal.ofReal_le_ofReal (pow_bound A (cf K) n y x x' _ _ hn a b hx' (by omega) (cf_nonneg K) c)))
        rintro M ⟨h, e⟩
        exact ⟨h.1, e⟩
    · intro M _
      have c1 := dat_count H hK hP L₀ g j D₀ hL hD hG hg x hx U (M.map (U.subtype.restrictScalars (𝓞 K)))
      have c2 := dat_count H hK hP L₀ g j D₀ hL hD hG hg x' hx' U (M.map (U.subtype.restrictScalars (𝓞 K)))
      rw [hsub] at c1 c2
      refine encard_le_mul _ _ (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.1) _ _ ?_ c1 ?_
      · rintro p ⟨⟨hp, -⟩, e⟩
        exact ⟨hp.1, by rw [inf_eq_map, e]⟩
      intro d hd
      refine encard_le_mul _ _ (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.2.1) _ _ ?_ c2 ?_
      · rintro p ⟨⟨⟨hp, hU⟩, e⟩, -⟩
        have h42 := (GlobalTheory.T.fixedLattice_inf_eq_and_pairing_of_isometry K V H hK hP L₀ g j D₀ hL hD hG hg x x' p hp).1
        rw [hU] at h42
        exact ⟨hp.2.1, by rw [← h42, inf_eq_map, e]⟩
      intro d' hd'
      have c3 := GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hP U d'.1 d.1 hd'.1.1.1 hd.1.1.1
      rw [hsub] at c3
      refine le_trans (ENat.toENNReal_le.2 ?_) c3
      refine Set.encard_le_encard_of_injOn (f := fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.2.2) ?_ ?_
      · rintro p ⟨⟨⟨⟨hp, hU⟩, -⟩, e1⟩, e2⟩
        refine ⟨hp.2.2.1, by rw [← e1, ← e2]; exact hp.2.2.2.1, fun y hy => ?_⟩
        rw [← hU] at hy
        have : p.2.2 y - y = 0 := hy
        exact sub_eq_zero.1 this
      · rintro p ⟨⟨-, e1⟩, e2⟩ q ⟨⟨-, f1⟩, f2⟩ e
        exact Prod.ext (e1.trans f1.symm) (Prod.ext (e2.trans f2.symm) e)
  · have hempty : {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun p hp => hcase ?_
      obtain ⟨-, a, -, c⟩ := key p hp
      have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
      have h1 : (2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) ≤ 1 :=
        pow_le_one₀ (by positivity) ((div_le_one (by linarith)).2 hg')
      have h2 : A ≤ (D₀ : ℝ) * x * x' := by
        calc A ≤ 1 * D₀ * x * x' := by rw [hA]; gcongr
          _ = _ := by ring
      have a' : (1 : ℝ) ≤ (GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) : ℝ) ^ 2 :=
        one_le_pow₀ (by exact_mod_cast a)
      have h3 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    rw [hempty]
    simp

end GlobalTheory.DegCnt.FixedSpaceCount
