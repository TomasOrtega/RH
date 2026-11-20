import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Rewrite using `[← (hG v).2 0]`. Simplify using `[Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord_zero]`.
-/
theorem gram_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (v : InfinitePlace K) : N v.embedding 0 = 0 := by
  rw [← (hG v).2 0]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord_zero]

/- English proof (translation)
Establish `hs : ∀ z, ‖Formalism.HermitianLatticesTheory.realize b X z‖ ^ 2 = ∑ v : InfinitePlace K, N v.embedding z ^ 2` using `fun z => by`. Rewrite using `[GlobalTheory.AllWt.norm_realize_sq]`. Conclude with `Finset.sum_congr rfl fun v _ => by rw [(hG v).2]`. Establish `h1` using `hs (x + y)`. Rewrite `h1` using `[map_add, norm_add_sq_real, hs x, hs y]`.

Rewrite `h1` using `[Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inner_realize_eq_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {x y : V}
    (h : ∀ v : InfinitePlace K, N v.embedding (x + y) ^ 2 = N v.embedding x ^ 2 + N v.embedding y ^ 2) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  have hs : ∀ z, ‖Formalism.HermitianLatticesTheory.realize b X z‖ ^ 2 = ∑ v : InfinitePlace K, N v.embedding z ^ 2 := fun z => by
    rw [GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2]
  have h1 := hs (x + y)
  rw [map_add, norm_add_sq_real, hs x, hs y] at h1
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib] at h1
  linarith

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use `inner_realize_eq_zero hG fun v => ?_` and prove the remaining obligations. Establish `hmem : ∀ (k : ι) (z : V) (_ : z ∈ M k) (l : ι), (Pi.single k z : ι → V) l ∈ Submodule.span K (M l : Set V)`. Introduce `k z hz l`. Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality.

Simplify using `using Submodule.subset_span hz`. Simplify using `[Pi.single_apply, hl]`. Establish `h` using `hN v.embedding (Pi.single i x + Pi.single j y) fun l => Submodule.add_mem _ (hmem i x hx l) (hmem j y hy l)`. Establish `hsum : ∑ l, (Pi.single i x + Pi.single j y : ι → V) l = x + y`. Simplify using `[Finset.sum_add_distrib]`.

Establish `hpt : ∀ l, N v.embedding ((Pi.single i x + Pi.single j y : ι → V) l) ^ 2 = (Pi.single i (N v.embedding x ^ 2) : ι → ℝ) l + (Pi.single j (N v.embedding y ^ 2) : ι → ℝ) l`. Introduce `l`. Distinguish the cases in `hli : l = i`. Substitute `hli` using the available equality. Simplify using `[Pi.single_apply, hij]`.

Distinguish the cases in `hlj : l = j`. Substitute `hlj` using the available equality. Simplify using `[Pi.single_apply, hli]`. Simplify using `[Pi.single_apply, hli, hlj, gram_zero hG v]`. Rewrite `h` using `[hsum, Finset.sum_congr rfl fun l _ => hpt l, Finset.sum_add_distrib]`.

Simplify using `using h`.
-/
theorem inner_pair [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2)
    {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ M i) (hy : y ∈ M j) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  refine inner_realize_eq_zero hG fun v => ?_
  have hmem : ∀ (k : ι) (z : V) (_ : z ∈ M k) (l : ι),
      (Pi.single k z : ι → V) l ∈ Submodule.span K (M l : Set V) := by
    intro k z hz l
    by_cases hl : l = k
    · subst hl; simpa using Submodule.subset_span hz
    · simp [Pi.single_apply, hl]
  have h := hN v.embedding (Pi.single i x + Pi.single j y) fun l =>
    Submodule.add_mem _ (hmem i x hx l) (hmem j y hy l)
  have hsum : ∑ l, (Pi.single i x + Pi.single j y : ι → V) l = x + y := by
    simp [Finset.sum_add_distrib]
  have hpt : ∀ l, N v.embedding ((Pi.single i x + Pi.single j y : ι → V) l) ^ 2 =
      (Pi.single i (N v.embedding x ^ 2) : ι → ℝ) l + (Pi.single j (N v.embedding y ^ 2) : ι → ℝ) l := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [Pi.single_apply, hij]
    · by_cases hlj : l = j
      · subst hlj; simp [Pi.single_apply, hli]
      · simp [Pi.single_apply, hli, hlj, gram_zero hG v]
  rw [hsum, Finset.sum_congr rfl fun l _ => hpt l, Finset.sum_add_distrib] at h
  simpa using h

/- English proof (translation)
Establish `hX : ∀ v, IsUnit (X v).det` using `fun v => (hG v).1`. Rewrite using `[GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, GlobalTheory.AllWt.slope_sq_eq hG hL]`. Distinguish the cases in `h0 : L = ⊥`. Substitute `h0` using the available equality. Simplify using `[Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX]`.

Establish `hr : Formalism.HN.rkK L ≠ 0` using `fun h => h0 (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK b h)`. Establish `hrk` using `(Formalism.HN.plLat K V (Fin n) b X hX L hL).2.1`. Establish `hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b X) L = Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L / (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ)` using `rfl`. Establish `hn : (Module.finrank ℚ K : ℝ) ≠ 0`. Conclude with `(Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)).ne'` after adjusting the coercions.

Establish `hr' : (Formalism.HN.rkK L : ℝ) ≠ 0` using `by exact_mod_cast hr`. Rewrite using `[Formalism.HN.muDef, hs, hrk]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_eq [IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    GlobalTheory.AllWt.deg N L = 1 / (Module.finrank ℚ K : ℝ) * Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L +
      (Formalism.HN.rkK L : ℝ) * ((-Real.log 2 + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) / 2) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, GlobalTheory.AllWt.slope_sq_eq hG hL]
  by_cases h0 : L = ⊥
  · subst h0
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX]
  · have hr : Formalism.HN.rkK L ≠ 0 := fun h => h0 (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK b h)
    have hrk := (Formalism.HN.plLat K V (Fin n) b X hX L hL).2.1
    have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b X) L =
        Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L / (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) := rfl
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)).ne'
    have hr' : (Formalism.HN.rkK L : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [Formalism.HN.muDef, hs, hrk]
    push_cast
    field_simp
    ring

end GlobalTheory.OrthRankDeg

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hX : ∀ v, IsUnit (X v).det` using `fun v => (hG v).1`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `[Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX, Submodule.fg_bot]`. Consider the case `insert a s ha ih`.

Take `⟨ihfg, ihrk, ihdeg⟩` from `ih`. Rewrite using `[Finset.iSup_insert]`. Use `set B := ⨆ i ∈ s, M i with hB`. Establish `ho : ∀ x ∈ M a, ∀ y ∈ B, inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0`. Introduce `x hx y hy`.

Take `⟨μ, hμ⟩` from `(Submodule.mem_iSup_finset_iff_exists_sum M y).1 hy`. Rewrite using `[← hμ, map_sum, inner_sum]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Conclude with `inner_pair hG M hN (by rintro rfl; exact ha hi) hx (μ i).2`. Establish `hlA` using `(Formalism.HN.plLat K V (Fin n) b X hX (M a) (hM a)).1`.

Establish `hlB` using `(Formalism.HN.plLat K V (Fin n) b X hX B ihfg).1`. Take `⟨hl, hdeg, -⟩` from `(Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X)).2 (M a) B hlA hlB ho`. Establish `hfg : (M a ⊔ B).FG` using `(hM a).sup ihfg`. Establish `hinf : M a ⊓ B = ⊥`. Use `(Submodule.eq_bot_iff _).2 fun x hx => ?_` and prove the remaining obligations.

Establish `h1` using `ho x hx.1 x hx.2`. Rewrite `h1` using `[inner_self_eq_zero]`. Conclude with `Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])`. Establish `hrk` using `(Formalism.HN.degSupermod (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) (M a ⊔ B) (M a) B hl le_sup_left le_sup_right).1`. Rewrite `hrk` using `[hinf, (Formalism.HN.plLat K V (Fin n) b X hX _ hfg).2.1, (Formalism.HN.plLat K V (Fin n) b X hX _ (hM a)).2.1, (Formalism.HN.plLat K V (Fin n) b X hX _ ihfg).2.1, (Formalism.HN.plLat K V (Fin n) b X hX _ Submodule.fg_bot).2.1, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.r …`.

Establish `hrk'` using `Nat.eq_of_mul_eq_mul_left (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)) hrk`. Use `⟨hfg, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hrk', Finset.sum_insert ha, ihrk]`. Rewrite using `[hdeg, Finset.sum_insert ha, ihdeg]`.
-/
theorem sum_finset [IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hM : ∀ i, (M i).FG)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) (s : Finset ι) :
    (⨆ i ∈ s, M i).FG ∧ Formalism.HN.rkK (⨆ i ∈ s, M i) = ∑ i ∈ s, Formalism.HN.rkK (M i) ∧
      Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, M i) =
        ∑ i ∈ s, Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (M i) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  induction s using Finset.induction_on with
  | empty =>
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX, Submodule.fg_bot]
  | insert a s ha ih =>
    obtain ⟨ihfg, ihrk, ihdeg⟩ := ih
    rw [Finset.iSup_insert]
    set B := ⨆ i ∈ s, M i with hB
    have ho : ∀ x ∈ M a, ∀ y ∈ B,
        inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum M y).1 hy
      rw [← hμ, map_sum, inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact inner_pair hG M hN (by rintro rfl; exact ha hi) hx (μ i).2
    have hlA := (Formalism.HN.plLat K V (Fin n) b X hX (M a) (hM a)).1
    have hlB := (Formalism.HN.plLat K V (Fin n) b X hX B ihfg).1
    obtain ⟨hl, hdeg, -⟩ :=
      (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X)).2 (M a) B hlA hlB ho
    have hfg : (M a ⊔ B).FG := (hM a).sup ihfg
    have hinf : M a ⊓ B = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h1 := ho x hx.1 x hx.2
      rw [inner_self_eq_zero] at h1
      exact Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])
    have hrk := (Formalism.HN.degSupermod (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) (M a ⊔ B) (M a) B hl
      le_sup_left le_sup_right).1
    rw [hinf, (Formalism.HN.plLat K V (Fin n) b X hX _ hfg).2.1, (Formalism.HN.plLat K V (Fin n) b X hX _ (hM a)).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ ihfg).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ Submodule.fg_bot).2.1, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, mul_zero, add_zero,
      ← mul_add] at hrk
    have hrk' := Nat.eq_of_mul_eq_mul_left (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)) hrk
    refine ⟨hfg, ?_, ?_⟩
    · rw [hrk', Finset.sum_insert ha, ihrk]
    · rw [hdeg, Finset.sum_insert ha, ihdeg]

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ ι _ N M hG hM hN`. Use `letI : StarRing K := starRingOfComm`. Take `⟨⟨n, ⟨⟨b, X⟩, hbX⟩⟩⟩` from `hG`. Take `⟨hfg, hrk, hdeg⟩` from `sum_finset hbX M hM hN Finset.univ`. Establish `hu : (⨆ i ∈ (Finset.univ : Finset ι), M i) = ⨆ i, M i` using `by simp`.

Rewrite `hfg`, `hrk`, `hdeg` using `[hu]`. Use `⟨hrk, ?_⟩` and prove the remaining obligations. Rewrite using `[deg_eq hbX _ hfg, hdeg, hrk, Finset.mul_sum]`. Use `push_cast`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => (deg_eq hbX _ (hM i)).symm`.
-/
theorem rkK_deg_iSup : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ)
    (M : ι → Submodule (𝓞 K) V), HasGram N → (∀ i, (M i).FG) →
    (∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) → N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) →
    Formalism.HN.rkK (⨆ i, M i) = ∑ i, Formalism.HN.rkK (M i) ∧ deg N (⨆ i, M i) = ∑ i, deg N (M i) := by
  intro K V _ _ _ _ _ _ _ ι _ N M hG hM hN
  classical
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨⟨b, X⟩, hbX⟩⟩⟩ := hG
  obtain ⟨hfg, hrk, hdeg⟩ := sum_finset hbX M hM hN Finset.univ
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), M i) = ⨆ i, M i := by simp
  rw [hu] at hfg hrk hdeg
  refine ⟨hrk, ?_⟩
  rw [deg_eq hbX _ hfg, hdeg, hrk, Finset.mul_sum]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (deg_eq hbX _ (hM i)).symm

end GlobalTheory.OrthRankDeg
