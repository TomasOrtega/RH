import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SubquotientSizeInequality
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA

open Formalism.HN Matrix NumberField Finset GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality

noncomputable section

namespace GlobalTheory.SizeSubToQuot

/- English proof (translation)
Rewrite using `[Metric.le_infDist ⟨0, Q.zero_mem⟩]`. Introduce `y hy`. Establish `h0 : Pᗮ.starProjection y = 0` using `Submodule.starProjection_orthogonal_apply_eq_zero (h hy)`. Rewrite using `[dist_eq_norm, ← sub_zero (Pᗮ.starProjection x), ← h0, ← map_sub]`. Conclude with `Submodule.norm_starProjection_apply_le _ _`.
-/
theorem norm_proj_le_infDist {ι : Type} [Fintype ι] (P Q : Submodule ℂ (EuclideanSpace ℂ ι)) (h : Q ≤ P)
    (x : EuclideanSpace ℂ ι) :
    ‖Pᗮ.starProjection x‖ ≤ Metric.infDist x (Q : Set (EuclideanSpace ℂ ι)) := by
  rw [Metric.le_infDist ⟨0, Q.zero_mem⟩]
  intro y hy
  have h0 : Pᗮ.starProjection y = 0 := Submodule.starProjection_orthogonal_apply_eq_zero (h hy)
  rw [dist_eq_norm, ← sub_zero (Pᗮ.starProjection x), ← h0, ← map_sub]
  exact Submodule.norm_starProjection_apply_le _ _

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)

omit [IsTotallyComplex K] in

/- English proof (translation)
Establish `hle : S ⊔ N ≤ L` using `sup_le hS.1 hN`. Establish `hsp : Submodule.span K ((S ⊔ N : Submodule (𝓞 K) V) : Set V) = Submodule.span K (S : Set V)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `y hy`.

Take `⟨s, hs, n, hn, rfl⟩` from `Submodule.mem_sup.1 hy`. Conclude with `Submodule.add_mem _ (Submodule.subset_span hs) (h hn)`. Conclude with `Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)`. Establish `h1` using `(plLat K V ι b X hX _ (Submodule.FG.of_le hL hle)).2.1`. Establish `h2` using `(plLat K V ι b X hX _ (Submodule.FG.of_le hL hS.1)).2.1`.

Establish `h3 : rkK (S ⊔ N) = rkK S` using `by unfold rkK; rw [hsp]`. Establish `h4` using `(satBasic _ _ _ (Formalism.HermitianLatticesTheory.realize b X) L (plLat K V ι b X hX L hL).1).2.2.1 S (S ⊔ N) hS le_sup_left hle (by rw [h1, h2, h3])`. Conclude with `sup_eq_left.1 h4`.
-/
theorem le_of_subset_span (hX : ∀ v, IsUnit (X v).det) {L S N : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hN : N ≤ L)
    (h : (N : Set V) ⊆ Submodule.span K (S : Set V)) : N ≤ S := by
  have hle : S ⊔ N ≤ L := sup_le hS.1 hN
  have hsp : Submodule.span K ((S ⊔ N : Submodule (𝓞 K) V) : Set V) = Submodule.span K (S : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
      exact Submodule.add_mem _ (Submodule.subset_span hs) (h hn)
    · exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)
  have h1 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hle)).2.1
  have h2 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hS.1)).2.1
  have h3 : rkK (S ⊔ N) = rkK S := by unfold rkK; rw [hsp]
  have h4 := (satBasic _ _ _ (Formalism.HermitianLatticesTheory.realize b X) L (plLat K V ι b X hX L hL).1).2.2.1 S (S ⊔ N) hS
    le_sup_left hle (by rw [h1, h2, h3])
  exact sup_eq_left.1 h4

/- English proof (translation)
Establish `hfinV : FiniteDimensional K V` using `Module.Finite.of_basis b`. Set `e` to `Module.finBasis K U`. Set `T : InfinitePlace K → ((Fin (Module.finrank K U) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι)` to `fun v => Fintype.linearCombination ℂ (fun k => WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (e k : V)))`. Establish `hT : ∀ v (x : U), (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (x : V)) : EuclideanSpace ℂ ι) = T v (fun k => v.embedding (e.repr x k))`. Introduce `v x`.

Establish `hx : (x : V) = ∑ k, e.repr x k • (e k : V)`. Establish `h` using `congrArg U.subtype (e.sum_repr x)`. Rewrite `h` using `[map_sum]`. Conclude with `h.symm`. Rewrite using `[hx, PlaceDecomposition.fcoord_lincomb, WithLp.toLp_sum]`.

Simplify using `only [T, Fintype.linearCombination_apply, WithLp.toLp_smul]`. Establish `hinj : ∀ v, Function.Injective (T v)`. Introduce `v`. Establish `hle : QuotientRealization.pv b X U v ≤ LinearMap.range (T v)`. Rewrite using `[QuotientRealization.pv, Submodule.span_le]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨_, (hT v ⟨y, hy⟩).symm⟩`. Establish `h1` using `Submodule.finrank_mono hle`. Rewrite `h1` using `[QuotientRealization.finrank_pv b X hX]`. Establish `h4` using `LinearMap.finrank_range_add_finrank_ker (T v)`.

Rewrite `h4` using `[Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Establish `h5 : Module.finrank ℂ (LinearMap.ker (T v)) = 0` using `by omega`. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.finrank_eq_zero.1 h5`. Establish `hM` using `fun v => QuotientRealization.exists_mat (T v) (hinj v)`.

Use `choose M hMu hMn using hM`. Use `⟨_, e, fun v => (M v)⁻¹, fun v => Matrix.isUnit_nonsing_inv_det _ (hMu v), fun v x => ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.HermitianLatticesTheory.normAt, PlaceOperatorNorms.cnorm_eq, Submodule.subtype_apply, hT, ← hMn v]`. Simplify using `only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.nonsing_inv_nonsing_inv _ (hMu v)]`. Both sides reduce to the same expression.
-/
theorem exists_frames_subspace (hX : ∀ v, IsUnit (X v).det) (U : Submodule K V) :
    ∃ (m : ℕ) (e : Module.Basis (Fin m) K U) (Y : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ),
      (∀ v, IsUnit (Y v).det) ∧
      ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v (U.subtype x) = Formalism.HermitianLatticesTheory.normAt e Y v x := by
  have hfinV : FiniteDimensional K V := Module.Finite.of_basis b
  let e := Module.finBasis K U
  let T : InfinitePlace K → ((Fin (Module.finrank K U) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) := fun v =>
    Fintype.linearCombination ℂ (fun k => WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (e k : V)))
  have hT : ∀ v (x : U), (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (x : V)) : EuclideanSpace ℂ ι) =
      T v (fun k => v.embedding (e.repr x k)) := by
    intro v x
    have hx : (x : V) = ∑ k, e.repr x k • (e k : V) := by
      have h := congrArg U.subtype (e.sum_repr x)
      rw [map_sum] at h
      exact h.symm
    rw [hx, PlaceDecomposition.fcoord_lincomb, WithLp.toLp_sum]
    simp only [T, Fintype.linearCombination_apply, WithLp.toLp_smul]
  have hinj : ∀ v, Function.Injective (T v) := by
    intro v
    have hle : QuotientRealization.pv b X U v ≤ LinearMap.range (T v) := by
      rw [QuotientRealization.pv, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, (hT v ⟨y, hy⟩).symm⟩
    have h1 := Submodule.finrank_mono hle
    rw [QuotientRealization.finrank_pv b X hX] at h1
    have h4 := LinearMap.finrank_range_add_finrank_ker (T v)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h4
    have h5 : Module.finrank ℂ (LinearMap.ker (T v)) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.1 h5
  have hM := fun v => QuotientRealization.exists_mat (T v) (hinj v)
  choose M hMu hMn using hM
  refine ⟨_, e, fun v => (M v)⁻¹, fun v => Matrix.isUnit_nonsing_inv_det _ (hMu v), fun v x => ?_⟩
  rw [Formalism.HermitianLatticesTheory.normAt, PlaceOperatorNorms.cnorm_eq, Submodule.subtype_apply, hT, ← hMn v]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.nonsing_inv_nonsing_inv _ (hMu v)]
  rfl

/- English proof (translation)
Establish `h` using `Submodule.mem_map_of_mem (f := ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι)) (QuotientRealization.fcoord_mem_span b X S v hy)`. Rewrite `h` using `[Submodule.map_span, Set.image_image]`. Conclude with `h`.
-/
theorem ptAt_mem_spanAt (S : Submodule (𝓞 K) V) (v : InfinitePlace K) {y : V}
    (hy : y ∈ Submodule.span K (S : Set V)) : ptAt b X v y ∈ spanAt b X v S := by
  have h := Submodule.mem_map_of_mem
    (f := ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι))
    (QuotientRealization.fcoord_mem_span b X S v hy)
  rw [Submodule.map_span, Set.image_image] at h
  exact h

/- English proof (translation)
Establish `hQ` using `quotRealize K V ι b X hX B B' hB hS`. Use `set W := Submodule.span K (B' : Set V) with hW`. Take `⟨κ, _, _, b', X', hX', hnorm, hq⟩` from `hQ`. Use `set U := Submodule.span K (A : Set V) with hU`. Take `⟨m, e, Y, hY, hiso⟩` from `exists_frames_subspace b X hX U`.

Use `set A₀ : Submodule (𝓞 K) U := A.comap (U.subtype.restrictScalars (𝓞 K)) with hA₀`. Establish `hmapA : A₀.map (U.subtype.restrictScalars (𝓞 K)) = A`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hy`.

Introduce `y hy`. Conclude with `⟨⟨y, Submodule.subset_span hy⟩, hy, rfl⟩`. Establish `hA₀fg : A₀.FG`. Use `Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_` and prove the remaining obligations. Rewrite using `[hmapA]`.

Conclude with `hA`. Establish `hre` using `(rerealize K U (Fin m) V ι e Y b X U.subtype hY hX U.injective_subtype hiso A₀ hA₀fg).2.2.2.2.2.2`. Rewrite `hre` using `[hmapA]`. Use `set ψ : U →ₗ[K] V ⧸ W := W.mkQ ∘ₗ φ ∘ₗ U.subtype with hψ`. Use `set Bq := B.map (W.mkQ.restrictScalars (𝓞 K)) with hBq`.

Establish `hBfg : Bq.FG` using `hB.map _`. Establish `hABq : A₀.map (ψ.restrictScalars (𝓞 K)) ≤ Bq`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨φ y, hAB _ hy, rfl⟩`. Take `⟨y₀, hy₀, hy₀'⟩` from `hne`.

Establish `h0 : A₀.map (ψ.restrictScalars (𝓞 K)) ≠ ⊥`. Introduce `h0`. Establish `h1 : ψ.restrictScalars (𝓞 K) ⟨y₀, Submodule.subset_span hy₀⟩ ∈ A₀.map (ψ.restrictScalars (𝓞 K))` using `Submodule.mem_map_of_mem hy₀`. Rewrite `h1` using `[h0, Submodule.mem_bot]`. Establish `h2 : φ y₀ ∈ W` using `(Submodule.Quotient.mk_eq_zero W).1 h1`.

Establish `h3 : B ⊓ W.restrictScalars (𝓞 K) ≤ B'` using `le_of_subset_span b X hX hB hS inf_le_left fun z hz => hz.2`. Conclude with `hy₀' (h3 ⟨hAB _ hy₀, h2⟩)`. Establish `hA0 : A₀ ≠ ⊥` using `fun h => h0 (by rw [h, Submodule.map_bot])`. Establish `hB0 : Bq ≠ ⊥` using `fun h => h0 (le_bot_iff.1 (h ▸ hABq))`. Establish `hM` using `sizeIneq K U (Fin m) _ κ e Y b' X' hY hX' ψ A₀ Bq hA₀fg hBfg hABq h0`.

Establish `hop : ∀ v, opNormAt e Y b' X' v ψ ≤ c v`. Introduce `v`. Use `Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points e Y b' X' hY _ v (c v) (hc v) fun y => ?_` and prove the remaining obligations. Rewrite using `[← hiso]`. Use `le_trans ?_ (hn v y y.2)` and prove the remaining obligations.

Rewrite using `[hψ, LinearMap.comp_apply, hnorm]`. Use `norm_proj_le_infDist _ _ ?_ _` and prove the remaining obligations. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `⟨z, Submodule.subset_span hz, rfl⟩`.

Establish `hP : (∏ v, opNormAt e Y b' X' v ψ) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ))` using `Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _) (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hop v) (by positivity)`. Establish `hleast : lo ≤ leastSize b' X' Bq`. Use `le_csInf ⟨_, Bq, le_rfl, hB0, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨N, hNB, hN0, rfl⟩`. Use `set N' := B ⊓ N.comap (W.mkQ.restrictScalars (𝓞 K)) with hN'`.

Establish `hS0 : ∀ s ∈ B', W.mkQ s = 0` using `fun s hs => (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span hs)`. Establish `hSN : B' ≤ N'`. Introduce `s hs`. Use `⟨hS.1 hs, ?_⟩` and prove the remaining obligations. Use `show W.mkQ s ∈ N`.

Rewrite using `[hS0 s hs]`. Conclude with `N.zero_mem`. Establish `hmap : N'.map (W.mkQ.restrictScalars (𝓞 K)) = N`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `hy.2`. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `hNB hz`. Conclude with `⟨y, ⟨hy, hz⟩, rfl⟩`. Establish `hne : B' ≠ N'`.

Introduce `h`. Apply `hN0` to reduce the goal to its premises. Rewrite using `[← hmap, ← h, eq_bot_iff]`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `hS0 s hs`.

Establish `hlt` using `hl N' (lt_of_le_of_ne hSN hne) inf_le_left`. Rewrite `hlt` using `[(hq N' hSN inf_le_left).2, hmap]`. Then use the resulting hypothesis. Establish `hpos : 0 < largestSize e Y A₀`. Rewrite using `[(sizeMu K U (Fin m) e Y hY A₀ hA₀fg hA0).2.2.2.2.1]`. Conclude with `Real.exp_pos _`.

Use `le_trans ?_ (hM.trans hP)` and prove the remaining obligations. Conclude with `div_le_div₀ (hlo.le.trans hleast) hleast hpos (hre ▸ hh)`.
-/
theorem size_ineq_to_quot (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) {A B B' : Submodule (𝓞 K) V}
    (hA : A.FG) (hB : B.FG) (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) B B') (hAB : ∀ y ∈ A, φ y ∈ B)
    (hne : ∃ y ∈ A, φ y ∉ B') {lo hi : ℝ} (hlo : 0 < lo)
    (hl : ∀ N, B' < N → N ≤ B → lo ≤ sizeQ b X N B') (hh : largestSize b X A ≤ hi)
    (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hn : ∀ v, ∀ y ∈ Submodule.span K (A : Set V),
      distAt b X v B' (φ y) ≤ c v * Formalism.HermitianLatticesTheory.normAt b X v y) :
    lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) := by
  have hQ := quotRealize K V ι b X hX B B' hB hS
  set W := Submodule.span K (B' : Set V) with hW
  obtain ⟨κ, _, _, b', X', hX', hnorm, hq⟩ := hQ
  set U := Submodule.span K (A : Set V) with hU
  obtain ⟨m, e, Y, hY, hiso⟩ := exists_frames_subspace b X hX U
  set A₀ : Submodule (𝓞 K) U := A.comap (U.subtype.restrictScalars (𝓞 K)) with hA₀
  have hmapA : A₀.map (U.subtype.restrictScalars (𝓞 K)) = A := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy
    · intro y hy
      exact ⟨⟨y, Submodule.subset_span hy⟩, hy, rfl⟩
  have hA₀fg : A₀.FG := by
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    rw [hmapA]; exact hA
  have hre := (rerealize K U (Fin m) V ι e Y b X U.subtype hY hX U.injective_subtype hiso A₀ hA₀fg).2.2.2.2.2.2
  rw [hmapA] at hre
  set ψ : U →ₗ[K] V ⧸ W := W.mkQ ∘ₗ φ ∘ₗ U.subtype with hψ
  set Bq := B.map (W.mkQ.restrictScalars (𝓞 K)) with hBq
  have hBfg : Bq.FG := hB.map _
  have hABq : A₀.map (ψ.restrictScalars (𝓞 K)) ≤ Bq := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨φ y, hAB _ hy, rfl⟩
  obtain ⟨y₀, hy₀, hy₀'⟩ := hne
  have h0 : A₀.map (ψ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h0
    have h1 : ψ.restrictScalars (𝓞 K) ⟨y₀, Submodule.subset_span hy₀⟩ ∈
        A₀.map (ψ.restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hy₀
    rw [h0, Submodule.mem_bot] at h1
    have h2 : φ y₀ ∈ W := (Submodule.Quotient.mk_eq_zero W).1 h1
    have h3 : B ⊓ W.restrictScalars (𝓞 K) ≤ B' :=
      le_of_subset_span b X hX hB hS inf_le_left fun z hz => hz.2
    exact hy₀' (h3 ⟨hAB _ hy₀, h2⟩)
  have hA0 : A₀ ≠ ⊥ := fun h => h0 (by rw [h, Submodule.map_bot])
  have hB0 : Bq ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hABq))
  have hM := sizeIneq K U (Fin m) _ κ e Y b' X' hY hX' ψ A₀ Bq hA₀fg hBfg hABq h0
  have hop : ∀ v, opNormAt e Y b' X' v ψ ≤ c v := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points e Y b' X' hY _ v (c v) (hc v) fun y => ?_
    rw [← hiso]
    refine le_trans ?_ (hn v y y.2)
    rw [hψ, LinearMap.comp_apply, hnorm]
    refine norm_proj_le_infDist _ _ ?_ _
    refine Submodule.span_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, Submodule.subset_span hz, rfl⟩
  have hP : (∏ v, opNormAt e Y b' X' v ψ) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤
      (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) :=
    Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _)
      (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hop v) (by positivity)
  have hleast : lo ≤ leastSize b' X' Bq := by
    refine le_csInf ⟨_, Bq, le_rfl, hB0, rfl⟩ ?_
    rintro _ ⟨N, hNB, hN0, rfl⟩
    set N' := B ⊓ N.comap (W.mkQ.restrictScalars (𝓞 K)) with hN'
    have hS0 : ∀ s ∈ B', W.mkQ s = 0 := fun s hs =>
      (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span hs)
    have hSN : B' ≤ N' := by
      intro s hs
      refine ⟨hS.1 hs, ?_⟩
      show W.mkQ s ∈ N
      rw [hS0 s hs]; exact N.zero_mem
    have hmap : N'.map (W.mkQ.restrictScalars (𝓞 K)) = N := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩; exact hy.2
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := hNB hz
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
    have hne : B' ≠ N' := by
      intro h
      apply hN0
      rw [← hmap, ← h, eq_bot_iff]
      rintro _ ⟨s, hs, rfl⟩
      exact hS0 s hs
    have hlt := hl N' (lt_of_le_of_ne hSN hne) inf_le_left
    rwa [(hq N' hSN inf_le_left).2, hmap] at hlt
  have hpos : 0 < largestSize e Y A₀ := by
    rw [(sizeMu K U (Fin m) e Y hY A₀ hA₀fg hA0).2.2.2.2.1]; exact Real.exp_pos _
  refine le_trans ?_ (hM.trans hP)
  exact div_le_div₀ (hlo.le.trans hleast) hleast hpos (hre ▸ hh)

end General

/- English proof (translation)
Introduce `K _ _ _ _ n X hX φ A B B' hA hB hS hAB hne lo hi hlo hl hh c hc hn`. Use `size_ineq_to_quot (Pi.basisFun K (Fin n)) X hX (Matrix.toLin' φ) hA hB hS hAB hne hlo hl hh c hc fun v y hy => ?_` and prove the remaining obligations. Establish `h` using `hn v _ (ptAt_mem_spanAt (Pi.basisFun K (Fin n)) X A v hy)`. Rewrite `h` using `[norm_ptAt]`. Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations.

Unfold `distAt ptAt`. Rewrite using `[PlaceOperatorNorms.fcoord_map (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin n)) X hX v, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Both sides reduce to the same expression.
-/
theorem size_ineq_sub_to_quot : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) → ∀ (φ : Matrix (Fin n) (Fin n) K) (A B B' : Submodule (𝓞 K) (Fin n → K)), A.FG → B.FG → IsSat (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) X) B B' → (∀ y ∈ A, φ *ᵥ y ∈ B) → (∃ y ∈ A, φ *ᵥ y ∉ B') → ∀ lo hi : ℝ, 0 < lo → (∀ N, B' < N → N ≤ B → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N B') → largestSize (Pi.basisFun K (Fin n)) X A ≤ hi → ∀ c : InfinitePlace K → ℝ, (∀ v, 0 ≤ c v) → (∀ v, ∀ u ∈ spanAt (Pi.basisFun K (Fin n)) X v A, Metric.infDist (Matrix.toEuclideanLin ((X v)⁻¹ * φ.map v.embedding * X v) u) (spanAt (Pi.basisFun K (Fin n)) X v B' : Set (EuclideanSpace ℂ (Fin n))) ≤ c v * ‖u‖) → lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) := by
  intro K _ _ _ _ n X hX φ A B B' hA hB hS hAB hne lo hi hlo hl hh c hc hn
  refine size_ineq_to_quot (Pi.basisFun K (Fin n)) X hX (Matrix.toLin' φ) hA hB hS hAB hne hlo hl hh c hc
    fun v y hy => ?_
  have h := hn v _ (ptAt_mem_spanAt (Pi.basisFun K (Fin n)) X A v hy)
  rw [norm_ptAt] at h
  refine le_trans (le_of_eq ?_) h
  unfold distAt ptAt
  rw [PlaceOperatorNorms.fcoord_map (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin n)) X hX v,
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rfl

end GlobalTheory.SizeSubToQuot
