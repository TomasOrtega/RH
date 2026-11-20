import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTrivialPointwise
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPointStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.NearLower

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
  (X : InfinitePlace K → Matrix ι ι ℂ)

omit [IsTotallyComplex K] in

/- English proof (translation)
Establish `hle : S ⊔ N ≤ L` using `sup_le hS.1 hN`. Establish `hsp : Submodule.span K ((S ⊔ N : Submodule (𝓞 K) V) : Set V) = Submodule.span K (S : Set V)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `y hy`.

Take `⟨s, hs, n, hn, rfl⟩` from `Submodule.mem_sup.1 hy`. Conclude with `Submodule.add_mem _ (Submodule.subset_span hs) (h hn)`. Conclude with `Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)`. Establish `h1` using `(plLat K V ι b X hX _ (Submodule.FG.of_le hL hle)).2.1`. Establish `h2` using `(plLat K V ι b X hX _ (Submodule.FG.of_le hL hS.1)).2.1`.

Establish `h3 : rkK (S ⊔ N) = rkK S` using `by unfold rkK; rw [hsp]`. Establish `h4` using `(satBasic _ _ _ (Formalism.HermitianLatticesTheory.realize b X) L (plLat K V ι b X hX L hL).1).2.2.1 S (S ⊔ N) hS le_sup_left hle (by rw [h1, h2, h3])`. Conclude with `sup_eq_left.1 h4`.
-/
theorem le_of_le_span (hX : ∀ v, IsUnit (X v).det) {L S N : Submodule (𝓞 K) V} (hL : L.FG)
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
Take `⟨-, -, ⟨N, hsat, hN, hsl⟩, -⟩` from `muChar _ _ _ (Formalism.HermitianLatticesTheory.realize b X) B (plLat K V ι b X hX B hB).1 h0`. Use `⟨N, hsat.1, hN, ?_⟩` and prove the remaining obligations. Rewrite using `[(sizeMu K V ι b X hX B hB h0).2.2.2.1, (sizeMu K V ι b X hX N (Submodule.FG.of_le hB hsat.1) hN).1, hsl]`.
-/
theorem exists_size_eq_least (hX : ∀ v, IsUnit (X v).det) {B : Submodule (𝓞 K) V} (hB : B.FG) (h0 : B ≠ ⊥) :
    ∃ N : Submodule (𝓞 K) V, N ≤ B ∧ N ≠ ⊥ ∧ size b X N = leastSize b X B := by
  obtain ⟨-, -, ⟨N, hsat, hN, hsl⟩, -⟩ :=
    muChar _ _ _ (Formalism.HermitianLatticesTheory.realize b X) B (plLat K V ι b X hX B hB).1 h0
  refine ⟨N, hsat.1, hN, ?_⟩
  rw [(sizeMu K V ι b X hX B hB h0).2.2.2.1,
    (sizeMu K V ι b X hX N (Submodule.FG.of_le hB hsat.1) hN).1, hsl]

/- English proof (translation)
Establish `hQ` using `quotRealize K V ι b X hX L S hL hS`. Use `set U := Submodule.span K (S : Set V) with hU`. Take `⟨κ, _, _, b', X', hX', hnorm, hq⟩` from `hQ`. Distinguish the cases in `h0 : A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) = ⊥`. Use `le_of_le_span b X hX hL hS hψ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `: (U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K) y ∈ A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K))` using `Submodule.mem_map_of_mem hy`. Rewrite `this` using `[h0, Submodule.mem_bot]`. Conclude with `(Submodule.Quotient.mk_eq_zero U).1 this`. It suffices to derive a contradiction.

Establish `hA0 : A ≠ ⊥` using `fun h => h0 (by rw [h, Submodule.map_bot])`. Establish `hAfg : A.FG` using `Submodule.FG.of_le hL hA`. Use `set B := L.map (U.mkQ.restrictScalars (𝓞 K)) with hB`. Establish `hBfg : B.FG` using `hL.map _`. Establish `hAB : A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) ≤ B`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨ψ y, hψ ⟨y, hy, rfl⟩, rfl⟩`. Establish `hB0 : B ≠ ⊥` using `fun h => h0 (le_bot_iff.1 (h ▸ hAB))`. Establish `hM` using `sizeIneq K V ι _ κ b X b' X' hX hX' (U.mkQ ∘ₗ ψ) A B hAfg hBfg hAB h0`. Establish `hop : ∀ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ) ≤ δ`.

Introduce `v`. Use `Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X b' X' hX _ v δ hδ.le fun y => ?_` and prove the remaining obligations. Use `le_trans ?_ (hn v y)` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, hnorm]`. Use `(Submodule.norm_starProjection_apply_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[Formalism.HermitianLatticesTheory.normAt, Formalism.HN.PlaceOperatorNorms.cnorm_eq]`. Both sides reduce to the same expression. Establish `hf : (0 : ℝ) < nPl K`. Establish `: 0 < nPl K` using `Fintype.card_pos`. Conclude with `this` after adjusting the coercions.

Establish `hP : (∏ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ)) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤ δ`. Establish `h1 : ∏ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ) ≤ δ ^ nPl K`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hδ.le, mul_one_div_cancel hf.ne', Real.rpow_one]`.

Take `⟨N, hNB, hN0, hNs⟩` from `exists_size_eq_least b' X' hX' hBfg hB0`. Use `set N' := L ⊓ N.comap (U.mkQ.restrictScalars (𝓞 K)) with hN'`. Establish `hS0 : ∀ s ∈ S, U.mkQ s = 0` using `fun s hs => (Submodule.Quotient.mk_eq_zero U).2 (Submodule.subset_span hs)`. Establish `hSN : S ≤ N'`. Introduce `s hs`.

Use `⟨hS.1 hs, ?_⟩` and prove the remaining obligations. Use `show U.mkQ s ∈ N`. Rewrite using `[hS0 s hs]`. Conclude with `N.zero_mem`. Establish `hmap : N'.map (U.mkQ.restrictScalars (𝓞 K)) = N`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hy.2`. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `hNB hz`.

Conclude with `⟨y, ⟨hy, hz⟩, rfl⟩`. Establish `hne : S ≠ N'`. Introduce `h`. Apply `hN0` to reduce the goal to its premises. Rewrite using `[← hmap, ← h, eq_bot_iff]`.

Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `hS0 s hs`. Establish `hlt` using `hSt N' (lt_of_le_of_ne hSN hne) inf_le_left`. Rewrite `hlt` using `[(hq N' hSN inf_le_left).2, hmap, hNs]`. Establish `hpos : 0 < largestSize b X A`.

Rewrite using `[(sizeMu K V ι b X hX A hAfg hA0).2.2.2.2.1]`. Conclude with `Real.exp_pos _`. Establish `h2` using `(div_le_iff₀ hpos).1 (hM.trans hP)`. Establish `h3` using `mul_le_mul_of_nonneg_left (hAt hA0) hδ.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem map_le_of_sizes (hX : ∀ v, IsUnit (X v).det) {L S A : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hA : A ≤ L) (ψ : V →ₗ[K] V)
    (hψ : A.map (ψ.restrictScalars (𝓞 K)) ≤ L) {δ t : ℝ} (hδ : 0 < δ)
    (hn : ∀ v y, Formalism.HermitianLatticesTheory.normAt b X v (ψ y) ≤ δ * Formalism.HermitianLatticesTheory.normAt b X v y)
    (hAt : A ≠ ⊥ → largestSize b X A ≤ t)
    (hSt : ∀ N, S < N → N ≤ L → δ * t < sizeQ b X N S) :
    A.map (ψ.restrictScalars (𝓞 K)) ≤ S := by
  have hQ := quotRealize K V ι b X hX L S hL hS
  set U := Submodule.span K (S : Set V) with hU
  obtain ⟨κ, _, _, b', X', hX', hnorm, hq⟩ := hQ
  by_cases h0 : A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) = ⊥
  · refine le_of_le_span b X hX hL hS hψ ?_
    rintro _ ⟨y, hy, rfl⟩
    have : (U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K) y ∈ A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) :=
      Submodule.mem_map_of_mem hy
    rw [h0, Submodule.mem_bot] at this
    exact (Submodule.Quotient.mk_eq_zero U).1 this
  exfalso
  have hA0 : A ≠ ⊥ := fun h => h0 (by rw [h, Submodule.map_bot])
  have hAfg : A.FG := Submodule.FG.of_le hL hA
  set B := L.map (U.mkQ.restrictScalars (𝓞 K)) with hB
  have hBfg : B.FG := hL.map _
  have hAB : A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨ψ y, hψ ⟨y, hy, rfl⟩, rfl⟩
  have hB0 : B ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hAB))
  have hM := sizeIneq K V ι _ κ b X b' X' hX hX' (U.mkQ ∘ₗ ψ) A B hAfg hBfg hAB h0

  have hop : ∀ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ) ≤ δ := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X b' X' hX _ v δ hδ.le fun y => ?_
    refine le_trans ?_ (hn v y)
    rw [LinearMap.comp_apply, hnorm]
    refine (Submodule.norm_starProjection_apply_le _ _).trans (le_of_eq ?_)
    rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HN.PlaceOperatorNorms.cnorm_eq]
    rfl
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hP : (∏ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ)) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤ δ := by
    have h1 : ∏ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ) ≤ δ ^ nPl K := by
      calc _ ≤ ∏ _v : InfinitePlace K, δ := Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hop v
        _ = δ ^ nPl K := by rw [Finset.prod_const, Finset.card_univ]; rfl
    calc _ ≤ (δ ^ nPl K) ^ ((1 : ℝ) / (nPl K : ℝ)) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _) h1 (by positivity)
      _ = δ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, mul_one_div_cancel hf.ne', Real.rpow_one]

  obtain ⟨N, hNB, hN0, hNs⟩ := exists_size_eq_least b' X' hX' hBfg hB0
  set N' := L ⊓ N.comap (U.mkQ.restrictScalars (𝓞 K)) with hN'
  have hS0 : ∀ s ∈ S, U.mkQ s = 0 := fun s hs => (Submodule.Quotient.mk_eq_zero U).2 (Submodule.subset_span hs)
  have hSN : S ≤ N' := by
    intro s hs
    refine ⟨hS.1 hs, ?_⟩
    show U.mkQ s ∈ N
    rw [hS0 s hs]; exact N.zero_mem
  have hmap : N'.map (U.mkQ.restrictScalars (𝓞 K)) = N := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy.2
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := hNB hz
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
  have hne : S ≠ N' := by
    intro h
    apply hN0
    rw [← hmap, ← h, eq_bot_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact hS0 s hs
  have hlt := hSt N' (lt_of_le_of_ne hSN hne) inf_le_left
  rw [(hq N' hSN inf_le_left).2, hmap, hNs] at hlt
  have hpos : 0 < largestSize b X A := by
    rw [(sizeMu K V ι b X hX A hAfg hA0).2.2.2.2.1]; exact Real.exp_pos _
  have h2 := (div_le_iff₀ hpos).1 (hM.trans hP)
  have h3 := mul_le_mul_of_nonneg_left (hAt hA0) hδ.le
  linarith

end General

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.cnorm Formalism.REAL.hs`. Rewrite using `[← Real.sqrt_mul (by positivity), Finset.sum_mul]`. Use `Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Use `le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => ‖M i j‖) (fun j => ‖u j‖))` and prove the remaining obligations. Use `pow_le_pow_left₀ (norm_nonneg _) ?_ 2` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)`.
-/
theorem cnorm_mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M *ᵥ u) ≤ Real.sqrt (Formalism.REAL.hs M) * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm Formalism.REAL.hs
  rw [← Real.sqrt_mul (by positivity), Finset.sum_mul]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => ‖M i j‖) (fun j => ‖u j‖))
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  simp only [Matrix.mulVec, dotProduct]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)

/- English proof (translation)
Unfold `Formalism.REAL.hs`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.norm_conj ((M - 1) i j)]`. Simplify using `only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hs_conj_sub_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (M.map (starRingEnd ℂ) - 1) = Formalism.REAL.hs (M - 1) := by
  unfold Formalism.REAL.hs
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.norm_conj ((M - 1) i j)]
  simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hX` using `GlobalTheory.NearLowerCompare.frm_isUnit I x`. Establish `e : (frm I x w)⁻¹ * (LinearMap.toMatrix (bas I) (bas I) (Matrix.toLin' (g - 1))).map w.embedding * frm I x w = (frm I x w)⁻¹ * g.map w.embedding * frm I x w - 1`. Rewrite using `[LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hX w)]`. Unfold `Formalism.HermitianLatticesTheory.normAt`. Rewrite using `[Formalism.HN.PlaceOperatorNorms.fcoord_map (bas I) (frm I x) (bas I) (frm I x) hX w, e]`.

Conclude with `(cnorm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))`.
-/
theorem normAt_sub_one_le (I : AutInst) (x : I.GA) (g : Matrix (Fin I.n) (Fin I.n) I.E) (w : InfinitePlace I.E)
    {δ : ℝ} (h : Real.sqrt (Formalism.REAL.hs ((frm I x w)⁻¹ * g.map w.embedding * frm I x w - 1)) ≤ δ)
    (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w (Matrix.toLin' (g - 1) y) ≤
      δ * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  have hX := GlobalTheory.NearLowerCompare.frm_isUnit I x
  have e : (frm I x w)⁻¹ * (LinearMap.toMatrix (bas I) (bas I) (Matrix.toLin' (g - 1))).map w.embedding *
      frm I x w = (frm I x w)⁻¹ * g.map w.embedding * frm I x w - 1 := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.map_sub _ (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (hX w)]
  unfold Formalism.HermitianLatticesTheory.normAt
  rw [Formalism.HN.PlaceOperatorNorms.fcoord_map (bas I) (frm I x) (bas I) (frm I x) hX w, e]
  exact (cnorm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))

/- English proof (translation)
Establish `: IsTotallyComplex I.E` using `I.cm.cmUnram.1`. Take `⟨-, -, -, -, -, hK, hw⟩` from `GlobalTheory.T.autPoint_rational_equivariance I x γ a h1 h2 h3`. Establish `hΛ` using `hK.1 ha.2.1`. Take `⟨hA, -, -, -, hAt, -⟩` from `GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht`. Take `⟨hS, -, -, -, -, -, hSt, -⟩` from `GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (de * t) (mul_pos hde ht)`.

Use `map_le_of_sizes (bas I) (frm I x) (GlobalTheory.NearLowerCompare.frm_isUnit I x) (GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg hS hA.1 _ ?_ hde ?_ hAt hSt` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `hy' : y ∈ lamX I x` using `hA.1 hy`. Establish `: Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E) y ∈ lamX I x`. Rewrite using `[← hΛ]`.

Conclude with `⟨y, hy', rfl⟩`. Simplify `(lamX I x).sub_mem this hy'` using `[map_sub, Matrix.sub_mulVec]`. Introduce `w`. Use `normAt_sub_one_le I x _ w ?_` and prove the remaining obligations. Break down `hw w with h | h` into its components or cases.

Rewrite using `[h]`. Conclude with `ha.2.2 _`. Rewrite using `[h, hs_conj_sub_one]`. Conclude with `ha.2.2 _`.
-/
theorem lowers (I : AutInst) (x : I.GA) (de : ℝ) (hde : 0 < de) (γ : GL (Fin I.n) I.E) (a : I.GA)
    (h1 : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (h2 : ∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (h3 : I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (ha : a ∈ nearSet I x de) (t : ℝ) (ht : 0 < t) :
    (stepLe I x t).map ((Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1)).restrictScalars (𝓞 I.E)) ≤
      stepLe I x (de * t) := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  obtain ⟨-, -, -, -, -, hK, hw⟩ := GlobalTheory.T.autPoint_rational_equivariance I x γ a h1 h2 h3
  have hΛ := hK.1 ha.2.1
  obtain ⟨hA, -, -, -, hAt, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht
  obtain ⟨hS, -, -, -, -, -, hSt, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (de * t) (mul_pos hde ht)
  refine map_le_of_sizes (bas I) (frm I x) (GlobalTheory.NearLowerCompare.frm_isUnit I x)
    (GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg hS hA.1 _ ?_ hde ?_ hAt hSt
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ lamX I x := hA.1 hy
    have : Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E) y ∈ lamX I x := by
      rw [← hΛ]; exact ⟨y, hy', rfl⟩
    simpa [map_sub, Matrix.sub_mulVec] using (lamX I x).sub_mem this hy'
  · intro w
    refine normAt_sub_one_le I x _ w ?_
    rcases hw w with h | h
    · rw [h]; exact ha.2.2 _
    · rw [h, hs_conj_sub_one]; exact ha.2.2 _

/- English proof (translation)
Use `Set.eq_singleton_iff_unique_mem.2 ⟨GlobalTheory.Count.Test.one_mem_nearSet I x hde.le, fun a ha => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hn : I.n = 0`. Use `GlobalTheory.NearLowerCompare.subsingleton_GA I hn` as an intermediate fact. Conclude with `Subsingleton.elim _ _`. Establish `hn1 : 1 ≤ I.n` using `Nat.one_le_iff_ne_zero.2 hn`.

Take `⟨γ, h1, h2, h3⟩` from `ha.1`. Establish `hlow` using `lowers I x de hde γ a h1 h2 h3 ha 2 two_pos`. Establish `hbot : stepLe I x (de * 2) = ⊥` using `((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (de * 2) (by positivity)).2.2.2.2.2.2.2.2 hn1).2.1.2 (by linarith)`. Establish `hlat` using `GlobalTheory.NearLowerCompare.lamX_isLattice I x`. Establish `h0 : lamX I x ≠ ⊥`.

Introduce `h0`. Establish `h1` using `hlat.span_eq_top`. Rewrite `h1` using `[h0]`. Establish `: Nonempty (Fin I.n)` using `⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩`. Simplify using `at h1`.

Establish `hle : lamX I x ≤ stepLe I x 2`. Use `le_sSup ⟨le_rfl, h0, ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x).2.1 hn1]`. Conclude with `inv_le_of_inv_le₀ two_pos (by linarith)`. Establish `hz : Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) = 0`.

Use `LinearMap.ext_on hlat.span_eq_top fun y hy => ?_` and prove the remaining obligations. Use `hlow ⟨y, hle hy, rfl⟩` as an intermediate fact. Rewrite `this` using `[hbot, Submodule.mem_bot]`. Conclude with `this`. Establish `hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = 1` using `sub_eq_zero.1 (Matrix.toLin'.map_eq_zero_iff.1 hz)`.

Rewrite `h2`, `h3` using `[hγ]`. Use `Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))` and prove the remaining obligations. Use `h2 v` as an intermediate fact. Rewrite `this` using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))]`. Conclude with `this`.

Rewrite `h3` using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `h3`.
-/
theorem nearSet_eq (I : AutInst) (x : I.GA) (de : ℝ) (hde : 0 < de) (hde' : de < 1 / 4)
    (hl : 1 / 2 ≤ least I x) : nearSet I x de = {1} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨GlobalTheory.Count.Test.one_mem_nearSet I x hde.le, fun a ha => ?_⟩
  by_cases hn : I.n = 0
  · have := GlobalTheory.NearLowerCompare.subsingleton_GA I hn
    exact Subsingleton.elim _ _
  have hn1 : 1 ≤ I.n := Nat.one_le_iff_ne_zero.2 hn
  obtain ⟨γ, h1, h2, h3⟩ := ha.1
  have hlow := lowers I x de hde γ a h1 h2 h3 ha 2 two_pos
  have hbot : stepLe I x (de * 2) = ⊥ :=
    ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (de * 2) (by positivity)).2.2.2.2.2.2.2.2 hn1).2.1.2 (by linarith)
  have hlat := GlobalTheory.NearLowerCompare.lamX_isLattice I x
  have h0 : lamX I x ≠ ⊥ := by
    intro h0
    have h1 := hlat.span_eq_top
    rw [h0] at h1
    have : Nonempty (Fin I.n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    simp at h1
  have hle : lamX I x ≤ stepLe I x 2 := by
    refine le_sSup ⟨le_rfl, h0, ?_⟩
    rw [(GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x).2.1 hn1]
    exact inv_le_of_inv_le₀ two_pos (by linarith)
  have hz : Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) = 0 := by
    refine LinearMap.ext_on hlat.span_eq_top fun y hy => ?_
    have := hlow ⟨y, hle hy, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact this
  have hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = 1 :=
    sub_eq_zero.1 (Matrix.toLin'.map_eq_zero_iff.1 hz)
  rw [hγ] at h2 h3
  refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))
  · have := h2 v
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))] at this
    exact this
  · rw [Matrix.map_one _ (map_zero _) (map_one _)] at h3
    exact h3

/- English proof (translation)
Introduce `I x de h0 h1` and use `⟨lowers I x de h0, nearSet_eq I x de h0 h1⟩`.
-/
theorem near_lowers_steps : ∀ (I : AutInst) (x : I.GA) (de : ℝ), 0 < de → de < 1 / 4 → (∀ (γ : GL (Fin I.n) I.E) (a : I.GA), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → a ∈ nearSet I x de → ∀ t : ℝ, 0 < t → (stepLe I x t).map ((Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1)).restrictScalars (𝓞 I.E)) ≤ stepLe I x (de * t)) ∧ (1 / 2 ≤ least I x → nearSet I x de = {1}) :=
  fun I x de h0 h1 => ⟨lowers I x de h0, nearSet_eq I x de h0 h1⟩

end GlobalTheory.NearLower
