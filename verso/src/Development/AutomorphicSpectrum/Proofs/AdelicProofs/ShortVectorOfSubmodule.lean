import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineDegreeBundle
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.BaseChangeIndex
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealNormPrincipalInExtensionStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealLineLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMatrixPosDefConjugateStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LinearIndependentCoordinatesDenominatorStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianLatticeDegreeEqBundleDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SpanBaseChangeCoordinatesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Lines

noncomputable section

open scoped ComplexOrder nonZeroDivisors
open Matrix

abbrev extVec {K K' : Type} [Field K] [Field K'] [Algebra K K'] {n : ℕ} (w : Fin n → K) : Fin n → K' :=
  fun j => algebraMap K K' (w j)

/- English proof (translation)
Take `⟨S, hS⟩` from `hM`. Use `⟨S.image (extVec (K' := K')), le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ hx`. Simplify using `only [Finset.coe_image] at hx`.

Take `⟨w, hw, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨w, hS ▸ Submodule.subset_span hw, rfl⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Rewrite `hw` using `[SetLike.mem_coe]`.

Rewrite `hw` using `[← hS]`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)`. Consider the case `zero`. Establish `: extVec (K'` using `K') (0 : Fin n → K) = 0 := by funext j; simp [extVec]`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: extVec (K'` using `K') (x + y) = extVec x + extVec y := by funext j; simp [extVec]`. Rewrite `*` using `[SetLike.mem_coe]`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Establish `: extVec (K'` using `K') (a • x) = (algebraMap (𝓞 K) (𝓞 K') a) • extVec x := by`. Use function extensionality and compare the values at `j`.

Simplify using `only [extVec, Pi.smul_apply, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression. Rewrite `*` using `[SetLike.mem_coe]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem ext_span_fg {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] {n : ℕ}
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : M.FG) :
    (Submodule.span (𝓞 K') ((extVec (K' := K') : (Fin n → K) → (Fin n → K')) '' M)).FG := by
  classical
  obtain ⟨S, hS⟩ := hM
  refine ⟨S.image (extVec (K' := K')), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ hx
    simp only [Finset.coe_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Submodule.subset_span ⟨w, hS ▸ Submodule.subset_span hw, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe] at hw
    rw [← hS] at hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
    | zero =>
      have : extVec (K' := K') (0 : Fin n → K) = 0 := by funext j; simp [extVec]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : extVec (K' := K') (x + y) = extVec x + extVec y := by funext j; simp [extVec]
      rw [SetLike.mem_coe] at *
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : extVec (K' := K') (a • x) = (algebraMap (𝓞 K) (𝓞 K') a) • extVec x := by
        funext j
        simp only [extVec, Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [SetLike.mem_coe] at *
      rw [this]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[Submodule.span_span_of_tower, eq_top_iff]`. Establish `key : ∀ w : Fin n → K, extVec (K'` using `K') w ∈ Submodule.span K' ((extVec (K' := K') : (Fin n → K) → (Fin n → K')) '' M) := by`. Introduce `w`. Establish `hw : w ∈ Submodule.span K (M : Set (Fin n → K))` using `hM ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero`. Establish `: extVec (K'` using `K') (0 : Fin n → K) = 0 := by funext j; simp [extVec]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy`. Establish `: extVec (K'` using `K') (x + y) = extVec x + extVec y := by funext j; simp [extVec]`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Establish `: extVec (K'` using `K') (a • x) = (algebraMap K K' a) • extVec x := by`. Use function extensionality and compare the values at `j`. Simplify using `[extVec]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.

Rewrite using `[← (Pi.basisFun K' (Fin n)).span_eq]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Establish `: (Pi.basisFun K' (Fin n)) j = extVec (K'` using `K') (Pi.single j 1 : Fin n → K) := by`. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.basisFun_apply, extVec, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this]`. Conclude with `key _`.
-/
theorem ext_span_top {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] {n : ℕ}
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.span K (M : Set (Fin n → K)) = ⊤) :
    Submodule.span K' ((Submodule.span (𝓞 K') ((extVec (K' := K') : (Fin n → K) → (Fin n → K')) '' M) :
      Submodule (𝓞 K') (Fin n → K')) : Set (Fin n → K')) = ⊤ := by
  rw [Submodule.span_span_of_tower, eq_top_iff]
  have key : ∀ w : Fin n → K, extVec (K' := K') w ∈ Submodule.span K' ((extVec (K' := K') : (Fin n → K) → (Fin n → K')) '' M) := by
    intro w
    have hw : w ∈ Submodule.span K (M : Set (Fin n → K)) := hM ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : extVec (K' := K') (0 : Fin n → K) = 0 := by funext j; simp [extVec]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : extVec (K' := K') (x + y) = extVec x + extVec y := by funext j; simp [extVec]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : extVec (K' := K') (a • x) = (algebraMap K K' a) • extVec x := by
        funext j; simp [extVec]
      rw [this]; exact Submodule.smul_mem _ _ hx
  rw [← (Pi.basisFun K' (Fin n)).span_eq]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  have : (Pi.basisFun K' (Fin n)) j = extVec (K' := K') (Pi.single j 1 : Fin n → K) := by
    funext k
    simp only [Pi.basisFun_apply, extVec, Pi.single_apply]
    split_ifs <;> simp
  rw [this]
  exact key _

/- English proof (translation)
Use `set M : Submodule (𝓞 K') (Fin n → K') := Submodule.span (𝓞 K') ((fun (w : Fin n → K) j => algebraMap K K' (w j)) '' F.lattice) with hMdef`. Establish `hfg : M.FG` using `ext_span_fg F.lattice F.fg`. Establish `htop : Submodule.span K' (M : Set (Fin n → K')) = ⊤` using `ext_span_top F.lattice F.span_eq`. Take `⟨I, d, hI, hd, hIv, hidx⟩` from `GlobalTheory.T.ideal_line_lattice_index K' n M hfg htop v hv`. Take `⟨K'', _, _, _, y, hy0, hyI, hyN⟩` from `GlobalTheory.T.ideal_norm_principal_in_extension K' I hI`.

Use `letI algK : Algebra K K'' := ((algebraMap K' K'').comp (algebraMap K K')).toAlgebra`. Use `haveI tower : IsScalarTower K K' K'' := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hdL : (d : K') ≠ 0` using `by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]`. Establish `hyL : (y : K'') ≠ 0` using `by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]`. Use `set d'' : K'' := algebraMap K' K'' (d : K') with hd''`.

Establish `hd''0 : d'' ≠ 0` using `(map_ne_zero _).mpr hdL`. Use `set M'' : Submodule (𝓞 K'') (Fin n → K'') := Submodule.span (𝓞 K'') ((fun (w : Fin n → K) j => algebraMap K K'' (w j)) '' F.lattice) with hM''`. Establish `hext : ∀ u ∈ M, (fun j => algebraMap K' K'' (u j)) ∈ M''`. Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨w, hw, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨w, hw, rfl⟩`. Consider the case `zero`. Establish `: (fun j : Fin n => algebraMap K' K'' ((0 : Fin n → K') j)) = 0` using `by funext j; simp`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: (fun j => algebraMap K' K'' ((x + y) j)) = (fun j => algebraMap K' K'' (x j)) + (fun j => algebraMap K' K'' (y j))` using `by funext j; simp`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Establish `: (fun j => algebraMap K' K'' ((a • x) j)) = (algebraMap (𝓞 K') (𝓞 K'') a) • (fun j => algebraMap K' K'' (x j))`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`. Use `set x : Fin n → K'' := fun j => (y : K'') / d'' * algebraMap K' K'' (v j) with hx`. Establish `hxM : x ∈ M''`.

Establish `key : ∀ z ∈ I.map (algebraMap (𝓞 K') (𝓞 K'')), (fun j => (z : K'') / d'' * algebraMap K' K'' (v j)) ∈ M''`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨t, ht, rfl⟩` from `hz`.

Establish `h1` using `hext _ (hIv t ht)`. Use `h1 using 2 with j` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, map_div₀, hd'']`. Both sides reduce to the same expression. Consider the case `zero`.

Establish `: (fun j => ((0 : 𝓞 K'') : K'') / d'' * algebraMap K' K'' (v j)) = 0` using `by funext j; simp`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb`. Establish `: (fun j => ((a + b : 𝓞 K'') : K'') / d'' * algebraMap K' K'' (v j)) = (fun j => (a : K'') / d'' * algebraMap K' K'' (v j)) + (fun j => (b : K'') / d'' * algebraMap K' K'' (v j))`.

Use function extensionality and compare the values at `j`. Simplify using `only [Pi.add_apply, map_add, add_div, add_mul]`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul a b _ hb`.

Establish `: (fun j => ((a • b : 𝓞 K'') : K'') / d'' * algebraMap K' K'' (v j)) = a • (fun j => (b : K'') / d'' * algebraMap K' K'' (v j))`. Use function extensionality and compare the values at `j`. Establish `e : ((a • b : 𝓞 K'') : K'') = (a : K'') * (b : K'')` using `rfl`. Rewrite using `[e, Pi.smul_apply, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `_ = (a : K'') * _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hb`. Conclude with `key y hyI`. Establish `hx0 : x ≠ 0`.

Take `⟨j, hj⟩` from `Function.ne_iff.mp hv`. Introduce `h`. Use `congrFun h j` as an intermediate fact. Simplify using `only [hx, Pi.zero_apply, mul_eq_zero, div_eq_zero_iff] at this`. Break down `this with (h | h) | h` into its components or cases.

Conclude with `hyL h`. Conclude with `hd''0 h`. Conclude with `hj ((map_eq_zero _).mp h)`. Use `⟨K'', inferInstance, inferInstance, algK, x, hx0, hxM, ?_⟩` and prove the remaining obligations. Use `set Q : (K' →+* ℂ) → ℝ := fun σ => (star (fun j => σ (v j)) ⬝ᵥ (F.metric (σ.comp (algebraMap K K')) *ᵥ fun j => σ (v j))).re with hQ`.

Establish `hQpos : ∀ σ, 0 < Q σ` using `fun σ => by`. Establish `hne : (fun j => σ (v j)) ≠ 0`. Take `⟨j, hj⟩` from `Function.ne_iff.mp hv`. Introduce `h`. Conclude with `hj ((map_eq_zero _).mp (congrFun h j))`.

Conclude with `(GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.quad_pos (F.posDef _) hne).2`. Use `set r : ℝ := (Module.finrank K' K'' : ℝ) with hr`. Establish `hrpos : 0 < r`. Establish `: 0 < Module.finrank K' K''` using `Module.finrank_pos`. Rewrite using `[hr]`.

Conclude with `this` after adjusting the coercions. Establish `hfr : (Module.finrank ℚ K'' : ℝ) = Module.finrank ℚ K' * r`. Rewrite using `[hr, ← Module.finrank_mul_finrank ℚ K' K'']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hfr' : (0 : ℝ) < Module.finrank ℚ K'`. Establish `: 0 < Module.finrank ℚ K'` using `Module.finrank_pos`. Conclude with `this` after adjusting the coercions. Establish `hNI : (0 : ℝ) < I.absNorm`. Use `Ideal.absNorm_eq_zero_iff.not.mpr hI` as an intermediate fact.

Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions. Establish `hNd : (0 : ℝ) < |((Algebra.norm ℚ (d : K') : ℚ) : ℝ)|`. Rewrite using `[abs_pos]`. Conclude with `(Algebra.norm_ne_zero_iff.mpr hdL)` after adjusting the coercions. Establish `hterm : ∀ τ : K'' →+* ℂ, Real.log (Real.sqrt (star (fun j => τ (x j)) ⬝ᵥ (F.metric (τ.comp (algebraMap K K'')) *ᵥ fun j => τ (x j))).re) = Real.log ‖τ (y : K'')‖ - Real.log ‖(τ.comp (algebraMap K' K'')) (d : K')‖ + 1 / 2 * Real.log (Q (τ.comp (algebraMap K' K'')))`.

Introduce `τ`. Use `set σ := τ.comp (algebraMap K' K'') with hσ`. Establish `hcomp : τ.comp (algebraMap K K'') = σ.comp (algebraMap K K')` using `rfl`. Establish `hτx : (fun j => τ (x j)) = (τ (y : K'') / σ (d : K')) • (fun j => σ (v j))`. Use function extensionality and compare the values at `j`.

Simplify using `only [hx, map_mul, map_div₀, Pi.smul_apply, smul_eq_mul, hd'']`. Both sides reduce to the same expression. Establish `hc : τ (y : K'') / σ (d : K') ≠ 0` using `div_ne_zero ((map_ne_zero _).mpr hyL) ((map_ne_zero _).mpr hdL)`. Rewrite using `[hcomp, hτx, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.quad_smul]`. Establish `hs : star (τ (y : K'') / σ (d : K')) * (τ (y : K'') / σ (d : K')) = ((‖τ (y : K'') / σ (d : K')‖ ^ 2 : ℝ) : ℂ)`.

Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hs, Complex.re_ofReal_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _), Real.log_mul (by positivity) (Real.sqrt_pos.mpr (hQpos σ)).ne', Real.log_sqrt (hQpos σ).le, norm_div, Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hyL)) (norm_ne_zero_iff.mpr ((map …`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsum : ∑ τ : K'' →+* ℂ, Real.log (Real.sqrt (star (fun j => τ (x j)) ⬝ᵥ (F.metric (τ.comp (algebraMap K K'')) *ᵥ fun j => τ (x j))).re) = r * (Real.log I.absNorm - Real.log |((Algebra.norm ℚ (d : K') : ℚ) : ℝ)| + 1 / 2 * ∑ σ : K' →+* ℂ, Real.log (Q σ))`. Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.sum_log_norm hyL, hyN, GroundTheory.Heights₂.Heights.LatticeLemmas.sum_comp_algebraMap K'' (fun σ => Real.log ‖σ (d : K')‖), GroundTh …`. Expand and normalize the polynomial expressions, which then agree. Establish `hgram : ∀ σ : K' →+* ℂ, Real.log (gramAt (F.metric (σ.comp (algebraMap K K'))) σ (fun _ : Fin 1 => v)).det.re = Real.log (Q σ)`.

Introduce `σ`. Rewrite using `[Matrix.det_fin_one]`. Both sides reduce to the same expression. Establish `hline : F.lineDegree K' v = (Real.log |((Algebra.norm ℚ (d : K') : ℚ) : ℝ)| - Real.log I.absNorm - 1 / 2 * ∑ σ : K' →+* ℂ, Real.log (Q σ)) / Module.finrank ℚ K'`. Rewrite using `[HermLattice.lineDegree, normalise, subDegree, hidx, Real.log_div hNd.ne' hNI.ne']`.

Repeatedly rewrite using `[hgram]`. Rewrite using `[hline, mean, hsum, hfr]`. Apply `le_of_eq` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lattice_line (K : Type) [Field K] [NumberField K] (n : ℕ) (F : HermLattice K n)
    (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (v : Fin n → K') (hv : v ≠ 0) :
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K K'') (x : Fin n → K''), x ≠ 0 ∧
      x ∈ Submodule.span (𝓞 K'') ((fun (w : Fin n → K) j => algebraMap K K'' (w j)) '' F.lattice) ∧
      F.lineDegree K' v ≤ -mean K'' (fun τ => Real.log (Real.sqrt
        (star (fun j => τ (x j)) ⬝ᵥ (F.metric (τ.comp (algebraMap K K'')) *ᵥ fun j => τ (x j))).re)) := by
  classical
  set M : Submodule (𝓞 K') (Fin n → K') :=
    Submodule.span (𝓞 K') ((fun (w : Fin n → K) j => algebraMap K K' (w j)) '' F.lattice) with hMdef
  have hfg : M.FG := ext_span_fg F.lattice F.fg
  have htop : Submodule.span K' (M : Set (Fin n → K')) = ⊤ := ext_span_top F.lattice F.span_eq
  obtain ⟨I, d, hI, hd, hIv, hidx⟩ := GlobalTheory.T.ideal_line_lattice_index K' n M hfg htop v hv
  obtain ⟨K'', _, _, _, y, hy0, hyI, hyN⟩ := GlobalTheory.T.ideal_norm_principal_in_extension K' I hI
  letI algK : Algebra K K'' := ((algebraMap K' K'').comp (algebraMap K K')).toAlgebra
  haveI tower : IsScalarTower K K' K'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hdL : (d : K') ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hyL : (y : K'') ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  set d'' : K'' := algebraMap K' K'' (d : K') with hd''
  have hd''0 : d'' ≠ 0 := (map_ne_zero _).mpr hdL
  set M'' : Submodule (𝓞 K'') (Fin n → K'') :=
    Submodule.span (𝓞 K'') ((fun (w : Fin n → K) j => algebraMap K K'' (w j)) '' F.lattice) with hM''
  have hext : ∀ u ∈ M, (fun j => algebraMap K' K'' (u j)) ∈ M'' := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    | zero =>
      have : (fun j : Fin n => algebraMap K' K'' ((0 : Fin n → K') j)) = 0 := by funext j; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun j => algebraMap K' K'' ((x + y) j)) =
          (fun j => algebraMap K' K'' (x j)) + (fun j => algebraMap K' K'' (y j)) := by funext j; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun j => algebraMap K' K'' ((a • x) j)) =
          (algebraMap (𝓞 K') (𝓞 K'') a) • (fun j => algebraMap K' K'' (x j)) := by
        funext j
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [this]; exact Submodule.smul_mem _ _ hx
  set x : Fin n → K'' := fun j => (y : K'') / d'' * algebraMap K' K'' (v j) with hx
  have hxM : x ∈ M'' := by
    have key : ∀ z ∈ I.map (algebraMap (𝓞 K') (𝓞 K'')),
        (fun j => (z : K'') / d'' * algebraMap K' K'' (v j)) ∈ M'' := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨t, ht, rfl⟩ := hz
        have h1 := hext _ (hIv t ht)
        convert h1 using 2 with j
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_div₀, hd'']
        rfl
      | zero =>
        have : (fun j => ((0 : 𝓞 K'') : K'') / d'' * algebraMap K' K'' (v j)) = 0 := by funext j; simp
        rw [this]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : (fun j => ((a + b : 𝓞 K'') : K'') / d'' * algebraMap K' K'' (v j)) =
            (fun j => (a : K'') / d'' * algebraMap K' K'' (v j)) +
              (fun j => (b : K'') / d'' * algebraMap K' K'' (v j)) := by
          funext j
          simp only [Pi.add_apply, map_add, add_div, add_mul]
        rw [this]; exact Submodule.add_mem _ ha hb
      | smul a b _ hb =>
        have : (fun j => ((a • b : 𝓞 K'') : K'') / d'' * algebraMap K' K'' (v j)) =
            a • (fun j => (b : K'') / d'' * algebraMap K' K'' (v j)) := by
          funext j
          have e : ((a • b : 𝓞 K'') : K'') = (a : K'') * (b : K'') := rfl
          rw [e, Pi.smul_apply, Algebra.smul_def]
          change _ = (a : K'') * _
          ring
        rw [this]; exact Submodule.smul_mem _ _ hb
    exact key y hyI
  have hx0 : x ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    intro h
    have := congrFun h j
    simp only [hx, Pi.zero_apply, mul_eq_zero, div_eq_zero_iff] at this
    rcases this with (h | h) | h
    · exact hyL h
    · exact hd''0 h
    · exact hj ((map_eq_zero _).mp h)
  refine ⟨K'', inferInstance, inferInstance, algK, x, hx0, hxM, ?_⟩
  set Q : (K' →+* ℂ) → ℝ := fun σ => (star (fun j => σ (v j)) ⬝ᵥ
    (F.metric (σ.comp (algebraMap K K')) *ᵥ fun j => σ (v j))).re with hQ
  have hQpos : ∀ σ, 0 < Q σ := fun σ => by
    have hne : (fun j => σ (v j)) ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      intro h
      exact hj ((map_eq_zero _).mp (congrFun h j))
    exact (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.quad_pos (F.posDef _) hne).2
  set r : ℝ := (Module.finrank K' K'' : ℝ) with hr
  have hrpos : 0 < r := by
    have : 0 < Module.finrank K' K'' := Module.finrank_pos
    rw [hr]; exact_mod_cast this
  have hfr : (Module.finrank ℚ K'' : ℝ) = Module.finrank ℚ K' * r := by
    rw [hr, ← Module.finrank_mul_finrank ℚ K' K'']
    push_cast; ring
  have hfr' : (0 : ℝ) < Module.finrank ℚ K' := by
    have : 0 < Module.finrank ℚ K' := Module.finrank_pos
    exact_mod_cast this
  have hNI : (0 : ℝ) < I.absNorm := by
    have := Ideal.absNorm_eq_zero_iff.not.mpr hI
    exact_mod_cast Nat.pos_of_ne_zero this
  have hNd : (0 : ℝ) < |((Algebra.norm ℚ (d : K') : ℚ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hdL)
  have hterm : ∀ τ : K'' →+* ℂ, Real.log (Real.sqrt
      (star (fun j => τ (x j)) ⬝ᵥ (F.metric (τ.comp (algebraMap K K'')) *ᵥ fun j => τ (x j))).re) =
      Real.log ‖τ (y : K'')‖ - Real.log ‖(τ.comp (algebraMap K' K'')) (d : K')‖ +
        1 / 2 * Real.log (Q (τ.comp (algebraMap K' K''))) := by
    intro τ
    set σ := τ.comp (algebraMap K' K'') with hσ
    have hcomp : τ.comp (algebraMap K K'') = σ.comp (algebraMap K K') := rfl
    have hτx : (fun j => τ (x j)) = (τ (y : K'') / σ (d : K')) • (fun j => σ (v j)) := by
      funext j
      simp only [hx, map_mul, map_div₀, Pi.smul_apply, smul_eq_mul, hd'']
      rfl
    have hc : τ (y : K'') / σ (d : K') ≠ 0 :=
      div_ne_zero ((map_ne_zero _).mpr hyL) ((map_ne_zero _).mpr hdL)
    rw [hcomp, hτx, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.quad_smul]
    have hs : star (τ (y : K'') / σ (d : K')) * (τ (y : K'') / σ (d : K')) =
        ((‖τ (y : K'') / σ (d : K')‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']
      push_cast; rfl
    rw [hs, Complex.re_ofReal_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _),
      Real.log_mul (by positivity) (Real.sqrt_pos.mpr (hQpos σ)).ne', Real.log_sqrt (hQpos σ).le,
      norm_div, Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hyL))
        (norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hdL))]
    ring
  have hsum : ∑ τ : K'' →+* ℂ, Real.log (Real.sqrt
      (star (fun j => τ (x j)) ⬝ᵥ (F.metric (τ.comp (algebraMap K K'')) *ᵥ fun j => τ (x j))).re) =
      r * (Real.log I.absNorm - Real.log |((Algebra.norm ℚ (d : K') : ℚ) : ℝ)| +
        1 / 2 * ∑ σ : K' →+* ℂ, Real.log (Q σ)) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.sum_log_norm hyL, hyN,
      GroundTheory.Heights₂.Heights.LatticeLemmas.sum_comp_algebraMap K'' (fun σ => Real.log ‖σ (d : K')‖),
      GroundTheory.Heights₂.Heights.LatticeLemmas.sum_comp_algebraMap K'' (fun σ => Real.log (Q σ)),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.sum_log_norm hdL, Real.log_pow]
    ring
  have hgram : ∀ σ : K' →+* ℂ, Real.log (gramAt (F.metric (σ.comp (algebraMap K K'))) σ (fun _ : Fin 1 => v)).det.re =
      Real.log (Q σ) := by
    intro σ
    rw [Matrix.det_fin_one]
    rfl
  have hline : F.lineDegree K' v =
      (Real.log |((Algebra.norm ℚ (d : K') : ℚ) : ℝ)| - Real.log I.absNorm -
        1 / 2 * ∑ σ : K' →+* ℂ, Real.log (Q σ)) / Module.finrank ℚ K' := by
    rw [HermLattice.lineDegree, normalise, subDegree, hidx, Real.log_div hNd.ne' hNI.ne']
    simp_rw [hgram]
  rw [hline, mean, hsum, hfr]
  apply le_of_eq
  field_simp
  ring

/- English proof (translation)
Introduce `hS L _ _ B F hF`. Use `haveI : Module.IsTorsionFree (𝓞 L) B.carrier := inferInstance`. Use `haveI : Module.IsTorsionFree (𝓞 L) F := Function.Injective.moduleIsTorsionFree F.subtype Subtype.val_injective (fun _ _ => rfl)`. Use `haveI : Module.Finite (𝓞 L) F := inferInstance`. Use `set i : ℕ := B.rank F with hi`.

Use `set f : Fin i → F := (HermitianBundle.exists_linearIndependent_rank B F).choose with hfdef`. Establish `hf : LinearIndependent (𝓞 L) f` using `(HermitianBundle.exists_linearIndependent_rank B F).choose_spec`. Establish `hf' : LinearIndependent (𝓞 L) (fun j => (f j : B.carrier))` using `hf.map' F.subtype (Submodule.ker_subtype F)`. Take `⟨c, hcinj, hcf, hcD⟩` from `GlobalTheory.T.linear_independent_coordinates_denominator L F i f hf rfl`. Take `⟨hpos, hconj⟩` from `GlobalTheory.T.gram_matrix_pos_def_conjugate L B i _ hf'`.

Establish `hspan : Submodule.span L ((LinearMap.range c : Submodule (𝓞 L) (Fin i → L)) : Set (Fin i → L)) = ⊤`. Rewrite using `[eq_top_iff, ← (Pi.basisFun L (Fin i)).span_eq]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `Submodule.subset_span ⟨f j, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcf j]`. Use function extensionality and compare the values at `k`. Simplify using `[Pi.single_apply, Pi.basisFun_apply]`. Set `Fl : HermLattice L i` to `{ lattice := LinearMap.range c fg := by`. Establish `: (⊤ : Submodule (𝓞 L) F).FG` using `Module.Finite.fg_top`.

Rewrite using `[LinearMap.range_eq_map]`. Conclude with `this.map c`. Use `span_eq := hspan`. Use `metric := fun σ => gramMat B σ (fun j => (f j : B.carrier))`. Use `posDef := hpos`.

Use `conj := hconj }`. Establish `hdeg : Fl.degree = B.degreeWith F f` using `GlobalTheory.T.hermitian_lattice_degree_eq_bundle_degree L B F i f c Fl hf rfl hcinj hcf rfl (fun _ => rfl)`. Establish `hslope : Fl.slope = B.slope F`. Rewrite using `[HermLattice.slope, normalise, hdeg]`. Both sides reduce to the same expression.

Establish `hne : ∃ x : F, x ≠ 0`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff F).mp hF`. Conclude with `⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩`. Establish `hi1 : 1 ≤ i`. Take `⟨x, hx⟩` from `hne`.

Establish `h1 : LinearIndependent (𝓞 L) (fun _ : Fin 1 => x)`. Rewrite using `[linearIndependent_unique_iff]`. Conclude with `fun h => hx h`. Establish `h2` using `h1.fintype_card_le_finrank`. Rewrite `h2` using `[Fintype.card_fin]`.

Conclude with `h2`. Establish `hile : i ≤ Module.finrank (𝓞 L) B.carrier` using `Submodule.finrank_le F`. Take `⟨K', _, _, _, v, hv, hle⟩` from `hS L i hi1 Fl 1 one_pos`. Take `⟨K'', _, _, _, x, hx0, hxM, hlin⟩` from `lattice_line L i Fl K' v hv`. Take `⟨X, hX⟩` from `GlobalTheory.T.baseChange_inner_self_eq_gramMat_form L B F i f c hcD K'' x hxM`.

Use `⟨K'', inferInstance, inferInstance, inferInstance, X, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Take `⟨τ⟩ : Nonempty (K'' →+* ℂ)` from `inferInstance`. Establish `h` using `hX τ`. Establish `hne' : (fun j => τ (x j)) ≠ 0`.

Take `⟨j, hj⟩` from `Function.ne_iff.mp hx0`. Introduce `h`. Conclude with `hj ((map_eq_zero _).mp (congrFun h j))`. Establish `hq` using `(GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.quad_pos (Fl.posDef (τ.comp (algebraMap L K''))) hne').2`. Express the relevant statement in the definitionally equal form `0 < (star (fun j => τ (x j)) ⬝ᵥ (gramMat B (τ.comp (algebraMap L K'')) (fun j => (f j : B.carrier)) *ᵥ fun j => τ (x j))).re at hq`.

Rewrite `hq` using `[← h, TensorProduct.tmul_zero]`. Establish `h0` using `((B.baseChange K'').metric.form τ).add_left 0 0 0`. Simplify using `only [add_zero] at h0`. Establish `h00 : ((B.baseChange K'').metric.form τ).inner 0 0 = 0` using `by simpa using h0`. Rewrite `hq` using `[h00]`.

Simplify using `at hq`. Establish `hlog : Real.log i ≤ Real.log (Module.finrank (𝓞 L) B.carrier)` using `Real.log_le_log (by exact_mod_cast hi1) (by exact_mod_cast hile)`. Establish `hmean : (fun σ : K'' →+* ℂ => Real.log (Real.sqrt (((B.baseChange K'').metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K''] X) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K''] X) : ℂ).re)) = (fun τ => Real.log (Real.sqrt (star (fun j => τ (x j)) ⬝ᵥ (Fl.metric (τ.comp (algebraMap L K'')) *ᵥ fun j => τ ( …`. Use function extensionality and compare the values at `τ`. Rewrite using `[hX τ]`.

Rewrite using `[hmean]`. Rewrite `hle` using `[hslope]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem short_vector_of_submodule : LineOfLargeDegree.Statement → ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier), F ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (x : (B.baseChange L').carrier), x ≠ 0 ∧ B.slope F - 1 / 2 * Real.log (Module.finrank (𝓞 L) B.carrier) - 1 ≤ -mean L' (fun σ => Real.log (Real.sqrt (((B.baseChange L').metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L'] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L'] x) : ℂ).re)) := by
  intro hS L _ _ B F hF
  classical
  haveI : Module.IsTorsionFree (𝓞 L) B.carrier := inferInstance
  haveI : Module.IsTorsionFree (𝓞 L) F :=
    Function.Injective.moduleIsTorsionFree F.subtype Subtype.val_injective (fun _ _ => rfl)
  haveI : Module.Finite (𝓞 L) F := inferInstance
  set i : ℕ := B.rank F with hi
  set f : Fin i → F := (HermitianBundle.exists_linearIndependent_rank B F).choose with hfdef
  have hf : LinearIndependent (𝓞 L) f := (HermitianBundle.exists_linearIndependent_rank B F).choose_spec
  have hf' : LinearIndependent (𝓞 L) (fun j => (f j : B.carrier)) := hf.map' F.subtype (Submodule.ker_subtype F)
  obtain ⟨c, hcinj, hcf, hcD⟩ := GlobalTheory.T.linear_independent_coordinates_denominator L F i f hf rfl
  obtain ⟨hpos, hconj⟩ := GlobalTheory.T.gram_matrix_pos_def_conjugate L B i _ hf'
  have hspan : Submodule.span L ((LinearMap.range c : Submodule (𝓞 L) (Fin i → L)) : Set (Fin i → L)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun L (Fin i)).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨f j, ?_⟩
    rw [hcf j]
    funext k
    simp [Pi.single_apply, Pi.basisFun_apply]
  let Fl : HermLattice L i :=
    { lattice := LinearMap.range c
      fg := by
        have : (⊤ : Submodule (𝓞 L) F).FG := Module.Finite.fg_top
        rw [LinearMap.range_eq_map]
        exact this.map c
      span_eq := hspan
      metric := fun σ => gramMat B σ (fun j => (f j : B.carrier))
      posDef := hpos
      conj := hconj }
  have hdeg : Fl.degree = B.degreeWith F f := GlobalTheory.T.hermitian_lattice_degree_eq_bundle_degree L B F i f c Fl hf rfl hcinj hcf rfl (fun _ => rfl)
  have hslope : Fl.slope = B.slope F := by
    rw [HermLattice.slope, normalise, hdeg]
    rfl
  have hne : ∃ x : F, x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff F).mp hF
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  have hi1 : 1 ≤ i := by
    obtain ⟨x, hx⟩ := hne
    have h1 : LinearIndependent (𝓞 L) (fun _ : Fin 1 => x) := by
      rw [linearIndependent_unique_iff]
      exact fun h => hx h
    have h2 := h1.fintype_card_le_finrank
    rw [Fintype.card_fin] at h2
    exact h2
  have hile : i ≤ Module.finrank (𝓞 L) B.carrier := Submodule.finrank_le F
  obtain ⟨K', _, _, _, v, hv, hle⟩ := hS L i hi1 Fl 1 one_pos
  obtain ⟨K'', _, _, _, x, hx0, hxM, hlin⟩ := lattice_line L i Fl K' v hv
  obtain ⟨X, hX⟩ := GlobalTheory.T.baseChange_inner_self_eq_gramMat_form L B F i f c hcD K'' x hxM
  refine ⟨K'', inferInstance, inferInstance, inferInstance, X, ?_, ?_⟩
  · rintro rfl
    obtain ⟨τ⟩ : Nonempty (K'' →+* ℂ) := inferInstance
    have h := hX τ
    have hne' : (fun j => τ (x j)) ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hx0
      intro h
      exact hj ((map_eq_zero _).mp (congrFun h j))
    have hq := (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LineDegreeBundle.quad_pos (Fl.posDef (τ.comp (algebraMap L K''))) hne').2
    change 0 < (star (fun j => τ (x j)) ⬝ᵥ (gramMat B (τ.comp (algebraMap L K'')) (fun j => (f j : B.carrier)) *ᵥ fun j => τ (x j))).re at hq
    rw [← h, TensorProduct.tmul_zero] at hq
    have h0 := ((B.baseChange K'').metric.form τ).add_left 0 0 0
    simp only [add_zero] at h0
    have h00 : ((B.baseChange K'').metric.form τ).inner 0 0 = 0 := by simpa using h0
    rw [h00] at hq
    simp at hq
  · have hlog : Real.log i ≤ Real.log (Module.finrank (𝓞 L) B.carrier) :=
      Real.log_le_log (by exact_mod_cast hi1) (by exact_mod_cast hile)
    have hmean : (fun σ : K'' →+* ℂ => Real.log (Real.sqrt (((B.baseChange K'').metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K''] X) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K''] X) : ℂ).re)) =
        (fun τ => Real.log (Real.sqrt
        (star (fun j => τ (x j)) ⬝ᵥ (Fl.metric (τ.comp (algebraMap L K'')) *ᵥ fun j => τ (x j))).re)) := by
      funext τ
      rw [hX τ]
    rw [hmean]
    rw [hslope] at hle
    linarith

end
end GlobalTheory.CompanionTheory.Ar.Lines
