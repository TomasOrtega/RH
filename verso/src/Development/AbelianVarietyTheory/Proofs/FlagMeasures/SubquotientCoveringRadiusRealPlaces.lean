import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiusHomSubquotientSublatticeStatement

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Count.SubquotFrame

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec σ M u i).symm`.
-/
theorem map_mulVec' {n : ℕ} (σ : ℂ →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    M.map σ *ᵥ (fun i => σ (u i)) = fun i => σ ((M *ᵥ u) i) := by
  funext i
  exact (RingHom.map_mulVec σ M u i).symm

/- English proof (translation)
Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero σ) (map_one σ)]`.
-/
theorem map_inv' {n : ℕ} (σ : ℂ →+* ℂ) (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    (G.map σ)⁻¹ = G⁻¹.map σ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero σ) (map_one σ)]

/- English proof (translation)
Establish `hw : w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E)))`. Apply `(GlobalTheory.Count.FrameMajorant.comap_bijective I).1` to reduce the goal to its premises. Use `show w.comap (algebraMap I.F I.E) = (InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E)))).comap (algebraMap I.F I.E)`. Rewrite using `[InfinitePlace.comap_mk]`. Establish `hc : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) = (w.comap (algebraMap I.F I.E)).embedding`.

Use extensionality with `a`. Simplify using `[I.φ_over]`. Rewrite using `[hc, InfinitePlace.mk_embedding]`. Distinguish the cases in `h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))`. Use `⟨RingHom.id ℂ, fun z => rfl, fun z => rfl, fun a => by rw [h]; rfl, ?_⟩` and prove the remaining obligations.

Unfold `frm`. Rewrite using `[if_pos h]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `h2 : ComplexEmbedding.conjugate w.embedding = I.φ (w.comap (algebraMap I.F I.E))` using `(InfinitePlace.mk_eq_iff.mp ((InfinitePlace.mk_embedding w).trans hw)).resolve_left h`.

Use `⟨starRingEnd ℂ, fun z => Complex.conj_conj z, fun z => Complex.norm_conj z, fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h2]`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Unfold `frm`. Rewrite using `[if_neg h]`.
-/
theorem exists_invol (I : AutInst) (x : I.GA) (w : InfinitePlace I.E) :
    ∃ σ : ℂ →+* ℂ, (∀ z, σ (σ z) = z) ∧ (∀ z, ‖σ z‖ = ‖z‖) ∧
      (∀ a, w.embedding a = σ (I.φ (w.comap (algebraMap I.F I.E)) a)) ∧
      frm I x w = (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).map σ := by
  have hw : w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
    apply (GlobalTheory.Count.FrameMajorant.comap_bijective I).1
    show w.comap (algebraMap I.F I.E) =
      (InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E)))).comap (algebraMap I.F I.E)
    rw [InfinitePlace.comap_mk]
    have hc : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) =
        (w.comap (algebraMap I.F I.E)).embedding := by
      ext a
      simp [I.φ_over]
    rw [hc, InfinitePlace.mk_embedding]
  by_cases h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))
  · refine ⟨RingHom.id ℂ, fun z => rfl, fun z => rfl, fun a => by rw [h]; rfl, ?_⟩
    unfold frm
    rw [if_pos h]
    ext i j
    simp
  · have h2 : ComplexEmbedding.conjugate w.embedding = I.φ (w.comap (algebraMap I.F I.E)) :=
      (InfinitePlace.mk_eq_iff.mp ((InfinitePlace.mk_embedding w).trans hw)).resolve_left h
    refine ⟨starRingEnd ℂ, fun z => Complex.conj_conj z, fun z => Complex.norm_conj z, fun a => ?_, ?_⟩
    · rw [← h2]
      simp [ComplexEmbedding.conjugate_coe_eq]
    · unfold frm
      rw [if_neg h]

/- English proof (translation)
Rewrite using `[map_mulVec', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (M⁻¹ * T), Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]`.
-/
private theorem map_conj_mulVec_map_inv_mulVec {n : ℕ} (σ : ℂ →+* ℂ) (M T : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det)
    (u : Fin n → ℂ) :
    (M⁻¹ * T * M).map σ *ᵥ (fun i => σ ((M⁻¹ *ᵥ u) i)) = fun i => σ ((M⁻¹ *ᵥ (T *ᵥ u)) i) := by
  rw [map_mulVec', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (M⁻¹ * T),
    Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Consider the case `add y z _ _ hy hz`. Use `Submodule.add_mem _ hy hz using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec_add]`.

Consider the case `smul c y _ hy`. Use `Submodule.smul_mem _ (σ c) hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec_smul]`.
-/
private theorem map_mulVec_mem_span_image_of_mem_span {n : ℕ} (σ : ℂ →+* ℂ) (N : Matrix (Fin n) (Fin n) ℂ) (s : Set (Fin n → ℂ))
    (u : Fin n → ℂ) (hu : u ∈ Submodule.span ℂ s) :
    (fun i => σ ((N *ᵥ u) i)) ∈ Submodule.span ℂ ((fun u : Fin n → ℂ => fun i => σ ((N *ᵥ u) i)) '' s) := by
  induction hu using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext i
    simp
  | add y z _ _ hy hz =>
    convert Submodule.add_mem _ hy hz using 1
    funext i
    simp [Matrix.mulVec_add]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ (σ c) hy using 1
    funext i
    simp [Matrix.mulVec_smul]

/- English proof (translation)
Establish `key` using `map_mulVec' σ D (fun i => σ (z i))`. Simplify using `only [hσ] at key`. Rewrite `key` using `[h]`. Simplify using `only [hσ] at key`. Conclude with `key`.
-/
private theorem isCMExt_apply_apply {n : ℕ} (σ : ℂ →+* ℂ) (hσ : ∀ z, σ (σ z) = z) (D : Matrix (Fin n) (Fin n) ℂ)
    (z r : Fin n → ℂ) (h : D *ᵥ (fun i => σ (z i)) = fun i => σ (r i)) : D.map σ *ᵥ z = r := by
  have key := map_mulVec' σ D (fun i => σ (z i))
  simp only [hσ] at key
  rw [h] at key
  simp only [hσ] at key
  exact key

/- English proof (translation)
Establish `k1 : ∀ B : Matrix (Fin n) (Fin n) ℂ, P⁻¹ * (P * B) = B` using `fun B => by`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]`. Establish `k2 : ∀ B : Matrix (Fin n) (Fin n) ℂ, U⁻¹ * (U * B) = B` using `fun B => by`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]`. Rewrite using `[Matrix.mul_inv_rev]`.

Simplify using `only [Matrix.mul_assoc, k1, k2, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]`.
-/
private theorem inv_mul_inv_mul_conj_mul_mul_eq_self {n : ℕ} (P U Q : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P.det)
    (hU : IsUnit U.det) : U⁻¹ * P⁻¹ * (P * U * Q * (P * U)⁻¹) * P * U = Q := by
  have k1 : ∀ B : Matrix (Fin n) (Fin n) ℂ, P⁻¹ * (P * B) = B := fun B => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
  have k2 : ∀ B : Matrix (Fin n) (Fin n) ℂ, U⁻¹ * (U * B) = B := fun B => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc, k1, k2, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]

/- English proof (translation)
Simplify using `only [Formalism.REAL.hs, Matrix.map_apply, hσ]`.
-/
private theorem hs_map_of_norm_preserving {n : ℕ} (σ : ℂ →+* ℂ) (hσ : ∀ z, ‖σ z‖ = ‖z‖) (G : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (G.map σ) = Formalism.REAL.hs G := by
  simp only [Formalism.REAL.hs, Matrix.map_apply, hσ]

/- English proof (translation)
Introduce `I x A S R lo hi hA hSat hR hlo hhi hsz hlg T hTS hTA`. Establish `hfm` using `GlobalTheory.Count.FrameMajorant.frames_give_majorants I x`. Establish `: IsTotallyComplex I.E` using `hfm.1`. Establish `hnp : nPl I.E = I.f` using `hfm.2.1`. Establish `hbij` using `GlobalTheory.Count.FrameMajorant.comap_bijective I`.

Use `choose σ hσi hσn hσe hσf using fun w : InfinitePlace I.E => exists_invol I x w`. Establish `hPu : ∀ v, IsUnit (I.P v).det` using `fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)`. Establish `hUu : ∀ v, IsUnit (uMat (x.1 v)).det` using `fun v => (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)`. Establish `hMu : ∀ v, IsUnit (I.P v * uMat (x.1 v)).det` using `fun v => by`. Rewrite using `[Matrix.det_mul]`.

Conclude with `(hPu v).mul (hUu v)`. Establish `hco : ∀ (w : InfinitePlace I.E) (y : Fin I.n → I.E), Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => σ w (((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *ᵥ fun j => I.φ (w.comap (algebraMap I.F I.E)) (y j)) i)`. Introduce `w y`. Establish `hv : Formalism.HermitianLatticesTheory.vecAt (bas I) w y = fun i => σ w (I.φ (w.comap (algebraMap I.F I.E)) (y i))`. Use function extensionality and compare the values at `i`.

Simplify using `only [Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]`. Conclude with `hσe w (y i)`. Unfold `Formalism.HermitianLatticesTheory.fcoord`. Rewrite using `[hσf w, map_inv' (σ w) _ (hMu _), hv]`. Conclude with `map_mulVec' (σ w) _ _`.

Set `T' : InfinitePlace I.E → Matrix (Fin I.n) (Fin I.n) ℂ` to `fun w => ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ * T (w.comap (algebraMap I.F I.E)) * (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w)`. Establish `hT'S : ∀ w, ∀ y ∈ S, T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w y = 0`. Introduce `w y hy`. Use `show T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = 0`. Rewrite using `[hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _), hTS _ y hy]`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hT'A : ∀ w, ∀ y ∈ A, T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w y ∈ Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w '' (R : Set (Fin I.n → I.E)))`. Introduce `w y hy`. Use `show T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y ∈ Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w '' (R : Set (Fin I.n → I.E)))`.

Rewrite using `[hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _)]`. Use `Submodule.span_mono ?_ (map_mulVec_mem_span_image_of_mem_span (σ w) _ _ _ (hTA _ y hy))` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨r, hr, rfl⟩, rfl⟩`. Conclude with `⟨r, hr, hco w r⟩`. Take `⟨Φ, hΦS, hΦA, D', hD', hnorm⟩` from `GlobalTheory.T.coveringRadius_hom_subquotient_sublattice I.E I.n (frm I x) A S R lo hi (GlobalTheory.Count.FrameMajorant.frm_unit I x) hA hSat hR hlo hhi hsz hlg T' hT'S hT'A`.

Set `wv : InfinitePlace I.F → InfinitePlace I.E` to `Function.surjInv hbij.2`. Establish `hwv : ∀ w, wv (w.comap (algebraMap I.F I.E)) = w` using `fun w => hbij.1 (Function.surjInv_eq hbij.2 _)`. Use `⟨Φ, hΦS, hΦA, fun v => (I.P v * uMat (x.1 v)) * (D' (wv v)).map (σ (wv v)) * (I.P v * uMat (x.1 v))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Take `⟨w, rfl⟩` from `hbij.2 v`.

Introduce `u hu`. Simplify using `only [hwv]`. Unfold `spanAt at hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨y, hy, rfl⟩` from `hz`. Establish `e1` using `hD' w y hy`. Establish `hX : (frm I x w)⁻¹ * Φ.map w.embedding * frm I x w = ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ * Φ.map (I.φ (w.comap (algebraMap I.F I.E))) * (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w)`. Establish `hΦ : Φ.map w.embedding = (Φ.map (I.φ (w.comap (algebraMap I.F I.E)))).map (σ w)`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply]`. Conclude with `hσe w _`. Rewrite using `[hσf w, map_inv' (σ w) _ (hMu _), hΦ, ← Matrix.map_mul, ← Matrix.map_mul]`. Rewrite `e1` using `[hX]`. Express the relevant statement in the definitionally equal form `D' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = _ at e1`.

Establish `hsub : T' w - ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ * Φ.map (I.φ (w.comap (algebraMap I.F I.E))) * (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) = ((I.P (w.comap (algebraMap I.F I.E)) * uM …`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul]`. Use extensionality with `i j`. Simplify using `only [T', Matrix.sub_apply, Matrix.map_apply, map_sub]`. Rewrite `e1` using `[hsub]`.

Rewrite `e1` using `[hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _)]`. Establish `e2` using `isCMExt_apply_apply (σ w) (hσi w) _ _ _ e1`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hMu _), Matrix.one_mulVec]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]`.

Consider the case `smul c a _ ha => rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ha]`. Establish `hterm : ∀ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * ((I.P v * uMat (x.1 v)) * (D' (wv v)).map (σ (wv v)) * (I.P v * uMat (x.1 v))⁻¹) * I.P v * uMat (x.1 v)) = Formalism.REAL.hs (D' (wv v))`. Introduce `v`. Establish `hu : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹` using `by first`. Consider the case `rfl`.

Consider the case `simp only [Formalism.MainNotions.S.uMat, Subgroup.coe_inv, Matrix.coe_units_inv]`. Rewrite using `[hu, inv_mul_inv_mul_conj_mul_mul_eq_self _ _ _ (hPu v) (hUu v), hs_map_of_norm_preserving _ (hσn _)]`. Establish `hsum : ∑ v, Formalism.REAL.hs (D' (wv v)) = ∑ w, Formalism.REAL.hs (D' w)` using `(Fintype.sum_bijective _ hbij (fun w => Formalism.REAL.hs (D' w)) (fun v => Formalism.REAL.hs (D' (wv v))) (fun w => by rw [hwv w])).symm`. Unfold `normAt`. Simplify using `only [hterm]`.

Rewrite using `[hsum]`. Rewrite `hnorm` using `[hnp]`. Unfold `AutInst.rd`. Conclude with `hnorm`.
-/
theorem subquot_frame : ∀ (I : AutInst) (x : I.GA) (A S R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ), A.FG → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (bas I) (frm I x) N S) → largestSize (bas I) (frm I x) R ≤ hi → ∀ T : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ y ∈ S, T v *ᵥ (fun i => I.φ v (y i)) = 0) → (∀ v, ∀ y ∈ A, T v *ᵥ (fun i => I.φ v (y i)) ∈ spanAt I R v) → ∃ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ S, Φ *ᵥ y = 0) ∧ (∀ y ∈ A, Φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ u ∈ spanAt I A v, D v *ᵥ u = (T v - Φ.map (I.φ v)) *ᵥ u) ∧ normAt I x D ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt I.f * I.rd * hi / (2 * lo) := by
  intro I x A S R lo hi hA hSat hR hlo hhi hsz hlg T hTS hTA
  classical
  have hfm := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have : IsTotallyComplex I.E := hfm.1
  have hnp : nPl I.E = I.f := hfm.2.1
  have hbij := GlobalTheory.Count.FrameMajorant.comap_bijective I
  choose σ hσi hσn hσe hσf using fun w : InfinitePlace I.E => exists_invol I x w
  have hPu : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have hUu : ∀ v, IsUnit (uMat (x.1 v)).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hMu : ∀ v, IsUnit (I.P v * uMat (x.1 v)).det := fun v => by
    rw [Matrix.det_mul]
    exact (hPu v).mul (hUu v)

  have hco : ∀ (w : InfinitePlace I.E) (y : Fin I.n → I.E),
      Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => σ w (((I.P (w.comap (algebraMap I.F I.E)) *
        uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *ᵥ
          fun j => I.φ (w.comap (algebraMap I.F I.E)) (y j)) i) := by
    intro w y
    have hv : Formalism.HermitianLatticesTheory.vecAt (bas I) w y = fun i => σ w (I.φ (w.comap (algebraMap I.F I.E)) (y i)) := by
      funext i
      simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
      exact hσe w (y i)
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [hσf w, map_inv' (σ w) _ (hMu _), hv]
    exact map_mulVec' (σ w) _ _
  let T' : InfinitePlace I.E → Matrix (Fin I.n) (Fin I.n) ℂ := fun w =>
    ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
      T (w.comap (algebraMap I.F I.E)) *
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w)
  have hT'S : ∀ w, ∀ y ∈ S, T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w y = 0 := by
    intro w y hy
    show T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = 0
    rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _), hTS _ y hy]
    funext i
    simp
  have hT'A : ∀ w, ∀ y ∈ A, T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w y ∈
      Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w '' (R : Set (Fin I.n → I.E))) := by
    intro w y hy
    show T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y ∈
      Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w '' (R : Set (Fin I.n → I.E)))
    rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _)]
    refine Submodule.span_mono ?_ (map_mulVec_mem_span_image_of_mem_span (σ w) _ _ _ (hTA _ y hy))
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, hco w r⟩
  obtain ⟨Φ, hΦS, hΦA, D', hD', hnorm⟩ := GlobalTheory.T.coveringRadius_hom_subquotient_sublattice I.E I.n (frm I x) A S R lo hi
    (GlobalTheory.Count.FrameMajorant.frm_unit I x) hA hSat hR hlo hhi hsz hlg T' hT'S hT'A
  let wv : InfinitePlace I.F → InfinitePlace I.E := Function.surjInv hbij.2
  have hwv : ∀ w, wv (w.comap (algebraMap I.F I.E)) = w := fun w =>
    hbij.1 (Function.surjInv_eq hbij.2 _)
  refine ⟨Φ, hΦS, hΦA, fun v => (I.P v * uMat (x.1 v)) * (D' (wv v)).map (σ (wv v)) *
    (I.P v * uMat (x.1 v))⁻¹, ?_, ?_⟩
  · intro v
    obtain ⟨w, rfl⟩ := hbij.2 v
    intro u hu
    simp only [hwv]
    unfold spanAt at hu
    induction hu using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      have e1 := hD' w y hy
      have hX : (frm I x w)⁻¹ * Φ.map w.embedding * frm I x w =
          ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            Φ.map (I.φ (w.comap (algebraMap I.F I.E))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) := by
        have hΦ : Φ.map w.embedding = (Φ.map (I.φ (w.comap (algebraMap I.F I.E)))).map (σ w) := by
          ext i j
          simp only [Matrix.map_apply]
          exact hσe w _
        rw [hσf w, map_inv' (σ w) _ (hMu _), hΦ, ← Matrix.map_mul, ← Matrix.map_mul]
      rw [hX] at e1
      change D' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = _ at e1
      have hsub : T' w - ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            Φ.map (I.φ (w.comap (algebraMap I.F I.E))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) =
          ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            (T (w.comap (algebraMap I.F I.E)) - Φ.map (I.φ (w.comap (algebraMap I.F I.E)))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        ext i j
        simp only [T', Matrix.sub_apply, Matrix.map_apply, map_sub]
      rw [hsub] at e1
      rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _)] at e1
      have e2 := isCMExt_apply_apply (σ w) (hσi w) _ _ _ e1
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hMu _), Matrix.one_mulVec]
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]
    | smul c a _ ha => rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ha]
  · have hterm : ∀ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * ((I.P v * uMat (x.1 v)) *
        (D' (wv v)).map (σ (wv v)) * (I.P v * uMat (x.1 v))⁻¹) * I.P v * uMat (x.1 v)) =
        Formalism.REAL.hs (D' (wv v)) := by
      intro v
      have hu : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹ := by
        first
          | rfl
          | simp only [Formalism.MainNotions.S.uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
      rw [hu, inv_mul_inv_mul_conj_mul_mul_eq_self _ _ _ (hPu v) (hUu v), hs_map_of_norm_preserving _ (hσn _)]
    have hsum : ∑ v, Formalism.REAL.hs (D' (wv v)) = ∑ w, Formalism.REAL.hs (D' w) :=
      (Fintype.sum_bijective _ hbij (fun w => Formalism.REAL.hs (D' w)) (fun v => Formalism.REAL.hs (D' (wv v)))
        (fun w => by rw [hwv w])).symm
    unfold normAt
    simp only [hterm]
    rw [hsum]
    rw [hnp] at hnorm
    unfold AutInst.rd
    exact hnorm

end GlobalTheory.Count.SubquotFrame
