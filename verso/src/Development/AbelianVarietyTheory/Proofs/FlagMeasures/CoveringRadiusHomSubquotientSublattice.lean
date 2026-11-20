import Mathlib
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.Complexify
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBoundsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientLatticeRealizedIsometricallyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricRealisationOfSublatticeStatement

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.SubquotCover

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_pow]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`.
-/
theorem sum_normSq_eq_trace {a b : Type} [Fintype a] [Fintype b] (M : Matrix a b ℂ) :
    ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (Mᴴ * M) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[sum_normSq_eq_trace, sum_normSq_eq_trace, conjTranspose_mul, conjTranspose_mul]`. Establish `hmid : Qᴴ * (Mᴴ * Pᴴ) * (P * M * Q) = Qᴴ * (Mᴴ * M * Q)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Pᴴ P, hP, Matrix.one_mul]`.

Rewrite using `[hmid, Matrix.trace_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one]`.
-/
theorem sum_normSq_mul {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq b] [DecidableEq c]
    (P : Matrix a b ℂ) (M : Matrix b c ℂ) (Q : Matrix c d ℂ) (hP : Pᴴ * P = 1)
    (hQ : Q * Qᴴ = 1) :
    ∑ i, ∑ j, ‖(P * M * Q) i j‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace, conjTranspose_mul, conjTranspose_mul]
  have hmid : Qᴴ * (Mᴴ * Pᴴ) * (P * M * Q) = Qᴴ * (Mᴴ * M * Q) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, hP, Matrix.one_mul]
  rw [hmid, Matrix.trace_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [vecAt, Pi.basisFun_repr, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`.
-/
theorem vecAt_mulVec {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ}
    (w : InfinitePlace K) (M : Matrix (Fin a) (Fin b) K) (y : Fin b → K) :
    vecAt (Pi.basisFun K (Fin a)) w (M *ᵥ y)
      = M.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin b)) w y := by
  funext i
  simp only [vecAt, Pi.basisFun_repr, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    map_mul]

/- English proof (translation)
Rewrite using `[fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]`.
-/
theorem mulVec_fcoord {K : Type} [Field K] [NumberField K] [StarRing K] {a : ℕ}
    (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (w : InfinitePlace K) (hX : IsUnit (X w).det) (y : Fin a → K) :
    X w *ᵥ fcoord (Pi.basisFun K (Fin a)) X w y = vecAt (Pi.basisFun K (Fin a)) w y := by
  rw [fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]

/- English proof (translation)
Introduce `K _ _ _ _ n X A S R lo hi hX hA hSat hR hlo hhi hsize hlarge T hTS hTR`. Take `⟨m, q, X', Q, hm, hX', hQ, hqf, -, hQS, hqS, hspan, hN⟩` from `GlobalTheory.T.quotient_lattice_realized_isometrically K n X A S hX hA hSat`. Take `⟨r, e, X'', P, B, hr, hX'', hP, hPe, hB, hBspan, heB, hRB, hlB⟩` from `GlobalTheory.T.exists_isometric_realisation_of_sublattice' K n X R hX hR`. Take `⟨φ', hφ'B, hbound⟩` from `GlobalTheory.T.lattice_pair_volume_bounds K m r X' X'' (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K))) B lo hi hX' hX'' (hA.map _) hB hspan hBspan hlo hhi (fun N' hN' hN'0 => by`. Take `⟨N, hSN, hNA, heq⟩` from `hN N' hN' hN'0`.

Rewrite using `[← heq]`. Conclude with `hsize N hSN hNA)`. Use the proof step `(by rw [hlB]; exact hlarge) (fun w => (P w)ᴴ * T w * (Q w)ᴴ)`. Use `⟨e * φ' * q, ?_, ?_, fun w => P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Rewrite using `[← Matrix.mulVec_mulVec, hqS y hy, Matrix.mulVec_zero]`. Introduce `y hy`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Apply `heB` to reduce the goal to its premises. Apply `hφ'B` to reduce the goal to its premises.

Conclude with `Submodule.mem_map.mpr ⟨y, hy, by simp [Matrix.toLin'_apply]⟩`. Introduce `w y hy set u := fcoord (Pi.basisFun K (Fin n)) X w y with hu`. Establish `hQu : Q w *ᵥ u = fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y)` using `(hqf w y hy).symm`. Establish `hXu : X w *ᵥ u = vecAt (Pi.basisFun K (Fin n)) w y` using `mulVec_fcoord X w (hX w) y`. Establish `hX'u : X' w *ᵥ (Q w *ᵥ u) = q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y`.

Rewrite using `[hQu, mulVec_fcoord X' w (hX' w), vecAt_mulVec]`. Establish `hTQ : T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u)) = T w *ᵥ u`. Establish `hmem : u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))` using `hQS w u (Submodule.subset_span ⟨y, hy, rfl⟩)`. Establish `hker : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) ≤ LinearMap.ker (Matrix.mulVecLin (T w))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `hTS w z hz`. Establish `h0` using `hker hmem`. Rewrite `h0` using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, sub_eq_zero]`. Conclude with `h0.symm`.

Establish `hPP : ∀ v ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K))), P w *ᵥ ((P w)ᴴ *ᵥ v) = v`. Introduce `v hv`. Establish `hle : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K))) ≤ LinearMap.range (Matrix.mulVecLin (P w))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Take `⟨z, -, rfl⟩` from `hRB x hx`. Use `⟨(X'' w)⁻¹ *ᵥ vecAt (Pi.basisFun K (Fin r)) w z, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hPe w, ← Matrix.mulVec_mulVec, ← vecAt_mulVec]`. Both sides reduce to the same expression. Take `⟨z, rfl⟩` from `hle hv`.

Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec _ (P w)ᴴ, hP w, Matrix.one_mulVec]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Use `_ = T w *ᵥ u - ((X w)⁻¹ * e.map w.embedding) *ᵥ (φ'.map w.embedding *ᵥ (q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y)) := by`. Rewrite using `[hTQ, hPP _ (hTR w y hy), hX'u, hPe w]`.

Use `_ = (T w - (X w)⁻¹ * (e * φ' * q).map w.embedding * X w) *ᵥ u := by`. Rewrite using `[Matrix.sub_mulVec, ← hXu, Matrix.map_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `hm' : (m : ℝ) = (rkK A : ℝ) - rkK S` using `by rw [← hm]; push_cast; ring`. Establish `hr' : (r : ℝ) = rkK R` using `by rw [hr]`.

Rewrite using `[← hm', ← hr']`. Use `Eq.trans_le ?_ hbound` and prove the remaining obligations. Use `congr 1`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [Formalism.REAL.hs]`.

Conclude with `sum_normSq_mul (P w) _ (Q w) (hP w) (hQ w)`.
-/
theorem subquot_cover : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S R : Submodule (𝓞 K) (Fin n → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N S) → largestSize (Pi.basisFun K (Fin n)) X R ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ S, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = 0) → (∀ w, ∀ y ∈ A, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))) → ∃ φ : Matrix (Fin n) (Fin n) K, (∀ y ∈ S, φ *ᵥ y = 0) ∧ (∀ y ∈ A, φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ A, D w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = (T w - (X w)⁻¹ * φ.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ Real.sqrt (∑ w, Formalism.REAL.hs (D w)) ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt (nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (nPl K : ℝ))) * hi / (2 * lo) := by
  intro K _ _ _ _ n X A S R lo hi hX hA hSat hR hlo hhi hsize hlarge T hTS hTR
  obtain ⟨m, q, X', Q, hm, hX', hQ, hqf, -, hQS, hqS, hspan, hN⟩ :=
    GlobalTheory.T.quotient_lattice_realized_isometrically K n X A S hX hA hSat
  obtain ⟨r, e, X'', P, B, hr, hX'', hP, hPe, hB, hBspan, heB, hRB, hlB⟩ :=
    GlobalTheory.T.exists_isometric_realisation_of_sublattice' K n X R hX hR
  obtain ⟨φ', hφ'B, hbound⟩ := GlobalTheory.T.lattice_pair_volume_bounds K m r X' X''
    (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K))) B lo hi hX' hX'' (hA.map _) hB hspan
    hBspan hlo hhi
    (fun N' hN' hN'0 => by
      obtain ⟨N, hSN, hNA, heq⟩ := hN N' hN' hN'0
      rw [← heq]
      exact hsize N hSN hNA)
    (by rw [hlB]; exact hlarge) (fun w => (P w)ᴴ * T w * (Q w)ᴴ)
  refine ⟨e * φ' * q, ?_, ?_,
    fun w => P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w,
    ?_, ?_⟩
  · intro y hy
    rw [← Matrix.mulVec_mulVec, hqS y hy, Matrix.mulVec_zero]
  · intro y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    apply heB
    apply hφ'B
    exact Submodule.mem_map.mpr ⟨y, hy, by simp [Matrix.toLin'_apply]⟩
  · intro w y hy
    set u := fcoord (Pi.basisFun K (Fin n)) X w y with hu
    have hQu : Q w *ᵥ u = fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) := (hqf w y hy).symm
    have hXu : X w *ᵥ u = vecAt (Pi.basisFun K (Fin n)) w y := mulVec_fcoord X w (hX w) y
    have hX'u : X' w *ᵥ (Q w *ᵥ u) = q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y := by
      rw [hQu, mulVec_fcoord X' w (hX' w), vecAt_mulVec]

    have hTQ : T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u)) = T w *ᵥ u := by
      have hmem : u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈
          Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) :=
        hQS w u (Submodule.subset_span ⟨y, hy, rfl⟩)
      have hker : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))
          ≤ LinearMap.ker (Matrix.mulVecLin (T w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        exact hTS w z hz
      have h0 := hker hmem
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, sub_eq_zero] at h0
      exact h0.symm

    have hPP : ∀ v ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K))),
        P w *ᵥ ((P w)ᴴ *ᵥ v) = v := by
      intro v hv
      have hle : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))
          ≤ LinearMap.range (Matrix.mulVecLin (P w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨z, -, rfl⟩ := hRB x hx
        refine ⟨(X'' w)⁻¹ *ᵥ vecAt (Pi.basisFun K (Fin r)) w z, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hPe w, ← Matrix.mulVec_mulVec,
          ← vecAt_mulVec]
        rfl
      obtain ⟨z, rfl⟩ := hle hv
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec _ (P w)ᴴ, hP w, Matrix.one_mulVec]
    calc (P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w) *ᵥ u
        = P w *ᵥ ((P w)ᴴ *ᵥ (T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u))))
          - (P w * (X'' w)⁻¹) *ᵥ (φ'.map w.embedding *ᵥ (X' w *ᵥ (Q w *ᵥ u))) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
            Matrix.mul_assoc]
      _ = T w *ᵥ u - ((X w)⁻¹ * e.map w.embedding) *ᵥ (φ'.map w.embedding *ᵥ
            (q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y)) := by
          rw [hTQ, hPP _ (hTR w y hy), hX'u, hPe w]
      _ = (T w - (X w)⁻¹ * (e * φ' * q).map w.embedding * X w) *ᵥ u := by
          rw [Matrix.sub_mulVec, ← hXu, Matrix.map_mul, Matrix.map_mul]
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · have hm' : (m : ℝ) = (rkK A : ℝ) - rkK S := by rw [← hm]; push_cast; ring
    have hr' : (r : ℝ) = rkK R := by rw [hr]
    rw [← hm', ← hr']
    refine Eq.trans_le ?_ hbound
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Formalism.REAL.hs]
    exact sum_normSq_mul (P w) _ (Q w) (hP w) (hQ w)

end GlobalTheory.SubquotCover
