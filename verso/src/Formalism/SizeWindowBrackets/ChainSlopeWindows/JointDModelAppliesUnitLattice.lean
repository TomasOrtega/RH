import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf
import Formalism.SizeWindowBrackets.ChainSlopeWindows.CorollaryModelSideCondition
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)

section Lin

variable {m n o : Type} [Fintype m] [Fintype n] [Fintype o] [DecidableEq m] [DecidableEq n]
  [DecidableEq o]

/- English proof (authored)
In the standard Euclidean coordinate bases, the matrix of a composite is the product of the two matrices, in the same order as their action. Thus the maps represented by both sides agree.
-/
theorem to_euclidean_lin_mul (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B :=
  Matrix.toLpLin_mul 2 2 2 A B

/- English proof (authored)
The identity matrix sends each coordinate basis vector to itself, so its corresponding Euclidean linear map is the identity.
-/
theorem to_euclidean_lin_one : Matrix.toEuclideanLin (1 : Matrix n n ℂ) = LinearMap.id :=
  Matrix.toLpLin_one 2

/- English proof (authored)
Use the standard orthonormal coordinate basis for the map represented by A. The trace is the sum of its diagonal coefficients in that basis, which is the matrix trace of A.
-/
theorem to_euclidean_lin_trace (A : Matrix n n ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ n) (Matrix.toEuclideanLin A) = A.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

/- English proof (authored)
In the standard orthonormal coordinate bases, the adjoint has the conjugate transpose matrix. Translating that matrix back to a Euclidean map gives the stated adjoint.
-/
theorem to_euclidean_lin_adjoint_eq (A : Matrix m n ℂ) :
    LinearMap.adjoint (Matrix.toEuclideanLin A) = Matrix.toEuclideanLin Aᴴ :=
  (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm

/- English proof (authored)
The squared Hilbert–Schmidt norm of the linear map is the real part of the trace of its adjoint composed with itself. The coordinate matrix of that composite is the conjugate transpose of A times A. Its real trace is the sum of the squared moduli of the entries of A.
-/
theorem hs_norm_sq_to_euclidean_lin (A : Matrix m n ℂ) : hs2 (Matrix.toEuclideanLin A) = hsSq A := by
  unfold hs2
  rw [to_euclidean_lin_adjoint_eq, ← to_euclidean_lin_mul, to_euclidean_lin_trace, HilbertSchmidtNormSquare.hsSq_eq_re]

/- English proof (authored)
The frame kernel is c times the adjoint composed with the original map. In coordinates, composition gives matrix multiplication, the adjoint gives the conjugate transpose, and the identity map gives the identity matrix. The representation preserves scalar multiplication and subtraction, giving the formula.
-/
theorem frame_kernel_to_lin_sub_id (c : ℝ) (A : Matrix m n ℂ) :
    frK c (Matrix.toEuclideanLin A) - LinearMap.id
      = Matrix.toEuclideanLin ((c : ℂ) • (Aᴴ * A) - 1) := by
  unfold frK
  rw [to_euclidean_lin_adjoint_eq, ← to_euclidean_lin_mul, map_sub, map_smul, to_euclidean_lin_one]

end Lin

/- English proof (authored)
The diagonal kernel uses the weight's square root twice. Their product is the weight itself because it is nonnegative. Factor this scalar out of the Gram matrix.
-/
theorem weighted_gram_eq_smul {I α : Type} [Fintype α] {ι : I → Type} (B : ∀ i, Matrix α (ι i) ℂ)
    (ga : I → ℝ) (i : I) (hi : 0 ≤ ga i) : KdG B ga i = ((ga i : ℝ) : ℂ) • ((B i)ᴴ * B i) := by
  unfold KdG KpG
  rw [Real.sqrt_mul_self hi]

/- English proof (authored)
Express the linear kernel minus the identity as the map of the scalar-weighted Gram matrix minus the identity. Its squared Hilbert–Schmidt norm equals the corresponding matrix norm. For a nonnegative weight the scalar-weighted Gram matrix is exactly the diagonal kernel.
-/
theorem hilbert_schmidt_transfer_holds : BridgeHS := by
  intro I α _ ι _ _ B ga i hi
  classical
  rw [frame_kernel_to_lin_sub_id, hs_norm_sq_to_euclidean_lin, weighted_gram_eq_smul B ga i hi]

/- English proof (authored)
Each weighted summand of the frame operator is the map composed with its adjoint, multiplied by its weight. The corresponding matrix is the weighted product of the matrix and its conjugate transpose. Add these identities over the family using linearity of the matrix-to-map correspondence.
-/
theorem weighted_frame_operator_to_lin {I α : Type} [Fintype I] [Fintype α] [DecidableEq α] {ι : I → Type}
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) :
    frQ ga (fun i => Matrix.toEuclideanLin (B i)) = Matrix.toEuclideanLin (QmG B ga) := by
  unfold frQ QmG
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, to_euclidean_lin_mul, to_euclidean_lin_adjoint_eq]

/- English proof (authored)
Represent the frame operator by its weighted matrix sum. Its square is then represented by the square of that sum. Tracing the operator and its square gives the corresponding two matrix traces.
-/
theorem quadratic_transfer_holds : BridgeQ := by
  intro I α _ _ _ ι _ _ B ga
  rw [weighted_frame_operator_to_lin, ← to_euclidean_lin_mul, to_euclidean_lin_trace, to_euclidean_lin_trace]
  exact ⟨rfl, rfl⟩

/- English proof (authored)
The squared Hilbert–Schmidt norm sums the squared moduli over row and column indices. Changing both indices by their bijections permutes the terms of this double sum, leaving it unchanged.
-/
theorem hs_sq_reindex {m n m' n' : Type} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) : hsSq (Matrix.reindex e f M) = hsSq M := by
  unfold HilbertSchmidtNormSquare.hsSq
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← f.symm.sum_comp]
  rfl

/- English proof (authored)
When rows and columns are relabeled by the same bijection, the diagonal entries are permuted by that bijection. Their sum is unchanged.
-/
theorem matrix_trace_reindex {m m' : Type} [Fintype m] [Fintype m'] (e : m ≃ m')
    (M : Matrix m m ℂ) : (Matrix.reindex e e M).trace = M.trace := by
  unfold Matrix.trace
  rw [← e.symm.sum_comp]
  rfl

/- English proof (authored)
Relabel the column coordinates of each matrix by its chosen finite-coordinate bijection. In the weighted product of the first conjugate transpose and the second matrix, the common ambient relabeling cancels by a change of summation index. The two remaining relabelings act on the row and column indices of the kernel.
-/
theorem kernel_matrix_reindex {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i j : I) :
    HilbertSchmidtNormSquare.Kp (toFin B) ga i j
      = Matrix.reindex (Fintype.equivFin (ι i)) (Fintype.equivFin (ι j)) (KpG B ga i j) := by
  unfold HilbertSchmidtNormSquare.Kp KpG toFin
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_smul, Pi.smul_apply]

/- English proof (authored)
Apply the kernel reindexing identity with both arguments equal. The identity matrix is unchanged by simultaneous reindexing of rows and columns. Subtract it to obtain the reindexed deviation.
-/
theorem weighted_gram_sub_one_reindex {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i : I) :
    HilbertSchmidtNormSquare.Kd (toFin B) ga i - 1
      = Matrix.reindex (Fintype.equivFin (ι i)) (Fintype.equivFin (ι i)) (KdG B ga i - 1) := by
  unfold HilbertSchmidtNormSquare.Kd KdG
  rw [kernel_matrix_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_sub, Matrix.submatrix_one_equiv, Pi.sub_apply]

/- English proof (authored)
Expand both weighted matrix sums and compare each term. In a matrix times its conjugate transpose, the common relabeling of its column coordinates cancels in the sum over those coordinates. Only the ambient relabeling remains on the product, and it commutes with the weighted sum.
-/
theorem quadratic_matrix_fin_reindex {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) :
    HilbertSchmidtNormSquare.Qm (toFin B) ga
      = Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin α) (QmG B ga) := by
  unfold HilbertSchmidtNormSquare.Qm QmG toFin
  rw [← Matrix.coe_reindexLinearEquiv ℂ ℂ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_smul, Pi.smul_apply]

/- English proof (authored)
The kernel and Gram-deviation reindexing identities preserve the corresponding squared norms. The ambient reindexing identity preserves the trace of the quadratic matrix and the trace of its square because it preserves matrix multiplication. Finally, the labels change only by bijections, so the total rank is unchanged.
-/
theorem transfer_fin_index_holds : BridgeFin := by
  intro I α _ _ ι _ _ B ga
  refine ⟨fun i j => ?_, fun i => ?_, ?_, ?_, rfl⟩
  · rw [kernel_matrix_reindex, hs_sq_reindex]
  · rw [weighted_gram_sub_one_reindex, hs_sq_reindex]
  · rw [quadratic_matrix_fin_reindex, matrix_trace_reindex]
  · rw [quadratic_matrix_fin_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    exact matrix_trace_reindex (Fintype.equivFin α) (QmG B ga * QmG B ga)

/- English proof (authored)
The two input-size formulations differ only by relabeling the row and column coordinates. The off-diagonal kernel norms and the diagonal deviation norms agree by the transfer identities. The remaining dimensions and numerical bounds are the same, so each set of conditions implies the other.
-/
theorem input_size_transfer_holds : BridgeInputS := by
  intro I α _ _ ι _ _ B ga Dstar η0 η1 e0
  obtain ⟨h1, h2, -, -, -⟩ := transfer_fin_index_holds I α ι B ga
  unfold HilbertSchmidtNormSquare.InputS InputSG
  simp only [h1, h2]

/- English proof (authored)
Under finite-coordinate relabeling, the shared middle coordinates in the compression product are merely permuted, so the product transfers directly. The compression map is an isometry exactly when its Gram matrix is the identity. That Gram matrix is carried to the same simultaneous relabeling of rows and columns, which preserves the identity and can be reversed by the inverse bijection.
-/
theorem ramification_transfer_holds : BridgeRam := by
  intro I α _ ιf ι _ _ _ Bf Vr
  constructor
  · funext i
    unfold toFin HilbertSchmidtNormSquare.Bram toFinV
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  · unfold HilbertSchmidtNormSquare.Isom toFinV
    refine forall_congr' fun i => ?_
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    constructor
    · intro h
      have := congrArg (fun M => M.submatrix (Fintype.equivFin (ι i)) (Fintype.equivFin (ι i))) h
      simpa using this
    · intro h
      rw [h, Matrix.submatrix_one_equiv]

/- English proof (authored)
The finite-coordinate form uses the trace and the square trace of the weighted matrix sum. Relabeling preserves both. The matrix-to-linear-map transfer identifies them with the two operator traces, so the trace-ratio inequalities agree.
-/
theorem first_family_transfer_holds : FrameTraceRatioFinEquiv := by
  intro I α _ _ ι _ _ B ga η
  classical
  obtain ⟨-, -, h3, h4, -⟩ := transfer_fin_index_holds I α ι B ga
  obtain ⟨q1, q2⟩ := quadratic_transfer_holds I α ι B ga
  unfold HilbertSchmidtNormSquare.F1 FrameTraceRatioLinear
  rw [h3, h4, q1, q2]

/- English proof (authored)
The total rank is unchanged by the finite-coordinate bijections. For each nonnegative weight the squared deviation is unchanged under reindexing, and the norm transfer identifies that same deviation with the linear-map norm. Substituting these equalities in the summed bound gives the equivalence.
-/
theorem second_family_transfer_holds : FrameDeviationFinEquiv := by
  intro I α _ _ ι _ _ B ga e hga
  obtain ⟨-, h2, -, -, h5⟩ := transfer_fin_index_holds I α ι B ga
  unfold HilbertSchmidtNormSquare.F2 FrameDeviationLinear
  rw [h5]
  simp only [h2, fun i => hilbert_schmidt_transfer_holds I α ι B ga i (hga i)]
  rfl

/- English proof (authored)
Expand the error function and its logarithmic term. Reassociate multiplication by four with the factor u. The resulting error expression is the one in the desired conclusion, so the inequalities agree.
-/
theorem transfer_conclusion_holds : BridgeConcl := by
  intro s mu logI δ u HH η e
  unfold PhiMonotonicityLemmas.ConclF PhiMonotonicityLemmas.ErrF PhiMonotonicityLemmas.phi
  rw [mul_assoc 4 u]

/- English proof (authored)
Transfer the finite-size and isometry assumptions to matrices on numbered coordinates. Apply the matrix bounds for the compressed trace square and the diagonal deviation. Use the compression identity to identify their family and transfer both conclusions back to the linear maps. The square-root bound and ramification-scale bound imply that twice the initial error is at most one quarter. Finally, the original total rank is positive by the dimension lower bound, and the retained-rank estimate preserves positivity because the fractional loss is below one.
-/
theorem ramification_linear_case_holds : RamLin := by
  intro I α _ _ ιf ι _ _ _ _ Bf Vr ga Dstar sg η0 η1 e0 de hV hga hD hsg hsg20 hR h0 h0' h1 he0 hse
    hde hde4 hcor hS
  have hS' := (input_size_transfer_holds I α ιf Bf ga Dstar η0 η1 e0).2 hS
  obtain ⟨hB, hI⟩ := ramification_transfer_holds I α ιf ι Bf Vr
  have hV' := hI.2 hV
  have f1 := HilbertSchmidtNormSquare.compressTraceSquareBound I (Fintype.card α) (fun i => Fintype.card (ιf i))
    (fun i => Fintype.card (ι i)) (toFin Bf) (toFinV Vr) ga Dstar sg η0 η1 e0 de hV' hga hD hsg hsg20
    hR h0 h0' h1 he0 hse hde hde4 hcor hS'
  obtain ⟨hRr, f2⟩ := HilbertSchmidtNormSquare.compressDiagDefectBound I (Fintype.card α) (fun i => Fintype.card (ιf i))
    (fun i => Fintype.card (ι i)) (toFin Bf) (toFinV Vr) ga de e0 hV' (by linarith) he0 hS'.2.1 hcor
  rw [← hB] at f1 f2
  refine ⟨(first_family_transfer_holds I α ι _ ga _).1 f1, (second_family_transfer_holds I α ι _ ga _ hga).1 f2, ?_, ?_⟩
  · have hs := Real.sq_sqrt he0
    have hn := Real.sqrt_nonneg e0
    nlinarith
  · have hpos : (0 : ℝ) < RsG ιf := lt_of_lt_of_le (div_pos hD hsg) hR
    have hpos' : (0 : ℝ) < HilbertSchmidtNormSquare.Rs (fun i => Fintype.card (ι i)) := by
      refine lt_of_lt_of_le ?_ hRr
      exact mul_pos (by linarith) hpos
    unfold HilbertSchmidtNormSquare.Rs at hpos'
    exact_mod_cast hpos'

/- English proof (authored)
Extract the individual geometric and numerical assumptions from the grouped hypotheses. Together with the given frame estimates and their parameter bounds they are exactly the hypotheses of the flat lattice theorem. Applying it gives the slope inequality.
-/
theorem flat_lattice_theorem_holds : TheoremFLat := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ hG hN hγ hF2 he he4 hF1 hη
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hG
  obtain ⟨n1, n2, n3, n4, n5⟩ := hN
  exact theoremF K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ g1 g2 g3 g4 g5 g6 g7 g8
    g9 g10 g11 n1 n2 n3 n4 n5 g12 g13 g14 g15 hγ hF2 he he4 hF1 hη

/- English proof (authored)
Extract the individual geometric and numerical assumptions from the grouped hypotheses and keep the given frame bounds. Apply the sharp lattice theorem with these data to obtain the slope inequality with the stated deletion and error terms.
-/
theorem sharp_flat_lattice_theorem_holds :
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → FrameDeviationLinear Ball γ e → 0 ≤ e → e ≤ 1 / 4 → FrameTraceRatioLinear Ball γ η → 0 ≤ η →
    s - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH)
      ≤ muDef b' X' cc := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ hG hN hγ hF2 he he4 hF1 hη
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hG
  obtain ⟨n1, n2, n3, n4, n5⟩ := hN
  exact theoremFSharp K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ g1 g2 g3 g4 g5 g6
    g7 g8 g9 g10 g11 n1 n2 n3 n4 n5 g12 g13 g14 g15 hγ hF2 he he4 hF1 hη

/- English proof (authored)
Apply the linear compression estimate to obtain the trace-ratio bound with parameter 5 times the scale plus 3 times the square root of the deficit, and the deviation bound with parameter twice the initial error. The supplied matrix product identifies these compressed matrices with the given family. The parameters are nonnegative and the deviation bound is at most one quarter. Apply the two flat lattice inequalities to the same geometric and numerical data to obtain both conclusions.
-/
theorem ramification_condition_holds :
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u HH δ Dstar sg η0 η1 e0 de : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    (s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u)
          + ((5 * sg + 3 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * HH)
      ≤ muDef b' X' cc) ∧
    (s - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u)
          + ((5 * sg + 3 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * HH)
      ≤ muDef b' X' cc) := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr s u HH δ Dstar sg η0 η1 e0 de hG hN hγ hBV hV hD hsg hsg20 hR h0 h0' h1 he0
    hse hde hde4 hcor hS
  obtain ⟨f1, f2, he, -⟩ := ramification_linear_case_holds I (κ ⊕ κ₁) ιf ι Bf Vr γ Dstar sg η0 η1 e0 de hV
    (fun i => (hγ i).le) hD hsg hsg20 hR h0 h0' h1 he0 hse hde hde4 hcor hS
  have hB : Ball = fun i => Bf i * Vr i := funext hBV
  rw [← hB] at f1 f2
  exact ⟨flat_lattice_theorem_holds K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH (2 * e0)
      (5 * sg + 3 * Real.sqrt de) δ hG hN hγ f2 (by positivity) he f1 (by positivity),
    sharp_flat_lattice_theorem_holds K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH (2 * e0)
      (5 * sg + 3 * Real.sqrt de) δ hG hN hγ f2 (by positivity) he f1 (by positivity)⟩

/- English proof (authored)
The ramification estimate supplies two slope bounds under exactly these assumptions. Its first bound is the one required here.
-/
theorem joint_a_ramified_holds : JointARam := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr s u HH δ Dstar sg η0 η1 e0 de hG hN hγ hBV hV hD hsg hsg20 hR h0 h0' h1 he0
    hse hde hde4 hcor hS
  exact (ramification_condition_holds K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr s u HH δ Dstar sg η0
    η1 e0 de hG hN hγ hBV hV hD hsg hsg20 hR h0 h0' h1 he0 hse hde hde4 hcor hS).1

/- English proof (authored)
The lattice is nonzero because it spans a vector space with positive basis cardinality. Together with finite generation and the invertible metric data, it gives a realized lattice to which the maximal-slope characterization applies. That characterization bounds the slope of the lattice itself by its maximal slope.
-/
theorem slope_le_max_slope {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ w, IsUnit (X w).det) (N : Submodule (𝓞 K) V) (hFG : N.FG)
    (hsp : Submodule.span K (N : Set V) = ⊤) (hc : 0 < Fintype.card ι) :
    muDef b X N ≤ muMaxDef b X N := by
  have hne : N ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Submodule K V) = ⊤ := by rw [← hsp]; simp
    have : Subsingleton (Submodule K V) := subsingleton_of_bot_eq_top h0
    have : Subsingleton V := (Submodule.subsingleton_iff K).1 inferInstance
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_zero_of_subsingleton] at this
    omega
  have hLat := (plLat K V ι b X hX N hFG).1
  have := (muChar _ _ _ (Formalism.HermitianLatticesTheory.realize b X) N hLat hne).2.2.2.2
  unfold muDef muMaxDef
  linarith

/- English proof (authored)
Sum the common lower bound on each coordinate dimension over the words. The result is the word count times that lower bound and is at most the total rank. The word-count hypothesis bounds the count below by C₀Γ² divided by the scale. Multiplying by the nonnegative dimension lower bound cancels C₀ and Γ², leaving the dimension parameter divided by the scale. This gives the required lower bound on the total rank.
-/
theorem word_count_bound_holds : WordsR := by
  intro I _ ιf _ Dstar sg C0 Gam hD hsg hC hG hI hd
  have h1 : (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0) ≤ RsG ιf := by
    unfold RsG
    calc (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0)
        = ∑ _i : I, Dstar * (Gam ^ 2)⁻¹ / C0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i, (Fintype.card (ιf i) : ℝ) := Finset.sum_le_sum fun i _ => hd i
  have h2 : 0 ≤ Dstar * (Gam ^ 2)⁻¹ / C0 := by positivity
  have h3 : C0 * Gam ^ 2 / sg * (Dstar * (Gam ^ 2)⁻¹ / C0) = Dstar / sg := by
    field_simp
  calc Dstar / sg = C0 * Gam ^ 2 / sg * (Dstar * (Gam ^ 2)⁻¹ / C0) := h3.symm
    _ ≤ (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0) := mul_le_mul_of_nonneg_right hI h2
    _ ≤ RsG ιf := h1

end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
