import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SubquotientSizeInequality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSizeEqLeast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAndNcardLeProdOfLevels
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSubspaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRealSubmoduleBlockFinrankLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubmoduleSkewBlockFinrankLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarProjectionInfOrthogonalEqOfMemOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFramesSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoweringDifferenceOfIsometries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFirstBlocksByLayers
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerAddInnerEqZeroSpan

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.NearCount

abbrev Hn (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

def opM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Hn n →L[ℂ] Hn n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem opM_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Hn n) :
    opM M u = WithLp.toLp 2 (M *ᵥ u.ofLp) := rfl

/- English proof (translation)
Simplify using `[opM]`.
-/
theorem opM_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) : opM (M - N) = opM M - opM N := by
  simp [opM]

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun u => ?_` and prove the remaining obligations. Rewrite using `[opM_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul (by unfold hs; positivity)]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Unfold `hs`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `h1 : ‖(M *ᵥ u.ofLp) i‖ ≤ ∑ j, ‖M i j‖ * ‖u j‖`. Unfold `Matrix.mulVec dotProduct`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)`. Conclude with `(pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)`.
-/
theorem norm_opM_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ‖opM M‖ ≤ Real.sqrt (hs M) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun u => ?_
  rw [opM_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (by unfold hs; positivity)]
  apply Real.sqrt_le_sqrt
  unfold hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(M *ᵥ u.ofLp) i‖ ≤ ∑ j, ‖M i j‖ * ‖u j‖ := by
    unfold Matrix.mulVec dotProduct
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

/- English proof (translation)
Rewrite using `[opM_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]`.
-/
theorem inner_opM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u z : Hn n) :
    ⟪u, opM M z⟫_ℂ = star u.ofLp ⬝ᵥ (M *ᵥ z.ofLp) := by
  rw [opM_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/- English proof (translation)
Rewrite using `[opM_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Jm, Matrix.mulVec_diagonal, norm_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_opJ {n : ℕ} (ε : Fin n → Bool) (u : Hn n) : ‖opM (Jm ε) u‖ = ‖u‖ := by
  rw [opM_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Jm, Matrix.mulVec_diagonal, norm_mul]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[opM_apply, opM_apply, PiLp.inner_apply, PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Jm, Matrix.mulVec_diagonal]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem inner_opJ {n : ℕ} (ε : Fin n → Bool) (u z : Hn n) :
    ⟪opM (Jm ε) u, z⟫_ℂ = ⟪u, opM (Jm ε) z⟫_ℂ := by
  rw [opM_apply, opM_apply, PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Jm, Matrix.mulVec_diagonal]
  split_ifs <;> simp

/- English proof (translation)
Use `Submodule.finrank_add_inf_finrank_orthogonal h` as an intermediate fact. Rewrite `this` using `[inf_comm]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_piece {n : ℕ} {A A' : Submodule ℂ (Hn n)} (h : A' ≤ A) :
    Module.finrank ℂ ↥(A ⊓ A'ᗮ) = Module.finrank ℂ A - Module.finrank ℂ A' := by
  have := Submodule.finrank_add_inf_finrank_orthogonal h
  rw [inf_comm] at this
  omega

variable (I : AutInst) (x : I.GA)

abbrev pt (w : InfinitePlace I.E) (y : Fin I.n → I.E) : Hn I.n := ptAt (bas I) (frm I x) w y

abbrev sp (w : InfinitePlace I.E) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Submodule ℂ (Hn I.n) :=
  spanAt (bas I) (frm I x) w S

def op (w : InfinitePlace I.E) (φ : Matrix (Fin I.n) (Fin I.n) I.E) : Hn I.n →L[ℂ] Hn I.n :=
  opM ((frm I x w)⁻¹ * φ.map w.embedding * frm I x w)

def sg (w : InfinitePlace I.E) : Hn I.n →L[ℂ] Hn I.n := opM (Jm (I.ε (w.comap (algebraMap I.F I.E))))

abbrev hf (y z : Fin I.n → I.E) : I.E := Formalism.UG.hform (starRingEnd I.E) I.J y z

/- English proof (translation)
Unfold `op`. Rewrite using `[← opM_sub, Matrix.map_sub _ (map_sub _), Matrix.mul_sub, Matrix.sub_mul]`.
-/
theorem op_sub (w : InfinitePlace I.E) (φ ψ : Matrix (Fin I.n) (Fin I.n) I.E) :
    op I x w (φ - ψ) = op I x w φ - op I x w ψ := by
  unfold op
  rw [← opM_sub, Matrix.map_sub _ (map_sub _), Matrix.mul_sub, Matrix.sub_mul]

/- English proof (translation)
Use `show frm I x w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = _`. Unfold `Formalism.HermitianLatticesTheory.fcoord`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (FrameMajorant.frm_unit I x w), Matrix.one_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.HermitianLatticesTheory.vecAt]`.
-/
theorem frm_pt (w : InfinitePlace I.E) (y : Fin I.n → I.E) :
    frm I x w *ᵥ (pt I x w y).ofLp = fun i => w.embedding (y i) := by
  show frm I x w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = _
  unfold Formalism.HermitianLatticesTheory.fcoord
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (FrameMajorant.frm_unit I x w), Matrix.one_mulVec]
  funext i
  simp [Formalism.HermitianLatticesTheory.vecAt]

/- English proof (translation)
Unfold `op`. Rewrite using `[opM_apply, ← Matrix.mulVec_mulVec, frm_pt, ← Matrix.mulVec_mulVec]`. Use `show _ = WithLp.toLp 2 ((frm I x w)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt (bas I) w (φ *ᵥ y))`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Simplify using `[Formalism.HermitianLatticesTheory.vecAt, Matrix.mulVec, dotProduct]`.
-/
theorem op_pt (w : InfinitePlace I.E) (φ : Matrix (Fin I.n) (Fin I.n) I.E) (y : Fin I.n → I.E) :
    op I x w φ (pt I x w y) = pt I x w (φ *ᵥ y) := by
  unfold op
  rw [opM_apply, ← Matrix.mulVec_mulVec, frm_pt, ← Matrix.mulVec_mulVec]
  show _ = WithLp.toLp 2 ((frm I x w)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt (bas I) w (φ *ᵥ y))
  congr 2
  funext i
  simp [Formalism.HermitianLatticesTheory.vecAt, Matrix.mulVec, dotProduct]

/- English proof (translation)
Establish `hc` using `I.cm.cmUnram.2.1`. Establish `h1 : w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z) = star (fun i => w.embedding (y i)) ⬝ᵥ (I.J.map w.embedding *ᵥ fun i => w.embedding (z i))`. Simplify using `only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, starRingEnd_apply, hc, mul_assoc]`. Rewrite using `[sg, inner_opM, hf, h1, ← frm_pt I x w y, ← frm_pt I x w z, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ((FrameMajorant.frames_give_majorants I x).2.2.2.2 w).2.1]`.
-/
theorem inner_pt (w : InfinitePlace I.E) (y z : Fin I.n → I.E) :
    ⟪pt I x w y, sg I w (pt I x w z)⟫_ℂ = w.embedding (hf I y z) := by
  have hc := I.cm.cmUnram.2.1
  have h1 : w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z) =
      star (fun i => w.embedding (y i)) ⬝ᵥ (I.J.map w.embedding *ᵥ fun i => w.embedding (z i)) := by
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Finset.mul_sum, starRingEnd_apply, hc, mul_assoc]
  rw [sg, inner_opM, hf, h1, ← frm_pt I x w y, ← frm_pt I x w z, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ((FrameMajorant.frames_give_majorants I x).2.2.2.2 w).2.1]

/- English proof (translation)
Use `I.cm.cmUnram.1` as an intermediate fact. Establish `h : sp I x w S = (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w '' (S : Set _))).map ((WithLp.linearEquiv 2 ℂ (Fin I.n → ℂ)).symm : (Fin I.n → ℂ) →ₗ[ℂ] Hn I.n)`. Rewrite using `[Submodule.map_span, Set.image_image]`. Both sides reduce to the same expression. Rewrite using `[h, LinearEquiv.finrank_map_eq]`.

Conclude with `PlaceDecomposition.finrank_span_complex _ _ (FrameMajorant.frm_unit I x) S w`.
-/
theorem finrank_sp (w : InfinitePlace I.E) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Module.finrank ℂ (sp I x w S) = rkK S := by
  have := I.cm.cmUnram.1
  have h : sp I x w S = (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w '' (S : Set _))).map
      ((WithLp.linearEquiv 2 ℂ (Fin I.n → ℂ)).symm : (Fin I.n → ℂ) →ₗ[ℂ] Hn I.n) := by
    rw [Submodule.map_span, Set.image_image]; rfl
  rw [h, LinearEquiv.finrank_map_eq]
  exact PlaceDecomposition.finrank_span_complex _ _ (FrameMajorant.frm_unit I x) S w

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem sp_mono (w : InfinitePlace I.E) {S S' : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : S ≤ S') :
    sp I x w S ≤ sp I x w S' := Submodule.span_mono (Set.image_mono h)

/- English proof (translation)
Establish `: sp I x w A ≤ (sp I x w B).comap (op I x w φ : Hn I.n →ₗ[ℂ] Hn I.n)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `show op I x w φ (pt I x w y) ∈ sp I x w B`. Rewrite using `[op_pt]`.

Conclude with `Submodule.subset_span ⟨_, h y hy, rfl⟩`. Conclude with `fun u hu => this hu`.
-/
theorem op_mem (w : InfinitePlace I.E) (φ : Matrix (Fin I.n) (Fin I.n) I.E)
    {A B : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : ∀ y ∈ A, φ *ᵥ y ∈ B) :
    ∀ u ∈ sp I x w A, op I x w φ u ∈ sp I x w B := by
  have : sp I x w A ≤ (sp I x w B).comap (op I x w φ : Hn I.n →ₗ[ℂ] Hn I.n) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    show op I x w φ (pt I x w y) ∈ sp I x w B
    rw [op_pt]
    exact Submodule.subset_span ⟨_, h y hy, rfl⟩
  exact fun u hu => this hu

/- English proof (translation)
Use `first`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `@_root_.GlobalTheory.InnerSumZeroSpan.main`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `_root_.GlobalTheory.InnerSumZeroSpan.main`.

Consider the case `exact @_root_.GlobalTheory.InnerSumZeroSpan.main`. Consider the case `exact _root_.GlobalTheory.InnerSumZeroSpan.main`. Consider the case `(apply _root_.GlobalTheory.InnerSumZeroSpan.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.InnerSumZeroSpan.main <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.InnerSumZeroSpan.main <;> first | assumption | infer_instance)`.

Consider the case `(intros; exact _root_.GlobalTheory.InnerSumZeroSpan.main ..)`.
-/
theorem span_inner {n : ℕ} (L M : Hn n →L[ℂ] Hn n) (s t : Set (Hn n))
    (h : ∀ u ∈ s, ∀ z ∈ t, ⟪L u, z⟫_ℂ + ⟪u, M z⟫_ℂ = 0) :
    ∀ u ∈ Submodule.span ℂ s, ∀ z ∈ Submodule.span ℂ t, ⟪L u, z⟫_ℂ + ⟪u, M z⟫_ℂ = 0 := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.InnerSumZeroSpan.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.InnerSumZeroSpan.main
  | exact @_root_.GlobalTheory.InnerSumZeroSpan.main
  | exact _root_.GlobalTheory.InnerSumZeroSpan.main
  | (apply _root_.GlobalTheory.InnerSumZeroSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InnerSumZeroSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InnerSumZeroSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InnerSumZeroSpan.main ..)

/- English proof (translation)
Introduce `u hu z hz`. Use `span_inner 0 (sg I w) _ _ (by` as an intermediate fact. Introduce and unpack `_ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩`. Rewrite using `[inner_pt, h s hs y hy]`. Use the proof step `simp) z hz u hu`.

Simplify using `using this`.
-/
theorem sp_orth (w : InfinitePlace I.E) {A B : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (h : ∀ s ∈ A, ∀ y ∈ B, hf I s y = 0) :
    ∀ u ∈ sp I x w B, ∀ z ∈ sp I x w A, ⟪z, sg I w u⟫_ℂ = 0 := by
  intro u hu z hz
  have := span_inner 0 (sg I w) _ _ (by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [inner_pt, h s hs y hy]; simp) z hz u hu
  simpa using this

/- English proof (translation)
Use `span_inner _ _ _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[op_pt, op_pt, sg, inner_opJ, ← sg, inner_pt, inner_pt, ← map_add, h s hs y hy, map_zero]`.
-/
theorem sp_skew (w : InfinitePlace I.E) (φ : Matrix (Fin I.n) (Fin I.n) I.E)
    {A : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (h : ∀ s ∈ A, ∀ y ∈ A, hf I (φ *ᵥ s) y + hf I s (φ *ᵥ y) = 0) :
    ∀ u ∈ sp I x w A, ∀ z ∈ sp I x w A,
      ⟪(sg I w ∘L op I x w φ) u, z⟫_ℂ + ⟪u, (sg I w ∘L op I x w φ) z⟫_ℂ = 0 := by
  refine span_inner _ _ _ _ ?_
  rintro _ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [op_pt, op_pt, sg, inner_opJ, ← sg, inner_pt, inner_pt, ← map_add, h s hs y hy, map_zero]

def rho (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (p : ℕ) : ℕ := rkK (G (p + 1)) - rkK (G p)

def dimB (a : ℕ) (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (q p : ℕ) : ℕ :=
  if q + p = 2 * a then rho I G p ^ 2 else 2 * rho I G (2 * a - q) * rho I G p

def lowSet (a : ℕ) (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (de : ℝ) :
    Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {γ | Formalism.UG.cT (starRingEnd I.E) γ * I.J * γ = I.J ∧
    (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ - 1) *ᵥ y ∈ G p) ∧ ∀ w, ‖op I x w (γ - 1)‖ ≤ de}

/- English proof (translation)
Use `I.cm.cmUnram.1` as an intermediate fact. Break down `T.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩` into its components or cases. Simplify using `only [Finset.card_empty, Nat.cast_zero]`. Check the signs of the components of the expression. Establish `hadj` using `fun γ (hγ : γ ∈ T) γ' (hγ' : γ' ∈ T) => GlobalTheory.lowering_difference_of_isometries I.E (𝓞 I.E) I.n I.J I.J_herm a G h0 hmono hperp γ γ' (hT hγ).1 (hT hγ').1 (hT hγ).2.1 (hT hγ').2.1 (p - q) (by omega) (hlev γ hγ γ' hγ')`.

Establish `horth : ∀ i k, i + k ≤ 2 * a + 1 → ∀ s ∈ G i, ∀ y ∈ G k, hf I s y = 0` using `fun i k h s hs y hy => ((hperp i (by omega) y).1 (hmono (by omega) hy)).2 s hs`. Set `E` to `fun w => sp I x w (G (p + 1)) ⊓ (sp I x w (G p))ᗮ`. Set `E'` to `fun w => sp I x w (G (2 * a - q + 1)) ⊓ (sp I x w (G (2 * a - q)))ᗮ`. Establish `hE : ∀ w r, Module.finrank ℂ ↥(sp I x w (G (r + 1)) ⊓ (sp I x w (G r))ᗮ) = rho I G r`. Introduce `w r`.

Rewrite using `[finrank_piece (sp_mono I x w (hmono (Nat.le_succ r))), finrank_sp, finrank_sp, rho]`. Set `blk` to `fun w (φ : Matrix (Fin I.n) (Fin I.n) I.E) => (E' w).starProjection ∘L (sg I w ∘L op I x w φ) ∘L (E w).starProjection`. Establish `hsub : ∀ w φ ψ, blk w φ - blk w ψ = blk w (φ - ψ)`. Introduce `w φ ψ`. Simplify using `only [blk, op_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]`.

Establish `hU : ∀ w, ∃ U : Submodule ℝ (Hn I.n →L[ℂ] Hn I.n), Module.finrank ℝ U ≤ dimB I a G q p ∧ ∀ γ ∈ T, blk w (γ - γ₀) ∈ U`. Introduce `w`. Distinguish the cases in `h : q + p = 2 * a`. Take `⟨U, h1, h2⟩` from `GlobalTheory.exists_submodule_skew_block_finrank_le I.n (E w)`. Use `⟨U, by rw [dimB, if_pos h, ← hE w p]; exact h1, fun γ hγ => ?_⟩` and prove the remaining obligations.

Establish `hp : 2 * a - q = p` using `by omega`. Simplify using `only [blk, E', hp]`. Use `h2 _ fun u hu z hz => sp_skew I x w _ (A := G (p + 1)) ?_ u hu.1 z hz.1` and prove the remaining obligations. Conclude with `fun s hs y hy => (hadj γ hγ γ₀ hγ₀).2 p p (by omega) (by omega) (by omega) s hs y hy`. Take `⟨U, h1, h2⟩` from `GlobalTheory.exists_real_submodule_block_finrank_le I.n (E w) (E' w)`.

Conclude with `⟨U, by rw [dimB, if_neg h, ← hE w p, ← hE w (2 * a - q)]; exact h1, fun γ _ => h2 _⟩`. Use `choose U hU1 hU2 using hU`. Establish `hnorm : ∀ w φ, ‖blk w φ‖ ≤ ‖op I x w φ‖`. Introduce `w φ`. Use `ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_` and prove the remaining obligations.

Simplify using `only [blk, ContinuousLinearMap.comp_apply]`. Use `(Submodule.norm_starProjection_apply_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[sg, norm_opJ]`. Conclude with `(ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ _) (norm_nonneg _))`. Establish `hf' : Fintype.card (InfinitePlace I.E) = I.f` using `(FrameMajorant.frames_give_majorants I x).2.1`.

Establish `: FiniteDimensional ℝ (Hn I.n →L[ℂ] Hn I.n)` using `Module.Finite.trans ℂ _`. Rewrite using `[← hf']`. Use `GlobalTheory.packing_geometric_mean_subspaces (InfinitePlace I.E) (Hn I.n →L[ℂ] Hn I.n) U _ hU1 _ T (fun γ w => blk w (γ - γ₀)) (lo / hi) (2 * de) (div_pos hlo0 hhi0) (by positivity) ?_ ?_` and prove the remaining obligations. Introduce `γ hγ w`. Use `⟨hU2 w γ hγ, (hnorm w _).trans ?_⟩` and prove the remaining obligations.

Establish `: γ - γ₀ = (γ - 1) - (γ₀ - 1)` using `by abel`. Rewrite using `[this, op_sub]`. Establish `h1` using `(hT hγ).2.2 w`. Establish `h2` using `(hT hγ₀).2.2 w`. Conclude with `(norm_sub_le _ _).trans (by linarith)`.

Introduce `γ hγ γ' hγ' hne`. Establish `hex : ∃ y ∈ G (p + 1), (γ - γ') *ᵥ y ∉ G q`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hne (hsep γ hγ γ' hγ' hcon)`.

Establish `hD` using `(hadj γ hγ γ' hγ').1`. Establish `hA : ∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G (q + 1)` using `fun y hy => by`. Use `hD (p + 1) (by omega) y hy` as an intermediate fact. Rewrite `this` using `[show p + 1 - (p - q) = q + 1 by omega]`. Then use the resulting hypothesis. Establish `hA' : ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G q` using `fun y hy => by`.

Use `hD p (by omega) y hy` as an intermediate fact. Rewrite `this` using `[show p - (p - q) = q by omega]`. Then use the resulting hypothesis. Establish `hFG` using `(GlobalTheory.PointLattice.lamX_selfDual I x).2.1`. Establish `hne0 : G (p + 1) ≠ ⊥`. Take `⟨y, hy, hy'⟩` from `hex`.

Introduce `h`. Rewrite `hy` using `[h, Submodule.mem_bot]`. Conclude with `hy' (by rw [hy, Matrix.mulVec_zero]; exact zero_mem _)`. Simplify using `only [hsub, sub_sub_sub_cancel_right]`. Use `GlobalTheory.SizeSubToQuot.size_ineq_sub_to_quot I.E I.n (frm I x) (FrameMajorant.frm_unit I x) (γ - γ') (G (p + 1)) (lamX I x) (G q) (Submodule.FG.of_le hFG (hsat _).1) hFG (hsat q) (fun y hy => (hsat _).1 (hA y hy)) hex lo hi hlo0 hlo (hhi hne0) (fun w => ‖blk w (γ - γ')‖) (fun …` and prove the remaining obligations.

Use `GlobalTheory.infDist_le_norm_block_mul I.n (sp I x w (G (p + 1))) (sp I x w (G p)) (sp I x w (G (q + 1))) (sp I x w (G q)) (sp I x w (G (2 * a - q + 1))) (sp I x w (G (2 * a - q))) (sg I w) (op I x w (γ - γ')) (norm_opJ _) (sp_mono I x w (hmono (Nat.le_succ _))) (sp_mono I x w (h …` and prove the remaining obligations. Rewrite using `[finrank_sp, finrank_sp, show 2 * a - q + 1 = 2 * a + 1 - q by omega]`. Conclude with `hrk q (by omega)`.
-/
theorem block_count (a : ℕ) (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : G 0 = ⊥)
    (hmono : Monotone G) (hsat : ∀ p, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G p))
    (hperp : ∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, hf I s y = 0)
    (hrk : ∀ p ≤ 2 * a + 1, rkK (G (2 * a + 1 - p)) + rkK (G p) = I.n)
    (q p : ℕ) (hqp : q < p) (hle : q + p ≤ 2 * a) (lo hi : ℝ) (hlo0 : 0 < lo) (hhi0 : 0 < hi)
    (hlo : ∀ N, G q < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N (G q))
    (hhi : G (p + 1) ≠ ⊥ → largestSize (bas I) (frm I x) (G (p + 1)) ≤ hi)
    (de : ℝ) (hde : 0 < de) (T : Finset (Matrix (Fin I.n) (Fin I.n) I.E))
    (hT : (↑T : Set _) ⊆ lowSet I x a G de)
    (hlev : ∀ γ ∈ T, ∀ γ' ∈ T, ∀ q' p' : ℕ, q' < p' → q' + p' ≤ 2 * a → p' - q' < p - q →
      ∀ y ∈ G (p' + 1), (γ - γ') *ᵥ y ∈ G q')
    (hsep : ∀ γ ∈ T, ∀ γ' ∈ T, (∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G q) → γ = γ') :
    (T.card : ℝ) ≤ (1 + 2 * (2 * de) / (lo / hi)) ^ (dimB I a G q p * I.f) := by
  have := I.cm.cmUnram.1
  rcases T.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hadj := fun γ (hγ : γ ∈ T) γ' (hγ' : γ' ∈ T) =>
    GlobalTheory.lowering_difference_of_isometries I.E (𝓞 I.E) I.n I.J I.J_herm a G h0 hmono hperp γ γ' (hT hγ).1 (hT hγ').1
      (hT hγ).2.1 (hT hγ').2.1 (p - q) (by omega) (hlev γ hγ γ' hγ')
  have horth : ∀ i k, i + k ≤ 2 * a + 1 → ∀ s ∈ G i, ∀ y ∈ G k, hf I s y = 0 := fun i k h s hs y hy =>
    ((hperp i (by omega) y).1 (hmono (by omega) hy)).2 s hs
  let E := fun w => sp I x w (G (p + 1)) ⊓ (sp I x w (G p))ᗮ
  let E' := fun w => sp I x w (G (2 * a - q + 1)) ⊓ (sp I x w (G (2 * a - q)))ᗮ
  have hE : ∀ w r, Module.finrank ℂ ↥(sp I x w (G (r + 1)) ⊓ (sp I x w (G r))ᗮ) = rho I G r := by
    intro w r
    rw [finrank_piece (sp_mono I x w (hmono (Nat.le_succ r))), finrank_sp, finrank_sp, rho]
  let blk := fun w (φ : Matrix (Fin I.n) (Fin I.n) I.E) =>
    (E' w).starProjection ∘L (sg I w ∘L op I x w φ) ∘L (E w).starProjection
  have hsub : ∀ w φ ψ, blk w φ - blk w ψ = blk w (φ - ψ) := by
    intro w φ ψ
    simp only [blk, op_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  have hU : ∀ w, ∃ U : Submodule ℝ (Hn I.n →L[ℂ] Hn I.n), Module.finrank ℝ U ≤ dimB I a G q p ∧
      ∀ γ ∈ T, blk w (γ - γ₀) ∈ U := by
    intro w
    by_cases h : q + p = 2 * a
    · obtain ⟨U, h1, h2⟩ := GlobalTheory.exists_submodule_skew_block_finrank_le I.n (E w)
      refine ⟨U, by rw [dimB, if_pos h, ← hE w p]; exact h1, fun γ hγ => ?_⟩
      have hp : 2 * a - q = p := by omega
      simp only [blk, E', hp]
      refine h2 _ fun u hu z hz => sp_skew I x w _ (A := G (p + 1)) ?_ u hu.1 z hz.1
      exact fun s hs y hy => (hadj γ hγ γ₀ hγ₀).2 p p (by omega) (by omega) (by omega) s hs y hy
    · obtain ⟨U, h1, h2⟩ := GlobalTheory.exists_real_submodule_block_finrank_le I.n (E w) (E' w)
      exact ⟨U, by rw [dimB, if_neg h, ← hE w p, ← hE w (2 * a - q)]; exact h1, fun γ _ => h2 _⟩
  choose U hU1 hU2 using hU
  have hnorm : ∀ w φ, ‖blk w φ‖ ≤ ‖op I x w φ‖ := by
    intro w φ
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    simp only [blk, ContinuousLinearMap.comp_apply]
    refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
    rw [sg, norm_opJ]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ _) (norm_nonneg _))
  have hf' : Fintype.card (InfinitePlace I.E) = I.f := (FrameMajorant.frames_give_majorants I x).2.1
  have : FiniteDimensional ℝ (Hn I.n →L[ℂ] Hn I.n) := Module.Finite.trans ℂ _
  rw [← hf']
  refine GlobalTheory.packing_geometric_mean_subspaces (InfinitePlace I.E) (Hn I.n →L[ℂ] Hn I.n) U _ hU1 _ T
    (fun γ w => blk w (γ - γ₀)) (lo / hi) (2 * de) (div_pos hlo0 hhi0) (by positivity) ?_ ?_
  · intro γ hγ w
    refine ⟨hU2 w γ hγ, (hnorm w _).trans ?_⟩
    have : γ - γ₀ = (γ - 1) - (γ₀ - 1) := by abel
    rw [this, op_sub]
    have h1 := (hT hγ).2.2 w
    have h2 := (hT hγ₀).2.2 w
    exact (norm_sub_le _ _).trans (by linarith)
  · intro γ hγ γ' hγ' hne
    have hex : ∃ y ∈ G (p + 1), (γ - γ') *ᵥ y ∉ G q := by
      by_contra hcon
      push Not at hcon
      exact hne (hsep γ hγ γ' hγ' hcon)
    have hD := (hadj γ hγ γ' hγ').1
    have hA : ∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G (q + 1) := fun y hy => by
      have := hD (p + 1) (by omega) y hy
      rwa [show p + 1 - (p - q) = q + 1 by omega] at this
    have hA' : ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G q := fun y hy => by
      have := hD p (by omega) y hy
      rwa [show p - (p - q) = q by omega] at this
    have hFG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1
    have hne0 : G (p + 1) ≠ ⊥ := by
      obtain ⟨y, hy, hy'⟩ := hex
      intro h
      rw [h, Submodule.mem_bot] at hy
      exact hy' (by rw [hy, Matrix.mulVec_zero]; exact zero_mem _)
    simp only [hsub, sub_sub_sub_cancel_right]
    refine GlobalTheory.SizeSubToQuot.size_ineq_sub_to_quot I.E I.n (frm I x) (FrameMajorant.frm_unit I x) (γ - γ') (G (p + 1)) (lamX I x)
      (G q) (Submodule.FG.of_le hFG (hsat _).1) hFG (hsat q) (fun y hy => (hsat _).1 (hA y hy)) hex lo hi hlo0
      hlo (hhi hne0) (fun w => ‖blk w (γ - γ')‖) (fun w => norm_nonneg _) fun w u hu => ?_
    refine GlobalTheory.infDist_le_norm_block_mul I.n (sp I x w (G (p + 1))) (sp I x w (G p)) (sp I x w (G (q + 1)))
      (sp I x w (G q)) (sp I x w (G (2 * a - q + 1))) (sp I x w (G (2 * a - q))) (sg I w)
      (op I x w (γ - γ')) (norm_opJ _) (sp_mono I x w (hmono (Nat.le_succ _)))
      (sp_mono I x w (hmono (Nat.le_succ _))) (sp_orth I x w (horth _ _ (by omega)))
      (sp_orth I x w (horth _ _ (by omega))) ?_ (op_mem I x w _ hA) (op_mem I x w _ hA') u hu
    rw [finrank_sp, finrank_sp, show 2 * a - q + 1 = 2 * a + 1 - q by omega]
    exact hrk q (by omega)

/- English proof (translation)
Establish `hmem : ∀ q p : ℕ, q < p → q + p ≤ 2 * a → (q, p) ∈ ((Finset.range a) ×ˢ (Finset.range (2 * a + 1))).filter (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a)`. Introduce `q p h1 h2`. Simplify using `only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Use `GlobalTheory.finite_and_ncard_le_prod_of_levels _ (ℕ × ℕ) _ _ (fun b => b.2 - b.1) (fun b γ γ' => ∀ y ∈ G (b.2 + 1), (γ - γ') *ᵥ y ∈ G b.1) _ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `b`. Use `⟨fun γ y _ => by simp, fun {γ γ'} h y hy => ?_, fun {γ γ' γ''} h h' y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← neg_sub, Matrix.neg_mulVec]`. Conclude with `neg_mem (h y hy)`. Rewrite using `[← sub_add_sub_cancel γ γ' γ'', Matrix.add_mulVec]`.

Conclude with `add_mem (h y hy) (h' y hy)`. Introduce `γ hγ γ' hγ' h`. Establish `hD` using `(GlobalTheory.lowering_difference_of_isometries I.E (𝓞 I.E) I.n I.J I.J_herm a G h0 hmono hperp γ γ' hγ.1 hγ'.1 hγ.2.1 hγ'.2.1 (2 * a + 1) (by omega) (fun q p h1 h2 _ => h (q, p) (hmem q p h1 h2))).1 (2 * a + 1) le_rfl`. Rewrite `hD` using `[Nat.sub_self, h0, htop]`. Establish `hspan` using `(GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1`.

Establish `: Matrix.toLin' (γ - γ') = 0`. Use `LinearMap.ext_on hspan fun y hy => ?_` and prove the remaining obligations. Simplify `hD y hy` using `[Matrix.sub_mulVec]`. Rewrite using `[← sub_eq_zero]`. Conclude with `Matrix.toLin'.injective (by rw [this, map_zero])`.

Introduce and unpack `⟨q, p⟩ hb T hT hlev hsep`. Simplify using `only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb`. Conclude with `block_count I x a G h0 hmono hsat hperp hrk q p hb.2.1 hb.2.2 _ _ (ht q) (ht p) (hlo q hb.1.1) (hhi p (by omega)) de hde T hT (fun γ hγ γ' hγ' q' p' h1 h2 h3 => hlev γ hγ γ' hγ' (q', p') (hmem q' p' h1 h2) h3) hsep`.
-/
theorem core_count (a : ℕ) (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : G 0 = ⊥)
    (hmono : Monotone G) (hsat : ∀ p, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G p))
    (hperp : ∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, hf I s y = 0)
    (hrk : ∀ p ≤ 2 * a + 1, rkK (G (2 * a + 1 - p)) + rkK (G p) = I.n)
    (htop : G (2 * a + 1) = lamX I x) (t : ℕ → ℝ) (ht : ∀ p, 0 < t p)
    (hlo : ∀ q < a, ∀ N, G q < N → N ≤ lamX I x → t q ≤ sizeQ (bas I) (frm I x) N (G q))
    (hhi : ∀ p ≤ 2 * a, G (p + 1) ≠ ⊥ → largestSize (bas I) (frm I x) (G (p + 1)) ≤ t p)
    (de : ℝ) (hde : 0 < de) :
    (lowSet I x a G de).Finite ∧ (((lowSet I x a G de).ncard : ℕ) : ℝ) ≤
      ∏ b ∈ ((Finset.range a) ×ˢ (Finset.range (2 * a + 1))).filter
        (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a),
        (1 + 2 * (2 * de) / (t b.1 / t b.2)) ^ (dimB I a G b.1 b.2 * I.f) := by
  have hmem : ∀ q p : ℕ, q < p → q + p ≤ 2 * a → (q, p) ∈ ((Finset.range a) ×ˢ
      (Finset.range (2 * a + 1))).filter (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a) := by
    intro q p h1 h2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  refine GlobalTheory.finite_and_ncard_le_prod_of_levels _ (ℕ × ℕ) _ _ (fun b => b.2 - b.1)
    (fun b γ γ' => ∀ y ∈ G (b.2 + 1), (γ - γ') *ᵥ y ∈ G b.1) _ ?_ ?_ ?_
  · intro b
    refine ⟨fun γ y _ => by simp, fun {γ γ'} h y hy => ?_, fun {γ γ' γ''} h h' y hy => ?_⟩
    · rw [← neg_sub, Matrix.neg_mulVec]; exact neg_mem (h y hy)
    · rw [← sub_add_sub_cancel γ γ' γ'', Matrix.add_mulVec]; exact add_mem (h y hy) (h' y hy)
  · intro γ hγ γ' hγ' h
    have hD := (GlobalTheory.lowering_difference_of_isometries I.E (𝓞 I.E) I.n I.J I.J_herm a G h0 hmono hperp γ γ' hγ.1 hγ'.1
      hγ.2.1 hγ'.2.1 (2 * a + 1) (by omega) (fun q p h1 h2 _ => h (q, p) (hmem q p h1 h2))).1
      (2 * a + 1) le_rfl
    rw [Nat.sub_self, h0, htop] at hD
    have hspan := (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1
    have : Matrix.toLin' (γ - γ') = 0 := by
      refine LinearMap.ext_on hspan fun y hy => ?_
      simpa [Matrix.sub_mulVec] using hD y hy
    rw [← sub_eq_zero]
    exact Matrix.toLin'.injective (by rw [this, map_zero])
  · rintro ⟨q, p⟩ hb T hT hlev hsep
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb
    exact block_count I x a G h0 hmono hsat hperp hrk q p hb.2.1 hb.2.2 _ _ (ht q) (ht p)
      (hlo q hb.1.1) (hhi p (by omega)) de hde T hT
      (fun γ hγ γ' hγ' q' p' h1 h2 h3 => hlev γ hγ γ' hγ' (q', p') (hmem q' p' h1 h2) h3) hsep

/- English proof (translation)
Simplify using `only [hf, Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]`.
-/
theorem hf_dot (y z : Fin I.n → I.E) : hf I y z = (starRingEnd I.E ∘ y) ⬝ᵥ (I.J *ᵥ z) := by
  simp only [hf, Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use `⟨fun hy => ?_, fun h => Submodule.subset_span h⟩` and prove the remaining obligations. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact hy`. Consider the case `zero => exact ⟨zero_mem _, fun s _ => by simp [hf, Formalism.UG.hform]⟩`. Consider the case `add y z _ _ h1 h2`.

Use `⟨add_mem h1.1 h2.1, fun s hs => ?_⟩` and prove the remaining obligations. Establish `e1` using `h1.2 s hs`. Establish `e2` using `h2.2 s hs`. Rewrite `*` using `[hf_dot]`. Rewrite using `[Matrix.mulVec_add, dotProduct_add, e1, e2, add_zero]`.

Consider the case `smul c y _ h1`. Use `⟨Submodule.smul_mem _ _ h1.1, fun s hs => ?_⟩` and prove the remaining obligations. Establish `e1` using `h1.2 s hs`. Rewrite `*` using `[hf_dot]`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, e1, smul_zero]`.
-/
theorem mem_perpIn (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, hf I s y = 0 := by
  refine ⟨fun hy => ?_, fun h => Submodule.subset_span h⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => by simp [hf, Formalism.UG.hform]⟩
  | add y z _ _ h1 h2 =>
    refine ⟨add_mem h1.1 h2.1, fun s hs => ?_⟩
    have e1 := h1.2 s hs
    have e2 := h2.2 s hs
    rw [hf_dot] at *
    rw [Matrix.mulVec_add, dotProduct_add, e1, e2, add_zero]
  | smul c y _ h1 =>
    refine ⟨Submodule.smul_mem _ _ h1.1, fun s hs => ?_⟩
    have e1 := h1.2 s hs
    rw [hf_dot] at *
    rw [Matrix.mulVec_smul, dotProduct_smul, e1, smul_zero]

/- English proof (translation)
Take `⟨S, hF, hj⟩` from `h`. Establish `hF'` using `((GlobalTheory.PointFlag.flag_spec I x).2.2 a S τ hF).1`. Take `⟨hS0, hSm, hSl, -, hSi, -⟩` from `hF`. Establish `hst` using `GlobalTheory.CountSteps.steps I x`. Take `⟨-, -, hd, hp⟩` from `GlobalTheory.Count.PerpStep.main I x`.

Establish `hsat : ∀ i, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S i)`. Introduce `i`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => rw [hSl]; exact (hst _ (by norm_num)).2.1`. Consider the case `cast i => rw [(hF' i).1]`.

Conclude with `(hst _ (hSi i).1).2.1`. Set `S' : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)` to `fun p => S ⟨min p a, by omega⟩`. Establish `hS'm : Monotone S'` using `fun p q h => hSm.monotone (by simp only [Fin.mk_le_mk]; omega)`. Establish `hS'a : S' a = stepLt I x (1 / 2)`. Rewrite using `[← hSl]; exact congrArg S (Fin.ext (by simp))`.

Establish `hS'c : ∀ i : Fin a, S' i = S i.castSucc` using `fun i => congrArg S (Fin.ext (by simp))`. Establish `hS's : ∀ i : Fin a, S' (i + 1) = S i.succ` using `fun i => congrArg S (Fin.ext (by simp))`. Establish `hiso : S' a ≤ perpIn I x (S' a)`. Rewrite using `[hS'a, (hd _ (by norm_num)).2]`. Conclude with `((hst (1 / 2) (by norm_num)).2.2.1.trans ((hst (1 / 2) (by norm_num)).2.2.2.1 _ (by norm_num))).trans (hst (1 / 2)⁻¹ (by norm_num)).2.2.1`.

Establish `hanti : ∀ p q, p ≤ q → perpIn I x (S' q) ≤ perpIn I x (S' p)` using `fun p q h => (hp _ _ (hsat _) (hsat _) (hS'm h)).2.2.2.1`. Set `τ' : ℕ → ℝ` to `fun p => if h : p < a then τ ⟨p, h⟩ else 1`. Establish `hτ' : ∀ i : Fin a, τ' i = τ i` using `fun i => dif_pos i.2`. Establish `hτ0 : ∀ p, 0 < τ' p` using `fun p => by`. Simplify using `only [τ']`.

Use `split_ifs with h`. Conclude with `(hSi _).1`. Conclude with `one_pos`. Establish `hLe : ∀ p < a, S' (p + 1) = stepLe I x (τ' p)` using `fun p h => by`. Rewrite using `[hS's ⟨p, h⟩, (hSi _).2.2.1, ← hτ']`.

Establish `hLt : ∀ p < a, S' p = stepLt I x (τ' p)` using `fun p h => by`. Rewrite using `[hS'c ⟨p, h⟩, (hF' _).1, ← hτ']`. Use `⟨fun p => if p ≤ a then S' p else perpIn I x (S' (2 * a + 1 - p)), fun p => if p < a then τ' p else if p = a then 2 else (τ' (2 * a - p))⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩` and prove the remaining obligations. Simplify using `only [Nat.zero_le, if_true]`. Rewrite using `[← hS0]; exact congrArg S (Fin.ext (by simp))`.

Introduce `p q h`. Distinguish the cases in `h1 : q ≤ a`. Simplify using `only [if_pos h1, if_pos (h.trans h1)]`. Conclude with `hS'm h`. Distinguish the cases in `h2 : p ≤ a`.

Simplify using `only [if_neg h1, if_pos h2]`. Conclude with `((hS'm h2).trans hiso).trans (hanti _ _ (by omega))`. Simplify using `only [if_neg h1, if_neg h2]`. Conclude with `hanti _ _ (by omega)`. Introduce `p`.

Distinguish the cases in `h1 : p ≤ a`. Simplify using `only [if_pos h1]`. Conclude with `hsat _`. Simplify using `only [if_neg h1]`. Conclude with `(hp _ _ (hsat _) (hsat _) le_rfl).1`.

Introduce `p hpa`. Distinguish the cases in `h1 : p ≤ a`. Simplify using `only [if_pos h1, if_neg (show ¬ 2 * a + 1 - p ≤ a by omega)]`. Rewrite using `[show 2 * a + 1 - (2 * a + 1 - p) = p by omega]`. Simplify using `only [if_neg h1, if_pos (show 2 * a + 1 - p ≤ a by omega)]`.

Conclude with `(hp _ _ (hsat _) (hsat _) le_rfl).2.2.1.symm`. Introduce `p hpa`. Break down `lt_trichotomy p a with h1 | rfl | h1` into its components or cases. Simplify using `only [if_pos h1, if_pos (show p + 1 ≤ a by omega)]; exact hLe p h1`. Simplify using `only [lt_irrefl, if_false, if_true, if_neg (show ¬ p + 1 ≤ p by omega)]`.

Rewrite using `[show 2 * p + 1 - (p + 1) = p by omega, hS'a, (hd _ (by norm_num)).2]`. Evaluate the numerical expressions. Simplify using `only [if_neg h1.not_gt, if_neg h1.ne', if_neg (show ¬ p + 1 ≤ a by omega)]`. Rewrite using `[show 2 * a + 1 - (p + 1) = 2 * a - p by omega, hLt _ (by omega), (hd _ (hτ0 _)).2]`. Introduce `p hpa`.

Break down `lt_trichotomy p a with h1 | rfl | h1` into its components or cases. Simplify using `only [if_pos h1, if_pos h1.le, if_neg h1.ne]`. Conclude with `hLt p h1`. Simplify using `only [le_rfl, if_true]`. Conclude with `hS'a`.

Simplify using `only [if_neg h1.not_gt, if_neg h1.ne', if_neg h1.not_ge]`. Rewrite using `[show 2 * a + 1 - p = 2 * a - p + 1 by omega, hLe _ (by omega), (hd _ (hτ0 _)).1]`. Introduce `p`. Use `hτ0 p` as an intermediate fact. Use `hτ0 (2 * a - p)` as an intermediate fact.

Simplify using `only`. Apply the tactic sequence `split_ifs <;> positivity`. Introduce `i`. Establish `hi` using `i.2`. Use `⟨by simp only [if_pos hi, hτ'], ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [if_neg (show ¬ 2 * a - i < a by omega), if_neg (show ¬ 2 * a - i = a by omega)]`. Rewrite using `[show 2 * a - (2 * a - i) = i by omega, hτ']`. Simplify using `only [if_pos (show i + 1 ≤ a by omega), if_pos hi.le]`. Rewrite using `[hS's, hS'c, hj]`.
-/
theorem exists_chain (a : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (h : HasType I x j τ) :
    ∃ (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (t : ℕ → ℝ), G 0 = ⊥ ∧ Monotone G ∧
      (∀ p, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G p)) ∧
      (∀ p ≤ 2 * a + 1, G (2 * a + 1 - p) = perpIn I x (G p)) ∧
      (∀ p ≤ 2 * a, G (p + 1) = stepLe I x (t p)) ∧
      (∀ p ≤ 2 * a, G p = stepLt I x (if p = a then 1 / 2 else t p)) ∧ (∀ p, 0 < t p) ∧
      (∀ i : Fin a, t i = τ i ∧ t (2 * a - i) = (τ i)⁻¹ ∧ rkK (G (i + 1)) = rkK (G i) + j i) ∧ t a = 2 := by
  obtain ⟨S, hF, hj⟩ := h
  have hF' := ((GlobalTheory.PointFlag.flag_spec I x).2.2 a S τ hF).1
  obtain ⟨hS0, hSm, hSl, -, hSi, -⟩ := hF
  have hst := GlobalTheory.CountSteps.steps I x
  obtain ⟨-, -, hd, hp⟩ := GlobalTheory.Count.PerpStep.main I x
  have hsat : ∀ i, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S i) := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hSl]; exact (hst _ (by norm_num)).2.1
    | cast i => rw [(hF' i).1]; exact (hst _ (hSi i).1).2.1
  let S' : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E) := fun p => S ⟨min p a, by omega⟩
  have hS'm : Monotone S' := fun p q h => hSm.monotone (by simp only [Fin.mk_le_mk]; omega)
  have hS'a : S' a = stepLt I x (1 / 2) := by
    rw [← hSl]; exact congrArg S (Fin.ext (by simp))
  have hS'c : ∀ i : Fin a, S' i = S i.castSucc := fun i => congrArg S (Fin.ext (by simp))
  have hS's : ∀ i : Fin a, S' (i + 1) = S i.succ := fun i => congrArg S (Fin.ext (by simp))
  have hiso : S' a ≤ perpIn I x (S' a) := by
    rw [hS'a, (hd _ (by norm_num)).2]
    exact ((hst (1 / 2) (by norm_num)).2.2.1.trans ((hst (1 / 2) (by norm_num)).2.2.2.1 _ (by norm_num))).trans
      (hst (1 / 2)⁻¹ (by norm_num)).2.2.1
  have hanti : ∀ p q, p ≤ q → perpIn I x (S' q) ≤ perpIn I x (S' p) := fun p q h =>
    (hp _ _ (hsat _) (hsat _) (hS'm h)).2.2.2.1
  let τ' : ℕ → ℝ := fun p => if h : p < a then τ ⟨p, h⟩ else 1
  have hτ' : ∀ i : Fin a, τ' i = τ i := fun i => dif_pos i.2
  have hτ0 : ∀ p, 0 < τ' p := fun p => by
    simp only [τ']; split_ifs with h
    · exact (hSi _).1
    · exact one_pos
  have hLe : ∀ p < a, S' (p + 1) = stepLe I x (τ' p) := fun p h => by
    rw [hS's ⟨p, h⟩, (hSi _).2.2.1, ← hτ']
  have hLt : ∀ p < a, S' p = stepLt I x (τ' p) := fun p h => by
    rw [hS'c ⟨p, h⟩, (hF' _).1, ← hτ']
  refine ⟨fun p => if p ≤ a then S' p else perpIn I x (S' (2 * a + 1 - p)),
    fun p => if p < a then τ' p else if p = a then 2 else (τ' (2 * a - p))⁻¹,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩
  · simp only [Nat.zero_le, if_true]
    rw [← hS0]; exact congrArg S (Fin.ext (by simp))
  · intro p q h
    by_cases h1 : q ≤ a
    · simp only [if_pos h1, if_pos (h.trans h1)]; exact hS'm h
    · by_cases h2 : p ≤ a
      · simp only [if_neg h1, if_pos h2]
        exact ((hS'm h2).trans hiso).trans (hanti _ _ (by omega))
      · simp only [if_neg h1, if_neg h2]
        exact hanti _ _ (by omega)
  · intro p
    by_cases h1 : p ≤ a
    · simp only [if_pos h1]; exact hsat _
    · simp only [if_neg h1]; exact (hp _ _ (hsat _) (hsat _) le_rfl).1
  · intro p hpa
    by_cases h1 : p ≤ a
    · simp only [if_pos h1, if_neg (show ¬ 2 * a + 1 - p ≤ a by omega)]
      rw [show 2 * a + 1 - (2 * a + 1 - p) = p by omega]
    · simp only [if_neg h1, if_pos (show 2 * a + 1 - p ≤ a by omega)]
      exact (hp _ _ (hsat _) (hsat _) le_rfl).2.2.1.symm
  · intro p hpa
    rcases lt_trichotomy p a with h1 | rfl | h1
    · simp only [if_pos h1, if_pos (show p + 1 ≤ a by omega)]; exact hLe p h1
    · simp only [lt_irrefl, if_false, if_true, if_neg (show ¬ p + 1 ≤ p by omega)]
      rw [show 2 * p + 1 - (p + 1) = p by omega, hS'a, (hd _ (by norm_num)).2]
      norm_num
    · simp only [if_neg h1.not_gt, if_neg h1.ne', if_neg (show ¬ p + 1 ≤ a by omega)]
      rw [show 2 * a + 1 - (p + 1) = 2 * a - p by omega, hLt _ (by omega), (hd _ (hτ0 _)).2]
  · intro p hpa
    rcases lt_trichotomy p a with h1 | rfl | h1
    · simp only [if_pos h1, if_pos h1.le, if_neg h1.ne]; exact hLt p h1
    · simp only [le_rfl, if_true]; exact hS'a
    · simp only [if_neg h1.not_gt, if_neg h1.ne', if_neg h1.not_ge]
      rw [show 2 * a + 1 - p = 2 * a - p + 1 by omega, hLe _ (by omega), (hd _ (hτ0 _)).1]
  · intro p
    have := hτ0 p
    have := hτ0 (2 * a - p)
    dsimp only
    split_ifs <;> positivity
  · intro i
    have hi := i.2
    refine ⟨by simp only [if_pos hi, hτ'], ?_, ?_⟩
    · simp only [if_neg (show ¬ 2 * a - i < a by omega), if_neg (show ¬ 2 * a - i = a by omega)]
      rw [show 2 * a - (2 * a - i) = i by omega, hτ']
    · simp only [if_pos (show i + 1 ≤ a by omega), if_pos hi.le]
      rw [hS's, hS'c, hj]

/- English proof (translation)
Use `⟨h1, fun p hp y hy => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `hl` using `(GlobalTheory.NearLower.near_lowers_steps I x de hde hde').1 γ g h1 h2 h3 hg (t p) (ht p)`. Rewrite `hy` using `[hLe p hp]`. Establish `hm : ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y ∈ stepLe I x (de * t p)` using `hl ⟨y, hy, Matrix.toLin'_apply _ _⟩`. Rewrite using `[hLt p hp]`.

Use `(GlobalTheory.CountSteps.steps I x _ (mul_pos hde (ht p))).2.2.2.1 _ ?_ hm` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[h, hta]`. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[ht p]`.

Establish `he : (frm I x w)⁻¹ * ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1).map w.embedding * frm I x w = (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w - 1`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ (FrameMajorant.frm_unit I x w)]`. Establish `hn` using `hg.2.2 (w.comap (algebraMap I.F I.E))`. Rewrite using `[op, he]`. Use `(norm_opM_le _).trans (le_trans (le_of_eq ?_) hn)` and prove the remaining obligations.

Break down `(GlobalTheory.PointEquivariance.equivariance I x γ g h1 h2 h3).2.2.2.2.2.2 w with h | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[h]`. Use `congr 1`. Unfold `hs`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.norm_conj]`. Simplify using `only [Matrix.sub_apply, Matrix.map_apply, map_sub, Complex.conj_conj, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mem_lowSet (de : ℝ) (hde : 0 < de) (hde' : de < 1 / 4) (a : ℕ)
    (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (t : ℕ → ℝ) (ht : ∀ p, 0 < t p) (hta : t a = 2)
    (hLe : ∀ p ≤ 2 * a, G (p + 1) = stepLe I x (t p))
    (hLt : ∀ p ≤ 2 * a, G p = stepLt I x (if p = a then 1 / 2 else t p))
    (g : I.GA) (hg : g ∈ nearSet I x de) (γ : GL (Fin I.n) I.E)
    (h1 : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (h2 : ∀ v, uMat (g.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (h3 : I.fmat g.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) ∈ lowSet I x a G de := by
  refine ⟨h1, fun p hp y hy => ?_, fun w => ?_⟩
  · have hl := (GlobalTheory.NearLower.near_lowers_steps I x de hde hde').1 γ g h1 h2 h3 hg (t p) (ht p)
    rw [hLe p hp] at hy
    have hm : ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y ∈ stepLe I x (de * t p) :=
      hl ⟨y, hy, Matrix.toLin'_apply _ _⟩
    rw [hLt p hp]
    refine (GlobalTheory.CountSteps.steps I x _ (mul_pos hde (ht p))).2.2.2.1 _ ?_ hm
    split_ifs with h
    · rw [h, hta]; linarith
    · nlinarith [ht p]
  · have he : (frm I x w)⁻¹ * ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1).map w.embedding * frm I x w =
        (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w - 1 := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ (FrameMajorant.frm_unit I x w)]
    have hn := hg.2.2 (w.comap (algebraMap I.F I.E))
    rw [op, he]
    refine (norm_opM_le _).trans (le_trans (le_of_eq ?_) hn)
    rcases (GlobalTheory.PointEquivariance.equivariance I x γ g h1 h2 h3).2.2.2.2.2.2 w with h | h
    · rw [h]
    · rw [h]
      congr 1
      unfold hs
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.norm_conj]
      simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Complex.conj_conj, Matrix.one_apply]
      split_ifs <;> simp

/- English proof (translation)
Establish `hl' : 0 < l'` using `by linarith`. Use `pow_le_pow_left₀ (by positivity) ?_ m` and prove the remaining obligations. Establish `: 2 * (2 * de) / l' ≤ 12 * de / l`. Rewrite using `[div_le_div_iff₀ hl' hl]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pow_le_pow_ratio {de l l' : ℝ} (hde : 0 < de) (hl : 0 < l) (h : l ≤ 3 * l') (m : ℕ) :
    (1 + 2 * (2 * de) / l') ^ m ≤ (1 + 12 * de / l) ^ m := by
  have hl' : 0 < l' := by linarith
  refine pow_le_pow_left₀ (by positivity) ?_ m
  have : 2 * (2 * de) / l' ≤ 12 * de / l := by
    rw [div_le_div_iff₀ hl' hl]; nlinarith
  linarith

/- English proof (translation)
Introduce `I x de hde hde' a j τ hty`. Take `⟨G, t, h0, hmono, hsat, hperp, hLe, hLt, ht, hti, hta⟩` from `exists_chain I x a j τ hty`. Establish `hst` using `GlobalTheory.CountSteps.steps I x`. Establish `htop : G (2 * a + 1) = lamX I x`. Use `hperp 0 (by omega)` as an intermediate fact.

Rewrite `this` using `[Nat.sub_zero, h0]`. Rewrite using `[this]`. Use extensionality with `y`. Rewrite using `[mem_perpIn]`. Use `⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[(Submodule.mem_bot _).1 hs]`. Simplify using `[hf, Formalism.UG.hform]`. Establish `hrk : ∀ p ≤ 2 * a + 1, rkK (G (2 * a + 1 - p)) + rkK (G p) = I.n` using `fun p hp => by`. Rewrite using `[hperp p hp]`. Conclude with `((GlobalTheory.Count.PerpStep.main I x).2.2.2 _ _ (hsat p) (hsat p) le_rfl).2.1`.

Take `⟨hfin, hcard⟩` from `core_count I x a G h0 hmono hsat (fun p hp y => by rw [hperp p hp, mem_perpIn, htop]) hrk htop t ht (fun q hq N h1 h2 => by`. Rewrite `h1`, the goal using `[hLt q (by omega), if_neg hq.ne]`. Conclude with `(hst _ (ht q)).2.2.2.2.2.2.2.1 N h1 h2)`. Use the proof step `(fun p hp hne => by`. Rewrite `hne`, the goal using `[hLe p hp]`.

Conclude with `(hst _ (ht p)).2.2.2.2.1 hne) de hde`. Set `e : I.GA → Matrix (Fin I.n) (Fin I.n) I.E` to `fun g => if h : g ∈ I.GFset then (h.choose : GL (Fin I.n) I.E) else 0`. Establish `hmap : Set.MapsTo e (nearSet I x de) (lowSet I x a G de)` using `fun g hg => by`. Establish `hs` using `hg.1.choose_spec`. Simplify using `only [e, dif_pos hg.1]`.

Conclude with `mem_lowSet I x de hde hde' a G t ht hta hLe hLt g hg _ hs.1 hs.2.1 hs.2.2`. Establish `hinj : Set.InjOn e (nearSet I x de)` using `fun g hg g' hg' h => by`. Establish `hs` using `hg.1.choose_spec`. Establish `hs'` using `hg'.1.choose_spec`. Simplify using `only [e, dif_pos hg.1, dif_pos hg'.1] at h`.

Use `Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))` and prove the remaining obligations. Conclude with `(hs.2.1 v).trans (h ▸ (hs'.2.1 v).symm)`. Conclude with `hs.2.2.trans (h ▸ hs'.2.2.symm)`. Use `⟨hfin.of_injOn hmap hinj, ?_⟩` and prove the remaining obligations. Establish `hle : (((nearSet I x de).ncard : ℕ) : ℝ) ≤ ((lowSet I x a G de).ncard : ℕ)`.

Conclude with `Set.ncard_le_ncard_of_injOn e hmap hinj hfin` after adjusting the coercions. Use `hle.trans (hcard.trans ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.prod_first_blocks_by_layers a (fun q p => (1 + 2 * (2 * de) / (t q / t p)) ^ (dimB I a G q p * I.f))]`. Establish `hτ : ∀ i, 0 < τ i` using `fun i => (hti i).1 ▸ ht i`. Establish `r1 : ∀ i : Fin a, rho I G i = j i` using `fun i => by rw [rho, (hti i).2.2]; omega`.

Establish `r2 : ∀ i : Fin a, rho I G (2 * a - i) = j i` using `fun i => by`. Establish `hi` using `i.2`. Establish `e1` using `hrk i (by omega)`. Establish `e2` using `hrk (i + 1) (by omega)`. Establish `e3` using `(hti i).2.2`.

Rewrite `e2` using `[show 2 * a + 1 - (i + 1) = 2 * a - i by omega]`. Rewrite using `[rho, show 2 * a - i + 1 = 2 * a + 1 - i by omega]`. Use linear arithmetic over natural numbers and integers. Establish `hsum : rkK (G a) = ∑ l, j l`. Establish `key : ∀ m, m ≤ a → rkK (G m) = ∑ l ∈ Finset.range m, rho I G l`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _`. Rewrite using `[h0]`. Simplify using `[rkK]`.

Consider the case `succ m ih`. Introduce `hm`. Establish `e3` using `(hti ⟨m, hm⟩).2.2`. Establish `e4` using `r1 ⟨m, hm⟩`. Rewrite using `[Finset.sum_range_succ, ← ih (by omega)]`.

Simplify using `only at e3 e4`. Use linear arithmetic over natural numbers and integers. Rewrite using `[key a le_rfl, Finset.sum_range]`. Conclude with `Finset.sum_congr rfl fun i _ => r1 i`. Establish `r3 : rho I G a = I.n - 2 * ∑ l, j l`.

Establish `e1` using `hrk a (by omega)`. Rewrite `e1` using `[show 2 * a + 1 - a = a + 1 by omega]`. Rewrite using `[rho]`. Use linear arithmetic over natural numbers and integers. Establish `hpos : ∀ q p m, 0 ≤ (1 + 2 * (2 * de) / (t q / t p)) ^ m` using `fun q p m => by`.

Use `ht q` as an intermediate fact. Use `ht p` as an intermediate fact. Check the signs of the components of the expression. Unfold `layerProd`. Use `mul_le_mul (Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun k _ => mul_nonneg (hpos _ _ _) (hpos _ _ _)) fun i _ => Finset.prod_le_prod (fun k _ => mul_nonneg (hpos _ _ _) (hpos _ _ _)) fun k hk => ?_) (Finset.prod_le_prod (fun i _ => mul_nonneg (hpos _ _ _) (hpos _ _ _)) …` and prove the remaining obligations.

Use `hτ i` as an intermediate fact. Use `hτ k` as an intermediate fact. Use the proof step `positivity)`. Establish `hik : (i : ℕ) < k` using `(Finset.mem_filter.1 hk).2`. Establish `hk'` using `k.2`.

Use `hτ i` as an intermediate fact. Use `hτ k` as an intermediate fact. Rewrite using `[dimB, dimB, if_neg (by omega), if_neg (by omega), r1, r2, r2, (hti i).1, (hti k).1, (hti k).2.1, div_inv_eq_mul]`. Use `mul_le_mul (pow_le_pow_ratio hde (by positivity) ?_ _) (pow_le_pow_ratio hde (by positivity) ?_ _) (by positivity) (by positivity)` and prove the remaining obligations. Establish `: 0 < τ i / τ k` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: 0 < τ i * τ k` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hi` using `i.2`. Use `hτ i` as an intermediate fact.

Rewrite using `[dimB, dimB, if_neg (by omega), if_pos (by omega), r2, r3, (hti i).1, hta, (hti i).2.1, div_inv_eq_mul]`. Use `mul_le_mul (pow_le_pow_ratio hde (by positivity) (by linarith) _) (pow_le_pow_ratio hde (by positivity) (by nlinarith) _) (by positivity) (by positivity)` and prove the remaining obligations.
-/
theorem near_count : ∀ (I : AutInst) (x : I.GA) (de : ℝ), 0 < de → de < 1 / 4 → ∀ (a : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ), HasType I x j τ → (nearSet I x de).Finite ∧ (((nearSet I x de).ncard : ℕ) : ℝ) ≤ layerProd I.n I.f j τ (fun la => 1 + 12 * de / la) := by
  intro I x de hde hde' a j τ hty
  classical
  obtain ⟨G, t, h0, hmono, hsat, hperp, hLe, hLt, ht, hti, hta⟩ := exists_chain I x a j τ hty
  have hst := GlobalTheory.CountSteps.steps I x
  have htop : G (2 * a + 1) = lamX I x := by
    have := hperp 0 (by omega)
    rw [Nat.sub_zero, h0] at this
    rw [this]
    ext y
    rw [mem_perpIn]
    refine ⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp [hf, Formalism.UG.hform]
  have hrk : ∀ p ≤ 2 * a + 1, rkK (G (2 * a + 1 - p)) + rkK (G p) = I.n := fun p hp => by
    rw [hperp p hp]
    exact ((GlobalTheory.Count.PerpStep.main I x).2.2.2 _ _ (hsat p) (hsat p) le_rfl).2.1
  obtain ⟨hfin, hcard⟩ := core_count I x a G h0 hmono hsat
    (fun p hp y => by rw [hperp p hp, mem_perpIn, htop]) hrk htop t ht
    (fun q hq N h1 h2 => by
      rw [hLt q (by omega), if_neg hq.ne] at h1 ⊢
      exact (hst _ (ht q)).2.2.2.2.2.2.2.1 N h1 h2)
    (fun p hp hne => by
      rw [hLe p hp] at hne ⊢
      exact (hst _ (ht p)).2.2.2.2.1 hne) de hde
  let e : I.GA → Matrix (Fin I.n) (Fin I.n) I.E := fun g =>
    if h : g ∈ I.GFset then (h.choose : GL (Fin I.n) I.E) else 0
  have hmap : Set.MapsTo e (nearSet I x de) (lowSet I x a G de) := fun g hg => by
    have hs := hg.1.choose_spec
    simp only [e, dif_pos hg.1]
    exact mem_lowSet I x de hde hde' a G t ht hta hLe hLt g hg _ hs.1 hs.2.1 hs.2.2
  have hinj : Set.InjOn e (nearSet I x de) := fun g hg g' hg' h => by
    have hs := hg.1.choose_spec
    have hs' := hg'.1.choose_spec
    simp only [e, dif_pos hg.1, dif_pos hg'.1] at h
    refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))
    · exact (hs.2.1 v).trans (h ▸ (hs'.2.1 v).symm)
    · exact hs.2.2.trans (h ▸ hs'.2.2.symm)
  refine ⟨hfin.of_injOn hmap hinj, ?_⟩
  have hle : (((nearSet I x de).ncard : ℕ) : ℝ) ≤ ((lowSet I x a G de).ncard : ℕ) := by
    exact_mod_cast Set.ncard_le_ncard_of_injOn e hmap hinj hfin
  refine hle.trans (hcard.trans ?_)
  rw [GlobalTheory.prod_first_blocks_by_layers a (fun q p => (1 + 2 * (2 * de) / (t q / t p)) ^ (dimB I a G q p * I.f))]
  have hτ : ∀ i, 0 < τ i := fun i => (hti i).1 ▸ ht i
  have r1 : ∀ i : Fin a, rho I G i = j i := fun i => by rw [rho, (hti i).2.2]; omega
  have r2 : ∀ i : Fin a, rho I G (2 * a - i) = j i := fun i => by
    have hi := i.2
    have e1 := hrk i (by omega)
    have e2 := hrk (i + 1) (by omega)
    have e3 := (hti i).2.2
    rw [show 2 * a + 1 - (i + 1) = 2 * a - i by omega] at e2
    rw [rho, show 2 * a - i + 1 = 2 * a + 1 - i by omega]
    omega
  have hsum : rkK (G a) = ∑ l, j l := by
    have key : ∀ m, m ≤ a → rkK (G m) = ∑ l ∈ Finset.range m, rho I G l := by
      intro m
      induction m with
      | zero => intro _; rw [h0]; simp [rkK]
      | succ m ih =>
        intro hm
        have e3 := (hti ⟨m, hm⟩).2.2
        have e4 := r1 ⟨m, hm⟩
        rw [Finset.sum_range_succ, ← ih (by omega)]
        dsimp only at e3 e4
        omega
    rw [key a le_rfl, Finset.sum_range]
    exact Finset.sum_congr rfl fun i _ => r1 i
  have r3 : rho I G a = I.n - 2 * ∑ l, j l := by
    have e1 := hrk a (by omega)
    rw [show 2 * a + 1 - a = a + 1 by omega] at e1
    rw [rho]
    omega
  have hpos : ∀ q p m, 0 ≤ (1 + 2 * (2 * de) / (t q / t p)) ^ m := fun q p m => by
    have := ht q
    have := ht p
    positivity
  unfold layerProd
  refine mul_le_mul (Finset.prod_le_prod
      (fun i _ => Finset.prod_nonneg fun k _ => mul_nonneg (hpos _ _ _) (hpos _ _ _))
      fun i _ => Finset.prod_le_prod (fun k _ => mul_nonneg (hpos _ _ _) (hpos _ _ _)) fun k hk => ?_)
    (Finset.prod_le_prod (fun i _ => mul_nonneg (hpos _ _ _) (hpos _ _ _)) fun i _ => ?_)
    (Finset.prod_nonneg fun i _ => mul_nonneg (hpos _ _ _) (hpos _ _ _))
    (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => by
      have := hτ i
      have := hτ k
      positivity)
  · have hik : (i : ℕ) < k := (Finset.mem_filter.1 hk).2
    have hk' := k.2
    have := hτ i
    have := hτ k
    rw [dimB, dimB, if_neg (by omega), if_neg (by omega), r1, r2, r2, (hti i).1, (hti k).1, (hti k).2.1,
      div_inv_eq_mul]
    refine mul_le_mul (pow_le_pow_ratio hde (by positivity) ?_ _) (pow_le_pow_ratio hde (by positivity) ?_ _)
      (by positivity) (by positivity)
    · have : 0 < τ i / τ k := by positivity
      linarith
    · have : 0 < τ i * τ k := by positivity
      linarith
  · have hi := i.2
    have := hτ i
    rw [dimB, dimB, if_neg (by omega), if_pos (by omega), r2, r3, (hti i).1, hta, (hti i).2.1,
      div_inv_eq_mul]
    refine mul_le_mul (pow_le_pow_ratio hde (by positivity) (by linarith) _)
      (pow_le_pow_ratio hde (by positivity) (by nlinarith) _) (by positivity) (by positivity)

end GlobalTheory.NearCount
