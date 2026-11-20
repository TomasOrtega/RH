import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExactStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalFunctionMatrixRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsChangeOfEigenFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianPeriodLatticeBasisSameSignatureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunctionStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/- English proof (translation)
Rewrite using `[← Matrix.det_fromBlocks_zero₂₁ A 0 B, ← Matrix.det_mul, Matrix.fromBlocks_mul_fromRows]`. Simplify using the standard rewrite rules.
-/
theorem det_fromRows_mul (A : Matrix m m ℂ) (B : Matrix n n ℂ) (R : Matrix m (m ⊕ n) ℂ) (C : Matrix n (m ⊕ n) ℂ) :
    (Matrix.fromRows (A * R) (B * C)).det = A.det * B.det * (Matrix.fromRows R C).det := by
  rw [← Matrix.det_fromBlocks_zero₂₁ A 0 B, ← Matrix.det_mul, Matrix.fromBlocks_mul_fromRows]
  simp

/- English proof (translation)
Establish `h1 : N * R * K = 1`. Rewrite using `[Matrix.mul_assoc, mul_eq_one_comm, Matrix.mul_assoc]`. Conclude with `hR`. Establish `h2 : Mᵀ * C * (K * N) = 0`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc C, h]`.

Simplify using the standard rewrite rules. Establish `e1` using `det_fromRows_mul N 1 R C`. Establish `e2` using `det_fromRows_mul 1 Mᵀ R C`. Rewrite `e1`, `e2` using `[Matrix.one_mul]`. Rewrite using `[horVal_eq h h1 hS, horVal_eq h2 hR hS', e1, e2]`.

Simplify using `only [Matrix.det_one, Matrix.det_transpose]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem horVal_change {K : Matrix (m ⊕ n) m ℂ} {C : Matrix n (m ⊕ n) ℂ} {R : Matrix m (m ⊕ n) ℂ}
    {S S' : Matrix (m ⊕ n) n ℂ} (N : Matrix m m ℂ) (M : Matrix n n ℂ) (h : C * K = 0) (hS : C * S = 1)
    (hR : R * (K * N) = 1) (hS' : Mᵀ * C * S' = 1) :
    horVal K C * M.det = horVal (K * N) (Mᵀ * C) * N.det := by
  have h1 : N * R * K = 1 := by
    rw [Matrix.mul_assoc, mul_eq_one_comm, Matrix.mul_assoc]; exact hR
  have h2 : Mᵀ * C * (K * N) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h]; simp
  have e1 := det_fromRows_mul N 1 R C
  have e2 := det_fromRows_mul 1 Mᵀ R C
  rw [Matrix.one_mul] at e1 e2
  rw [horVal_eq h h1 hS, horVal_eq h2 hR hS', e1, e2]
  simp only [Matrix.det_one, Matrix.det_transpose]
  ring

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `DifferentiableAt.fun_sum fun s _ => (differentiableAt_const _).mul ?_` and prove the remaining obligations. Conclude with `(HasFDerivAt.finset_prod fun i _ => (h _ _).hasFDerivAt).differentiableAt`.
-/
theorem differentiableAt_det {A : V → Matrix m m ℂ} {b : V} (h : ∀ i j, DifferentiableAt ℂ (fun b => A b i j) b) :
    DifferentiableAt ℂ (fun b => (A b).det) b := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun s _ => (differentiableAt_const _).mul ?_
  exact (HasFDerivAt.finset_prod fun i _ => (h _ _).hasFDerivAt).differentiableAt

/- English proof (translation)
Establish `d1 : DifferentiableAt ℂ (fun b => (R * K b).det) b₀` using `differentiableAt_det fun i j => by`. Simplify using `only [Matrix.mul_apply]`. Conclude with `DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hK _ _)`. Establish `d2 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det) b₀` using `differentiableAt_det fun i j => by`. Break down `i with i | i` into its components or cases.

Conclude with `differentiableAt_const _`. Conclude with `hC i j`. Establish `n1 : (R * K b₀).det ≠ 0` using `by rw [hR]; simp`. Establish `d3 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det * ((R * K b).det)⁻¹) b₀` using `d2.fun_mul (d1.fun_inv n1)`. Use `d3.congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [h, d1.continuousAt.eventually_ne n1] with b ⟨h0, S, hS⟩ hb`. Establish `hu : IsUnit (R * K b).det` using `hb.isUnit`. Establish `e` using `det_fromRows_mul (R * K b)⁻¹ 1 R (C b)`. Rewrite `e` using `[Matrix.one_mul]`. Rewrite using `[horVal_eq h0 (R := (R * K b)⁻¹ * R) (by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]) hS, e, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_one]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem differentiableAt_horVal {K : V → Matrix (m ⊕ n) m ℂ} {C : V → Matrix n (m ⊕ n) ℂ} {b₀ : V}
    (hK : ∀ i j, DifferentiableAt ℂ (fun b => K b i j) b₀) (hC : ∀ i j, DifferentiableAt ℂ (fun b => C b i j) b₀)
    {R : Matrix m (m ⊕ n) ℂ} (hR : R * K b₀ = 1)
    (h : ∀ᶠ b in 𝓝 b₀, C b * K b = 0 ∧ ∃ S : Matrix (m ⊕ n) n ℂ, C b * S = 1) :
    DifferentiableAt ℂ (fun b => horVal (K b) (C b)) b₀ := by
  have d1 : DifferentiableAt ℂ (fun b => (R * K b).det) b₀ := differentiableAt_det fun i j => by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hK _ _)
  have d2 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det) b₀ := differentiableAt_det fun i j => by
    rcases i with i | i
    · exact differentiableAt_const _
    · exact hC i j
  have n1 : (R * K b₀).det ≠ 0 := by rw [hR]; simp
  have d3 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det * ((R * K b).det)⁻¹) b₀ :=
    d2.fun_mul (d1.fun_inv n1)
  refine d3.congr_of_eventuallyEq ?_
  filter_upwards [h, d1.continuousAt.eventually_ne n1] with b ⟨h0, S, hS⟩ hb
  have hu : IsUnit (R * K b).det := hb.isUnit
  have e := det_fromRows_mul (R * K b)⁻¹ 1 R (C b)
  rw [Matrix.one_mul] at e
  rw [horVal_eq h0 (R := (R * K b)⁻¹ * R) (by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]) hS, e,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_one]
  ring

end Lin

/- English proof (translation)
Take `⟨s, hs, hs0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Take `⟨t, ht, ht0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h'`. Establish `hst : s * t ∈ Y.H0 0` using `add_neg_cancel D ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hs ht`. Set `L : Y.H0 0 →ₗ[F] Y.H0 0` to `(LinearMap.mulLeft F (s * t)).restrict fun g hg => add_zero (0 : Y.Dv) ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hst hg`. Establish `hinj : Function.Injective L` using `fun a b e => Subtype.ext (mul_left_cancel₀ (mul_ne_zero hs0 ht0) (congrArg Subtype.val e))`.

Take `⟨u, hu⟩` from `LinearMap.injective_iff_surjective.1 hinj ⟨1, GlobalTheory.ProjVar.Var.eff_iff_one_mem.1 Y.eff_zero⟩`. Establish `hu' : s * t * u = 1` using `congrArg Subtype.val hu`. Use `⟨s, fun y => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `D.exists_isEqn y`. Establish `r1` using `hg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hs y)`.

Establish `r2` using `hg.neg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 ht y)`. Establish `r3` using `CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 u.2 y)`. Use `hg.generatesAt_iff.2 ((unitAt_iff (mul_ne_zero hs0 g.ne_zero)).2 ⟨r1, ?_⟩)` and prove the remaining obligations. Establish `e : (s * (g : Y.Fn))⁻¹ = t * ((g⁻¹ : Y.Fnˣ) : Y.Fn) * u`. Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations.

Rewrite using `[← hu', Units.val_inv_eq_inv_val]`. Use `g.ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Conclude with `e ▸ r2.mul r3`.
-/
theorem exists_generates {F : Type} [Field F] (Y : GlobalTheory.ProjVar.Var F) (D : Y.Dv) (h : Y.H0 D ≠ ⊥)
    (h' : Y.H0 (-D) ≠ ⊥) : ∃ s, ∀ y, D.GeneratesAt y s := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h'
  have hst : s * t ∈ Y.H0 0 := add_neg_cancel D ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hs ht
  let L : Y.H0 0 →ₗ[F] Y.H0 0 := (LinearMap.mulLeft F (s * t)).restrict fun g hg =>
    add_zero (0 : Y.Dv) ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hst hg
  have hinj : Function.Injective L := fun a b e =>
    Subtype.ext (mul_left_cancel₀ (mul_ne_zero hs0 ht0) (congrArg Subtype.val e))
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨1, GlobalTheory.ProjVar.Var.eff_iff_one_mem.1 Y.eff_zero⟩
  have hu' : s * t * u = 1 := congrArg Subtype.val hu
  refine ⟨s, fun y => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have r1 := hg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hs y)
  have r2 := hg.neg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 ht y)
  have r3 := CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 u.2 y)
  refine hg.generatesAt_iff.2 ((unitAt_iff (mul_ne_zero hs0 g.ne_zero)).2 ⟨r1, ?_⟩)
  have e : (s * (g : Y.Fn))⁻¹ = t * ((g⁻¹ : Y.Fnˣ) : Y.Fn) * u := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hu', Units.val_inv_eq_inv_val]
    have := g.ne_zero
    field_simp
  exact e ▸ r2.mul r3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {σ : c.F →+* ℂ}
  {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {τ : E →+* ℂ} {x : ∀ i, Idx Dw τ → (Fu.Di i).La}
  {hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E}

/- English proof (translation)
Establish `hex : ∃ iQ : Σ i : Fin Fu.n, (Fu.Di i).La →+ (Letter Dw → ℂ), Per Fu a iQ.1 iQ.2` using `⟨⟨i, Q⟩, h⟩`. Rewrite using `[horOf, dif_pos hex]`. Establish `hs` using `hex.choose_spec`. Generalize the expression as in `hex.choose = w at hs`. Take `⟨j, Q'⟩` from `w`.

Apply the tactic sequence `obtain rfl : j = i := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).1 _ _ _ _ hs h`. Apply the tactic sequence `obtain ⟨gm, h1, h2, h3⟩ := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).2 _ _ _ h hs`. Use `(GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one E H Dw l c σ _ τ (x j) (hm j) Q' gm (hx j) (GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ a j Q' _ _ hs (hx j)) h1).2.2 hl h2` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`.

Conclude with `AddMonoidHom.ext h3`.
-/
theorem horOf_eq {Z : Model Xo c β} (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (hx : ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i))
    (a : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (h : Per Fu a i Q) :
    horOf Fu τ x hm a = perVal c σ τ (x i) (hm i) Q := by
  have hex : ∃ iQ : Σ i : Fin Fu.n, (Fu.Di i).La →+ (Letter Dw → ℂ), Per Fu a iQ.1 iQ.2 := ⟨⟨i, Q⟩, h⟩
  rw [horOf, dif_pos hex]
  have hs := hex.choose_spec
  generalize hex.choose = w at hs
  obtain ⟨j, Q'⟩ := w
  obtain rfl : j = i := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).1 _ _ _ _ hs h
  obtain ⟨gm, h1, h2, h3⟩ := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).2 _ _ _ h hs
  have := (GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one E H Dw l c σ _ τ (x j) (hm j) Q' gm (hx j) (GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ a j Q' _ _ hs (hx j))
    h1).2.2 hl h2
  rw [← this]
  congr 1
  exact AddMonoidHom.ext h3

/- English proof (translation)
Establish `good` using `fun a i Q h => GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β T.Z σ g e Fu τ a i Q _ _ h (hx i)`. Use `⟨fun a ha => ?_, fun a a' M N ha hM hN => ?_, fun V _ _ _ B a hB hf hi b₀ hb => ?_, GlobalTheory.T.horizontal_function_matrix_relation E H Dw l Xo c O β Y T σ g e Fu τ x hm _ hσ hr hx (horOf_eq hl hx)⟩` and prove the remaining obligations. Take `⟨i, Q, h⟩` from `GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β T.Z σ g e Fu a ha`. Rewrite using `[horOf_eq hl hx a i Q h]`. Conclude with `(good a i Q h).perVal_ne_zero`.

Take `⟨i, Q, h⟩` from `GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β T.Z σ g e Fu a ha`. Take `⟨Q', h', hc⟩` from `GlobalTheory.T.periods_change_of_eigenFrame E H Dw l Xo c O β T.Z σ g e Fu a a' i Q h hM.1`. Establish `key : ∀ ρ M, Chg a a' ρ M → perMat (x i) Q ρ = Mᵀ * perMat (x i) Q' ρ` using `fun ρ M hM => by`. Use extensionality with `j k`. Simplify using `only [perMat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hc ρ M hM, mul_comm]`.

Establish `k2 : kerMat c σ τ (x i) (hm i) Q = kerMat c σ τ (x i) (hm i) Q' * N`. Rewrite using `[kerMat, key _ _ hN, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, kerMat]`. Take `⟨-, -, ⟨R, hR⟩, S, hS⟩` from `good a i Q h`. Take `⟨-, h0, -, S', hS'⟩` from `good a' i Q' h'`. Rewrite using `[horOf_eq hl hx a i Q h, horOf_eq hl hx a' i Q' h', perVal, perVal, k2, key _ _ hM]`.

Conclude with `horVal_change N M h0 hS' (k2 ▸ hR) (key _ _ hM ▸ hS)`. Take `⟨B', i, Q, hB', hb', -, hP, hd⟩` from `GlobalTheory.T.exists_locally_holomorphic_periods_family E H Dw l Xo c O β T.Z σ g e Fu V B a hB hf hi b₀ hb`. Establish `hn` using `hB'.mem_nhds hb'`. Establish `hd' : ∀ v z, DifferentiableAt ℂ (fun b => Q b v z) b₀` using `fun v z => (hd v z).differentiableAt hn`. Take `⟨R, hR⟩` from `(good _ i _ (hP b₀ hb')).2.2.1`.

Use `DifferentiableAt.differentiableWithinAt (DifferentiableAt.congr_of_eventuallyEq (differentiableAt_horVal (K := fun b => kerMat c σ τ (x i) (hm i) (Q b)) (C := fun b => perMat (x i) (Q b) τ) (fun j k => ?_) (fun j k => hd' _ _) hR ?_) ?_)` and prove the remaining obligations. Simplify using `only [kerMat, Matrix.mul_apply]`. Conclude with `DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hd' _ _)`. Use `filter_upwards [hn] with b hb`. Conclude with `⟨(good _ i _ (hP b hb)).2.1, (good _ i _ (hP b hb)).2.2.2⟩`.

Use `filter_upwards [hn] with b hb`. Conclude with `horOf_eq hl hx _ i _ (hP b hb)`.
-/
theorem horFn_horOf {Y : Model Xo c β} (T : TorModel Y) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hr : 1 ≤ Dw.p + Dw.q)
    (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (hx : ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) :
    HorFn (Z := T.Z) τ (horOf Fu τ x hm) := by
  have good := fun a i Q h => GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β T.Z σ g e Fu τ a i Q _ _ h (hx i)
  refine ⟨fun a ha => ?_, fun a a' M N ha hM hN => ?_, fun V _ _ _ B a hB hf hi b₀ hb => ?_,
    GlobalTheory.T.horizontal_function_matrix_relation E H Dw l Xo c O β Y T σ g e Fu τ x hm _ hσ hr hx (horOf_eq hl hx)⟩
  · obtain ⟨i, Q, h⟩ := GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β T.Z σ g e Fu a ha
    rw [horOf_eq hl hx a i Q h]
    exact (good a i Q h).perVal_ne_zero
  · obtain ⟨i, Q, h⟩ := GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β T.Z σ g e Fu a ha
    obtain ⟨Q', h', hc⟩ := GlobalTheory.T.periods_change_of_eigenFrame E H Dw l Xo c O β T.Z σ g e Fu a a' i Q h hM.1
    have key : ∀ ρ M, Chg a a' ρ M → perMat (x i) Q ρ = Mᵀ * perMat (x i) Q' ρ := fun ρ M hM => by
      ext j k
      simp only [perMat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hc ρ M hM, mul_comm]
    have k2 : kerMat c σ τ (x i) (hm i) Q = kerMat c σ τ (x i) (hm i) Q' * N := by
      rw [kerMat, key _ _ hN, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, kerMat]
    obtain ⟨-, -, ⟨R, hR⟩, S, hS⟩ := good a i Q h
    obtain ⟨-, h0, -, S', hS'⟩ := good a' i Q' h'
    rw [horOf_eq hl hx a i Q h, horOf_eq hl hx a' i Q' h', perVal, perVal, k2, key _ _ hM]
    exact horVal_change N M h0 hS' (k2 ▸ hR) (key _ _ hM ▸ hS)
  · obtain ⟨B', i, Q, hB', hb', -, hP, hd⟩ := GlobalTheory.T.exists_locally_holomorphic_periods_family E H Dw l Xo c O β T.Z σ g e Fu V B a hB hf hi b₀ hb
    have hn := hB'.mem_nhds hb'
    have hd' : ∀ v z, DifferentiableAt ℂ (fun b => Q b v z) b₀ := fun v z => (hd v z).differentiableAt hn
    obtain ⟨R, hR⟩ := (good _ i _ (hP b₀ hb')).2.2.1
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.congr_of_eventuallyEq
      (differentiableAt_horVal (K := fun b => kerMat c σ τ (x i) (hm i) (Q b)) (C := fun b => perMat (x i) (Q b) τ)
        (fun j k => ?_) (fun j k => hd' _ _) hR ?_) ?_)
    · simp only [kerMat, Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hd' _ _)
    · filter_upwards [hn] with b hb
      exact ⟨(good _ i _ (hP b hb)).2.1, (good _ i _ (hP b hb)).2.2.2⟩
    · filter_upwards [hn] with b hb
      exact horOf_eq hl hx _ i _ (hP b hb)

end GlobalTheory.ShFam.Hor

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
  Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo in

/- English proof (translation)
Introduce `D A N j S κ s fl k τ`. Establish `hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀` using `rfl`. Take `⟨g, e, Fu, -⟩` from `(s.unf κ.σ₀ hσ).1.2.2.2.2.2`. Use `choose x hm hx using fun i : Fin Fu.n => GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature _ A.H S.Dw (Fu.Di i) (DV.tauEmb D τ) (Fu.sig i)`. Establish `hr : 1 ≤ S.Dw.p + S.Dw.q` using `by have := S.two_le; have := S.rank_eq; omega`.

Take `⟨h1, h2⟩` from `GlobalTheory.T.H0_divOf_ne_bot_of_horFn _ A.H S.Dw κ.l _ κ.c _ _ s.T.Z κ.σ₀ _ κ.e (fl.C k) (DV.tauEmb D τ) _ (A.cm τ) (GlobalTheory.ShFam.Hor.horFn_horOf (Fu := Fu) s.T hσ hr κ.good hx)`. Conclude with `Classical.epsilon_spec (GlobalTheory.ShFam.Hor.exists_generates _ _ h1 h2)`.
-/
theorem GlobalTheory.ShFam.Hor.isFlat_flatSec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag) (k : s.Comp) (τ : D.what₂.Tau), IsFlat (fl.C k) (DV.tauEmb D τ) (flatSec s fl k τ) := by
  intro D A N j S κ s fl k τ
  have hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl
  obtain ⟨g, e, Fu, -⟩ := (s.unf κ.σ₀ hσ).1.2.2.2.2.2
  choose x hm hx using fun i : Fin Fu.n =>
    GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature _ A.H S.Dw (Fu.Di i) (DV.tauEmb D τ) (Fu.sig i)
  have hr : 1 ≤ S.Dw.p + S.Dw.q := by have := S.two_le; have := S.rank_eq; omega
  obtain ⟨h1, h2⟩ := GlobalTheory.T.H0_divOf_ne_bot_of_horFn _ A.H S.Dw κ.l _ κ.c _ _ s.T.Z κ.σ₀ _ κ.e (fl.C k) (DV.tauEmb D τ) _ (A.cm τ)
    (GlobalTheory.ShFam.Hor.horFn_horOf (Fu := Fu) s.T hσ hr κ.good hx)
  exact Classical.epsilon_spec (GlobalTheory.ShFam.Hor.exists_generates _ _ h1 h2)
