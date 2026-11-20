import Formalism.FlagUnipotentLattices.StabiliserComplementDecomposition
import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
import Formalism.FormalDegreeBessel.FinalG

open Finset Matrix
open scoped ComplexConjugate TensorProduct

namespace Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants

/- English proof (translation)
Introduce `k r z z' g hT hT'`. Unfold `Gf`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Use `mul_nonneg (mul_nonneg hT hT') (Complex.normSq_nonneg (Dmin k r z z' g ⟨r, by omega⟩))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gauge_le_determinant : GfLeD := by
  intro k r z z' g hT hT'
  unfold Gf
  rw [Complex.normSq_eq_norm_sq]
  have := mul_nonneg (mul_nonneg hT hT') (Complex.normSq_nonneg (Dmin k r z z' g ⟨r, by omega⟩))
  linarith

/- English proof (translation)
Introduce `V _ _ h r y f' b`. Establish `h1 : h (formalDeterminantVector h y f') (f' b) = ((Matrix.of fun a b => h (y a) (f' b)).adjugate * (Matrix.of fun a b => h (y a) (f' b))) (Fin.last r) b`. Simplify using `[formalDeterminantVector, Matrix.mul_apply, map_sum]`. Rewrite using `[h1, Matrix.adjugate_mul]`. Distinguish the cases in `hb : b = Fin.last r`.

Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hb, Ne.symm hb]`.
-/
theorem orthogonality_relation : DualVectorOrthogonal := by
  intro V _ _ h r y f' b
  have h1 : h (formalDeterminantVector h y f') (f' b) =
      ((Matrix.of fun a b => h (y a) (f' b)).adjugate * (Matrix.of fun a b => h (y a) (f' b))) (Fin.last r) b := by
    simp [formalDeterminantVector, Matrix.mul_apply, map_sum]
  rw [h1, Matrix.adjugate_mul]
  by_cases hb : b = Fin.last r
  · subst hb; simp
  · simp [hb, Ne.symm hb]

/- English proof (translation)
Introduce `n H e v x`. Establish `key : ∀ w : Fin n → ℂ, ∑ j, herm H (Pi.single j 1) w * x j = herm H x w`. Introduce `w`. Simplify using `only [herm, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Use extensionality with `i`. Simplify using `only [rankTwoSkewMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[← key v, ← key e, Finset.sum_mul, Finset.sum_mul]`. Apply the tactic sequence `congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem matrix_action_evaluation_holds : RankTwoSkewMatrixApply := by
  intro n H e v x
  have key : ∀ w : Fin n → ℂ, ∑ j, herm H (Pi.single j 1) w * x j = herm H x w := by
    intro w
    simp only [herm, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  ext i
  simp only [rankTwoSkewMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib]
  rw [← key v, ← key e, Finset.sum_mul, Finset.sum_mul]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Introduce `V ι _ _ _ c x P d ka la la1 hla hd hP hc`. Establish `h1 : ‖d‖ * ‖P‖ ≤ ∑ i, ‖c i‖ * ‖x i‖`. Rewrite using `[← norm_smul, hP]`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_smul _ _).le)`. Establish `h2 : (∑ i, ‖c i‖ * ‖x i‖) ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * ∑ i, ‖x i‖ ^ 2` using `Finset.sum_mul_sq_le_sq_mul_sq _ _ _`.

Establish `h3 : (‖d‖ * ‖P‖) ^ 2 ≤ (∑ i, ‖c i‖ * ‖x i‖) ^ 2` using `pow_le_pow_left₀ (by positivity) h1 2`. Establish `hX : 0 ≤ ∑ i, ‖x i‖ ^ 2` using `Finset.sum_nonneg fun i _ => by positivity`. Establish `h4 : (‖d‖ * ‖P‖) ^ 2 ≤ 4 * la ^ 2 * ∑ i, ‖x i‖ ^ 2` using `h3.trans (h2.trans (mul_le_mul_of_nonneg_right hc hX))`. Rewrite `h4` using `[hd]`. Establish `e : (ka * la1 / la) ^ 2 * ‖P‖ ^ 2 = (2 * ka * la1 * ‖P‖) ^ 2 / (4 * la ^ 2)` using `by field_simp; ring`.

Rewrite using `[e, div_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem majorant_cauchy_schwarz_holds : MomentPointwiseBound := by
  intro V ι _ _ _ c x P d ka la la1 hla hd hP hc
  have h1 : ‖d‖ * ‖P‖ ≤ ∑ i, ‖c i‖ * ‖x i‖ := by
    rw [← norm_smul, hP]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_smul _ _).le)
  have h2 : (∑ i, ‖c i‖ * ‖x i‖) ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * ∑ i, ‖x i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : (‖d‖ * ‖P‖) ^ 2 ≤ (∑ i, ‖c i‖ * ‖x i‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have hX : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h4 : (‖d‖ * ‖P‖) ^ 2 ≤ 4 * la ^ 2 * ∑ i, ‖x i‖ ^ 2 :=
    h3.trans (h2.trans (mul_le_mul_of_nonneg_right hc hX))
  rw [hd] at h4
  have e : (ka * la1 / la) ^ 2 * ‖P‖ ^ 2 = (2 * ka * la1 * ‖P‖) ^ 2 / (4 * la ^ 2) := by
    field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  linarith

/- English proof (translation)
Introduce `R _ d Z l h`. Unfold `leadingPrincipalMinor LeadingPrincipalMinor`. Rewrite using `[← Matrix.det_submatrix_equiv_self (Fin.castLEOrderIso h).toEquiv]`. Both sides reduce to the same expression.
-/
theorem leading_minor_codings_agree' : LeadingMinorCodingsAgree := by
  intro R _ d Z l h
  unfold leadingPrincipalMinor LeadingPrincipalMinor
  rw [← Matrix.det_submatrix_equiv_self (Fin.castLEOrderIso h).toEquiv]
  rfl

/- English proof (translation)
Introduce `k r z z' g l`. Rewrite using `[leading_minor_codings_agree' _ _ _ _ (Nat.le_of_lt_succ l.isLt)]`. Both sides reduce to the same expression.
-/
theorem minimal_degree_comparison : DminBridge := by
  intro k r z z' g l
  rw [leading_minor_codings_agree' _ _ _ _ (Nat.le_of_lt_succ l.isLt)]
  rfl

/- English proof (translation)
Introduce `V _ _ h hherm r f T hG a e v he hv`. Establish `hlast : ∀ b : Fin (r + 1), b ≤ a.castSucc → b ≠ Fin.last r`. Introduce `b hb hE`. Establish `h1 : (b : ℕ) ≤ (a : ℕ)` using `hb`. Establish `h2 : (b : ℕ) = r` using `by rw [hE]; rfl`.

Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsub : Submodule.span ℂ (f '' {b | b < a.castSucc}) ≤ Submodule.span ℂ (f '' {b | b ≤ a.castSucc})` using `Submodule.span_mono (Set.image_mono fun b (hb : b < a.castSucc) => (le_of_lt hb : b ≤ a.castSucc))`. Establish `heX : e ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc})`. Establish `h1 : f a.castSucc ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc})` using `Submodule.subset_span ⟨a.castSucc, (le_refl _ : a.castSucc ≤ a.castSucc), rfl⟩`.

Use `Submodule.add_mem _ (hsub he) h1` as an intermediate fact. Simplify using `using this`. Establish `hxe : ∀ x, (∀ b, b ≤ a.castSucc → h x (f b) = 0) → h x e = 0`. Introduce `x hx`. Use `Submodule.span_induction (p := fun y _ => h x y = 0) ?_ ?_ ?_ ?_ heX` and prove the remaining obligations.

Introduce and unpack `y ⟨b, hb, rfl⟩`. Conclude with `hx b hb`. Simplify using the standard rewrite rules. Introduce `y w _ _ hy hw`. Simplify using `[hy, hw]`.

Introduce `c y _ hy`. Simplify using `[hy]`. Establish `hev : h e v = 0`. Use `Submodule.span_induction (p := fun y _ => h y v = 0) ?_ ?_ ?_ ?_ heX` and prove the remaining obligations. Introduce and unpack `y ⟨b, hb, rfl⟩`.

Conclude with `hv b hb`. Simplify using the standard rewrite rules. Introduce `y w _ _ hy hw`. Simplify using `[hy, hw]`. Introduce `c y _ hy`.

Simplify using `[hy]`. Establish `hfe : ∀ b, h (f b) e = 0`. Introduce `b`. Apply `hxe` to reduce the goal to its premises. Introduce `c hc`.

Rewrite using `[hG]`. Simplify using `[hlast c hc]`. Establish `hX : ∀ x, (∀ b : Fin r, h x (f b.castSucc) = 0) → rankTwoSkewOperator h e v x = h x v • e`. Introduce `x hx`. Establish `: h x e = 0`.

Apply `hxe` to reduce the goal to its premises. Introduce `b hb`. Establish `hb' : (b : ℕ) < r` using `lt_of_le_of_lt (show (b : ℕ) ≤ (a : ℕ) from hb) a.isLt`. Use `hx ⟨b, hb'⟩` as an intermediate fact. Simplify using `using this`.

Simplify using `[rankTwoSkewOperator, this]`. Establish `hYf : ∀ b, rankTwoSkewOperator h e v (f b) = h (f b) v • e`. Introduce `b`. Simplify using `[rankTwoSkewOperator, hfe b]`. Use `⟨heX, hX, hYf, fun b hb => by rw [hYf, hv b hb, zero_smul], ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hYf, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ he`. Establish `hee : h e e = 0`. Apply `hxe` to reduce the goal to its premises. Introduce `b hb`.

Rewrite using `[hherm, hfe b]`. Simplify using the standard rewrite rules. Simplify using `[rankTwoSkewOperator, hev, hee]`. Establish `: h v e = 0` using `by rw [hherm, hev]; simp`. Simplify using `[rankTwoSkewOperator, this]`.
-/
theorem lie_algebra_nilpotent_part_holds : RankTwoSkewInNilradical := by
  intro V _ _ h hherm r f T hG a e v he hv
  have hlast : ∀ b : Fin (r + 1), b ≤ a.castSucc → b ≠ Fin.last r := by
    intro b hb hE
    have h1 : (b : ℕ) ≤ (a : ℕ) := hb
    have h2 : (b : ℕ) = r := by rw [hE]; rfl
    have := a.isLt; omega
  have hsub : Submodule.span ℂ (f '' {b | b < a.castSucc}) ≤ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) :=
    Submodule.span_mono (Set.image_mono fun b (hb : b < a.castSucc) => (le_of_lt hb : b ≤ a.castSucc))
  have heX : e ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) := by
    have h1 : f a.castSucc ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) :=
      Submodule.subset_span ⟨a.castSucc, (le_refl _ : a.castSucc ≤ a.castSucc), rfl⟩
    have := Submodule.add_mem _ (hsub he) h1
    simpa using this

  have hxe : ∀ x, (∀ b, b ≤ a.castSucc → h x (f b) = 0) → h x e = 0 := by
    intro x hx
    refine Submodule.span_induction (p := fun y _ => h x y = 0) ?_ ?_ ?_ ?_ heX
    · rintro y ⟨b, hb, rfl⟩; exact hx b hb
    · simp
    · intro y w _ _ hy hw; simp [hy, hw]
    · intro c y _ hy; simp [hy]
  have hev : h e v = 0 := by
    refine Submodule.span_induction (p := fun y _ => h y v = 0) ?_ ?_ ?_ ?_ heX
    · rintro y ⟨b, hb, rfl⟩; exact hv b hb
    · simp
    · intro y w _ _ hy hw; simp [hy, hw]
    · intro c y _ hy; simp [hy]
  have hfe : ∀ b, h (f b) e = 0 := by
    intro b; apply hxe; intro c hc
    rw [hG]; simp [hlast c hc]
  have hX : ∀ x, (∀ b : Fin r, h x (f b.castSucc) = 0) → rankTwoSkewOperator h e v x = h x v • e := by
    intro x hx
    have : h x e = 0 := by
      apply hxe; intro b hb
      have hb' : (b : ℕ) < r := lt_of_le_of_lt (show (b : ℕ) ≤ (a : ℕ) from hb) a.isLt
      have := hx ⟨b, hb'⟩
      simpa using this
    simp [rankTwoSkewOperator, this]
  have hYf : ∀ b, rankTwoSkewOperator h e v (f b) = h (f b) v • e := by
    intro b; simp [rankTwoSkewOperator, hfe b]
  refine ⟨heX, hX, hYf, fun b hb => by rw [hYf, hv b hb, zero_smul], ?_, ?_, ?_⟩
  · rw [hYf, ← smul_sub]; exact Submodule.smul_mem _ _ he
  · have hee : h e e = 0 := by
      apply hxe; intro b hb
      rw [hherm, hfe b]; simp
    simp [rankTwoSkewOperator, hev, hee]
  · have : h v e = 0 := by rw [hherm, hev]; simp
    simp [rankTwoSkewOperator, this]

/- English proof (translation)
Introduce `V _ _ n y a`. Use `set K : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < a}) with hK`. Establish `: FiniteDimensional ℂ K` using `FiniteDimensional.span_of_finite ℂ (Set.toFinite _)`. Establish `hPm : K.starProjection (y a) ∈ K` using `Submodule.starProjection_apply_mem _ _`. Establish `hort : ∀ w ∈ K, inner ℂ (y a - K.starProjection (y a)) w = 0`.

Introduce `w hw`. Establish `h` using `Submodule.sub_starProjection_mem_orthogonal (K := K) (y a)`. Rewrite `h` using `[Submodule.mem_orthogonal']`. Conclude with `h _ hw`. Use `⟨y a - K.starProjection (y a), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `: y a - K.starProjection (y a) - y a = -(K.starProjection (y a))` using `by abel`. Rewrite using `[this]`. Conclude with `K.neg_mem hPm`. Introduce `b hb`. Conclude with `hort _ (Submodule.subset_span ⟨b, hb, rfl⟩)`.

Unfold `majorantDistance`. Rewrite using `[← hK, Metric.infDist_eq_iInf]`. Use `(Submodule.norm_eq_iInf_iff_inner_eq_zero K (u := y a) hPm).mpr hort` as an intermediate fact. Rewrite using `[this]`. Conclude with `iInf_congr fun w => (dist_eq_norm _ _).symm`.

Establish `h1 : inner ℂ (y a - K.starProjection (y a)) (y a) = inner ℂ (y a - K.starProjection (y a)) (y a - K.starProjection (y a))`. Rewrite using `[inner_sub_right (y a - K.starProjection (y a)) (y a), hort _ hPm, sub_zero]`. Rewrite using `[h1, inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem majorant_orthogonal_component : MajorantOrthogonalComponent := by
  intro V _ _ n y a
  set K : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < a}) with hK
  have : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hPm : K.starProjection (y a) ∈ K := Submodule.starProjection_apply_mem _ _
  have hort : ∀ w ∈ K, inner ℂ (y a - K.starProjection (y a)) w = 0 := by
    intro w hw
    have h := Submodule.sub_starProjection_mem_orthogonal (K := K) (y a)
    rw [Submodule.mem_orthogonal'] at h; exact h _ hw
  refine ⟨y a - K.starProjection (y a), ?_, ?_, ?_, ?_⟩
  · have : y a - K.starProjection (y a) - y a = -(K.starProjection (y a)) := by abel
    rw [this]; exact K.neg_mem hPm
  · intro b hb
    exact hort _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · unfold majorantDistance
    rw [← hK, Metric.infDist_eq_iInf]
    have := (Submodule.norm_eq_iInf_iff_inner_eq_zero K (u := y a) hPm).mpr hort
    rw [this]
    exact iInf_congr fun w => (dist_eq_norm _ _).symm
  · have h1 : inner ℂ (y a - K.starProjection (y a)) (y a) =
        inner ℂ (y a - K.starProjection (y a)) (y a - K.starProjection (y a)) := by
      rw [inner_sub_right (y a - K.starProjection (y a)) (y a), hort _ hPm, sub_zero]
    rw [h1, inner_self_eq_norm_sq_to_K]; push_cast; rfl

/- English proof (translation)
Establish `hPhase : MajorantPhaseChoice` using `majorant_phase_estimate_holds`. Introduce `V _ _ θ hθ r y a hl`. Take `⟨e', he1, _, he3, _⟩` from `majorant_orthogonal_component V (r + 1) y a.castSucc`. Take `⟨u, hu1, hu2, hu3, hu4⟩` from `majorant_orthogonal_component V (r + 1) y a.succ`. Establish `hu0 : u ≠ 0`.

Introduce `h`. Apply `hl` to reduce the goal to its premises. Rewrite using `[← hu3, h, norm_zero]`. Take `⟨p1, p2, p3⟩` from `hPhase V θ hθ u (y a.succ) (y '' {b | b ≤ a.castSucc}) hu0 (by`. Introduce and unpack `w ⟨b, hb, rfl⟩`.

Conclude with `hu2 b (lt_of_le_of_lt (show b ≤ a.castSucc from hb) (Fin.castSucc_lt_succ)))`. Use `hu4`. Use `⟨e', _, he1, he3, p1, fun b hb => p2 _ ⟨b, hb, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[p3, hu3]`.
-/
theorem majorant_parameter_choice_holds : SkewVectorChoice := by
  have hPhase : MajorantPhaseChoice := majorant_phase_estimate_holds
  intro V _ _ θ hθ r y a hl
  obtain ⟨e', he1, _, he3, _⟩ := majorant_orthogonal_component V (r + 1) y a.castSucc
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := majorant_orthogonal_component V (r + 1) y a.succ
  have hu0 : u ≠ 0 := by
    intro h; apply hl; rw [← hu3, h, norm_zero]
  obtain ⟨p1, p2, p3⟩ := hPhase V θ hθ u (y a.succ) (y '' {b | b ≤ a.castSucc}) hu0
    (by
      rintro w ⟨b, hb, rfl⟩
      exact hu2 b (lt_of_le_of_lt (show b ≤ a.castSucc from hb) (Fin.castSucc_lt_succ)))
    hu4
  refine ⟨e', _, he1, he3, p1, fun b hb => p2 _ ⟨b, hb, rfl⟩, ?_⟩
  rw [p3, hu3]

noncomputable def tensorBasisCoordinates {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (xi : Module.Basis (Fin n) ℂ V) : (W ⊗[ℂ] V) →ₗ[ℂ] (Fin n → W) :=
  (TensorProduct.piScalarRight ℂ ℂ W (Fin n)).toLinearMap ∘ₗ LinearMap.lTensor W xi.equivFun.toLinearMap

/- English proof (translation)
Introduce `n H hH g hg e v`. Take `⟨hgu, hgi⟩` from `(unitary_group_holds n H hH).2.2 g hg`. Establish `hgg : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hgu`. Establish `hu : ∀ x w : Fin n → ℂ, herm H (g *ᵥ x) w = herm H x (g⁻¹ *ᵥ w)`. Introduce `x w`.

Rewrite using `[← ggHerm_unitary H g hg x (g⁻¹ *ᵥ w), Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [Matrix.toLin'_apply]`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matrix_action_evaluation_holds, matrix_action_evaluation_holds, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hu]`.
-/
theorem matrix_adjoint_action_holds : RankTwoSkewConjugation := by
  intro n H hH g hg e v
  obtain ⟨hgu, hgi⟩ := (unitary_group_holds n H hH).2.2 g hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  have hu : ∀ x w : Fin n → ℂ, herm H (g *ᵥ x) w = herm H x (g⁻¹ *ᵥ w) := by
    intro x w
    rw [← ggHerm_unitary H g hg x (g⁻¹ *ᵥ w), Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matrix_action_evaluation_holds, matrix_action_evaluation_holds, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hu]

noncomputable def hermitianSesquilinearForm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => herm H x y)
    (fun u v w => gk_herm_add_left H u v w) (fun c u w => gk_herm_smul_left H c u w)
    (fun u v w => gk_herm_add_right H u v w) (fun c u w => gk_herm_smul_right H c u w)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma s1c2_hL_apply {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (x y : ι → ℂ) : hermitianSesquilinearForm H x y = herm H x y := rfl

/- English proof (translation)
Simplify using `only [← s1c2_hL_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]`.
-/
lemma s1c2_herm_sum_left {ι σ : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (s : Finset σ) (c : σ → ℂ) (a : σ → ι → ℂ)
    (y : ι → ℂ) : herm H (∑ i ∈ s, c i • a i) y = ∑ i ∈ s, c i * herm H (a i) y := by
  simp only [← s1c2_hL_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

/- English proof (translation)
Simplify using `only [← s1c2_hL_apply, map_sum, map_smulₛₗ, smul_eq_mul]`. Both sides reduce to the same expression.
-/
lemma s1c2_herm_sum_right {ι σ : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (s : Finset σ) (c : σ → ℂ) (a : σ → ι → ℂ)
    (x : ι → ℂ) : herm H x (∑ i ∈ s, c i • a i) = ∑ i ∈ s, star (c i) * herm H x (a i) := by
  simp only [← s1c2_hL_apply, map_sum, map_smulₛₗ, smul_eq_mul]; rfl

/- English proof (translation)
Simplify using `only [← s1c2_hL_apply, map_sub, LinearMap.sub_apply]`.
-/
lemma s1c2_herm_sub_left {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (u v w : ι → ℂ) :
    herm H (u - v) w = herm H u w - herm H v w := by
  simp only [← s1c2_hL_apply, map_sub, LinearMap.sub_apply]

/- English proof (translation)
Rewrite using `[herm, herm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`.
-/
lemma s1c2_herm_conj {ι : Type*} [Fintype ι] (H g : Matrix ι ι ℂ) (v w : ι → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
  rw [herm, herm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

/- English proof (translation)
Rewrite using `[ggHerm_bvec_right]`. Simplify using the standard rewrite rules.
-/
lemma s1c2_herm_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    herm A (Pi.single j 1) (Pi.single i 1) = A i j := by
  rw [ggHerm_bvec_right]; simp

/- English proof (translation)
Establish `: pᴴ * H * p = H`. Apply `Matrix.ext` to reduce the goal to its premises. Introduce `i j`. Rewrite using `[← s1c2_herm_single (pᴴ * H * p) i j, ← s1c2_herm_conj, h, s1c2_herm_single]`. Conclude with `this`.
-/
lemma s1c2_UH_of_isom {ι : Type*} [Fintype ι] [DecidableEq ι] (H p : Matrix ι ι ℂ)
    (h : ∀ x y, herm H (p *ᵥ x) (p *ᵥ y) = herm H x y) : p ∈ UH H := by
  have : pᴴ * H * p = H := by
    apply Matrix.ext
    intro i j
    rw [← s1c2_herm_single (pᴴ * H * p) i j, ← s1c2_herm_conj, h, s1c2_herm_single]
  exact this

section ext
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

noncomputable def gramCoordinateMap (H : Matrix ι ι ℂ) (v : σ → ι → ℂ) : (ι → ℂ) →ₗ[ℂ] (σ → ℂ) :=
  ((Matrix.of fun i j => herm H (v j) (v i))⁻¹).mulVecLin ∘ₗ LinearMap.pi fun j => (hermitianSesquilinearForm H).flip (v j)

end ext

open Formalism.QuantumDeterminants.WeylGroupFacts in
/- English proof (translation)
The claim follows from `Formalism.QuantumDeterminants.GBasic.Hpk_herm k r`.
-/
lemma s1c2_Hh (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r

/- English proof (translation)
Establish `h` using `ggHerm_swap (Hpk k r) (s1c2_Hh k r) z z`. Establish `him : (herm (Hpk k r) z z).im = 0`. Establish `h2` using `congrArg Complex.im h`. Simplify using `only [Complex.star_def, Complex.conj_im] at h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[Tz]`. Simplify using `[him]`.
-/
lemma s1c2_hzz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := ggHerm_swap (Hpk k r) (s1c2_Hh k r) z z
  have him : (herm (Hpk k r) z z).im = 0 := by
    have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  apply Complex.ext
  · simp [Tz]
  · simp [him]

/- English proof (translation)
Rewrite using `[ggBlockA k r z hz b a, Matrix.smul_apply, smul_eq_mul, s1c2_hzz]`. Distinguish the cases in `h : a = Fin.last r ∧ b = Fin.last r`. Take `⟨rfl, rfl⟩` from `h`. Simplify using `[ggLastU]`. Rewrite using `[if_neg h]`.

Establish `: ggLastU r b a = 0`. Unfold `ggLastU`. Rewrite using `[if_neg (fun h' => h ⟨h'.2, h'.1⟩)]`. Rewrite using `[this, mul_zero]`.
-/
lemma s1c2_gram_f (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z a) (fvec k r z b) =
      if a = Fin.last r ∧ b = Fin.last r then -((Tz k r z : ℝ) : ℂ) else 0 := by
  rw [ggBlockA k r z hz b a, Matrix.smul_apply, smul_eq_mul, s1c2_hzz]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · obtain ⟨rfl, rfl⟩ := h; simp [ggLastU]
  · rw [if_neg h]
    have : ggLastU r b a = 0 := by
      unfold ggLastU
      rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
    rw [this, mul_zero]

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[h]`. Conclude with `ha.1 _`. Conclude with `ha.2 _ _ (lt_of_le_of_ne (Fin.le_last b) h)`.
-/
lemma s1c2_upper_last {r : ℕ} (a : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (ha : IsUpperUnitriangular a) (b : Fin (r + 1)) :
    a (Fin.last r) b = if b = Fin.last r then 1 else 0 := by
  split_ifs with h
  · rw [h]; exact ha.1 _
  · exact ha.2 _ _ (lt_of_le_of_ne (Fin.le_last b) h)

/- English proof (translation)
Establish `hdet : B.det = 1` using `gh_det_upper hB.1 hB.2`. Establish `h` using `congrFun (congrFun (Matrix.mul_adjugate B) (Fin.last r)) c`. Rewrite `h` using `[hdet, one_smul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]`. Rewrite `h` using `[hB.1, one_mul]`. Rewrite using `[h, Matrix.one_apply]`.

Distinguish the cases in `hc : c = Fin.last r`. Simplify using `[hc]`. Simplify using `[hc, Ne.symm hc]`. Introduce `d _ hd`. Rewrite using `[s1c2_upper_last B hB, if_neg hd, zero_mul]`.

Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.
-/
lemma s1c2_adj_last {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hB : IsUpperUnitriangular B) (c : Fin (r + 1)) :
    B.adjugate (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  have hdet : B.det = 1 := gh_det_upper hB.1 hB.2
  have h := congrFun (congrFun (Matrix.mul_adjugate B) (Fin.last r)) c
  rw [hdet, one_smul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)] at h
  · rw [hB.1, one_mul] at h
    rw [h, Matrix.one_apply]
    by_cases hc : c = Fin.last r
    · simp [hc]
    · simp [hc, Ne.symm hc]
  · intro d _ hd; rw [s1c2_upper_last B hB, if_neg hd, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'

/- English proof (translation)
Use `set M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => hermitianSesquilinearForm H (y a) (f' b) with hM`. Use `set B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := A'.map star with hB`. Establish `hBu : IsUpperUnitriangular B` using `⟨fun i => by simp [hB, hA'.1], fun i j hij => by simp [hB, hA'.2 i j hij]⟩`. Establish `hM' : (Matrix.of fun a b => hermitianSesquilinearForm H ((fun a => η⁻¹ *ᵥ ∑ e, A e a • y e) a) (f' b)) = Aᵀ * M * B`. Use extensionality with `a b`.

Simplify using `only [Matrix.of_apply, s1c2_hL_apply]`. Rewrite using `[← ggHerm_unitary H η hη, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv η hηu, Matrix.one_mulVec, hf, s1c2_herm_sum_left]`. Simplify using `only [s1c2_herm_sum_right, Matrix.mul_apply, Matrix.transpose_apply, hM, hB, Matrix.of_apply, Matrix.map_apply, s1c2_hL_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring` and prove the remaining obligations.

Establish `hAt : (Aᵀ).det = 1` using `by rw [Matrix.det_transpose]; exact gh_det_upper hA.1 hA.2`. Establish `hadj : (Aᵀ * M * B).adjugate * Aᵀ = B.adjugate * M.adjugate`. Rewrite using `[Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.adjugate_mul, hAt, one_smul, Matrix.mul_one]`. Establish `hrow : ∀ e, ∑ a, (Aᵀ * M * B).adjugate (Fin.last r) a * A e a = M.adjugate (Fin.last r) e`. Introduce `e`.

Establish `h1` using `congrFun (congrFun hadj (Fin.last r)) e`. Establish `h2 : ∑ j, B.adjugate (Fin.last r) j * M.adjugate j e = M.adjugate (Fin.last r) e`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[s1c2_adj_last B hBu, if_pos rfl, one_mul]`. Introduce `d _ hd`.

Rewrite using `[s1c2_adj_last B hBu, if_neg hd, zero_mul]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.mul_apply, h2]`. Conclude with `h1`.

Unfold `formalDeterminantVector`. Rewrite using `[hM', ← hM]`. Simplify using `only [← Matrix.mulVec_smul, ← Matrix.mulVec_sum]`. Use `congr 1`. Simplify using `only [Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, hrow]`.
-/
lemma transform_upper_unitriangular_change {ι : Type} [Fintype ι] [DecidableEq ι] (H η : Matrix ι ι ℂ) (hη : η ∈ UH H)
    (hηu : IsUnit η.det) {r : ℕ} (y f' : Fin (r + 1) → ι → ℂ) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hA : IsUpperUnitriangular A) (hA' : IsUpperUnitriangular A') (hf : ∀ b, η *ᵥ f' b = ∑ c, A' c b • f' c) :
    formalDeterminantVector (hermitianSesquilinearForm H) (fun a => η⁻¹ *ᵥ ∑ e, A e a • y e) f' = η⁻¹ *ᵥ formalDeterminantVector (hermitianSesquilinearForm H) y f' := by
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => hermitianSesquilinearForm H (y a) (f' b) with hM
  set B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := A'.map star with hB
  have hBu : IsUpperUnitriangular B :=
    ⟨fun i => by simp [hB, hA'.1], fun i j hij => by simp [hB, hA'.2 i j hij]⟩
  have hM' : (Matrix.of fun a b => hermitianSesquilinearForm H ((fun a => η⁻¹ *ᵥ ∑ e, A e a • y e) a) (f' b)) = Aᵀ * M * B := by
    ext a b
    simp only [Matrix.of_apply, s1c2_hL_apply]
    rw [← ggHerm_unitary H η hη, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv η hηu, Matrix.one_mulVec, hf,
      s1c2_herm_sum_left]
    simp only [s1c2_herm_sum_right, Matrix.mul_apply, Matrix.transpose_apply, hM, hB, Matrix.of_apply,
      Matrix.map_apply, s1c2_hL_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring
  have hAt : (Aᵀ).det = 1 := by rw [Matrix.det_transpose]; exact gh_det_upper hA.1 hA.2
  have hadj : (Aᵀ * M * B).adjugate * Aᵀ = B.adjugate * M.adjugate := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.adjugate_mul, hAt, one_smul, Matrix.mul_one]
  have hrow : ∀ e, ∑ a, (Aᵀ * M * B).adjugate (Fin.last r) a * A e a = M.adjugate (Fin.last r) e := by
    intro e
    have h1 := congrFun (congrFun hadj (Fin.last r)) e
    have h2 : ∑ j, B.adjugate (Fin.last r) j * M.adjugate j e = M.adjugate (Fin.last r) e := by
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [s1c2_adj_last B hBu, if_pos rfl, one_mul]
      · intro d _ hd; rw [s1c2_adj_last B hBu, if_neg hd, zero_mul]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    rw [Matrix.mul_apply, Matrix.mul_apply, h2] at h1
    exact h1
  unfold formalDeterminantVector
  rw [hM', ← hM]
  simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_sum]
  congr 1
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_smul, hrow]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma s1c2_N3xM_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    formalDeterminantVectorOnGroup k r z z' g = formalDeterminantVector (hermitianSesquilinearForm (Hpk k r)) (fun a => g⁻¹ *ᵥ fvec k r z a) (fvec k r z') := rfl

/- English proof (translation)
Take `⟨U, h1, h2, h3⟩` from `S_F hz hs`. Conclude with `⟨U, ⟨h2, h1⟩, (gj_cols _ _ _).1 h3⟩`.
-/
lemma s1c2_S_cols (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUpperUnitriangular U ∧ ∀ b, s *ᵥ fvec k r z b = ∑ e, U e b • fvec k r z e := by
  obtain ⟨U, h1, h2, h3⟩ := S_F hz hs
  exact ⟨U, ⟨h2, h1⟩, (gj_cols _ _ _).1 h3⟩

open Formalism.QuantumDeterminants.WeylGroupFacts in
/- English proof (translation)
Take `⟨A, hA, hAf⟩` from `s1c2_S_cols k r z hz _ ((symmetric_group_holds k r z hz).2.2 s hs)`. Take `⟨A', hA', hAf'⟩` from `s1c2_S_cols k r z' hz' _ hs'`. Establish `hsU : s' ∈ UH (Hpk k r)` using `Sset_UH hs'`. Rewrite using `[s1c2_N3xM_eq, s1c2_N3xM_eq, ← transform_upper_unitriangular_change (Hpk k r) s' hsU (isUnit_of_uh hsU) _ _ A A' hA hA' hAf']`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAf, Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul]`.
-/
lemma s1c2_N3xM_S (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (g s s' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) (hs' : s' ∈ Sset k r z') :
    formalDeterminantVectorOnGroup k r z z' (s * g * s') = s'⁻¹ *ᵥ formalDeterminantVectorOnGroup k r z z' g := by
  obtain ⟨A, hA, hAf⟩ := s1c2_S_cols k r z hz _ ((symmetric_group_holds k r z hz).2.2 s hs)
  obtain ⟨A', hA', hAf'⟩ := s1c2_S_cols k r z' hz' _ hs'
  have hsU : s' ∈ UH (Hpk k r) := Sset_UH hs'
  rw [s1c2_N3xM_eq, s1c2_N3xM_eq,
    ← transform_upper_unitriangular_change (Hpk k r) s' hsU (isUnit_of_uh hsU) _ _ A A' hA hA' hAf']
  congr 1
  funext a
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAf,
    Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]

def reflectFlagCoordinates (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if r ≤ i.val ∧ i.val ≤ r + k then x i else 0

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [N3om, reflectFlagCoordinates, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[hz' i (by omega), mul_zero, add_zero]`.
-/
lemma s1c2_om_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z')
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    N3om k r z z' g = reflectFlagCoordinates k r (formalDeterminantVectorOnGroup k r z z' g) +
      (herm (Hpk k r) (formalDeterminantVectorOnGroup k r z z' g) z' / (Tz k r z' : ℂ)) • z' := by
  funext i
  simp only [N3om, reflectFlagCoordinates, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rfl
  · rw [hz' i (by omega), mul_zero, add_zero]

/- English proof (translation)
Rewrite using `[ggHerm_swap _ (s1c2_Hh k r)]`. Establish `: herm (Hpk k r) z' d = 0`. Simplify using `only [herm, dotProduct, ggHpk_mulVec_Wb k r z' hz', Pi.star_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : r ≤ i.val ∧ i.val ≤ r + k`.

Rewrite using `[hd i h.1 h.2, star_zero, zero_mul]`. Rewrite using `[hz' i (by omega), mul_zero, mul_zero]`. Rewrite using `[this, star_zero]`.
-/
lemma s1c2_herm_mid (k r : ℕ) (z' d : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z')
    (hd : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 0) : herm (Hpk k r) d z' = 0 := by
  rw [ggHerm_swap _ (s1c2_Hh k r)]
  have : herm (Hpk k r) z' d = 0 := by
    simp only [herm, dotProduct, ggHpk_mulVec_Wb k r z' hz', Pi.star_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · rw [hd i h.1 h.2, star_zero, zero_mul]
    · rw [hz' i (by omega), mul_zero, mul_zero]
  rw [this, star_zero]

/- English proof (translation)
Use `s1c2_herm_mid k r z' (reflectFlagCoordinates k r x - x) hz' (by` as an intermediate fact. Introduce `i h1 h2`. Simplify using `[reflectFlagCoordinates, h1, h2])`. Rewrite `this` using `[s1c2_herm_sub_left, sub_eq_zero]`. Conclude with `this`.
-/
lemma s1c2_herm_Pm (k r : ℕ) (z' x : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') :
    herm (Hpk k r) (reflectFlagCoordinates k r x) z' = herm (Hpk k r) x z' := by
  have := s1c2_herm_mid k r z' (reflectFlagCoordinates k r x - x) hz' (by
    intro i h1 h2; simp [reflectFlagCoordinates, h1, h2])
  rw [s1c2_herm_sub_left, sub_eq_zero] at this
  exact this

/- English proof (translation)
Unfold `bvec`. Rewrite using `[ggHerm_bvec_right, gn_Hpk_mulVec_lo k r x _ a.isLt]`. Both sides reduce to the same expression.
-/
lemma s1c2_herm_e (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) x (bvec (eI k r a)) = x (esI k r a) := by
  unfold bvec
  rw [ggHerm_bvec_right, gn_Hpk_mulVec_lo k r x _ a.isLt]
  rfl

/- English proof (translation)
Simplify using `[fvec, hb]`.
-/
lemma s1c2_fvec_lt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) (hb : b.val < r) :
    fvec k r z b = bvec (eI k r ⟨b.val, hb⟩) := by
  simp [fvec, hb]

/- English proof (translation)
Establish `hb : 2 * r + k - i.val < r` using `by omega`. Establish `h` using `orthogonality_relation _ (hermitianSesquilinearForm (Hpk k r)) r (fun a => g⁻¹ *ᵥ fvec k r z a) (fvec k r z') ⟨2 * r + k - i.val, by omega⟩`. Rewrite `h` using `[if_neg (by intro h'; have := congrArg Fin.val h'; simp at this; omega), s1c2_hL_apply, ← s1c2_N3xM_eq, s1c2_fvec_lt k r z' _ hb, s1c2_herm_e]`. Establish `e : esI k r ⟨2 * r + k - i.val, hb⟩ = i`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [esI]`. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
lemma s1c2_x_top (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i : Fin (2 * r + k + 1)) (hi : r + k < i.val) :
    formalDeterminantVectorOnGroup k r z z' g i = 0 := by
  have hb : 2 * r + k - i.val < r := by omega
  have h := orthogonality_relation _ (hermitianSesquilinearForm (Hpk k r)) r (fun a => g⁻¹ *ᵥ fvec k r z a) (fvec k r z')
    ⟨2 * r + k - i.val, by omega⟩
  rw [if_neg (by intro h'; have := congrArg Fin.val h'; simp at this; omega), s1c2_hL_apply, ← s1c2_N3xM_eq,
    s1c2_fvec_lt k r z' _ hb, s1c2_herm_e] at h
  have e : esI k r ⟨2 * r + k - i.val, hb⟩ = i := by
    apply Fin.ext; simp only [esI]; omega
  rwa [e] at h

/- English proof (translation)
Introduce `k r z z' hz hz' hT' g hg`. Use `set X := formalDeterminantVectorOnGroup k r z z' g with hX`. Establish `hTc : ((Tz k r z' : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hT'`. Establish `hW : inWb k r (N3om k r z z' g)`. Introduce `i hi`.

Simplify using `only [N3om]`. Rewrite using `[if_neg (by omega)]`. Use `⟨hW, ?_, ?_⟩` and prove the remaining obligations. Introduce `b`. Distinguish the cases in `hb : b.val < r`.

Rewrite using `[s1c2_fvec_lt k r z' b hb, s1c2_herm_e]`. Conclude with `hW _ (Or.inr (by simp only [esI]; omega))`. Establish `hbl : fvec k r z' b = z'` using `by simp [fvec, hb]`. Rewrite using `[hbl, s1c2_om_eq k r z z' hz', gk_herm_add_left, gk_herm_smul_left, s1c2_herm_Pm k r z' _ hz', s1c2_hzz]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Use `⟨fun b => if hb : b.val < r then X (eI k r ⟨b.val, hb⟩) else -(herm (Hpk k r) X z' / (Tz k r z' : ℂ)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hi : i.val < r`.

Rewrite using `[hW i (Or.inl hi), add_zero, Finset.sum_eq_single ⟨i.val, by omega⟩]`. Rewrite using `[fvec_apply_lt z' hz' _ i hi, if_pos rfl, mul_one, dif_pos hi]`. Both sides reduce to the same expression. Introduce `c _ hc`. Rewrite using `[fvec_apply_lt z' hz' _ i hi, if_neg (fun h => hc (Fin.ext h)), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `push Not at hi`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[fvec_apply_ge z' _ i hi, if_pos (by simp), dif_neg (by simp)]`.

Distinguish the cases in `hk : i.val ≤ r + k`. Simplify using `only [N3om]`. Rewrite using `[if_pos ⟨hi, hk⟩]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hW i (Or.inr (by omega)), hz' i (Or.inr (by omega)), mul_zero, add_zero]`.

Conclude with `s1c2_x_top k r z z' g i (by omega)`. Introduce `c _ hc`. Rewrite using `[fvec_apply_ge z' _ i hi, if_neg (fun h => hc (Fin.ext (by simp; omega))), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem omega_decomposition : OrthogonalComplementDecomposition := by
  intro k r z z' hz hz' hT' g hg
  set X := formalDeterminantVectorOnGroup k r z z' g with hX
  have hTc : ((Tz k r z' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT'
  have hW : inWb k r (N3om k r z z' g) := by
    intro i hi
    simp only [N3om]
    rw [if_neg (by omega)]
  refine ⟨hW, ?_, ?_⟩
  · intro b
    by_cases hb : b.val < r
    · rw [s1c2_fvec_lt k r z' b hb, s1c2_herm_e]
      exact hW _ (Or.inr (by simp only [esI]; omega))
    · have hbl : fvec k r z' b = z' := by simp [fvec, hb]
      rw [hbl, s1c2_om_eq k r z z' hz', gk_herm_add_left, gk_herm_smul_left, s1c2_herm_Pm k r z' _ hz', s1c2_hzz]
      field_simp
      ring
  · refine ⟨fun b => if hb : b.val < r then X (eI k r ⟨b.val, hb⟩)
      else -(herm (Hpk k r) X z' / (Tz k r z' : ℂ)), ?_⟩
    funext i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i.val < r
    · rw [hW i (Or.inl hi), add_zero, Finset.sum_eq_single ⟨i.val, by omega⟩]
      · rw [fvec_apply_lt z' hz' _ i hi, if_pos rfl, mul_one, dif_pos hi]; rfl
      · intro c _ hc
        rw [fvec_apply_lt z' hz' _ i hi, if_neg (fun h => hc (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · push Not at hi
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [fvec_apply_ge z' _ i hi, if_pos (by simp), dif_neg (by simp)]
        by_cases hk : i.val ≤ r + k
        · simp only [N3om]
          rw [if_pos ⟨hi, hk⟩]; ring
        · rw [hW i (Or.inr (by omega)), hz' i (Or.inr (by omega)), mul_zero, add_zero]
          exact s1c2_x_top k r z z' g i (by omega)
      · intro c _ hc
        rw [fvec_apply_ge z' _ i hi, if_neg (fun h => hc (Fin.ext (by simp; omega))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Take `⟨h, hh, m, hm, h1⟩` from `(symmetric_group_holds k r z hz).1`. Establish `h1U : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z` using `⟨Formalism.QuantumDeterminants.WeylGroupFacts.uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩`. Conclude with `⟨1, h1U, n, hn, (Matrix.one_mul n).symm⟩`.
-/
lemma s1c2_N_sub_S (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hn : n ∈ Nset k r) : n ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, h1⟩ := (symmetric_group_holds k r z hz).1
  have h1U : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z :=
    ⟨Formalism.QuantumDeterminants.WeylGroupFacts.uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  exact ⟨1, h1U, n, hn, (Matrix.one_mul n).symm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, hh, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one, (Matrix.mul_one h).symm⟩`.
-/
lemma s1c2_UW_sub_S (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one, (Matrix.mul_one h).symm⟩

open Formalism.QuantumDeterminants.WeylGroupFacts in
/- English proof (translation)
Introduce `k r z z' hz hz' g hg n hn n' hn'`. Establish `hx` using `s1c2_N3xM_S k r z z' hz hz' g n n' (s1c2_N_sub_S k r z hz n hn) (s1c2_N_sub_S k r z' hz' n' hn')`. Use `set X := formalDeterminantVectorOnGroup k r z z' g with hX`. Establish `hcol : col k r n'⁻¹` using `((nset_iff _).1 (mem_n_inv hn')).2`. Establish `htop : ∀ i : Fin (2 * r + k + 1), r + k < i.val → X i = 0` using `fun i hi => s1c2_x_top k r z z' g i hi`.

Establish `hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (n'⁻¹ *ᵥ X) i = X i`. Introduce `i hi`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i]`. Distinguish the cases in `hk : i.val ≤ r + k`.

Rewrite using `[hcol i i hk (Or.inr hi), if_pos rfl, one_mul]`. Rewrite using `[htop i (by omega), mul_zero]`. Introduce `j _ hj`. Distinguish the cases in `hk : j.val ≤ r + k`. Rewrite using `[hcol i j hk (Or.inr hi), if_neg (Ne.symm hj), zero_mul]`.

Rewrite using `[htop j (by omega), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hP : reflectFlagCoordinates k r (n'⁻¹ *ᵥ X) = reflectFlagCoordinates k r X`. Use function extensionality and compare the values at `i`.

Simplify using `only [reflectFlagCoordinates]`. Use `split_ifs with h`. Conclude with `hmid i h.1`. Both sides reduce to the same expression. Rewrite using `[s1c2_om_eq k r z z' hz', s1c2_om_eq k r z z' hz', hx, hP, ← s1c2_herm_Pm k r z' (n'⁻¹ *ᵥ X) hz', hP, s1c2_herm_Pm k r z' X hz']`.
-/
theorem dual_vector_unipotent_invariant : DualVectorUnipotentInvariant := by
  intro k r z z' hz hz' g hg n hn n' hn'
  have hx := s1c2_N3xM_S k r z z' hz hz' g n n' (s1c2_N_sub_S k r z hz n hn) (s1c2_N_sub_S k r z' hz' n' hn')
  set X := formalDeterminantVectorOnGroup k r z z' g with hX
  have hcol : col k r n'⁻¹ := ((nset_iff _).1 (mem_n_inv hn')).2
  have htop : ∀ i : Fin (2 * r + k + 1), r + k < i.val → X i = 0 := fun i hi => s1c2_x_top k r z z' g i hi
  have hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (n'⁻¹ *ᵥ X) i = X i := by
    intro i hi
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases hk : i.val ≤ r + k
      · rw [hcol i i hk (Or.inr hi), if_pos rfl, one_mul]
      · rw [htop i (by omega), mul_zero]
    · intro j _ hj
      by_cases hk : j.val ≤ r + k
      · rw [hcol i j hk (Or.inr hi), if_neg (Ne.symm hj), zero_mul]
      · rw [htop j (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP : reflectFlagCoordinates k r (n'⁻¹ *ᵥ X) = reflectFlagCoordinates k r X := by
    funext i
    simp only [reflectFlagCoordinates]
    split_ifs with h
    · exact hmid i h.1
    · rfl
  rw [s1c2_om_eq k r z z' hz', s1c2_om_eq k r z z' hz', hx, hP, ← s1c2_herm_Pm k r z' (n'⁻¹ *ᵥ X) hz', hP,
    s1c2_herm_Pm k r z' X hz']

open Formalism.QuantumDeterminants.WeylGroupFacts in
/- English proof (translation)
Introduce `k r z z' hz hz' g hg h hh h' hh'`. Establish `hx` using `s1c2_N3xM_S k r z z' hz hz' g h h' (s1c2_UW_sub_S k r z h hh) (s1c2_UW_sub_S k r z' h' hh')`. Use `set X := formalDeterminantVectorOnGroup k r z z' g with hX`. Establish `hη : h'⁻¹ ∈ UWset k r z'` using `uw_inv hh'`. Establish `hb : block k r h'⁻¹` using `uw_block hη`.

Establish `hP : reflectFlagCoordinates k r (h'⁻¹ *ᵥ X) = h'⁻¹ *ᵥ reflectFlagCoordinates k r X`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`. Simplify using `only [reflectFlagCoordinates, if_pos hi, Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `split_ifs with hj`. Both sides reduce to the same expression. Rewrite using `[hb.1 i j (by omega), if_neg (by intro e; rw [e] at hi; exact hj hi), zero_mul, mul_zero]`. Simplify using `only [reflectFlagCoordinates, if_neg hi, Matrix.mulVec, dotProduct]`. Use `symm`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hb.2 i j (by omega)]`. Use `split_ifs with e hj`. Rewrite `hi` using `[e]`. Conclude with `absurd hj hi`.

Rewrite using `[mul_zero]`. Rewrite using `[zero_mul]`. Rewrite using `[zero_mul]`. Establish `hinner : herm (Hpk k r) (h'⁻¹ *ᵥ X) z' = herm (Hpk k r) X z'` using `by conv_lhs => rw [← hη.2.2]`. Conclude with `ggHerm_unitary _ _ hη.1 X z'`.

Rewrite using `[s1c2_om_eq k r z z' hz', s1c2_om_eq k r z z' hz', hx, hP, hinner, Matrix.mulVec_add, Matrix.mulVec_smul, hη.2.2]`.
-/
theorem dual_vector_equivariant : DualVectorEquivariant := by
  intro k r z z' hz hz' g hg h hh h' hh'
  have hx := s1c2_N3xM_S k r z z' hz hz' g h h' (s1c2_UW_sub_S k r z h hh) (s1c2_UW_sub_S k r z' h' hh')
  set X := formalDeterminantVectorOnGroup k r z z' g with hX
  have hη : h'⁻¹ ∈ UWset k r z' := uw_inv hh'
  have hb : block k r h'⁻¹ := uw_block hη
  have hP : reflectFlagCoordinates k r (h'⁻¹ *ᵥ X) = h'⁻¹ *ᵥ reflectFlagCoordinates k r X := by
    funext i
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · simp only [reflectFlagCoordinates, if_pos hi, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rfl
      · rw [hb.1 i j (by omega), if_neg (by intro e; rw [e] at hi; exact hj hi), zero_mul, mul_zero]
    · simp only [reflectFlagCoordinates, if_neg hi, Matrix.mulVec, dotProduct]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hb.2 i j (by omega)]
      split_ifs with e hj
      · rw [e] at hi; exact absurd hj hi
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
  have hinner : herm (Hpk k r) (h'⁻¹ *ᵥ X) z' = herm (Hpk k r) X z' := by
    conv_lhs => rw [← hη.2.2]
    exact ggHerm_unitary _ _ hη.1 X z'
  rw [s1c2_om_eq k r z z' hz', s1c2_om_eq k r z z' hz', hx, hP, hinner, Matrix.mulVec_add, Matrix.mulVec_smul,
    hη.2.2]

/- English proof (translation)
Use `(starRingEnd ℂ).map_det A` as an intermediate fact. Rewrite using `[show star A.det = (starRingEnd ℂ) A.det from rfl, this]`. Both sides reduce to the same expression.
-/
lemma s1c2_det_map_star {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (A.map star).det = star A.det := by
  have := (starRingEnd ℂ).map_det A
  rw [show star A.det = (starRingEnd ℂ) A.det from rfl, this]
  rfl

open Formalism.QuantumDeterminants.WeylGroupFacts in
/- English proof (translation)
Introduce `k r z z' hz hz' hT' g hg`. Establish `hgu : IsUnit g.det` using `isUnit_of_uh hg`. Establish `hgi : g⁻¹ ∈ UH (Hpk k r)` using `uh_inv hg`. Take `⟨hW, horth, co, hco⟩` from `omega_decomposition k r z z' hz hz' hT'.ne' g hg`. Establish `hM : (Matrix.of fun a b => hermitianSesquilinearForm (Hpk k r) (g⁻¹ *ᵥ fvec k r z a) (fvec k r z' b)) = (Zhat k r z z' g).map star`.

Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Matrix.map_apply, s1c2_hL_apply, Zhat]`. Rewrite using `[← ggHerm_unitary _ g hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hgu, Matrix.one_mulVec, ggHerm_swap _ (s1c2_Hh k r)]`. Establish `key` using `dual_vector_norm_sq _ (hermitianSesquilinearForm (Hpk k r)) (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ (s1c2_Hh k r) y x) r (fun a => g⁻¹ *ᵥ fvec k r z a) (fvec k r z') (Tz k r z) (Tz k r z') hT'.ne' (fun a b => by simp only [s1c2_hL_apply]; rw [ggHerm_unitary …`. Establish `: (∑ a, (Matrix.of fun a b => hermitianSesquilinearForm (Hpk k r) (g⁻¹ *ᵥ fvec k r z a) (fvec k r z' b)).adjugate (Fin.last r) a • (g⁻¹ *ᵥ fvec k r z a)) = formalDeterminantVectorOnGroup k r z z' g` using `rfl`.

Rewrite using `[this, hco, ← Finset.sum_erase_add _ _ (Finset.mem_univ (Fin.last r))])`. Establish `hfirst : herm (Hpk k r) (N3om k r z z' g) (N3om k r z z' g) = ((Gf k r z z' g / Tz k r z' : ℝ) : ℂ)`. Rewrite `key` using `[s1c2_hL_apply, hM]`. Rewrite using `[key, s1c2_det_map_star]`. Establish `h2 : leadingPrincipalMinor ((Zhat k r z z' g).map star) r = star (leadingPrincipalMinor (Zhat k r z z' g) r)`.

Unfold `leadingPrincipalMinor`. Rewrite using `[← s1c2_det_map_star]`. Both sides reduce to the same expression. Rewrite using `[h2]`. Establish `h3 : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det`.

Unfold `Dmin`. Use `congr 1`. Establish `h4 : Dmin k r z z' g ⟨r, by omega⟩ = leadingPrincipalMinor (Zhat k r z z' g) r` using `minimal_degree_comparison k r z z' g ⟨r, by omega⟩`. Unfold `Gf`. Rewrite using `[h3, h4]`.

Simplify using `only [Complex.star_def, Complex.normSq_conj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨hfirst, fun hT => ?_⟩` and prove the remaining obligations. Rewrite using `[hfirst, Complex.ofReal_re]`.

Conclude with `div_le_div_of_nonneg_right (gauge_le_determinant k r z z' g hT hT'.le) hT'.le`.
-/
theorem dual_vector_norm_on_group : DualVectorNormOnGroup := by
  intro k r z z' hz hz' hT' g hg
  have hgu : IsUnit g.det := isUnit_of_uh hg
  have hgi : g⁻¹ ∈ UH (Hpk k r) := uh_inv hg
  obtain ⟨hW, horth, co, hco⟩ := omega_decomposition k r z z' hz hz' hT'.ne' g hg
  have hM : (Matrix.of fun a b => hermitianSesquilinearForm (Hpk k r) (g⁻¹ *ᵥ fvec k r z a) (fvec k r z' b)) =
      (Zhat k r z z' g).map star := by
    ext a b
    simp only [Matrix.of_apply, Matrix.map_apply, s1c2_hL_apply, Zhat]
    rw [← ggHerm_unitary _ g hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hgu, Matrix.one_mulVec,
      ggHerm_swap _ (s1c2_Hh k r)]
  have key := dual_vector_norm_sq _ (hermitianSesquilinearForm (Hpk k r))
    (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ (s1c2_Hh k r) y x) r
    (fun a => g⁻¹ *ᵥ fvec k r z a) (fvec k r z') (Tz k r z) (Tz k r z') hT'.ne'
    (fun a b => by simp only [s1c2_hL_apply]; rw [ggHerm_unitary _ _ hgi, s1c2_gram_f k r z hz])
    (fun a b => by simp only [s1c2_hL_apply]; rw [s1c2_gram_f k r z' hz'])
    (∑ b ∈ univ.erase (Fin.last r), co b • fvec k r z' b) (N3om k r z z' g) (co (Fin.last r))
    (Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨b, (Finset.mem_erase.mp hb).1, rfl⟩))
    horth
    (by
      have : (∑ a, (Matrix.of fun a b => hermitianSesquilinearForm (Hpk k r) (g⁻¹ *ᵥ fvec k r z a) (fvec k r z' b)).adjugate
          (Fin.last r) a • (g⁻¹ *ᵥ fvec k r z a)) = formalDeterminantVectorOnGroup k r z z' g := rfl
      rw [this, hco, ← Finset.sum_erase_add _ _ (Finset.mem_univ (Fin.last r))])
  have hfirst : herm (Hpk k r) (N3om k r z z' g) (N3om k r z z' g) =
      ((Gf k r z z' g / Tz k r z' : ℝ) : ℂ) := by
    rw [s1c2_hL_apply, hM] at key
    rw [key, s1c2_det_map_star]
    have h2 : leadingPrincipalMinor ((Zhat k r z z' g).map star) r = star (leadingPrincipalMinor (Zhat k r z z' g) r) := by
      unfold leadingPrincipalMinor
      rw [← s1c2_det_map_star]; rfl
    rw [h2]
    have h3 : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := by
      unfold Dmin
      congr 1
    have h4 : Dmin k r z z' g ⟨r, by omega⟩ = leadingPrincipalMinor (Zhat k r z z' g) r := minimal_degree_comparison k r z z' g ⟨r, by omega⟩
    unfold Gf
    rw [h3, h4]
    simp only [Complex.star_def, Complex.normSq_conj]
    push_cast
    ring
  refine ⟨hfirst, fun hT => ?_⟩
  rw [hfirst, Complex.ofReal_re]
  exact div_le_div_of_nonneg_right (gauge_le_determinant k r z z' g hT hT'.le) hT'.le

/- English proof (translation)
Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify `h x` using `only [Matrix.toLin'_apply]`.
-/
lemma matrix_eq_of_forall_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simpa only [Matrix.toLin'_apply] using h x

/- English proof (translation)
Establish `h3' : Y * (Y * Y) = 0` using `by rw [← Matrix.mul_assoc]; exact h3`. Establish `h4 : Y * Y * (Y * Y) = 0` using `by rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]`. Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h3, h3', h4, smul_zero, add_zero]`. Use `module`.
-/
lemma s1c2_exp_add {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (h3 : Y * Y * Y = 0) (s t : ℂ) :
    1 + (s + t) • Y + ((s + t) ^ 2 / 2) • (Y * Y) =
      (1 + s • Y + (s ^ 2 / 2) • (Y * Y)) * (1 + t • Y + (t ^ 2 / 2) • (Y * Y)) := by
  have h3' : Y * (Y * Y) = 0 := by rw [← Matrix.mul_assoc]; exact h3
  have h4 : Y * Y * (Y * Y) = 0 := by rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h3, h3', h4, smul_zero, add_zero]
  module

open Formalism.QuantumDeterminants.WeylGroupFacts in
/- English proof (translation)
Introduce `k r z hz a e v he hv`. Use `set H := Hpk k r with hHdef`. Establish `hH : Hᴴ = H` using `s1c2_Hh k r`. Use `set Y := rankTwoSkewMatrix H e v with hY`. Take `⟨heX, hX, hYf, hY0, -, hYe, hYv⟩` from `lie_algebra_nilpotent_part_holds _ (hermitianSesquilinearForm H) (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ hH y x) r (fvec k r z) (Tz k r z) (fun b c => by simp only [s1c2_hL_apply]; exact s1c2_gram_f k r z hz b c) a e v he (fun b hb => by simp only [s1c2_hL_a …`.

Establish `hYx : ∀ x, Y *ᵥ x = rankTwoSkewOperator (hermitianSesquilinearForm H) e v x` using `fun x => matrix_action_evaluation_holds _ H e v x`. Establish `hYx' : ∀ x, Y *ᵥ x = herm H x v • e - herm H x e • v` using `fun x => matrix_action_evaluation_holds _ H e v x`. Establish `hYe' : Y *ᵥ e = 0` using `by rw [hYx]; exact hYe`. Establish `hYv' : Y *ᵥ v = herm H v v • e` using `by rw [hYx]; exact hYv`. Establish `hYY : ∀ x, Y *ᵥ (Y *ᵥ x) = (-(herm H x e * herm H v v)) • e`.

Introduce `x`. Rewrite using `[hYx' x, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hYe', hYv', smul_zero, zero_sub, smul_smul, neg_smul]`. Establish `h3 : Y * Y * Y = 0`. Apply `matrix_eq_of_forall_mulVec_eq` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYx' x, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hYe', hYv', Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, hYe']`. Simplify using the standard rewrite rules. Establish `hadd : ∀ s t : ℝ, nilpotentExpSquare H e v (s + t) = nilpotentExpSquare H e v s * nilpotentExpSquare H e v t`. Introduce `s t`. Unfold `nilpotentExpSquare`.

Rewrite using `[← hY]`. Use `push_cast`. Conclude with `s1c2_exp_add Y h3 s t`. Establish `hEx : ∀ (t : ℝ) x, nilpotentExpSquare H e v t *ᵥ x = x + (t : ℂ) • (Y *ᵥ x) + ((t : ℂ) ^ 2 / 2) • (Y *ᵥ (Y *ᵥ x))`. Introduce `t x`.

Unfold `nilpotentExpSquare`. Rewrite using `[← hY, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]`. Establish `hskew : ∀ x y, herm H (Y *ᵥ x) y = -herm H x (Y *ᵥ y)`. Introduce `x y`. Use `rank_two_operator_skew_hermitian _ (hermitianSesquilinearForm H) (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ hH y x) e v x y` as an intermediate fact.

Simplify using `only [s1c2_hL_apply] at this`. Rewrite using `[hYx' x, hYx' y]`. Conclude with `eq_neg_of_add_eq_zero_left this`. Establish `hadj : ∀ (t : ℝ) x y, herm H (nilpotentExpSquare H e v t *ᵥ x) y = herm H x (nilpotentExpSquare H e v (-t) *ᵥ y)`. Introduce `t x y`.

Rewrite using `[hEx, hEx]`. Simplify using `only [gk_herm_add_left, gk_herm_add_right, gk_herm_smul_left, gk_herm_smul_right, hskew]`. Establish `c1 : star (((-t : ℝ) : ℂ)) = -(t : ℂ)`. Rewrite using `[Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `c2 : star (((-t : ℝ) : ℂ) ^ 2 / 2) = (t : ℂ) ^ 2 / 2`. Establish `e2 : (((-t : ℝ) : ℂ) ^ 2 / 2) = (((t ^ 2 / 2 : ℝ)) : ℂ)` using `by push_cast; ring`. Rewrite using `[e2, Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c1, c2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hE0 : nilpotentExpSquare H e v 0 = 1` using `by simp [nilpotentExpSquare]`. Establish `hUH : ∀ t : ℝ, nilpotentExpSquare H e v t ∈ UH H`.

Introduce `t`. Apply `s1c2_UH_of_isom` to reduce the goal to its premises. Introduce `x y`. Rewrite using `[hadj, Matrix.mulVec_mulVec, ← hadd, neg_add_cancel, hE0, Matrix.one_mulVec]`. Establish `hsupp : ∀ y ∈ Submodule.span ℂ (fvec k r z '' {b | b < a.castSucc}), ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0`.

Introduce `y hy`. Use `Submodule.span_induction (p := fun y _ => ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `y ⟨b, hb, rfl⟩ i hi`. Establish `hb' : b.val < a.val` using `hb`. Rewrite using `[gj_fvec_apply k r z b (by omega), if_neg (by omega)]`.

Introduce `i _`. Both sides reduce to the same expression. Introduce `y w _ _ h1 h2 i hi`. Rewrite using `[Pi.add_apply, h1 i hi, h2 i hi, add_zero]`. Introduce `c y _ h1 i hi`.

Rewrite using `[Pi.smul_apply, h1 i hi, smul_zero]`. Establish `hei : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → e i = if i.val = a.val then 1 else 0`. Introduce `i hi`. Establish `h1` using `hsupp _ he i hi`. Rewrite `h1` using `[Pi.sub_apply, sub_eq_zero]`.

Rewrite using `[h1, gj_fvec_apply k r z a.castSucc (by simp)]`. Both sides reduce to the same expression. Establish `hEperp : ∀ (t : ℝ) x, (∀ b : Fin r, herm H x (fvec k r z b.castSucc) = 0) → nilpotentExpSquare H e v t *ᵥ x = x + ((t : ℂ) * herm H x v) • e`. Introduce `t x hx`. Establish `h1 : Y *ᵥ x = herm H x v • e` using `by rw [hYx]; exact hX x hx`.

Rewrite using `[hEx, h1, Matrix.mulVec_smul, hYe', smul_zero, smul_zero, add_zero, smul_smul]`. Establish `hEf : ∀ (t : ℝ) b, nilpotentExpSquare H e v t *ᵥ fvec k r z b = fvec k r z b + ((t : ℂ) * herm H (fvec k r z b) v) • e`. Introduce `t b`. Establish `h1 : Y *ᵥ fvec k r z b = herm H (fvec k r z b) v • e` using `by rw [hYx]; exact hYf b`. Rewrite using `[hEx, h1, Matrix.mulVec_smul, hYe', smul_zero, smul_zero, add_zero, smul_smul]`.

Use `⟨h3, hadd, fun t => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[nset_iff]`. Use `⟨hUH t, ?_⟩` and prove the remaining obligations. Introduce `i j hj hij`. Establish `hcolj : nilpotentExpSquare H e v t i j = (nilpotentExpSquare H e v t *ᵥ bvec j) i`.

Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hperp : ∀ b : Fin r, herm H (bvec j) (fvec k r z b.castSucc) = 0`. Introduce `b`. Rewrite using `[s1c2_fvec_lt k r z b.castSucc (by simp), s1c2_herm_e]`. Simplify using `only [bvec, Pi.single_apply, esI]`.

Rewrite using `[if_neg]`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hcolj, hEperp t _ hperp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Establish `hz0 : (t : ℂ) * herm H (bvec j) v * e i = 0`. Distinguish the cases in `hia : i.val ≤ a.val`. Establish `hja : j.val ≤ a.val`. Break down `hij with h | h` into its components or cases.

Use linear arithmetic over natural numbers and integers. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hjr : j.val < r` using `lt_of_le_of_lt hja a.isLt`. Establish `hbj : bvec j = fvec k r z ⟨j.val, by omega⟩`.

Rewrite using `[s1c2_fvec_lt k r z ⟨j.val, by omega⟩ hjr]; rfl`. Rewrite using `[hbj, hv ⟨j.val, by omega⟩ (by rw [Fin.le_def]; simpa using hja), mul_zero, zero_mul]`. Rewrite using `[hei i (by omega), if_neg (by omega), mul_zero]`. Rewrite using `[hz0, add_zero]`. Simplify using `only [bvec, Pi.single_apply]`.

Unfold `ell`. Establish `hterm : ∀ b : Fin r, (if h : b.val + 1 < r then nilpotentExpSquare H e v t (eI k r b) (eI k r ⟨b.val + 1, h⟩) else (nilpotentExpSquare H e v t *ᵥ z) (eI k r b)) = (nilpotentExpSquare H e v t *ᵥ fvec k r z b.succ) (eI k r b)`. Introduce `b`. Use `split_ifs with h`. Rewrite using `[s1c2_fvec_lt k r z b.succ (by simpa using h)]`.

Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `: fvec k r z b.succ = z`. Simplify using `[fvec, h]`. Rewrite using `[this]`. Rewrite using `[Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_eq_single a]`.

Rewrite using `[hEf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hei _ (by simp [eI]), if_pos (by simp [eI]), fvec_apply_lt z hz _ _ (by simp [eI]), if_neg (by simp [eI]), zero_add, mul_one]`. Introduce `b _ hb`. Rewrite using `[hEf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fvec_apply_lt z hz _ _ (by simp [eI]), if_neg (by simp [eI]), zero_add]`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Rewrite using `[hv b.succ (by rw [Fin.le_def]; simpa using h), mul_zero, zero_mul]`.

Establish `h' : a.val < b.val` using `h`. Rewrite using `[hei _ (by simp only [eI]; omega), if_neg (by simp only [eI]; omega), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem nilpotent_model_computation_holds : RankTwoNilpotentGroup := by
  intro k r z hz a e v he hv
  set H := Hpk k r with hHdef
  have hH : Hᴴ = H := s1c2_Hh k r
  set Y := rankTwoSkewMatrix H e v with hY
  obtain ⟨heX, hX, hYf, hY0, -, hYe, hYv⟩ := lie_algebra_nilpotent_part_holds _ (hermitianSesquilinearForm H)
    (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ hH y x) r (fvec k r z) (Tz k r z)
    (fun b c => by simp only [s1c2_hL_apply]; exact s1c2_gram_f k r z hz b c) a e v he
    (fun b hb => by simp only [s1c2_hL_apply]; exact hv b hb)
  have hYx : ∀ x, Y *ᵥ x = rankTwoSkewOperator (hermitianSesquilinearForm H) e v x := fun x => matrix_action_evaluation_holds _ H e v x
  have hYx' : ∀ x, Y *ᵥ x = herm H x v • e - herm H x e • v := fun x => matrix_action_evaluation_holds _ H e v x
  have hYe' : Y *ᵥ e = 0 := by rw [hYx]; exact hYe
  have hYv' : Y *ᵥ v = herm H v v • e := by rw [hYx]; exact hYv
  have hYY : ∀ x, Y *ᵥ (Y *ᵥ x) = (-(herm H x e * herm H v v)) • e := by
    intro x
    rw [hYx' x, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hYe', hYv', smul_zero, zero_sub,
      smul_smul, neg_smul]
  have h3 : Y * Y * Y = 0 := by
    apply matrix_eq_of_forall_mulVec_eq
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYx' x, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hYe', hYv', Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hYe']
    simp
  have hadd : ∀ s t : ℝ, nilpotentExpSquare H e v (s + t) = nilpotentExpSquare H e v s * nilpotentExpSquare H e v t := by
    intro s t
    unfold nilpotentExpSquare
    rw [← hY]
    push_cast
    exact s1c2_exp_add Y h3 s t
  have hEx : ∀ (t : ℝ) x, nilpotentExpSquare H e v t *ᵥ x = x + (t : ℂ) • (Y *ᵥ x) + ((t : ℂ) ^ 2 / 2) • (Y *ᵥ (Y *ᵥ x)) := by
    intro t x
    unfold nilpotentExpSquare
    rw [← hY, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_mulVec]
  have hskew : ∀ x y, herm H (Y *ᵥ x) y = -herm H x (Y *ᵥ y) := by
    intro x y
    have := rank_two_operator_skew_hermitian _ (hermitianSesquilinearForm H)
      (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ hH y x) e v x y
    simp only [s1c2_hL_apply] at this
    rw [hYx' x, hYx' y]
    exact eq_neg_of_add_eq_zero_left this
  have hadj : ∀ (t : ℝ) x y, herm H (nilpotentExpSquare H e v t *ᵥ x) y = herm H x (nilpotentExpSquare H e v (-t) *ᵥ y) := by
    intro t x y
    rw [hEx, hEx]
    simp only [gk_herm_add_left, gk_herm_add_right, gk_herm_smul_left, gk_herm_smul_right, hskew]
    have c1 : star (((-t : ℝ) : ℂ)) = -(t : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    have c2 : star (((-t : ℝ) : ℂ) ^ 2 / 2) = (t : ℂ) ^ 2 / 2 := by
      have e2 : (((-t : ℝ) : ℂ) ^ 2 / 2) = (((t ^ 2 / 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [e2, Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [c1, c2]; ring
  have hE0 : nilpotentExpSquare H e v 0 = 1 := by simp [nilpotentExpSquare]
  have hUH : ∀ t : ℝ, nilpotentExpSquare H e v t ∈ UH H := by
    intro t
    apply s1c2_UH_of_isom
    intro x y
    rw [hadj, Matrix.mulVec_mulVec, ← hadd, neg_add_cancel, hE0, Matrix.one_mulVec]

  have hsupp : ∀ y ∈ Submodule.span ℂ (fvec k r z '' {b | b < a.castSucc}),
      ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0 := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro y ⟨b, hb, rfl⟩ i hi
      have hb' : b.val < a.val := hb
      rw [gj_fvec_apply k r z b (by omega), if_neg (by omega)]
    · intro i _; rfl
    · intro y w _ _ h1 h2 i hi; rw [Pi.add_apply, h1 i hi, h2 i hi, add_zero]
    · intro c y _ h1 i hi; rw [Pi.smul_apply, h1 i hi, smul_zero]
  have hei : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → e i = if i.val = a.val then 1 else 0 := by
    intro i hi
    have h1 := hsupp _ he i hi
    rw [Pi.sub_apply, sub_eq_zero] at h1
    rw [h1, gj_fvec_apply k r z a.castSucc (by simp)]
    rfl

  have hEperp : ∀ (t : ℝ) x, (∀ b : Fin r, herm H x (fvec k r z b.castSucc) = 0) →
      nilpotentExpSquare H e v t *ᵥ x = x + ((t : ℂ) * herm H x v) • e := by
    intro t x hx
    have h1 : Y *ᵥ x = herm H x v • e := by rw [hYx]; exact hX x hx
    rw [hEx, h1, Matrix.mulVec_smul, hYe', smul_zero, smul_zero, add_zero, smul_smul]
  have hEf : ∀ (t : ℝ) b, nilpotentExpSquare H e v t *ᵥ fvec k r z b = fvec k r z b + ((t : ℂ) * herm H (fvec k r z b) v) • e := by
    intro t b
    have h1 : Y *ᵥ fvec k r z b = herm H (fvec k r z b) v • e := by rw [hYx]; exact hYf b
    rw [hEx, h1, Matrix.mulVec_smul, hYe', smul_zero, smul_zero, add_zero, smul_smul]
  refine ⟨h3, hadd, fun t => ⟨?_, ?_⟩⟩
  · rw [nset_iff]
    refine ⟨hUH t, ?_⟩
    intro i j hj hij
    have hcolj : nilpotentExpSquare H e v t i j = (nilpotentExpSquare H e v t *ᵥ bvec j) i := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hperp : ∀ b : Fin r, herm H (bvec j) (fvec k r z b.castSucc) = 0 := by
      intro b
      rw [s1c2_fvec_lt k r z b.castSucc (by simp), s1c2_herm_e]
      simp only [bvec, Pi.single_apply, esI]
      rw [if_neg]
      intro h'
      have := congrArg Fin.val h'
      simp at this
      omega
    rw [hcolj, hEperp t _ hperp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hz0 : (t : ℂ) * herm H (bvec j) v * e i = 0 := by
      by_cases hia : i.val ≤ a.val
      · have hja : j.val ≤ a.val := by
          rcases hij with h | h
          · omega
          · have := a.isLt; omega
        have hjr : j.val < r := lt_of_le_of_lt hja a.isLt
        have hbj : bvec j = fvec k r z ⟨j.val, by omega⟩ := by
          rw [s1c2_fvec_lt k r z ⟨j.val, by omega⟩ hjr]; rfl
        rw [hbj, hv ⟨j.val, by omega⟩ (by rw [Fin.le_def]; simpa using hja), mul_zero, zero_mul]
      · rw [hei i (by omega), if_neg (by omega), mul_zero]
    rw [hz0, add_zero]
    simp only [bvec, Pi.single_apply]
  · unfold ell
    have hterm : ∀ b : Fin r, (if h : b.val + 1 < r then nilpotentExpSquare H e v t (eI k r b) (eI k r ⟨b.val + 1, h⟩)
        else (nilpotentExpSquare H e v t *ᵥ z) (eI k r b)) = (nilpotentExpSquare H e v t *ᵥ fvec k r z b.succ) (eI k r b) := by
      intro b
      split_ifs with h
      · rw [s1c2_fvec_lt k r z b.succ (by simpa using h)]
        simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      · have : fvec k r z b.succ = z := by
          simp [fvec, h]
        rw [this]
    rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_eq_single a]
    · rw [hEf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hei _ (by simp [eI]), if_pos (by simp [eI]),
        fvec_apply_lt z hz _ _ (by simp [eI]), if_neg (by simp [eI]), zero_add, mul_one]
    · intro b _ hb
      rw [hEf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fvec_apply_lt z hz _ _ (by simp [eI]),
        if_neg (by simp [eI]), zero_add]
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hv b.succ (by rw [Fin.le_def]; simpa using h), mul_zero, zero_mul]
      · have h' : a.val < b.val := h
        rw [hei _ (by simp only [eI]; omega), if_neg (by simp only [eI]; omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `k r z hz a e v ka l he hv hl t`. Take `⟨_, _, h3⟩` from `nilpotent_model_computation_holds k r z hz a e v he hv`. Establish `h4` using `(h3 t).2`. Unfold `Formalism.QuantumDeterminants.psi`. Rewrite using `[h4, hl]`.

Establish `h5 : (ka : ℂ) * Formalism.QuantumDeterminants.cStd * ((t : ℂ) * (-Complex.I * (l : ℂ))) = ((-(2 * ka * l * t) : ℝ) : ℂ)`. Unfold `Formalism.QuantumDeterminants.cStd`. Use `push_cast`. Establish `: Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Take the linear combination `(2 * (ka : ℂ) * t * l) * this`.

Rewrite using `[h5, Complex.ofReal_re]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivative_of_psi_holds : CharacterDerivativeNorm := by
  intro k r z hz a e v ka l he hv hl t
  obtain ⟨_, _, h3⟩ := nilpotent_model_computation_holds k r z hz a e v he hv
  have h4 := (h3 t).2
  unfold Formalism.QuantumDeterminants.psi
  rw [h4, hl]
  have h5 : (ka : ℂ) * Formalism.QuantumDeterminants.cStd * ((t : ℂ) * (-Complex.I * (l : ℂ))) = ((-(2 * ka * l * t) : ℝ) : ℂ) := by
    unfold Formalism.QuantumDeterminants.cStd
    push_cast
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (2 * (ka : ℂ) * t * l) * this
  rw [h5, Complex.ofReal_re]
  congr 1
  push_cast
  ring

end Formalism.HermitianLatticeCounting.P
