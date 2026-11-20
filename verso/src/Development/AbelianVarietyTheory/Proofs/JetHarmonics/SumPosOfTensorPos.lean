import Mathlib

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField Matrix
open scoped MatrixOrder

section Evaluations

variable {Y : Type} [AddCommGroup Y] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)

def evalOn (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) : (ι × ι → ℤ) →ₗ[ℤ] ℝ where
  toFun n := ∑ p, (n p : ℝ) * B (b p.1) (b p.2)
  map_add' n n' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k n := by simp [Finset.mul_sum, mul_assoc]

def tensorCoord : Y →ₗ[ℤ] Y →ₗ[ℤ] (ι × ι → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y p => b.repr x p.1 * b.repr y p.2)
    (fun _ _ _ => by funext p; simp [add_mul]) (fun _ _ _ => by funext p; simp [mul_assoc])
    (fun _ _ _ => by funext p; simp [mul_add]) (fun _ _ _ => by funext p; simp [mul_left_comm])

/- English proof (translation)
Use `conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]`. Express the relevant statement in the definitionally equal form `∑ p : ι × ι, ((b.repr x p.1 * b.repr y p.2 : ℤ) : ℝ) * B (b p.1) (b p.2) = _`. Simplify using `only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, Fintype.sum_prod_type, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem evalOn_tensorCoord (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) :
    evalOn b B (tensorCoord b x y) = B x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  change ∑ p : ι × ι, ((b.repr x p.1 * b.repr y p.2 : ℤ) : ℝ) * B (b p.1) (b p.2) = _
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fintype.sum_prod_type, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Evaluations

/- English proof (translation)
Introduce `Y _ _ _ S hS l hl`. Set `b` to `Module.Free.chooseBasis ℤ Y`. Set `A : Submodule ℤ (_ × _ → ℤ)` to `⨅ β : S, LinearMap.ker (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))`. Establish `hA : ∀ n, n ∈ A ↔ ∀ β : S, evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n = 0` using `fun n => by`. Simplify using `[A, Submodule.mem_iInf]`.

Establish `: NoZeroSMulDivisors ℤ ((_ × _ → ℤ) ⧸ A)`. Use `⟨fun {k q} h => ?_⟩` and prove the remaining obligations. Take `⟨n, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Distinguish the cases in `hk : k = 0`. Conclude with `Or.inl hk`.

Use `right`. Rewrite `h` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hA]`. Rewrite using `[Submodule.Quotient.mk_eq_zero, hA]`. Introduce `β`. Establish `h1` using `h β`.

Rewrite `h1` using `[map_zsmul, zsmul_eq_mul]`. Conclude with `(mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hk)`. Establish `: Module.Free ℤ ((_ × _ → ℤ) ⧸ A)` using `Module.free_of_finite_type_torsion_free'`. Set `eb` to `Module.Free.chooseBasis ℤ ((_ × _ → ℤ) ⧸ A)`. Set `γ : Module.Free.ChooseBasisIndex ℤ ((_ × _ → ℤ) ⧸ A) → Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ` to `fun k => (tensorCoord b).compr₂ ((Int.castAddHom ℝ).toIntLinearMap ∘ₗ eb.coord k ∘ₗ A.mkQ)`.

Establish `hγ : ∀ k x y, γ k x y = (eb.repr (Submodule.Quotient.mk (tensorCoord b x y)) k : ℤ)` using `fun _ _ _ => rfl`. Establish `hγS : ∀ k, γ k ∈ S` using `fun k => hS _ fun x y x' y' h => by`. Establish `e : Submodule.Quotient.mk (p` using `A) (tensorCoord b x y) = Submodule.Quotient.mk (tensorCoord b x' y') := (Submodule.Quotient.eq A).2 ((hA _).2 fun β => by`. Rewrite using `[map_sub, evalOn_tensorCoord, evalOn_tensorCoord, h β β.2, sub_self])`. Rewrite using `[hγ, hγ, e]`.

Use `choose z hz using fun k => hl ⟨γ k, hγS k⟩ fun x y => ⟨_, hγ k x y⟩`. Take `⟨n, hn⟩` from `Submodule.Quotient.mk_surjective A (∑ k, z k • eb k)`. Set `e` to `(Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y)).symm`. Use `⟨_, fun t => n (e t) • b (e t).1, fun t => b (e t).2, fun β => ?_⟩` and prove the remaining obligations. Establish `hR : ∑ t, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n (e t) • b (e t).1) (b (e t).2) = evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n`.

Rewrite using `[e.sum_comp (fun p => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n p • b p.1) (b p.2))]`. Simplify using `[evalOn, zsmul_eq_mul]`. Rewrite using `[hR]`. Set `ψ` to `A.liftQ (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) (iInf_le _ β)`. Establish `hψ : ∀ m, ψ (Submodule.Quotient.mk m) = evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) m` using `fun m => Submodule.liftQ_apply _ _ _`.

Establish `hβ : β = ∑ k, ψ (eb k) • (⟨γ k, hγS k⟩ : S)`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext₂` to reduce the goal to its premises. Introduce `x y`. Rewrite using `[Submodule.coe_sum, LinearMap.sum_apply, LinearMap.sum_apply]`.

Simplify using `only [Submodule.coe_smul, LinearMap.smul_apply, hγ, smul_eq_mul]`. Rewrite using `[← evalOn_tensorCoord b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y, ← hψ]`. Use `conv_lhs => rw [← eb.sum_repr (Submodule.Quotient.mk (tensorCoord b x y))]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, zsmul_eq_mul, mul_comm]`. Rewrite using `[congrArg l hβ, map_sum, ← hψ, hn, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hz, smul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]`.
-/
theorem exists_eq_sum_eval : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (S : Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)), (∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ a b c d : Y, (∀ β ∈ S, β a b = β c d) → γ a b = γ c d) → γ ∈ S) → ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) → ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i) := by
  intro Y _ _ _ S hS l hl
  classical
  let b := Module.Free.chooseBasis ℤ Y
  let A : Submodule ℤ (_ × _ → ℤ) := ⨅ β : S, LinearMap.ker (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))
  have hA : ∀ n, n ∈ A ↔ ∀ β : S, evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n = 0 := fun n => by
    simp [A, Submodule.mem_iInf]
  have : NoZeroSMulDivisors ℤ ((_ × _ → ℤ) ⧸ A) := by
    refine ⟨fun {k q} h => ?_⟩
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hk : k = 0
    · exact Or.inl hk
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hA] at h
    rw [Submodule.Quotient.mk_eq_zero, hA]
    intro β
    have h1 := h β
    rw [map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hk)
  have : Module.Free ℤ ((_ × _ → ℤ) ⧸ A) := Module.free_of_finite_type_torsion_free'
  let eb := Module.Free.chooseBasis ℤ ((_ × _ → ℤ) ⧸ A)
  let γ : Module.Free.ChooseBasisIndex ℤ ((_ × _ → ℤ) ⧸ A) → Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := fun k =>
    (tensorCoord b).compr₂ ((Int.castAddHom ℝ).toIntLinearMap ∘ₗ eb.coord k ∘ₗ A.mkQ)
  have hγ : ∀ k x y, γ k x y = (eb.repr (Submodule.Quotient.mk (tensorCoord b x y)) k : ℤ) :=
    fun _ _ _ => rfl
  have hγS : ∀ k, γ k ∈ S := fun k => hS _ fun x y x' y' h => by
    have e : Submodule.Quotient.mk (p := A) (tensorCoord b x y) =
        Submodule.Quotient.mk (tensorCoord b x' y') := (Submodule.Quotient.eq A).2 ((hA _).2 fun β => by
      rw [map_sub, evalOn_tensorCoord, evalOn_tensorCoord, h β β.2, sub_self])
    rw [hγ, hγ, e]
  choose z hz using fun k => hl ⟨γ k, hγS k⟩ fun x y => ⟨_, hγ k x y⟩
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective A (∑ k, z k • eb k)
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y)).symm
  refine ⟨_, fun t => n (e t) • b (e t).1, fun t => b (e t).2, fun β => ?_⟩
  have hR : ∑ t, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n (e t) • b (e t).1) (b (e t).2) =
      evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n := by
    rw [e.sum_comp (fun p => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n p • b p.1) (b p.2))]
    simp [evalOn, zsmul_eq_mul]
  rw [hR]
  let ψ := A.liftQ (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) (iInf_le _ β)
  have hψ : ∀ m, ψ (Submodule.Quotient.mk m) = evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) m := fun m =>
    Submodule.liftQ_apply _ _ _
  have hβ : β = ∑ k, ψ (eb k) • (⟨γ k, hγS k⟩ : S) := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro x y
    rw [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [Submodule.coe_smul, LinearMap.smul_apply, hγ, smul_eq_mul]
    rw [← evalOn_tensorCoord b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y, ← hψ]
    conv_lhs => rw [← eb.sum_repr (Submodule.Quotient.mk (tensorCoord b x y))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  rw [congrArg l hβ, map_sum, ← hψ, hn, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hz, smul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]

/- English proof (translation)
Establish `hq : ∀ x : ι → ℚ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ))`. Introduce `x`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x`. Use `choose y hy using hd`. Establish `hd0 : ((d : ℤ) : ℝ) ≠ 0` using `by exact_mod_cast nonZeroDivisors.coe_ne_zero d`.

Establish `hxy : (fun i => (y i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (x i : ℝ))`. Use function extensionality and compare the values at `i`. Use `congrArg (fun q : ℚ => (q : ℝ)) (hy i)` as an intermediate fact. Simplify `this` using `[Submonoid.smul_def]`. Establish `h1` using `hp y`.

Rewrite `h1` using `[hxy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]`. Conclude with `nonneg_of_mul_nonneg_right h1 (mul_self_pos.2 hd0)`. Use `posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun x => ?_⟩` and prove the remaining obligations. Establish `hd : DenseRange (Pi.map fun (_ : ι) => (Rat.cast : ℚ → ℝ))` using `DenseRange.piMap fun _ => Rat.denseRange_cast`. Use `hd.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ N *ᵥ x) x ?_ (fun q => ?_)` and prove the remaining obligations.

Conclude with `isClosed_le continuous_const (by fun_prop)`. Conclude with `hq q`.
-/
theorem posSemidef_of_int {ι : Type} [Fintype ι] {N : Matrix ι ι ℝ} (hH : N.IsHermitian)
    (hp : ∀ x : ι → ℤ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ))) : N.PosSemidef := by
  have hq : ∀ x : ι → ℚ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) := by
    intro x
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
    choose y hy using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have hxy : (fun i => (y i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (x i : ℝ)) := by
      funext i
      have := congrArg (fun q : ℚ => (q : ℝ)) (hy i)
      simpa [Submonoid.smul_def] using this
    have h1 := hp y
    rw [hxy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
    exact nonneg_of_mul_nonneg_right h1 (mul_self_pos.2 hd0)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun x => ?_⟩
  have hd : DenseRange (Pi.map fun (_ : ι) => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ N *ᵥ x) x ?_ (fun q => ?_)
  · exact isClosed_le continuous_const (by fun_prop)
  · exact hq q

/- English proof (translation)
Establish `hd : M.det ≠ 0` using `fun h => by`. Take `⟨v, hv, h0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Simplify `hp v hv` using `[h0]`. Establish `h1 : (M.map (Int.cast : ℤ → ℝ)).PosSemidef`. Use `posSemidef_of_int (by ext i j; simp [hs i j]) fun x => ?_` and prove the remaining obligations.

Establish `: (fun i => (x i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (x i : ℝ)) = ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ)` using `by simp [dotProduct, mulVec]`. Rewrite using `[this]`. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Conclude with `(hp x hx).le` after adjusting the coercions.

Use `⟨hd, h1.posDef_iff_det_ne_zero.2 ?_⟩` and prove the remaining obligations. Rewrite using `[← Int.cast_det]`. Conclude with `hd` after adjusting the coercions.
-/
theorem posDef_of_int {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) :
    M.det ≠ 0 ∧ (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hd : M.det ≠ 0 := fun h => by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [h0] using hp v hv
  have h1 : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    refine posSemidef_of_int (by ext i j; simp [hs i j]) fun x => ?_
    have : (fun i => (x i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (x i : ℝ)) =
        ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ) := by simp [dotProduct, mulVec]
    rw [this]
    by_cases hx : x = 0
    · simp [hx]
    · exact_mod_cast (hp x hx).le
  refine ⟨hd, h1.posDef_iff_det_ne_zero.2 ?_⟩
  rw [← Int.cast_det]
  exact_mod_cast hd

/- English proof (translation)
Introduce `Y _ _ _ ι _ a c hs hp γ hγ h0 hne`. Set `b` to `Module.finBasis ℤ Y`. Set `M : Matrix _ _ ℤ` to `Matrix.of fun p q => ∑ i, b.coord p (a i) * b.coord q (c i)`. Establish `hM` using `(posDef_of_int M (fun p q => hs _ _) fun x hx => by`. Use `hp (∑ p, x p • b.coord p) fun h => hx (funext fun q => by` as an intermediate fact.

Simplify `LinearMap.congr_fun h (b q))` using `[Finsupp.single_apply]`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [dotProduct, mulVec, M, Matrix.of_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset ι))]`. Use `Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use the proof step `ring).2`. Set `G : Matrix _ _ ℝ` to `Matrix.of fun p q => γ (b p) (b q)`. Establish `hG : G.PosSemidef` using `posSemidef_of_int (by ext p q; simp [G, hγ (b p) (b q)]) fun x => by`.

Use `h0 (∑ p, x p • b p) using 1` and compare the differences between its conclusion and the goal. Simplify using `only [dotProduct, mulVec, G, Matrix.of_apply, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hγ (b p) (b q)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `htr : ∑ i, γ (a i) (c i) = (M.map (Int.cast : ℤ → ℝ) * G).trace`. Simplify using `only [← evalOn_tensorCoord b γ]`. Express the relevant statement in the definitionally equal form `∑ i, ∑ p : _ × _, ((b.repr (a i) p.1 * b.repr (c i) p.2 : ℤ) : ℝ) * γ (b p.1) (b p.2) = _`. Rewrite using `[Finset.sum_comm, Fintype.sum_prod_type]`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, M, G, Matrix.of_apply, Int.cast_sum, Finset.sum_mul, Module.Basis.coord_apply]`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hγ (b p) (b q)]`. Take `⟨C, hC⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg`. Establish `hCd : IsUnit C.det`. Use `Ne.isUnit fun h => hM.det_pos.ne' ?_` and prove the remaining obligations.

Rewrite using `[hC, det_mul, h, mul_zero]`. Establish `h1` using `hG.mul_mul_conjTranspose_same C`. Establish `h2 : (C * G * Cᴴ).trace = ∑ i, γ (a i) (c i)`. Rewrite using `[htr, hC, trace_mul_cycle, star_eq_conjTranspose]`. Rewrite using `[← h2]`.

Use `lt_of_le_of_ne h1.trace_nonneg fun h => hne ?_` and prove the remaining obligations. Establish `h3` using `h1.trace_eq_zero_iff.1 h.symm`. Establish `hu : IsUnit C` using `(Matrix.isUnit_iff_isUnit_det C).2 hCd`. Establish `h4 : G = 0`. Rewrite `h3` using `[← star_eq_conjTranspose, hu.star.mul_left_eq_zero, hu.mul_right_eq_zero]`. Then use the resulting hypothesis.

Conclude with `b.ext fun p => b.ext fun q => congrFun (congrFun h4 p) q`.
-/
theorem sum_pos_of_tensor_pos : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (ι : Type) [Fintype ι] (a c : ι → Y), (∀ f g : Y →ₗ[ℤ] ℤ, ∑ i, f (a i) * g (c i) = ∑ i, g (a i) * f (c i)) → (∀ f : Y →ₗ[ℤ] ℤ, f ≠ 0 → 0 < ∑ i, f (a i) * f (c i)) → ∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ x y, γ x y = γ y x) → (∀ x, 0 ≤ γ x x) → γ ≠ 0 → 0 < ∑ i, γ (a i) (c i) := by
  intro Y _ _ _ ι _ a c hs hp γ hγ h0 hne
  classical
  let b := Module.finBasis ℤ Y
  let M : Matrix _ _ ℤ := Matrix.of fun p q => ∑ i, b.coord p (a i) * b.coord q (c i)
  have hM := (posDef_of_int M (fun p q => hs _ _) fun x hx => by
    have := hp (∑ p, x p • b.coord p) fun h => hx (funext fun q => by
      simpa [Finsupp.single_apply] using LinearMap.congr_fun h (b q))
    convert this using 1
    simp only [dotProduct, mulVec, M, Matrix.of_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    ring).2
  let G : Matrix _ _ ℝ := Matrix.of fun p q => γ (b p) (b q)
  have hG : G.PosSemidef := posSemidef_of_int (by ext p q; simp [G, hγ (b p) (b q)]) fun x => by
    convert h0 (∑ p, x p • b p) using 1
    simp only [dotProduct, mulVec, G, Matrix.of_apply, map_sum, map_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]; ring
  have htr : ∑ i, γ (a i) (c i) = (M.map (Int.cast : ℤ → ℝ) * G).trace := by
    simp only [← evalOn_tensorCoord b γ]
    change ∑ i, ∑ p : _ × _, ((b.repr (a i) p.1 * b.repr (c i) p.2 : ℤ) : ℝ) * γ (b p.1) (b p.2) = _
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, M, G, Matrix.of_apply,
      Int.cast_sum, Finset.sum_mul, Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  have hCd : IsUnit C.det := by
    refine Ne.isUnit fun h => hM.det_pos.ne' ?_
    rw [hC, det_mul, h, mul_zero]
  have h1 := hG.mul_mul_conjTranspose_same C
  have h2 : (C * G * Cᴴ).trace = ∑ i, γ (a i) (c i) := by
    rw [htr, hC, trace_mul_cycle, star_eq_conjTranspose]
  rw [← h2]
  refine lt_of_le_of_ne h1.trace_nonneg fun h => hne ?_
  have h3 := h1.trace_eq_zero_iff.1 h.symm
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 hCd
  have h4 : G = 0 := by
    rwa [← star_eq_conjTranspose, hu.star.mul_left_eq_zero, hu.mul_right_eq_zero] at h3
  exact b.ext fun p => b.ext fun q => congrFun (congrFun h4 p) q

/- English proof (translation)
Assume the negation of the conclusion as `hu`. Take `⟨r, hr, α, hα⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) u).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hu)`. Establish `h1` using `h α`. Rewrite `h1` using `[mul_comm, ← hα, Algebra.trace_algebraMap, nsmul_eq_mul]`. Establish `hd : 0 < Module.finrank ℤ (𝓞 E)` using `Module.finrank_pos`.

Conclude with `mul_ne_zero (by exact_mod_cast hd.ne') hr h1`.
-/
theorem eq_zero_of_trace_mul (E : Type) [Field E] [NumberField E] {u : 𝓞 E}
    (h : ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * u) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) u).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hu)
  have h1 := h α
  rw [mul_comm, ← hα, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have hd : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  exact mul_ne_zero (by exact_mod_cast hd.ne') hr h1

/- English proof (translation)
Introduce `E _ _`. Set `ω` to `RingOfIntegers.basis E`. Set `d` to `(integralBasis E).traceDual`. Establish `: Algebra.IsAlgebraic ℤ E` using `(IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance`. Take `⟨k, hk, hint⟩` from `Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image d)`.

Set `θ : _ → 𝓞 E` to `fun s => k • (⟨k • d s, hint _ (by simp)⟩ : 𝓞 E)`. Establish `hN : (((k * k).toNat : ℕ) : ℤ) = k * k` using `Int.toNat_of_nonneg (mul_self_nonneg k)`. Establish `hθ : ∀ s t, Algebra.trace ℤ (𝓞 E) (ω t * θ s) = if t = s then k * k else 0`. Introduce `s t`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises.

Rewrite using `[Algebra.coe_trace_int]`. Establish `: ((ω t * θ s : 𝓞 E) : E) = k • k • (d s * integralBasis E t)`. Express the relevant statement in the definitionally equal form `(ω t : E) * (k • k • d s) = _`. Rewrite using `[integralBasis_apply, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, map_zsmul, map_zsmul, Module.Basis.trace_traceDual_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h3 : ∀ (g : 𝓞 E →ₗ[ℤ] ℤ) (α : 𝓞 E), Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = k * k * g α`. Introduce `g α`. Establish `: (Algebra.trace ℤ (𝓞 E)) ∘ₗ LinearMap.mulRight ℤ (∑ s, g (ω s) • θ s) = (k * k) • g` using `ω.ext fun t => by`.

Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hθ, LinearMap.smul_apply, smul_eq_mul]`. Simplify using `[mul_comm]`. Conclude with `LinearMap.congr_fun this α`. Use `⟨(k * k).toNat, _, inferInstance, ω, θ, ?_, ?_, fun g α => by rw [hN, h3]⟩` and prove the remaining obligations. Use `mul_self_pos.2 hk` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_trace_mul E fun α => ?_` and prove the remaining obligations. Establish `h4 : ∀ s, Algebra.trace ℤ (𝓞 E) (α * (θ s * ω s)) = k * k * ω.repr (α * ω s) s`. Introduce `s`.

Use `h3 (ω.coord s) (α * ω s)` as an intermediate fact. Simplify using `only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Rewrite using `[← this, mul_comm (θ s), mul_assoc]`. Rewrite using `[mul_sub, map_sub, Finset.mul_sum, map_sum, mul_comm α (_ : 𝓞 E), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, hN, Algebra.trace_eq_matrix_trace ω α]`. Simplify using `only [h4, Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Finset.mul_sum, sub_self]`.
-/
theorem exists_traceDual : ∀ (E : Type) [Field E] [NumberField E], ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (ω θ : ι → 𝓞 E), 0 < N ∧ ∑ s, θ s * ω s = (N : 𝓞 E) ∧ ∀ g : 𝓞 E →ₗ[ℤ] ℤ, ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = N * g α := by
  intro E _ _
  classical
  let ω := RingOfIntegers.basis E
  let d := (integralBasis E).traceDual
  have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨k, hk, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image d)
  let θ : _ → 𝓞 E := fun s => k • (⟨k • d s, hint _ (by simp)⟩ : 𝓞 E)
  have hN : (((k * k).toNat : ℕ) : ℤ) = k * k := Int.toNat_of_nonneg (mul_self_nonneg k)
  have hθ : ∀ s t, Algebra.trace ℤ (𝓞 E) (ω t * θ s) = if t = s then k * k else 0 := by
    intro s t
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_trace_int]
    have : ((ω t * θ s : 𝓞 E) : E) = k • k • (d s * integralBasis E t) := by
      change (ω t : E) * (k • k • d s) = _
      rw [integralBasis_apply, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
      ring
    rw [this, map_zsmul, map_zsmul, Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have h3 : ∀ (g : 𝓞 E →ₗ[ℤ] ℤ) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = k * k * g α := by
    intro g α
    have : (Algebra.trace ℤ (𝓞 E)) ∘ₗ LinearMap.mulRight ℤ (∑ s, g (ω s) • θ s) = (k * k) • g :=
      ω.ext fun t => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Finset.mul_sum, mul_smul_comm,
          map_sum, map_smul, hθ, LinearMap.smul_apply, smul_eq_mul]
        simp [mul_comm]
    exact LinearMap.congr_fun this α
  refine ⟨(k * k).toNat, _, inferInstance, ω, θ, ?_, ?_, fun g α => by rw [hN, h3]⟩
  · have := mul_self_pos.2 hk
    omega
  · rw [← sub_eq_zero]
    refine eq_zero_of_trace_mul E fun α => ?_
    have h4 : ∀ s, Algebra.trace ℤ (𝓞 E) (α * (θ s * ω s)) = k * k * ω.repr (α * ω s) s := by
      intro s
      have := h3 (ω.coord s) (α * ω s)
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      rw [← this, mul_comm (θ s), mul_assoc]
    rw [mul_sub, map_sub, Finset.mul_sum, map_sum, mul_comm α (_ : 𝓞 E), ← nsmul_eq_mul, map_nsmul,
      nsmul_eq_mul, hN, Algebra.trace_eq_matrix_trace ω α]
    simp only [h4, Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Finset.mul_sum, sub_self]

end GlobalTheory.PointStepCompare
