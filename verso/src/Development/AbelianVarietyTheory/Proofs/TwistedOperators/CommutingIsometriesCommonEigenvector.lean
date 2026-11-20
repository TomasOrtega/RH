import Mathlib
open scoped InnerProductSpace

namespace GlobalTheory

open Module.End in

/- English proof (translation)
Set `B : ι → Module.End ℂ U` to `fun i => (A i).toLinearMap.restrict (hU i)`. Establish `hBapp : ∀ i (x : U), ((B i x : U) : V) = A i x` using `fun i x => rfl`. Establish `hinner : ∀ i (x y : U), ⟪B i x, B i y⟫_ℂ = ⟪x, y⟫_ℂ`. Introduce `i x y`. Set `L : U →ₗᵢ[ℂ] U` to `{ toLinearMap := B i, norm_map' := fun x => hiso i x }`.

Conclude with `L.inner_map_map x y`. Set `D : ι → Module.End ℂ U` to `fun i => LinearMap.adjoint (B i)`. Establish `hDB : ∀ i, D i * B i = 1`. Introduce `i`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `y`. Rewrite using `[Module.End.mul_apply, LinearMap.adjoint_inner_right, hinner]`. Both sides reduce to the same expression.

Establish `hBD : ∀ i, B i * D i = 1` using `fun i => mul_eq_one_comm.mp (hDB i)`. Set `u : ι → (Module.End ℂ U)ˣ` to `fun i => ⟨B i, D i, hBD i, hDB i⟩`. Establish `hBB : ∀ i l, Commute (B i) (B l)`. Introduce `i l`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hcomm i l x`. Establish `hDBc : ∀ i l, Commute (D i) (B l)` using `fun i l => Commute.units_inv_left (u := u i) (hBB i l)`. Establish `hDD : ∀ i l, Commute (D i) (D l)` using `fun i l => Commute.units_inv_left (u := u i) (hDBc l i).symm`.

Set `T : ι ⊕ ι → Module.End ℂ U` to `Sum.elim (fun i => B i + D i) (fun i => Complex.I • (B i - D i))`. Establish `hTB : ∀ a k, Commute (T a) (B k)`. Introduce and unpack `(i|i) k`. Conclude with `(hBB i k).add_left (hDBc i k)`. Conclude with `((hBB i k).sub_left (hDBc i k)).smul_left _`.

Establish `hTD : ∀ a k, Commute (T a) (D k)`. Introduce and unpack `(i|i) k`. Conclude with `(hDBc k i).symm.add_left (hDD i k)`. Conclude with `((hDBc k i).symm.sub_left (hDD i k)).smul_left _`. Establish `hTT : ∀ a b, Commute (T a) (T b)`.

Introduce `a b`. Break down `b with i|i` into its components or cases. Conclude with `(hTB a i).add_right (hTD a i)`. Conclude with `((hTB a i).sub_right (hTD a i)).smul_right _`. Establish `hTsym : ∀ a, (T a).IsSymmetric`.

Introduce and unpack `(i|i) x y`. Simplify using `only [T, D, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [T, D, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsup` using `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTsym (fun a b _ => hTT a b)`. Establish `key : ∃ χ : ι ⊕ ι → ℂ, ∃ w ∈ ⨅ a, eigenspace (T a) (χ a), ⟪(w : V), x₀⟫_ℂ ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Set `x : U` to `⟨x₀, hx₀⟩`.

Establish `hle : (⨆ χ : ι ⊕ ι → ℂ, ⨅ a, eigenspace (T a) (χ a)) ≤ LinearMap.ker (innerₛₗ ℂ x)`. Use `iSup_le fun χ w hw => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, innerₛₗ_apply_apply, Submodule.coe_inner, ← inner_conj_symm, h χ w hw]`. Simplify using the standard rewrite rules. Rewrite `hle` using `[hsup]`.

Establish `hx : x ∈ LinearMap.ker (innerₛₗ ℂ x)` using `hle Submodule.mem_top`. Rewrite `hx` using `[LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero]`. Conclude with `hne (congrArg Subtype.val hx)`. Take `⟨χ, w, hw, hwx⟩` from `key`. Use `⟨w, w.2, hwx, fun i => ⟨(χ (Sum.inl i) - Complex.I * χ (Sum.inr i)) / 2, ?_⟩⟩` and prove the remaining obligations.

Rewrite `hw` using `[Submodule.mem_iInf]`. Establish `h1 : B i w + D i w = χ (Sum.inl i) • w`. Use `hw (Sum.inl i)` as an intermediate fact. Rewrite `this` using `[mem_eigenspace_iff]`. Simplify `this` using `[T]`.

Establish `h2 : Complex.I • (B i w - D i w) = χ (Sum.inr i) • w`. Use `hw (Sum.inr i)` as an intermediate fact. Rewrite `this` using `[mem_eigenspace_iff]`. Simplify `this` using `[T]`. Establish `h3 : B i w = ((χ (Sum.inl i) - Complex.I * χ (Sum.inr i)) / 2) • w`.

Establish `h2' : (B i w - D i w) = (-Complex.I * χ (Sum.inr i)) • w`. Use `congrArg (fun z : U => (-Complex.I) • z) h2` as an intermediate fact. Simplify using `only [smul_smul] at this`. Rewrite `this` using `[show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]`. Conclude with `this`.

Take the linear combination `(norm := module) (1/2 : ℂ) • h1 + (1/2 : ℂ) • h2'`. Use `congrArg Subtype.val h3` as an intermediate fact. Conclude with `this`.
-/
theorem exists_common_eigenvector_inner_ne_zero_of_commute_isometry
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (U : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ U) {ι : Type} (A : ι → V →L[ℂ] V) (x₀ : V)
    (hx₀ : x₀ ∈ U) (hne : x₀ ≠ 0) (hU : ∀ i, ∀ x ∈ U, A i x ∈ U)
    (hiso : ∀ i x, ‖A i x‖ = ‖x‖) (hcomm : ∀ i l x, A i (A l x) = A l (A i x)) :
    ∃ v ∈ U, ⟪v, x₀⟫_ℂ ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i v = c • v := by
  classical
  let B : ι → Module.End ℂ U := fun i => (A i).toLinearMap.restrict (hU i)
  have hBapp : ∀ i (x : U), ((B i x : U) : V) = A i x := fun i x => rfl
  have hinner : ∀ i (x y : U), ⟪B i x, B i y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro i x y
    let L : U →ₗᵢ[ℂ] U := { toLinearMap := B i, norm_map' := fun x => hiso i x }
    exact L.inner_map_map x y
  let D : ι → Module.End ℂ U := fun i => LinearMap.adjoint (B i)
  have hDB : ∀ i, D i * B i = 1 := by
    intro i
    apply LinearMap.ext; intro x
    apply ext_inner_left ℂ; intro y
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_right, hinner]
    rfl
  have hBD : ∀ i, B i * D i = 1 := fun i => mul_eq_one_comm.mp (hDB i)
  let u : ι → (Module.End ℂ U)ˣ := fun i => ⟨B i, D i, hBD i, hDB i⟩
  have hBB : ∀ i l, Commute (B i) (B l) := by
    intro i l
    apply LinearMap.ext; intro x
    apply Subtype.ext
    exact hcomm i l x
  have hDBc : ∀ i l, Commute (D i) (B l) := fun i l =>
    Commute.units_inv_left (u := u i) (hBB i l)
  have hDD : ∀ i l, Commute (D i) (D l) := fun i l =>
    Commute.units_inv_left (u := u i) (hDBc l i).symm
  let T : ι ⊕ ι → Module.End ℂ U :=
    Sum.elim (fun i => B i + D i) (fun i => Complex.I • (B i - D i))
  have hTB : ∀ a k, Commute (T a) (B k) := by
    rintro (i|i) k
    · exact (hBB i k).add_left (hDBc i k)
    · exact ((hBB i k).sub_left (hDBc i k)).smul_left _
  have hTD : ∀ a k, Commute (T a) (D k) := by
    rintro (i|i) k
    · exact (hDBc k i).symm.add_left (hDD i k)
    · exact ((hDBc k i).symm.sub_left (hDD i k)).smul_left _
  have hTT : ∀ a b, Commute (T a) (T b) := by
    intro a b
    rcases b with i|i
    · exact (hTB a i).add_right (hTD a i)
    · exact ((hTB a i).sub_right (hTD a i)).smul_right _
  have hTsym : ∀ a, (T a).IsSymmetric := by
    rintro (i|i) x y
    · simp only [T, D, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right,
        LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
      ring
    · simp only [T, D, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left,
        inner_smul_right, inner_sub_left, inner_sub_right,
        LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, Complex.conj_I]
      ring
  have hsup := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTsym (fun a b _ => hTT a b)
  have key : ∃ χ : ι ⊕ ι → ℂ, ∃ w ∈ ⨅ a, eigenspace (T a) (χ a), ⟪(w : V), x₀⟫_ℂ ≠ 0 := by
    by_contra h
    push_neg at h
    let x : U := ⟨x₀, hx₀⟩
    have hle : (⨆ χ : ι ⊕ ι → ℂ, ⨅ a, eigenspace (T a) (χ a)) ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      refine iSup_le fun χ w hw => ?_
      rw [LinearMap.mem_ker, innerₛₗ_apply_apply, Submodule.coe_inner, ← inner_conj_symm, h χ w hw]
      simp
    rw [hsup] at hle
    have hx : x ∈ LinearMap.ker (innerₛₗ ℂ x) := hle Submodule.mem_top
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at hx
    exact hne (congrArg Subtype.val hx)
  obtain ⟨χ, w, hw, hwx⟩ := key
  refine ⟨w, w.2, hwx, fun i => ⟨(χ (Sum.inl i) - Complex.I * χ (Sum.inr i)) / 2, ?_⟩⟩
  rw [Submodule.mem_iInf] at hw
  have h1 : B i w + D i w = χ (Sum.inl i) • w := by
    have := hw (Sum.inl i)
    rw [mem_eigenspace_iff] at this
    simpa [T] using this
  have h2 : Complex.I • (B i w - D i w) = χ (Sum.inr i) • w := by
    have := hw (Sum.inr i)
    rw [mem_eigenspace_iff] at this
    simpa [T] using this
  have h3 : B i w = ((χ (Sum.inl i) - Complex.I * χ (Sum.inr i)) / 2) • w := by
    have h2' : (B i w - D i w) = (-Complex.I * χ (Sum.inr i)) • w := by
      have := congrArg (fun z : U => (-Complex.I) • z) h2
      simp only [smul_smul] at this
      rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul] at this
      exact this
    linear_combination (norm := module) (1/2 : ℂ) • h1 + (1/2 : ℂ) • h2'
  have := congrArg Subtype.val h3
  exact this

end GlobalTheory
