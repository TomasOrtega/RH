import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderFaithfulLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.UPel.HT

/- English proof (translation)
Use `letI core : InnerProductSpace.Core ℝ V := { inner := fun x y => g x y conj_inner_symm := fun x y => by simpa using hs y x re_inner_nonneg := fun x => by`. Distinguish the cases in `h : x = 0`. Simplify using `[h]`. Simplify using `using (hp x h).le`. Use `add_left := fun x y z => by simp`.

Use `smul_left := fun x y r => by simp`. Use `definite := fun x hx => by`. Assume the negation of the conclusion as `h`. Conclude with `(hp x h).ne' hx }`. Use `letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)`.

Use `letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore`. Set `b` to `stdOrthonormalBasis ℝ V`. Rewrite using `[LinearMap.trace_eq_sum_inner _ b]`. Establish `key : ∀ i, ⟪b i, (T ∘ₗ T') (b i)⟫_ℝ = g (T' (b i)) (T' (b i))`. Introduce `i`.

Use `show g (b i) (T (T' (b i))) = _`. Rewrite using `[hs, hadj]`. Simplify using `only [key]`. Establish `hnn : ∀ i, 0 ≤ g (T' (b i)) (T' (b i))` using `fun i => by`. Distinguish the cases in `h : T' (b i) = 0`.

Simplify using `[h]`. Conclude with `(hp _ h).le`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, T' (b i) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hT'` to reduce the goal to its premises. Conclude with `b.toBasis.ext (fun i => by simpa using h i)`. Conclude with `Finset.sum_pos' (fun i _ => hnn i) ⟨i, Finset.mem_univ _, hp _ hi⟩`.
-/
theorem trace_comp_pos_of_adjoint {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u)
    (T T' : V →ₗ[ℝ] V) (hadj : ∀ u v, g (T u) v = g u (T' v)) (hT' : T' ≠ 0) :
    0 < LinearMap.trace ℝ V (T ∘ₗ T') := by
  letI core : InnerProductSpace.Core ℝ V :=
    { inner := fun x y => g x y
      conj_inner_symm := fun x y => by simpa using hs y x
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · simpa using (hp x h).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hp x h).ne' hx }
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b]
  have key : ∀ i, ⟪b i, (T ∘ₗ T') (b i)⟫_ℝ = g (T' (b i)) (T' (b i)) := by
    intro i
    show g (b i) (T (T' (b i))) = _
    rw [hs, hadj]
  simp only [key]
  have hnn : ∀ i, 0 ≤ g (T' (b i)) (T' (b i)) := fun i => by
    by_cases h : T' (b i) = 0
    · simp [h]
    · exact (hp _ h).le
  obtain ⟨i, hi⟩ : ∃ i, T' (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hT'
    exact b.toBasis.ext (fun i => by simpa using h i)
  exact Finset.sum_pos' (fun i _ => hnn i) ⟨i, Finset.mem_univ _, hp _ hi⟩

/- English proof (translation)
Introduce `p _ D x hx`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Take `⟨J, hJJ, hJinv, hpos, hcomm, -⟩` from `D.dom`. Set `A : D.O → (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La)` to `fun b => (DistribMulAction.toLinearMap ℤ D.La b).baseChange ℝ`.

Establish `hcomp : A x ∘ₗ A (D.star x).unop = (DistribMulAction.toLinearMap ℤ D.La (x * (D.star x).unop)).baseChange ℝ` using `by clear hcomm hpos hJinv hJJ`. Simplify using `only [A]`. Rewrite using `[← LinearMap.baseChange_comp]`. Use `congr 1`. Use extensionality with `y`.

Use `show x • ((D.star x).unop • y) = (x * (D.star x).unop) • y`. Rewrite using `[mul_smul]`. Establish `hA : ∀ b (r : ℝ) (y : D.La), A b (r ⊗ₜ y) = r ⊗ₜ (b • y)` using `fun _ _ _ => rfl`. Establish `hAJ : ∀ b, J ∘ₗ A b = A b ∘ₗ J` using `fun b => hcomm b (A b) (fun y => rfl)`. Establish `hEF : ∀ y z : D.La, D.EF y z = - D.EF z y`.

Introduce `y z`. Establish `h` using `D.alt (y + z)`. Simplify using `only [map_add, LinearMap.add_apply, D.alt y, D.alt z, zero_add, add_zero] at h`. Use linear arithmetic over natural numbers and integers. Establish `hanti : ∀ u v, D.EF.baseChange ℝ u v = - D.EF.baseChange ℝ v u`.

Introduce `u v`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r y`. Proceed by induction on `v using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul s z`. Rewrite using `[LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hEF y z]`. Simplify using `only [zsmul_eq_mul, Int.cast_neg]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `add v w hv hw`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[hv, hw]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add u w hu hw`.

Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[hu, hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `hadjB : ∀ b u v, D.EF.baseChange ℝ (A b u) v = D.EF.baseChange ℝ u (A (D.star b).unop v)`. Introduce `b u v`.

Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r y`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul s z`. Rewrite using `[hA, hA, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, D.adj]`. Consider the case `add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw]`. Consider the case `add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]`. Establish `hsym : ∀ u v, D.EF.baseChange ℝ (J u) v = D.EF.baseChange ℝ (J v) u`.

Introduce `u v`. Rewrite using `[← hJinv (J v) u, hJJ, map_neg, LinearMap.neg_apply, hanti v (J u), neg_neg]`. Establish `hadjg : ∀ u v, (D.EF.baseChange ℝ ∘ₗ J) (A x u) v = (D.EF.baseChange ℝ ∘ₗ J) u (A (D.star x).unop v)`. Introduce `u v`. Simplify using `only [LinearMap.comp_apply]`.

Rewrite using `[← LinearMap.comp_apply J (A x), hAJ, LinearMap.comp_apply, hadjB]`. Establish `hinj : ∀ y : D.La, (1 : ℝ) ⊗ₜ[ℤ] y = 0 → y = 0`. Introduce `y hy`. Use `(Module.forall_dual_apply_eq_zero_iff ℤ y).1 fun φ => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun t => TensorProduct.rid ℤ ℝ (LinearMap.baseChange ℝ φ t)) hy`.

Simplify using `only [LinearMap.baseChange_tmul, TensorProduct.rid_tmul, map_zero] at h`. Simplify using `using h`. Establish `hT' : A (D.star x).unop ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Establish `hz : ∀ y : D.La, (D.star x).unop • y = 0` using `fun y => hinj _ (by`. Use `LinearMap.congr_fun h0 ((1 : ℝ) ⊗ₜ y)` as an intermediate fact. Rewrite using `[hA, LinearMap.zero_apply] at this)` and apply the resulting hypothesis. Establish `h1` using `GlobalTheory.T.harrisTaylor_order_faithful_lattice p D _ hz`. Rewrite using `[← D.star_star x, h1]`.

Simplify using the standard rewrite rules. Establish `htr` using `trace_comp_pos_of_adjoint (D.EF.baseChange ℝ ∘ₗ J) (fun u v => by simp only [LinearMap.comp_apply]; exact hsym u v) (fun u hu => by simpa only [LinearMap.comp_apply] using hpos u hu) (A x) (A (D.star x).unop) hadjg hT'`. Rewrite `htr` using `[hcomp, LinearMap.trace_baseChange]`. Simplify using `using htr`.
-/
theorem trace_mul_star_pos : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), x ≠ 0 →
    0 < LinearMap.trace ℤ D.La (DistribMulAction.toLinearMap ℤ D.La (x * (D.star x).unop)) := by
  intro p _ D x hx
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨J, hJJ, hJinv, hpos, hcomm, -⟩ := D.dom
  let A : D.O → (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) := fun b =>
    (DistribMulAction.toLinearMap ℤ D.La b).baseChange ℝ
  have hcomp : A x ∘ₗ A (D.star x).unop =
      (DistribMulAction.toLinearMap ℤ D.La (x * (D.star x).unop)).baseChange ℝ := by
    clear hcomm hpos hJinv hJJ
    simp only [A]
    rw [← LinearMap.baseChange_comp]
    congr 1
    ext y
    show x • ((D.star x).unop • y) = (x * (D.star x).unop) • y
    rw [mul_smul]
  have hA : ∀ b (r : ℝ) (y : D.La), A b (r ⊗ₜ y) = r ⊗ₜ (b • y) := fun _ _ _ => rfl
  have hAJ : ∀ b, J ∘ₗ A b = A b ∘ₗ J := fun b => hcomm b (A b) (fun y => rfl)
  have hEF : ∀ y z : D.La, D.EF y z = - D.EF z y := by
    intro y z
    have h := D.alt (y + z)
    simp only [map_add, LinearMap.add_apply, D.alt y, D.alt z, zero_add, add_zero] at h
    omega
  have hanti : ∀ u v, D.EF.baseChange ℝ u v = - D.EF.baseChange ℝ v u := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hEF y z]
        simp only [zsmul_eq_mul, Int.cast_neg]
        ring
      | add v w hv hw =>
        simp only [map_add, LinearMap.add_apply]
        rw [hv, hw]
        ring
    | add u w hu hw =>
      simp only [map_add, LinearMap.add_apply]
      rw [hu, hw]
      ring
  have hadjB : ∀ b u v, D.EF.baseChange ℝ (A b u) v = D.EF.baseChange ℝ u (A (D.star b).unop v) := by
    intro b u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [hA, hA, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, D.adj]
      | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw]
    | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  have hsym : ∀ u v, D.EF.baseChange ℝ (J u) v = D.EF.baseChange ℝ (J v) u := by
    intro u v
    rw [← hJinv (J v) u, hJJ, map_neg, LinearMap.neg_apply, hanti v (J u), neg_neg]
  have hadjg : ∀ u v, (D.EF.baseChange ℝ ∘ₗ J) (A x u) v =
      (D.EF.baseChange ℝ ∘ₗ J) u (A (D.star x).unop v) := by
    intro u v
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.comp_apply J (A x), hAJ, LinearMap.comp_apply, hadjB]
  have hinj : ∀ y : D.La, (1 : ℝ) ⊗ₜ[ℤ] y = 0 → y = 0 := by
    intro y hy
    refine (Module.forall_dual_apply_eq_zero_iff ℤ y).1 fun φ => ?_
    have h := congrArg (fun t => TensorProduct.rid ℤ ℝ (LinearMap.baseChange ℝ φ t)) hy
    simp only [LinearMap.baseChange_tmul, TensorProduct.rid_tmul, map_zero] at h
    simpa using h
  have hT' : A (D.star x).unop ≠ 0 := by
    intro h0
    apply hx
    have hz : ∀ y : D.La, (D.star x).unop • y = 0 := fun y => hinj _ (by
      have := LinearMap.congr_fun h0 ((1 : ℝ) ⊗ₜ y)
      rwa [hA, LinearMap.zero_apply] at this)
    have h1 := GlobalTheory.T.harrisTaylor_order_faithful_lattice p D _ hz
    rw [← D.star_star x, h1]
    simp
  have htr := trace_comp_pos_of_adjoint (D.EF.baseChange ℝ ∘ₗ J)
    (fun u v => by simp only [LinearMap.comp_apply]; exact hsym u v)
    (fun u hu => by simpa only [LinearMap.comp_apply] using hpos u hu)
    (A x) (A (D.star x).unop) hadjg hT'
  rw [hcomp, LinearMap.trace_baseChange] at htr
  simpa using htr

end GlobalTheory.UPel.HT
