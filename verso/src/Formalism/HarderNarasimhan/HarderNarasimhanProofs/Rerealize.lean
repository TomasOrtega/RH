import Formalism.HarderNarasimhan.QuotRealize
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean

open Module NumberField

noncomputable section

namespace Formalism.HN

namespace Rerealization

section Lat

variable {G E F : Type*} [AddCommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/- English proof (translation)
Establish `h0 : ‖β (x - y)‖ = 0` using `by rw [hn, map_sub, h, sub_self, norm_zero]`. Rewrite `h0` using `[norm_eq_zero, map_sub, sub_eq_zero]`. Conclude with `h0`.
-/
theorem eq_of_eq (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) {x y : G}
    (h : α x = α y) : β x = β y := by
  have h0 : ‖β (x - y)‖ = 0 := by rw [hn, map_sub, h, sub_self, norm_zero]
  rw [norm_eq_zero, map_sub, sub_eq_zero] at h0
  exact h0

/- English proof (translation)
Rewrite using `[real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add, ← map_add, hn, hn, hn]`.
-/
theorem inner_eq (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (x y : G) :
    inner ℝ (β x) (β y) = inner ℝ (α x) (α y) := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, ← map_add, hn, hn, hn]

/- English proof (translation)
Use `set P : Matrix ι ι ℝ := (C.toMatrix C').map (Int.cast : ℤ → ℝ) with hP`. Establish `hC' : ∀ i, ((C' i : L) : F) = ∑ k, P k i • ((C k : L) : F)`. Introduce `i`. Establish `e` using `congrArg (fun w : L => (w : F)) (C.sum_repr (C' i))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at e`.

Rewrite using `[← e]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hP, Matrix.map_apply, Module.Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]`. Establish `hG : Matrix.gram ℝ (fun i => ((C' i : L) : F)) = P.transpose * Matrix.gram ℝ (fun i => ((C i : L) : F)) * P`. Use extensionality with `i j`.

Simplify using `only [Matrix.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hC', sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]`. Use `first`. Consider the case `(refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)`. Consider the case `(rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)`. Consider the case `(rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_;`.

Rewrite using `[real_inner_comm]`. Use the proof step `ring)`. Establish `hdet : (C.toMatrix C').det * (C'.toMatrix C).det = 1`. Rewrite using `[← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]`. Establish `hPd : P.det = ((C.toMatrix C').det : ℝ)`.

Rewrite using `[hP]`. Use `first`. Consider the case `exact (Int.cast_det _).symm`. Consider the case `exact ((Int.castRingHom ℝ).map_det _).symm`. Establish `hsq : P.det ^ 2 = 1`.

Rewrite using `[hPd]`. Apply the tactic sequence `rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;> simp [h]`. Rewrite using `[hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, show ∀ a b : ℝ, a * b * a = a ^ 2 * b from fun a b => by ring, hsq, one_mul]`.
-/
private theorem det_gram_basis_eq' {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ F)
    (C C' : Module.Basis ι ℤ L) :
    (Matrix.gram ℝ (fun i => ((C' i : L) : F))).det = (Matrix.gram ℝ (fun i => ((C i : L) : F))).det := by
  set P : Matrix ι ι ℝ := (C.toMatrix C').map (Int.cast : ℤ → ℝ) with hP
  have hC' : ∀ i, ((C' i : L) : F) = ∑ k, P k i • ((C k : L) : F) := by
    intro i
    have e := congrArg (fun w : L => (w : F)) (C.sum_repr (C' i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP, Matrix.map_apply, Module.Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]
  have hG : Matrix.gram ℝ (fun i => ((C' i : L) : F)) =
      P.transpose * Matrix.gram ℝ (fun i => ((C i : L) : F)) * P := by
    ext i j
    simp only [Matrix.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hC', sum_inner,
      inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    first
      | (refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_;
          rw [real_inner_comm]; ring)
  have hdet : (C.toMatrix C').det * (C'.toMatrix C).det = 1 := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  have hPd : P.det = ((C.toMatrix C').det : ℝ) := by
    rw [hP]
    first
      | exact (Int.cast_det _).symm
      | exact ((Int.castRingHom ℝ).map_det _).symm
  have hsq : P.det ^ 2 = 1 := by
    rw [hPd]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;> simp [h]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show ∀ a b : ℝ, a * b * a = a ^ 2 * b from fun a b => by ring, hsq, one_mul]

/- English proof (translation)
Establish `hr : Module.finrank ℤ L1 = Module.finrank ℤ L2` using `τ.finrank_eq`. Unfold `Formalism.F.covol`. Rewrite using `[dif_pos ‹DiscreteTopology L1›, dif_pos ‹DiscreteTopology L2›]`. Use `congr 1`. Set `B : Module.Basis (Fin (Module.finrank ℤ L2)) ℤ L2` to `((Module.finBasis ℤ L1).map τ).reindex (finCongr hr)`.

Establish `h1 : Matrix.gram ℝ (fun i => ((Module.finBasis ℤ L1 i : L1) : E)) = (Matrix.gram ℝ (fun i => ((B i : L2) : F))).submatrix (finCongr hr) (finCongr hr)`. Use extensionality with `i j`. Simplify using `[B, Matrix.gram, hτ]`. Rewrite using `[h1, Matrix.det_submatrix_equiv_self, det_gram_basis_eq' L2 (Module.finBasis ℤ L2) B]`.
-/
private theorem covol_eq_of_inner_preserving_equiv (L1 : Submodule ℤ E) (L2 : Submodule ℤ F) [DiscreteTopology L1]
    [DiscreteTopology L2] (τ : L1 ≃ₗ[ℤ] L2)
    (hτ : ∀ x y : L1, inner ℝ ((τ x : L2) : F) ((τ y : L2) : F) = inner ℝ (x : E) (y : E)) :
    Formalism.F.covol L1 = Formalism.F.covol L2 := by
  have hr : Module.finrank ℤ L1 = Module.finrank ℤ L2 := τ.finrank_eq
  unfold Formalism.F.covol
  rw [dif_pos ‹DiscreteTopology L1›, dif_pos ‹DiscreteTopology L2›]
  congr 1
  let B : Module.Basis (Fin (Module.finrank ℤ L2)) ℤ L2 :=
    ((Module.finBasis ℤ L1).map τ).reindex (finCongr hr)
  have h1 : Matrix.gram ℝ (fun i => ((Module.finBasis ℤ L1 i : L1) : E)) =
      (Matrix.gram ℝ (fun i => ((B i : L2) : F))).submatrix (finCongr hr) (finCongr hr) := by
    ext i j
    simp [B, Matrix.gram, hτ]
  rw [h1, Matrix.det_submatrix_equiv_self, det_gram_basis_eq' L2 (Module.finBasis ℤ L2) B]

/- English proof (translation)
Use `haveI := hα`. Use `haveI := hβ`. Establish `ex : ∀ y : (H.map α).toIntSubmodule, ∃ g ∈ H, α g = (y : E)` using `fun y => AddSubgroup.mem_map.mp y.2`. Set `τf : (H.map α).toIntSubmodule →+ (H.map β).toIntSubmodule` to `{ toFun := fun y => ⟨β (ex y).choose, AddSubgroup.mem_map.mpr ⟨_, (ex y).choose_spec.1, rfl⟩⟩ map_zero' := by`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show β (ex 0).choose = 0`. Rewrite using `[← map_zero β]`. Conclude with `eq_of_eq α β hn (by simp [(ex 0).choose_spec.2])`. Use the proof step `map_add' := fun y z => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show β (ex (y + z)).choose = β (ex y).choose + β (ex z).choose`. Rewrite using `[← map_add]`. Conclude with `eq_of_eq α β hn (by simp [(ex (y + z)).choose_spec.2, (ex y).choose_spec.2, (ex z).choose_spec.2]) }`. Establish `hval : ∀ (y : (H.map α).toIntSubmodule) (g : G), α g = (y : E) → ((τf y : (H.map β).toIntSubmodule) : F) = β g` using `fun y g hg => eq_of_eq α β hn (((ex y).choose_spec.2).trans hg.symm)`. Establish `hnorm : ∀ y, ‖((τf y : (H.map β).toIntSubmodule) : F)‖ = ‖(y : E)‖`.

Introduce `y`. Rewrite using `[hval y _ (ex y).choose_spec.2, hn, (ex y).choose_spec.2]`. Establish `hinj : Function.Injective τf`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`.

Establish `: ‖(y : E)‖ = 0` using `by rw [← hnorm, hy]; simp`. Conclude with `Subtype.ext (norm_eq_zero.mp this)`. Establish `hsurj : Function.Surjective τf`. Introduce and unpack `⟨z, hz⟩`. Take `⟨g, hg, rfl⟩` from `AddSubgroup.mem_map.mp hz`.

Conclude with `⟨⟨α g, AddSubgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩, Subtype.ext (hval _ g rfl)⟩`. Set `τ : (H.map α).toIntSubmodule ≃ₗ[ℤ] (H.map β).toIntSubmodule` to `(AddEquiv.ofBijective τf ⟨hinj, hsurj⟩).toIntLinearEquiv`. Establish `hτ : ∀ x y : (H.map α).toIntSubmodule, inner ℝ ((τ x : (H.map β).toIntSubmodule) : F) ((τ y : (H.map β).toIntSubmodule) : F) = inner ℝ (x : E) (y : E)`. Introduce `x y`. Conclude with `inner_eq ((H.map α).toIntSubmodule.subtype.toAddMonoidHom) (((H.map β).toIntSubmodule.subtype.toAddMonoidHom).comp τf) hnorm x y`.

Conclude with `⟨(covol_eq_of_inner_preserving_equiv _ _ τ hτ).symm, τ.finrank_eq.symm⟩`.
-/
theorem covol_rk_eq (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (H : AddSubgroup G)
    (hα : DiscreteTopology (H.map α).toIntSubmodule)
    (hβ : DiscreteTopology (H.map β).toIntSubmodule) :
    Formalism.F.covol (H.map β).toIntSubmodule = Formalism.F.covol (H.map α).toIntSubmodule ∧
      Formalism.F.rk (H.map β).toIntSubmodule = Formalism.F.rk (H.map α).toIntSubmodule := by
  haveI := hα
  haveI := hβ
  have ex : ∀ y : (H.map α).toIntSubmodule, ∃ g ∈ H, α g = (y : E) := fun y =>
    AddSubgroup.mem_map.mp y.2
  let τf : (H.map α).toIntSubmodule →+ (H.map β).toIntSubmodule :=
    { toFun := fun y => ⟨β (ex y).choose, AddSubgroup.mem_map.mpr ⟨_, (ex y).choose_spec.1, rfl⟩⟩
      map_zero' := by
        apply Subtype.ext
        show β (ex 0).choose = 0
        rw [← map_zero β]
        exact eq_of_eq α β hn (by simp [(ex 0).choose_spec.2])
      map_add' := fun y z => by
        apply Subtype.ext
        show β (ex (y + z)).choose = β (ex y).choose + β (ex z).choose
        rw [← map_add]
        exact eq_of_eq α β hn
          (by simp [(ex (y + z)).choose_spec.2, (ex y).choose_spec.2, (ex z).choose_spec.2]) }
  have hval : ∀ (y : (H.map α).toIntSubmodule) (g : G), α g = (y : E) → ((τf y : (H.map β).toIntSubmodule) : F) = β g := fun y g hg =>
    eq_of_eq α β hn (((ex y).choose_spec.2).trans hg.symm)
  have hnorm : ∀ y, ‖((τf y : (H.map β).toIntSubmodule) : F)‖ = ‖(y : E)‖ := by
    intro y
    rw [hval y _ (ex y).choose_spec.2, hn, (ex y).choose_spec.2]
  have hinj : Function.Injective τf := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have : ‖(y : E)‖ = 0 := by rw [← hnorm, hy]; simp
    exact Subtype.ext (norm_eq_zero.mp this)
  have hsurj : Function.Surjective τf := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.mp hz
    exact ⟨⟨α g, AddSubgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩, Subtype.ext (hval _ g rfl)⟩
  let τ : (H.map α).toIntSubmodule ≃ₗ[ℤ] (H.map β).toIntSubmodule :=
    (AddEquiv.ofBijective τf ⟨hinj, hsurj⟩).toIntLinearEquiv
  have hτ : ∀ x y : (H.map α).toIntSubmodule, inner ℝ ((τ x : (H.map β).toIntSubmodule) : F)
      ((τ y : (H.map β).toIntSubmodule) : F) = inner ℝ (x : E) (y : E) := by
    intro x y
    exact inner_eq ((H.map α).toIntSubmodule.subtype.toAddMonoidHom)
      (((H.map β).toIntSubmodule.subtype.toAddMonoidHom).comp τf) hnorm x y
  exact ⟨(covol_eq_of_inner_preserving_equiv _ _ τ hτ).symm, τ.finrank_eq.symm⟩

end Lat

section Abs

variable {R V E E₂ : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/- English proof (translation)
Use `haveI := h`. Rewrite using `[Formalism.F.deg, neg_neg, Real.exp_log (Formalism.F.covol_pos L)]`.
-/
theorem covol_eq_exp {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E'] (L : Submodule ℤ E') (h : DiscreteTopology L) :
    Formalism.F.covol L = Real.exp (- Formalism.F.deg L) := by
  haveI := h
  rw [Formalism.F.deg, neg_neg, Real.exp_log (Formalism.F.covol_pos L)]

/- English proof (translation)
Take `⟨a1, -, -, -, -, -, -, a8⟩` from `saturation_basic_properties R V E ρ L hL`. Take `⟨b1, -, -, -, -, -, -, b8⟩` from `saturation_basic_properties R V E₂ ρ₂ L hL₂`. Establish `T1 : ∀ N : Submodule R V, N ≤ L → Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) ∧ rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N ∧ slope ρ₂ N = slope ρ N`. Introduce `N hN`. Take `⟨c1, c2⟩` from `covol_rk_eq ρ ρ₂ hn N.toAddSubgroup (a1 N hN).2 (b1 N hN).2`.

Establish `h1 : Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N)` using `c1`. Establish `h2 : rk ρ₂ N = rk ρ N` using `c2`. Establish `h3 : deg ρ₂ N = deg ρ N`. Unfold `deg Formalism.F.deg`. Rewrite using `[h1]`.

Use `⟨h1, h2, h3, ?_⟩` and prove the remaining obligations. Unfold `slope Formalism.F.slope`. Conclude with `congrArg₂ (· / ·) h3 (congrArg (fun n : ℕ => (n : ℝ)) h2)`. Establish `T2 : ∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N`. Introduce `N`.

Rewrite using `[shiftInv_isSat_iff ρ₂ hL₂, shiftInv_isSat_iff ρ hL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hNL, h⟩`. Use `⟨hNL, fun N' h1 h2 h3 => h N' h1 h2 ?_⟩` and prove the remaining obligations. Rewrite using `[(T1 N' h2).2.1, (T1 N hNL).2.1, h3]`.

Introduce and unpack `⟨hNL, h⟩`. Use `⟨hNL, fun N' h1 h2 h3 => h N' h1 h2 ?_⟩` and prove the remaining obligations. Rewrite using `[← (T1 N' h2).2.1, ← (T1 N hNL).2.1, h3]`. Use `⟨T1, T2, ?_⟩` and prove the remaining obligations. Introduce `N hS`.

Establish `hS₂` using `(T2 N).2 hS`. Take `⟨q1, -, q3⟩` from `a8 N hS`. Take `⟨r1, -, r3⟩` from `b8 N hS₂`. Establish `hrk : Formalism.F.rk (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ N))`. Rewrite using `[q1, r1, (T1 L le_rfl).2.1, (T1 N hS.1).2.1]`.

Establish `hdeg : Formalism.F.deg (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.deg (Formalism.F.quot (zl ρ L) (zl ρ N))`. Rewrite using `[q3, r3, (T1 L le_rfl).2.2.1, (T1 N hS.1).2.2.1]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[covol_eq_exp _ (Formalism.F.degQuot E₂ _ _ hL₂.2 hS₂.2).1, covol_eq_exp _ (Formalism.F.degQuot E _ _ hL.2 hS.2).1, hdeg]`. Unfold `Formalism.F.slope`.

Rewrite using `[hdeg, hrk]`.
-/
theorem transfer (ρ : V →+ E) (ρ₂ : V →+ E₂) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (L : Submodule R V)
    (hL : IsLat ρ L) (hL₂ : IsLat ρ₂ L) :
    (∀ N : Submodule R V, N ≤ L → Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) ∧
      rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N ∧ slope ρ₂ N = slope ρ N) ∧
    (∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N) ∧
    (∀ N : Submodule R V, IsSat ρ L N →
      Formalism.F.covol (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.covol (Formalism.F.quot (zl ρ L) (zl ρ N)) ∧
      Formalism.F.slope (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) =
        Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N))) := by
  obtain ⟨a1, -, -, -, -, -, -, a8⟩ := saturation_basic_properties R V E ρ L hL
  obtain ⟨b1, -, -, -, -, -, -, b8⟩ := saturation_basic_properties R V E₂ ρ₂ L hL₂
  have T1 : ∀ N : Submodule R V, N ≤ L → Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) ∧
      rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N ∧ slope ρ₂ N = slope ρ N := by
    intro N hN
    obtain ⟨c1, c2⟩ := covol_rk_eq ρ ρ₂ hn N.toAddSubgroup (a1 N hN).2 (b1 N hN).2
    have h1 : Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) := c1
    have h2 : rk ρ₂ N = rk ρ N := c2
    have h3 : deg ρ₂ N = deg ρ N := by
      unfold deg Formalism.F.deg
      rw [h1]
    refine ⟨h1, h2, h3, ?_⟩
    unfold slope Formalism.F.slope
    exact congrArg₂ (· / ·) h3 (congrArg (fun n : ℕ => (n : ℝ)) h2)
  have T2 : ∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N := by
    intro N
    rw [shiftInv_isSat_iff ρ₂ hL₂, shiftInv_isSat_iff ρ hL]
    constructor
    · rintro ⟨hNL, h⟩
      refine ⟨hNL, fun N' h1 h2 h3 => h N' h1 h2 ?_⟩
      rw [(T1 N' h2).2.1, (T1 N hNL).2.1, h3]
    · rintro ⟨hNL, h⟩
      refine ⟨hNL, fun N' h1 h2 h3 => h N' h1 h2 ?_⟩
      rw [← (T1 N' h2).2.1, ← (T1 N hNL).2.1, h3]
  refine ⟨T1, T2, ?_⟩
  intro N hS
  have hS₂ := (T2 N).2 hS
  obtain ⟨q1, -, q3⟩ := a8 N hS
  obtain ⟨r1, -, r3⟩ := b8 N hS₂
  have hrk : Formalism.F.rk (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ N)) := by
    rw [q1, r1, (T1 L le_rfl).2.1, (T1 N hS.1).2.1]
  have hdeg : Formalism.F.deg (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) =
      Formalism.F.deg (Formalism.F.quot (zl ρ L) (zl ρ N)) := by
    rw [q3, r3, (T1 L le_rfl).2.2.1, (T1 N hS.1).2.2.1]
  refine ⟨?_, ?_⟩
  · rw [covol_eq_exp _ (Formalism.F.degQuot E₂ _ _ hL₂.2 hS₂.2).1,
      covol_eq_exp _ (Formalism.F.degQuot E _ _ hL.2 hS.2).1, hdeg]
  · unfold Formalism.F.slope
    rw [hdeg, hrk]

end Abs

end Rerealization

open Rerealization in
/- English proof (translation)
Introduce `K V ι V'' κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b'' X'' ψ hX hX'' hψ hnorm A hA`. Establish `hψ' : Function.Injective (ψ.restrictScalars (𝓞 K))` using `hψ`. Take `⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : V →+ EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2), ρ₂ = (Formalism.HermitianLatticesTheory.realize b'' X'').comp ψ.toAddMonoidHom` from `⟨_, rfl⟩`. Establish `hρ₂x : ∀ x, ρ₂ x = Formalism.HermitianLatticesTheory.realize b'' X'' (ψ x)` using `fun x => by rw [hρ₂]; rfl`. Establish `hn : ∀ x, ‖ρ₂ x‖ = ‖Formalism.HermitianLatticesTheory.realize b X x‖`.

Introduce `x`. Establish `h2 : ‖ρ₂ x‖ ^ 2 = ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2`. Rewrite using `[hρ₂x, PlaceOperatorNorms.norm_sq_realize, PlaceOperatorNorms.norm_sq_realize]`. Simplify using `only [hnorm]`. Establish `h3` using `congrArg Real.sqrt h2`.

Rewrite `h3` using `[Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]`. Then use the resulting hypothesis. Establish `hzl : ∀ N : Submodule (𝓞 K) V, zl (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))) = zl ρ₂ N`. Introduce `N`. Use extensionality with `y`. Rewrite using `[satR_mem_zl, satR_mem_zl]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨x, hx, hρ₂x x⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨ψ x, ⟨x, hx, rfl⟩, (hρ₂x x).symm⟩`.

Establish `hmc : ∀ N'' : Submodule (𝓞 K) V'', N'' ≤ A.map (ψ.restrictScalars (𝓞 K)) → ∃ N : Submodule (𝓞 K) V, N ≤ A ∧ N.map (ψ.restrictScalars (𝓞 K)) = N''`. Introduce `N'' h`. Use `⟨N''.comap (ψ.restrictScalars (𝓞 K)), ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨x', hx', hxx'⟩` from `h hx`.

Rewrite using `[← hψ' hxx']`. Conclude with `hx'`. Apply `le_antisymm (Submodule.map_comap_le _ _)` to reduce the goal to its premises. Introduce `y hy`. Take `⟨x, -, rfl⟩` from `h hy`.

Conclude with `⟨x, hy, rfl⟩`. Establish `hle : ∀ N : Submodule (𝓞 K) V, N.map (ψ.restrictScalars (𝓞 K)) ≤ A.map (ψ.restrictScalars (𝓞 K)) ↔ N ≤ A` using `fun N => Submodule.map_le_map_iff_of_injective hψ' N A`. Establish `hbot : ∀ N : Submodule (𝓞 K) V, N.map (ψ.restrictScalars (𝓞 K)) = ⊥ ↔ N = ⊥`. Introduce `N`. Rewrite using `[← Submodule.map_bot (ψ.restrictScalars (𝓞 K))]`.

Conclude with `(Submodule.map_injective_of_injective hψ').eq_iff`. Establish `hneA : ∀ N : Submodule (𝓞 K) V, N.map (ψ.restrictScalars (𝓞 K)) = A.map (ψ.restrictScalars (𝓞 K)) ↔ N = A` using `fun N => (Submodule.map_injective_of_injective hψ').eq_iff`. Establish `hrkK : ∀ N : Submodule (𝓞 K) V, rkK (N.map (ψ.restrictScalars (𝓞 K))) = rkK N`. Introduce `N`. Unfold `rkK`.

Establish `hs : Submodule.span K ((N.map (ψ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V'') : Set V'') = (Submodule.span K (N : Set V)).map ψ`. Rewrite using `[Submodule.map_coe, ← Submodule.span_image]`. Both sides reduce to the same expression. Rewrite using `[hs]`. Conclude with `(Submodule.equivMapOfInjective ψ hψ _).finrank_eq.symm`.

Establish `hlatA : IsLat (Formalism.HermitianLatticesTheory.realize b X) A` using `(place_lattice_structure K V ι b X hX A hA).1`. Establish `hlatA'' : IsLat (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K)))` using `(place_lattice_structure K V'' κ b'' X'' hX'' _ (hA.map _)).1`. Establish `hlatA₂ : IsLat ρ₂ A`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy h`.

Rewrite `h` using `[hρ₂x, hρ₂x]`. Conclude with `hψ (hlatA''.1 (Submodule.mem_map_of_mem hx) (Submodule.mem_map_of_mem hy) h)`. Rewrite using `[← hzl]`. Conclude with `hlatA''.2`. Take `⟨T1, T2, T3⟩` from `transfer (Formalism.HermitianLatticesTheory.realize b X) ρ₂ hn A hlatA hlatA₂`.

Establish `hht : ∀ N : Submodule (𝓞 K) V, N ≤ A → ht b'' X'' (N.map (ψ.restrictScalars (𝓞 K))) = ht b X N`. Introduce `N hN`. Unfold `ht`. Rewrite using `[hrkK, hzl, (T1 N hN).1]`. Establish `hsize : ∀ N : Submodule (𝓞 K) V, N ≤ A → size b'' X'' (N.map (ψ.restrictScalars (𝓞 K))) = size b X N`.

Introduce `N hN`. Unfold `size`. Rewrite using `[hht N hN, hrkK]`. Establish `hslope : ∀ N : Submodule (𝓞 K) V, N ≤ A → slope (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))) = slope (Formalism.HermitianLatticesTheory.realize b X) N`. Introduce `N hN`.

Rewrite using `[← (T1 N hN).2.2.2]`. Unfold `slope`. Rewrite using `[hzl]`. Establish `hsat : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) (N.map (ψ.restrictScalars (𝓞 K))) ↔ IsSat (Formalism.HermitianLatticesTheory.realize b X) A N`. Introduce `N`.

Rewrite using `[← T2 N]`. Unfold `IsSat`. Rewrite using `[hzl, hzl, hle]`. Establish `hqs : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N → Formalism.F.slope (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K)))) (zl (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map …`. Introduce `N hN`.

Rewrite using `[hzl, hzl]`. Conclude with `(T3 N hN).2`. Establish `hsizeQ : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N → sizeQ b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) (N.map (ψ.restrictScalars (𝓞 K))) = sizeQ b X A N`. Introduce `N hN`. Unfold `sizeQ htQ`.

Rewrite using `[hrkK, hrkK, hzl, hzl, (T3 N hN).1]`. Use `⟨hht A le_rfl, hsize A le_rfl, hslope A le_rfl, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `muMax`. Use `congr 1`. Use extensionality with `t`.

Simplify using `only [Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N'', hN'', hne, rfl⟩`. Take `⟨N, hN, rfl⟩` from `hmc N'' hN''`. Conclude with `⟨N, hN, fun h => hne ((hbot N).2 h), (hslope N hN).symm⟩`.

Introduce and unpack `⟨N, hN, hne, rfl⟩`. Conclude with `⟨_, (hle N).2 hN, fun h => hne ((hbot N).1 h), hslope N hN⟩`. Unfold `muMin`. Use `congr 1`. Use extensionality with `t`.

Simplify using `only [Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N'', hs, hne, rfl⟩`. Take `⟨N, -, rfl⟩` from `hmc N'' hs.1`. Establish `hs'` using `(hsat N).1 hs`.

Conclude with `⟨N, hs', fun h => hne ((hneA N).2 h), (hqs N hs').symm⟩`. Introduce and unpack `⟨N, hs, hne, rfl⟩`. Conclude with `⟨_, (hsat N).2 hs, fun h => hne ((hneA N).1 h), hqs N hs⟩`. Unfold `leastSize`. Use `congr 1`.

Use extensionality with `t`. Simplify using `only [Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N'', hN'', hne, rfl⟩`. Take `⟨N, hN, rfl⟩` from `hmc N'' hN''`.

Conclude with `⟨N, hN, fun h => hne ((hbot N).2 h), (hsize N hN).symm⟩`. Introduce and unpack `⟨N, hN, hne, rfl⟩`. Conclude with `⟨_, (hle N).2 hN, fun h => hne ((hbot N).1 h), hsize N hN⟩`. Unfold `largestSize`. Use `congr 1`.

Use extensionality with `t`. Simplify using `only [Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N'', hs, hne, rfl⟩`. Take `⟨N, -, rfl⟩` from `hmc N'' hs.1`.

Establish `hs'` using `(hsat N).1 hs`. Conclude with `⟨N, hs', fun h => hne ((hneA N).2 h), (hsizeQ N hs').symm⟩`. Introduce and unpack `⟨N, hs, hne, rfl⟩`. Conclude with `⟨_, (hsat N).2 hs, fun h => hne ((hneA N).1 h), hsizeQ N hs⟩`.
-/
theorem lattice_rerealization : Rerealize := by
  intro K V ι V'' κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b'' X'' ψ hX hX'' hψ hnorm A hA
  have hψ' : Function.Injective (ψ.restrictScalars (𝓞 K)) := hψ
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : V →+ EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2),
      ρ₂ = (Formalism.HermitianLatticesTheory.realize b'' X'').comp ψ.toAddMonoidHom := ⟨_, rfl⟩
  have hρ₂x : ∀ x, ρ₂ x = Formalism.HermitianLatticesTheory.realize b'' X'' (ψ x) := fun x => by rw [hρ₂]; rfl
  have hn : ∀ x, ‖ρ₂ x‖ = ‖Formalism.HermitianLatticesTheory.realize b X x‖ := by
    intro x
    have h2 : ‖ρ₂ x‖ ^ 2 = ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 := by
      rw [hρ₂x, PlaceOperatorNorms.norm_sq_realize, PlaceOperatorNorms.norm_sq_realize]
      simp only [hnorm]
    have h3 := congrArg Real.sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3
  have hzl : ∀ N : Submodule (𝓞 K) V,
      zl (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))) = zl ρ₂ N := by
    intro N
    ext y
    rw [satR_mem_zl, satR_mem_zl]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hρ₂x x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ψ x, ⟨x, hx, rfl⟩, (hρ₂x x).symm⟩
  have hmc : ∀ N'' : Submodule (𝓞 K) V'', N'' ≤ A.map (ψ.restrictScalars (𝓞 K)) →
      ∃ N : Submodule (𝓞 K) V, N ≤ A ∧ N.map (ψ.restrictScalars (𝓞 K)) = N'' := by
    intro N'' h
    refine ⟨N''.comap (ψ.restrictScalars (𝓞 K)), ?_, ?_⟩
    · intro x hx
      obtain ⟨x', hx', hxx'⟩ := h hx
      rw [← hψ' hxx']
      exact hx'
    · apply le_antisymm (Submodule.map_comap_le _ _)
      intro y hy
      obtain ⟨x, -, rfl⟩ := h hy
      exact ⟨x, hy, rfl⟩
  have hle : ∀ N : Submodule (𝓞 K) V,
      N.map (ψ.restrictScalars (𝓞 K)) ≤ A.map (ψ.restrictScalars (𝓞 K)) ↔ N ≤ A :=
    fun N => Submodule.map_le_map_iff_of_injective hψ' N A
  have hbot : ∀ N : Submodule (𝓞 K) V, N.map (ψ.restrictScalars (𝓞 K)) = ⊥ ↔ N = ⊥ := by
    intro N
    rw [← Submodule.map_bot (ψ.restrictScalars (𝓞 K))]
    exact (Submodule.map_injective_of_injective hψ').eq_iff
  have hneA : ∀ N : Submodule (𝓞 K) V,
      N.map (ψ.restrictScalars (𝓞 K)) = A.map (ψ.restrictScalars (𝓞 K)) ↔ N = A :=
    fun N => (Submodule.map_injective_of_injective hψ').eq_iff
  have hrkK : ∀ N : Submodule (𝓞 K) V, rkK (N.map (ψ.restrictScalars (𝓞 K))) = rkK N := by
    intro N
    unfold rkK
    have hs : Submodule.span K ((N.map (ψ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V'') : Set V'') =
        (Submodule.span K (N : Set V)).map ψ := by
      rw [Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective ψ hψ _).finrank_eq.symm
  have hlatA : IsLat (Formalism.HermitianLatticesTheory.realize b X) A := (place_lattice_structure K V ι b X hX A hA).1
  have hlatA'' : IsLat (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) :=
    (place_lattice_structure K V'' κ b'' X'' hX'' _ (hA.map _)).1
  have hlatA₂ : IsLat ρ₂ A := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy h
      rw [hρ₂x, hρ₂x] at h
      exact hψ (hlatA''.1 (Submodule.mem_map_of_mem hx) (Submodule.mem_map_of_mem hy) h)
    · rw [← hzl]
      exact hlatA''.2
  obtain ⟨T1, T2, T3⟩ := transfer (Formalism.HermitianLatticesTheory.realize b X) ρ₂ hn A hlatA hlatA₂
  have hht : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      ht b'' X'' (N.map (ψ.restrictScalars (𝓞 K))) = ht b X N := by
    intro N hN
    unfold ht
    rw [hrkK, hzl, (T1 N hN).1]
  have hsize : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      size b'' X'' (N.map (ψ.restrictScalars (𝓞 K))) = size b X N := by
    intro N hN
    unfold size
    rw [hht N hN, hrkK]
  have hslope : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      slope (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))) =
        slope (Formalism.HermitianLatticesTheory.realize b X) N := by
    intro N hN
    rw [← (T1 N hN).2.2.2]
    unfold slope
    rw [hzl]
  have hsat : ∀ N : Submodule (𝓞 K) V,
      IsSat (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K)))
        (N.map (ψ.restrictScalars (𝓞 K))) ↔ IsSat (Formalism.HermitianLatticesTheory.realize b X) A N := by
    intro N
    rw [← T2 N]
    unfold IsSat
    rw [hzl, hzl, hle]
  have hqs : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N →
      Formalism.F.slope (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))))
        (zl (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))))) =
      Formalism.F.slope (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) A) (zl (Formalism.HermitianLatticesTheory.realize b X) N)) := by
    intro N hN
    rw [hzl, hzl]
    exact (T3 N hN).2
  have hsizeQ : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N →
      sizeQ b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) (N.map (ψ.restrictScalars (𝓞 K))) =
        sizeQ b X A N := by
    intro N hN
    unfold sizeQ htQ
    rw [hrkK, hrkK, hzl, hzl, (T3 N hN).1]
  refine ⟨hht A le_rfl, hsize A le_rfl, hslope A le_rfl, ?_, ?_, ?_, ?_⟩
  · unfold muMax
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hN'', hne, rfl⟩
      obtain ⟨N, hN, rfl⟩ := hmc N'' hN''
      exact ⟨N, hN, fun h => hne ((hbot N).2 h), (hslope N hN).symm⟩
    · rintro ⟨N, hN, hne, rfl⟩
      exact ⟨_, (hle N).2 hN, fun h => hne ((hbot N).1 h), hslope N hN⟩
  · unfold muMin
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hs, hne, rfl⟩
      obtain ⟨N, -, rfl⟩ := hmc N'' hs.1
      have hs' := (hsat N).1 hs
      exact ⟨N, hs', fun h => hne ((hneA N).2 h), (hqs N hs').symm⟩
    · rintro ⟨N, hs, hne, rfl⟩
      exact ⟨_, (hsat N).2 hs, fun h => hne ((hneA N).1 h), hqs N hs⟩
  · unfold leastSize
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hN'', hne, rfl⟩
      obtain ⟨N, hN, rfl⟩ := hmc N'' hN''
      exact ⟨N, hN, fun h => hne ((hbot N).2 h), (hsize N hN).symm⟩
    · rintro ⟨N, hN, hne, rfl⟩
      exact ⟨_, (hle N).2 hN, fun h => hne ((hbot N).1 h), hsize N hN⟩
  · unfold largestSize
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hs, hne, rfl⟩
      obtain ⟨N, -, rfl⟩ := hmc N'' hs.1
      have hs' := (hsat N).1 hs
      exact ⟨N, hs', fun h => hne ((hneA N).2 h), (hsizeQ N hs').symm⟩
    · rintro ⟨N, hs, hne, rfl⟩
      exact ⟨_, (hsat N).2 hs, fun h => hne ((hneA N).1 h), hsizeQ N hs⟩

end Formalism.HN
