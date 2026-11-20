import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AutomorphicArithmetic.RealSpanData.RealData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PzIffPos

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private def Pz {R : Type} [Ring R] [Algebra ℝ R] (t : R) : Prop :=
  ∃ s : Finset ℝ, (∀ l ∈ s, 0 < l) ∧
    Polynomial.aeval t (∏ l ∈ s, (Polynomial.X - Polynomial.C l)) = 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, h⟩`. Use `⟨s, hs, hf ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_algHom_apply, h, map_zero]`. Introduce and unpack `⟨s, hs, h⟩`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_algHom_apply, h, map_zero]`.
-/
private theorem Pz_map_iff {R R' : Type} [Ring R] [Algebra ℝ R] [Ring R'] [Algebra ℝ R']
    (f : R →ₐ[ℝ] R') (hf : Function.Injective f) (t : R) : Pz (f t) ↔ Pz t := by
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, hf ?_⟩
    rw [← Polynomial.aeval_algHom_apply, h, map_zero]
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [Polynomial.aeval_algHom_apply, h, map_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, h⟩ i`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Use `Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : I => M) i) t (∏ l ∈ s, (Polynomial.X - Polynomial.C l))` as an intermediate fact. Rewrite `this` using `[h, map_zero]`.

Conclude with `this`. Introduce `h choose s hs h0 using h`. Use `⟨Finset.univ.biUnion s, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 hl`.

Conclude with `hs i l hi`. Use function extensionality and compare the values at `i`. Establish `hsub : s i ⊆ Finset.univ.biUnion s` using `Finset.subset_biUnion_of_mem s (Finset.mem_univ i)`. Use `Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : I => M) i) t (∏ l ∈ Finset.univ.biUnion s, (Polynomial.X - Polynomial.C l))` as an intermediate fact. Establish `e : Polynomial.aeval (t i) (∏ l ∈ Finset.univ.biUnion s, (Polynomial.X - Polynomial.C l)) = 0`.

Rewrite using `[← Finset.prod_sdiff hsub, map_mul, h0 i, mul_zero]`. Conclude with `this.symm.trans e`.
-/
private theorem Pz_pi {I M : Type} [Fintype I] [Ring M] [Algebra ℝ M] (t : I → M) :
    Pz t ↔ ∀ i, Pz (t i) := by
  constructor
  · rintro ⟨s, hs, h⟩ i
    refine ⟨s, hs, ?_⟩
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : I => M) i) t
      (∏ l ∈ s, (Polynomial.X - Polynomial.C l))
    rw [h, map_zero] at this
    exact this
  · intro h
    choose s hs h0 using h
    refine ⟨Finset.univ.biUnion s, ?_, ?_⟩
    · intro l hl
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hl
      exact hs i l hi
    · funext i
      have hsub : s i ⊆ Finset.univ.biUnion s := Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
      have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : I => M) i) t
        (∏ l ∈ Finset.univ.biUnion s, (Polynomial.X - Polynomial.C l))
      have e : Polynomial.aeval (t i) (∏ l ∈ Finset.univ.biUnion s, (Polynomial.X - Polynomial.C l)) = 0 := by
        rw [← Finset.prod_sdiff hsub, map_mul, h0 i, mul_zero]
      exact this.symm.trans e

/- English proof (translation)
Set `e` to `hT.eigenvectorBasis (n := Module.finrank ℝ W) rfl`. Set `lam` to `hT.eigenvalues (n := Module.finrank ℝ W) rfl`. Establish `hev : ∀ i, Module.End.HasEigenvector T (lam i) (e i)` using `fun i => hT.hasEigenvector_eigenvectorBasis rfl i`. Establish `hTe : ∀ i, T (e i) = lam i • e i` using `fun i => hev i |>.apply_eq_smul`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hs, h⟩ x hx`. Establish `hl : ∀ i, 0 < lam i`. Introduce `i`. Establish `h1` using `Module.End.aeval_apply_of_hasEigenvector (p := ∏ l ∈ s, (Polynomial.X - Polynomial.C l)) (hev i)`. Rewrite `h1` using `[h, LinearMap.zero_apply]`.

Establish `h2` using `(smul_eq_zero.1 h1.symm).resolve_right (hev i).2`. Rewrite `h2` using `[Polynomial.eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨l, hl, h3⟩` from `h2`. Establish `: lam i = l` using `by simpa [sub_eq_zero] using h3`. Conclude with `this ▸ hs l hl`.

Establish `hsum : inner ℝ (T x) x = ∑ i, lam i * (inner ℝ x (e i) * inner ℝ x (e i))`. Rewrite using `[← e.sum_inner_mul_inner (T x) x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hT x (e i), hTe i, inner_smul_right, real_inner_comm x (e i)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsum]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, inner ℝ x (e i) ≠ (0 : ℝ) := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hx` to reduce the goal to its premises.

Use `e.sum_inner_mul_inner x x` as an intermediate fact. Establish `h0 : inner ℝ x x = (0 : ℝ)` using `by rw [← this]; simp [hc]`. Conclude with `inner_self_eq_zero.1 h0`. Use `Finset.sum_pos' (fun j _ => mul_nonneg (hl j).le (mul_self_nonneg _)) ⟨i, Finset.mem_univ i, ?_⟩` and prove the remaining obligations. Conclude with `mul_pos (hl i) (mul_self_pos.2 hi)`.

Introduce `h`. Establish `hl : ∀ i, 0 < lam i`. Introduce `i`. Use `h (e i) (hev i).2` as an intermediate fact. Rewrite `this` using `[hTe i, inner_smul_left]`.

Simplify `this` using `[e.orthonormal.1 i]`. Use `⟨Finset.univ.image lam, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl'`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hl'`. Conclude with `hl i`.

Use `e.toBasis.ext fun i => ?_` and prove the remaining obligations. Rewrite using `[OrthonormalBasis.coe_toBasis]`. Rewrite using `[Module.End.aeval_apply_of_hasEigenvector (hev i), Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_image_of_mem lam (Finset.mem_univ i)) (by simp)]`. Simplify using the standard rewrite rules.
-/
private theorem Pz_iff_pos_inner {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (T : Module.End ℝ W) (hT : LinearMap.IsSymmetric T) :
    Pz T ↔ ∀ x, x ≠ 0 → 0 < inner ℝ (T x) x := by
  let e := hT.eigenvectorBasis (n := Module.finrank ℝ W) rfl
  let lam := hT.eigenvalues (n := Module.finrank ℝ W) rfl
  have hev : ∀ i, Module.End.HasEigenvector T (lam i) (e i) := fun i =>
    hT.hasEigenvector_eigenvectorBasis rfl i
  have hTe : ∀ i, T (e i) = lam i • e i := fun i => hev i |>.apply_eq_smul
  constructor
  · rintro ⟨s, hs, h⟩ x hx
    have hl : ∀ i, 0 < lam i := by
      intro i
      have h1 := Module.End.aeval_apply_of_hasEigenvector (p := ∏ l ∈ s, (Polynomial.X - Polynomial.C l)) (hev i)
      rw [h, LinearMap.zero_apply] at h1
      have h2 := (smul_eq_zero.1 h1.symm).resolve_right (hev i).2
      rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
      obtain ⟨l, hl, h3⟩ := h2
      have : lam i = l := by simpa [sub_eq_zero] using h3
      exact this ▸ hs l hl
    have hsum : inner ℝ (T x) x = ∑ i, lam i * (inner ℝ x (e i) * inner ℝ x (e i)) := by
      rw [← e.sum_inner_mul_inner (T x) x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT x (e i), hTe i, inner_smul_right, real_inner_comm x (e i)]
      ring
    rw [hsum]
    obtain ⟨i, hi⟩ : ∃ i, inner ℝ x (e i) ≠ (0 : ℝ) := by
      by_contra hc
      push_neg at hc
      apply hx
      have := e.sum_inner_mul_inner x x
      have h0 : inner ℝ x x = (0 : ℝ) := by rw [← this]; simp [hc]
      exact inner_self_eq_zero.1 h0
    refine Finset.sum_pos' (fun j _ => mul_nonneg (hl j).le (mul_self_nonneg _)) ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos (hl i) (mul_self_pos.2 hi)
  · intro h
    have hl : ∀ i, 0 < lam i := by
      intro i
      have := h (e i) (hev i).2
      rw [hTe i, inner_smul_left] at this
      simpa [e.orthonormal.1 i] using this
    refine ⟨Finset.univ.image lam, ?_, ?_⟩
    · intro l hl'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl'
      exact hl i
    · refine e.toBasis.ext fun i => ?_
      rw [OrthonormalBasis.coe_toBasis]
      rw [Module.End.aeval_apply_of_hasEigenvector (hev i), Polynomial.eval_prod,
        Finset.prod_eq_zero (Finset.mem_image_of_mem lam (Finset.mem_univ i)) (by simp)]
      simp

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh60.Pz_iff_pos Q hsym hpos T hT`.
-/
private theorem Pz_iff_pos {W : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (Q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsym : ∀ x y, Q x y = Q y x) (hpos : ∀ x, x ≠ 0 → 0 < Q x x)
    (T : Module.End ℝ W) (hT : ∀ x y, Q (T x) y = Q x (T y)) :
    Pz T ↔ ∀ x, x ≠ 0 → 0 < Q (T x) x :=
  _root_.UpperTheory.Reformulated.B.Qh60.Pz_iff_pos Q hsym hpos T hT

/- English proof (translation)
Simplify using `only [actOn, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Module.End.mul_apply, Algebra.algebraMap_eq_smul_one]`. Express the relevant statement in the definitionally equal form `r • (((1 : Module.End ℝ (ℝ ⊗[ℚ] V))) ((rep c).baseChange ℝ (s ⊗ₜ v))) = _`. Rewrite using `[LinearMap.baseChange_tmul, Module.End.one_apply, TensorProduct.smul_tmul', smul_eq_mul]`.
-/
private theorem actOn_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (r s : ℝ) (c : C) (v : V) :
    actOn rep ℝ (r ⊗ₜ c) (s ⊗ₜ v) = (r * s) ⊗ₜ rep c v := by
  simp only [actOn, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one]
  change r • (((1 : Module.End ℝ (ℝ ⊗[ℚ] V))) ((rep c).baseChange ℝ (s ⊗ₜ v))) = _
  rw [LinearMap.baseChange_tmul, Module.End.one_apply, TensorProduct.smul_tmul', smul_eq_mul]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Set `B` to `Module.Free.chooseBasis ℚ ℝ`. Take `⟨c, rfl⟩` from `TensorProduct.eq_repr_basis_left B x`. Establish `hc : c = 0`.

Use extensionality with `i`. Apply `hrep` to reduce the goal to its premises. Rewrite using `[Finsupp.zero_apply, map_zero]`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `h1 : actOn rep ℝ (c.sum fun i n => B i ⊗ₜ[ℚ] n) ((1 : ℝ) ⊗ₜ[ℚ] v) = 0` using `by rw [hx]; rfl`.

Rewrite `h1` using `[Finsupp.sum, map_sum, LinearMap.sum_apply]`. Simplify using `only [actOn_tmul, _root_.mul_one] at h1`. Establish `h2 : ((c.mapRange (fun y => rep y v) (by simp)).sum fun i n => B i ⊗ₜ[ℚ] n) = 0`. Rewrite using `[Finsupp.sum_mapRange_index (by simp)]`. Conclude with `h1`.

Establish `h3` using `TensorProduct.sum_tmul_basis_left_eq_zero B _ h2`. Simplify using `using DFunLike.congr_fun h3 i`. Simplify using `[hc]`.
-/
private theorem actOn_inj {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) :
    Function.Injective (actOn rep ℝ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  let B := Module.Free.chooseBasis ℚ ℝ
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left B x
  have hc : c = 0 := by
    ext i
    apply hrep
    rw [Finsupp.zero_apply, map_zero]
    refine LinearMap.ext fun v => ?_
    have h1 : actOn rep ℝ (c.sum fun i n => B i ⊗ₜ[ℚ] n) ((1 : ℝ) ⊗ₜ[ℚ] v) = 0 := by rw [hx]; rfl
    rw [Finsupp.sum, map_sum, LinearMap.sum_apply] at h1
    simp only [actOn_tmul, _root_.mul_one] at h1
    have h2 : ((c.mapRange (fun y => rep y v) (by simp)).sum fun i n => B i ⊗ₜ[ℚ] n) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      exact h1
    have h3 := TensorProduct.sum_tmul_basis_left_eq_zero B _ h2
    simpa using DFunLike.congr_fun h3 i
  simp [hc]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul a m`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul a' m'`.

Rewrite using `[LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h m m', neg_smul, mul_comm]`.
-/
private theorem bc_anti {R A M : Type} [CommRing R] [CommRing A] [AddCommGroup M] [Algebra R A]
    [Module R M] (B : LinearMap.BilinForm R M) (h : ∀ x y, B x y = -B y x) (x y : A ⊗[R] M) :
    B.baseChange A x y = -B.baseChange A y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd]; ring
    | tmul a' m' =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h m m', neg_smul,
        mul_comm]

/- English proof (translation)
Establish `h0 : ∀ x y, D.EF x y = -D.EF y x`. Introduce `x y`. Use `D.alt (x + y)` as an intermediate fact. Simplify using `only [map_add, LinearMap.add_apply, D.alt] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `bc_anti _ (bc_anti _ h0) x y`.
-/
private theorem E_anti {p : ℕ} [Fact p.Prime] (D : Datum p) (x y : ℝ ⊗[ℚ] VQ D) :
    (D.EF.baseChange ℚ).baseChange ℝ x y = -(D.EF.baseChange ℚ).baseChange ℝ y x := by
  have h0 : ∀ x y, D.EF x y = -D.EF y x := by
    intro x y
    have := D.alt (x + y)
    simp only [map_add, LinearMap.add_apply, D.alt] at this
    linarith
  exact bc_anti _ (bc_anti _ h0) x y

/- English proof (translation)
Proceed by induction on `b using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add b b' h h' => simp only [map_add, LinearMap.add_apply, MulOpposite.unop_add, h, h']`. Consider the case `tmul r c`. Rewrite using `[starT_tmul]`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']`. Consider the case `tmul s v`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']`. Consider the case `tmul t w`. Establish `h` using `L.adj c v w`. Rewrite `h` using `[show sh G c = (G.star c).unop from rfl]`.

Rewrite using `[actOn_tmul, actOn_tmul, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem E_adj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    (b : ℝ ⊗[ℚ] G.C) (x y : ℝ ⊗[ℚ] VQ D) :
    (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) y =
      (D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ (starT G.star ℝ b).unop y) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add b b' h h' => simp only [map_add, LinearMap.add_apply, MulOpposite.unop_add, h, h']
  | tmul r c =>
    rw [starT_tmul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | tmul s v =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']
      | tmul t w =>
        have h := L.adj c v w
        rw [show sh G c = (G.star c).unop from rfl] at h
        rw [actOn_tmul, actOn_tmul, LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, h]
        congr 1
        ring

/- English proof (translation)
Rewrite using `[Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]`.
-/
private theorem herm_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (x y : Fin n → ℂ) : star (star x ⬝ᵥ A *ᵥ y) = star y ⬝ᵥ A *ᵥ x := by
  rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]

/- English proof (translation)
Set `π : Matrix (Fin n) (Fin n) ℂ →ₐ[ℝ] Module.End ℝ (Fin n → ℂ)` to `AlgHom.ofLinearMap { toFun := fun m => (Matrix.mulVecLin m).restrictScalars ℝ map_add' := fun a b => LinearMap.ext fun x => by simp [Matrix.add_mulVec] map_smul' := fun r a => LinearMap.ext fun x => by simp [Matrix.smul_mulVec] } (LinearMap.ext fun x => by simp) (fun a b => Linea …`. Express the relevant statement in the definitionally equal form `(a * b) *ᵥ x = a *ᵥ (b *ᵥ x)`. Rewrite using `[Matrix.mulVec_mulVec])`. Establish `hπ : ∀ m x, π m x = m *ᵥ x` using `fun _ _ => rfl`. Establish `hπi : Function.Injective π` using `fun a b hab => Matrix.mulVec_injective (funext fun x => by rw [← hπ, ← hπ, hab])`.

Establish `hHh : H.IsHermitian` using `(Matrix.posDef_iff_dotProduct_mulVec.1 hH).1`. Set `Q : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun x y => (star x ⬝ᵥ (H *ᵥ y)).re) (fun x x' y => by simp [star_add, add_dotProduct]) (fun r x y => by simp [smul_dotProduct, star_smul]) (fun x y y' => by simp [Matrix.mulVec_add, dotProduct_add]) (fun r x y => by simp [Matrix.mulVec_smul, dotProduct_smul])`. Establish `hQ : ∀ x y, Q x y = (star x ⬝ᵥ (H *ᵥ y)).re` using `fun _ _ => rfl`. Establish `hsym : ∀ x y, Q x y = Q y x`. Introduce `x y`.

Rewrite using `[hQ, hQ, ← herm_conj H hHh y x]`. Simplify using the standard rewrite rules. Establish `hpos : ∀ x, x ≠ 0 → 0 < Q x x` using `fun x hx => by`. Use `(Complex.lt_def.1 ((Matrix.posDef_iff_dotProduct_mulVec.1 hH).2 hx)).1` as an intermediate fact. Rewrite using `[hQ]`.

Simplify using `using this`. Establish `hT : ∀ x y, Q (π M x) y = Q x (π M y)`. Introduce `x y`. Rewrite using `[hQ, hQ, hπ, hπ, Matrix.mulVec_mulVec, ← herm_conj _ hS y x, ← Matrix.mulVec_mulVec, herm_conj H hHh, ← herm_conj H hHh, ← herm_conj H hHh]`. Rewrite using `[← Pz_map_iff π hπi M, Pz_iff_pos Q hsym hpos (π M) hT, Matrix.posDef_iff_dotProduct_mulVec]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨hS, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `h x hx`. Rewrite `h1` using `[hsym, hQ, hπ, Matrix.mulVec_mulVec]`.

Establish `h2` using `herm_conj _ hS x x`. Use `Complex.lt_def.2 ⟨by simpa using h1, ?_⟩` and prove the remaining obligations. Simplify using `using (Complex.conj_eq_iff_im.1 h2).symm`. Introduce and unpack `⟨-, h⟩ x hx`. Rewrite using `[hsym, hQ, hπ, Matrix.mulVec_mulVec]`.

Simplify using `using (Complex.lt_def.1 (h hx)).1`.
-/
private theorem Pz_matrix {n : ℕ} (H M : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (hS : (H * M).IsHermitian) : Pz M ↔ (H * M).PosDef := by
  let π : Matrix (Fin n) (Fin n) ℂ →ₐ[ℝ] Module.End ℝ (Fin n → ℂ) :=
    AlgHom.ofLinearMap
      { toFun := fun m => (Matrix.mulVecLin m).restrictScalars ℝ
        map_add' := fun a b => LinearMap.ext fun x => by simp [Matrix.add_mulVec]
        map_smul' := fun r a => LinearMap.ext fun x => by simp [Matrix.smul_mulVec] }
      (LinearMap.ext fun x => by simp)
      (fun a b => LinearMap.ext fun x => by
        change (a * b) *ᵥ x = a *ᵥ (b *ᵥ x)
        rw [Matrix.mulVec_mulVec])
  have hπ : ∀ m x, π m x = m *ᵥ x := fun _ _ => rfl
  have hπi : Function.Injective π := fun a b hab =>
    Matrix.mulVec_injective (funext fun x => by rw [← hπ, ← hπ, hab])
  have hHh : H.IsHermitian := (Matrix.posDef_iff_dotProduct_mulVec.1 hH).1
  let Q : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => (star x ⬝ᵥ (H *ᵥ y)).re)
      (fun x x' y => by simp [star_add, add_dotProduct])
      (fun r x y => by simp [smul_dotProduct, star_smul])
      (fun x y y' => by simp [Matrix.mulVec_add, dotProduct_add])
      (fun r x y => by simp [Matrix.mulVec_smul, dotProduct_smul])
  have hQ : ∀ x y, Q x y = (star x ⬝ᵥ (H *ᵥ y)).re := fun _ _ => rfl
  have hsym : ∀ x y, Q x y = Q y x := by
    intro x y
    rw [hQ, hQ, ← herm_conj H hHh y x]
    simp
  have hpos : ∀ x, x ≠ 0 → 0 < Q x x := fun x hx => by
    have := (Complex.lt_def.1 ((Matrix.posDef_iff_dotProduct_mulVec.1 hH).2 hx)).1
    rw [hQ]
    simpa using this
  have hT : ∀ x y, Q (π M x) y = Q x (π M y) := by
    intro x y
    rw [hQ, hQ, hπ, hπ, Matrix.mulVec_mulVec, ← herm_conj _ hS y x, ← Matrix.mulVec_mulVec,
      herm_conj H hHh, ← herm_conj H hHh, ← herm_conj H hHh]
  rw [← Pz_map_iff π hπi M, Pz_iff_pos Q hsym hpos (π M) hT, Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨hS, fun x hx => ?_⟩
    have h1 := h x hx
    rw [hsym, hQ, hπ, Matrix.mulVec_mulVec] at h1
    have h2 := herm_conj _ hS x x
    refine Complex.lt_def.2 ⟨by simpa using h1, ?_⟩
    simpa using (Complex.conj_eq_iff_im.1 h2).symm
  · rintro ⟨-, h⟩ x hx
    rw [hsym, hQ, hπ, Matrix.mulVec_mulVec]
    simpa using (Complex.lt_def.1 (h hx)).1

/- English proof (translation)
Introduce `p _ D G L b hb`. Take `⟨J, hJJ, hJs, hJp, hJv⟩` from `L.orient`. Use `haveI : Module.Finite ℤ D.La := D.finLa`. Use `haveI : FiniteDimensional ℝ (ℝ ⊗[ℚ] VQ D) := inferInstance`. Set `a : ℝ ⊗[ℚ] G.C` to `-(J * b)`.

Establish `hJa : J * a = b`. Express the relevant statement in the definitionally equal form `J * -(J * b) = b`. Rewrite using `[_root_.mul_neg, ← _root_.mul_assoc, hJJ, neg_mul, _root_.one_mul, neg_neg]`. Establish `adjJ : ∀ x y, (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ J x) y = -(D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ J y)` using `fun x y => by`. Rewrite using `[E_adj, hJs, map_neg, LinearMap.neg_apply, map_neg]`.

Establish `adjb : ∀ x y, (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) y = -(D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ b y)` using `fun x y => by`. Rewrite using `[E_adj, hb, map_neg, LinearMap.neg_apply, map_neg]`. Establish `hJaX : ∀ x, actOn L.rep ℝ J (actOn L.rep ℝ a x) = actOn L.rep ℝ b x` using `fun x => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hJa]`. Set `Q : (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] ℝ` to `LinearMap.comp (show (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] ℝ from (D.EF.baseChange ℚ).baseChange ℝ) (actOn L.rep ℝ J)`.

Establish `hQ : ∀ x y, Q x y = (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ J x) y` using `fun _ _ => rfl`. Establish `hsym : ∀ x y, Q x y = Q y x` using `fun x y => by`. Rewrite using `[hQ, hQ, adjJ, E_anti D x, neg_neg]`. Establish `hT : ∀ x y, Q (actOn L.rep ℝ a x) y = Q x (actOn L.rep ℝ a y)` using `fun x y => by`. Rewrite using `[hQ, hQ, hJaX, adjJ, hJaX, adjb]`.

Establish `hL : (∀ x : ℝ ⊗[ℚ] VQ D, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) x) ↔ Pz a`. Rewrite using `[← Pz_map_iff (actOn L.rep ℝ) (actOn_inj L.rep L.rep_inj) a, Pz_iff_pos Q hsym hJp _ hT]`. Simplify using `only [hQ, hJaX]`. Set `Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ)` to `Pi.algHom ℝ _ fun v => G.psiR v`. Establish `hΨ : Function.Injective Ψ` using `G.psiR_pi_bijective.1`.

Rewrite using `[hL, ← Pz_map_iff Ψ hΨ a, Pz_pi]`. Use `forall_congr' fun v => ?_` and prove the remaining obligations. Use `set c : ℂ := if v.embedding (L.e D.ω) = D.ρc then -Complex.I else Complex.I with hc`. Establish `hcs : star c = -c`. Rewrite using `[hc]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `set h := G.gram v with hh`. Use `set X := G.psiR v J with hX`. Use `set Y := G.psiR v b with hY`. Establish `hXX : X * X = -1`.

Rewrite using `[hX, ← map_mul, hJJ, map_neg, map_one]`. Establish `hM : Ψ a v = -(X * Y)`. Express the relevant statement in the definitionally equal form `G.psiR v (-(J * b)) = _`. Rewrite using `[map_neg, map_mul]`. Establish `hHM : (c • (h * X)) * Ψ a v = c • (h * Y)`.

Rewrite using `[hM, smul_mul_assoc, _root_.mul_neg, _root_.mul_assoc, ← _root_.mul_assoc X X Y, hXX]`. Simplify using the standard rewrite rules. Establish `hhh : hᴴ = h` using `G.gram_herm v`. Establish `hinv : h * h⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (G.gram_det v))`. Establish `hYs : h * (-Y) = Yᴴ * h`.

Establish `h1` using `GlobalTheory.LKMid.psiR_starT G v b`. Rewrite `h1` using `[hb, map_neg]`. Rewrite using `[h1, ← _root_.mul_assoc, ← _root_.mul_assoc, hinv, _root_.one_mul]`. Establish `hSh : (c • (h * Y)).IsHermitian`. Express the relevant statement in the definitionally equal form `(c • (h * Y))ᴴ = _`.

Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hhh, ← hYs, hcs]`. Simplify using the standard rewrite rules. Rewrite `hSh`, the goal using `[← hHM]`. Conclude with `Pz_matrix _ _ (hJv v) hSh`.
-/
theorem UpperTheory.positivity_iff_gram_posDef :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (b : ℝ ⊗[ℚ] G.C), (starT G.star ℝ b).unop = -b → ((∀ x : ℝ ⊗[ℚ] VQ D, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) x) ↔ ∀ v' : InfinitePlace G.F, ((if v'.embedding (L.e D.ω) = D.ρc then -Complex.I else Complex.I) • (G.gram v' * G.psiR v' b)).PosDef) := by
  intro p _ D G L b hb
  obtain ⟨J, hJJ, hJs, hJp, hJv⟩ := L.orient
  haveI : Module.Finite ℤ D.La := D.finLa
  haveI : FiniteDimensional ℝ (ℝ ⊗[ℚ] VQ D) := inferInstance
  let a : ℝ ⊗[ℚ] G.C := -(J * b)
  have hJa : J * a = b := by
    change J * -(J * b) = b
    rw [_root_.mul_neg, ← _root_.mul_assoc, hJJ, neg_mul, _root_.one_mul, neg_neg]
  have adjJ : ∀ x y, (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ J x) y =
      -(D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ J y) := fun x y => by
    rw [E_adj, hJs, map_neg, LinearMap.neg_apply, map_neg]
  have adjb : ∀ x y, (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) y =
      -(D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ b y) := fun x y => by
    rw [E_adj, hb, map_neg, LinearMap.neg_apply, map_neg]
  have hJaX : ∀ x, actOn L.rep ℝ J (actOn L.rep ℝ a x) = actOn L.rep ℝ b x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, hJa]
  let Q : (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] ℝ :=
    LinearMap.comp (show (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] ℝ from (D.EF.baseChange ℚ).baseChange ℝ)
      (actOn L.rep ℝ J)
  have hQ : ∀ x y, Q x y = (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ J x) y := fun _ _ => rfl
  have hsym : ∀ x y, Q x y = Q y x := fun x y => by
    rw [hQ, hQ, adjJ, E_anti D x, neg_neg]
  have hT : ∀ x y, Q (actOn L.rep ℝ a x) y = Q x (actOn L.rep ℝ a y) := fun x y => by
    rw [hQ, hQ, hJaX, adjJ, hJaX, adjb]
  have hL : (∀ x : ℝ ⊗[ℚ] VQ D, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) x) ↔ Pz a := by
    rw [← Pz_map_iff (actOn L.rep ℝ) (actOn_inj L.rep L.rep_inj) a, Pz_iff_pos Q hsym hJp _ hT]
    simp only [hQ, hJaX]
  let Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    Pi.algHom ℝ _ fun v => G.psiR v
  have hΨ : Function.Injective Ψ := G.psiR_pi_bijective.1
  rw [hL, ← Pz_map_iff Ψ hΨ a, Pz_pi]
  refine forall_congr' fun v => ?_
  set c : ℂ := if v.embedding (L.e D.ω) = D.ρc then -Complex.I else Complex.I with hc
  have hcs : star c = -c := by
    rw [hc]
    split_ifs <;> simp
  set h := G.gram v with hh
  set X := G.psiR v J with hX
  set Y := G.psiR v b with hY
  have hXX : X * X = -1 := by
    rw [hX, ← map_mul, hJJ, map_neg, map_one]
  have hM : Ψ a v = -(X * Y) := by
    change G.psiR v (-(J * b)) = _
    rw [map_neg, map_mul]
  have hHM : (c • (h * X)) * Ψ a v = c • (h * Y) := by
    rw [hM, smul_mul_assoc, _root_.mul_neg, _root_.mul_assoc, ← _root_.mul_assoc X X Y, hXX]
    simp
  have hhh : hᴴ = h := G.gram_herm v
  have hinv : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (G.gram_det v))
  have hYs : h * (-Y) = Yᴴ * h := by
    have h1 := GlobalTheory.LKMid.psiR_starT G v b
    rw [hb, map_neg] at h1
    rw [h1, ← _root_.mul_assoc, ← _root_.mul_assoc, hinv, _root_.one_mul]
  have hSh : (c • (h * Y)).IsHermitian := by
    change (c • (h * Y))ᴴ = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hhh, ← hYs, hcs]
    simp
  rw [← hHM] at hSh ⊢
  exact Pz_matrix _ _ (hJv v) hSh
