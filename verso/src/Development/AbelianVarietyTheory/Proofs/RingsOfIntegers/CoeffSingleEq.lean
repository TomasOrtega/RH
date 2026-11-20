import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.FormalGroupCoeffSecondLinear

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open MvPowerSeries
open scoped Kronecker
namespace GlobalTheory.JacVal

section Series
variable {V : Type} [CommRing V] {σ τ : Type}

/- English proof (translation)
Take `⟨k, -, hk⟩` from `exists_eq_sum_X_mul (n := 0) (g := g - C (constantCoeff g)) fun d hd => by`. Establish `: d = 0`. Rewrite using `[← Finsupp.degree_eq_zero_iff]`. Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality.

Simplify using the standard rewrite rules. Conclude with `⟨k, by rw [← hk]; ring⟩`.
-/
theorem exists_decomp [Fintype σ] (g : MvPowerSeries σ V) :
    ∃ k : σ → MvPowerSeries σ V, g = C (constantCoeff g) + ∑ i, X i * k i := by
  classical
  obtain ⟨k, -, hk⟩ := exists_eq_sum_X_mul (n := 0) (g := g - C (constantCoeff g))
    fun d hd => by
      have : d = 0 := by
        rw [← Finsupp.degree_eq_zero_iff]; omega
      subst this
      simp
  exact ⟨k, by rw [← hk]; ring⟩

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]`. Simplify using the standard rewrite rules.
-/
theorem coeff_single_eq (q : τ) (f : MvPowerSeries τ V) :
    coeff (Finsupp.single q 1) f = constantCoeff (pderiv V q f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

/- English proof (translation)
Rewrite using `[coeff_single_eq, coeff_single_eq, Derivation.leibniz]`. Simplify using `[ha, _root_.mul_comm]`.
-/
theorem coeff_single_mul (q : τ) (a b : MvPowerSeries τ V) (ha : constantCoeff a = 0) :
    coeff (Finsupp.single q 1) (a * b) = coeff (Finsupp.single q 1) a * constantCoeff b := by
  rw [coeff_single_eq, coeff_single_eq, Derivation.leibniz]
  simp [ha, _root_.mul_comm]

/- English proof (translation)
Rewrite using `[coeff_single_eq]`. Simplify using the standard rewrite rules.
-/
theorem coeff_single_C (q : τ) (c : V) : coeff (Finsupp.single q 1) (C c : MvPowerSeries τ V) = 0 := by
  rw [coeff_single_eq]; simp

/- English proof (translation)
Rewrite using `[coeff_X]`. Distinguish the cases in `h : q = p`. Simplify using `[h]`. Rewrite using `[if_neg, if_neg h]`. Introduce `h'`.

Conclude with `h (Finsupp.single_left_injective one_ne_zero h')`.
-/
theorem coeff_single_X [DecidableEq τ] (q p : τ) :
    coeff (Finsupp.single q 1) (X p : MvPowerSeries τ V) = if q = p then 1 else 0 := by
  rw [coeff_X]
  by_cases h : q = p
  · simp [h]
  · rw [if_neg, if_neg h]
    intro h'
    exact h (Finsupp.single_left_injective one_ne_zero h')

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_decomp f`. Establish `hC : ψ (C (constantCoeff f)) = C (constantCoeff f)` using `ψ.commutes _`. Use `conv_lhs => rw [hk]`. Simplify using `[hC, h]`.
-/
theorem const_hom [Fintype σ] (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V)
    (h : ∀ j, constantCoeff (ψ (X j)) = 0) (f : MvPowerSeries σ V) : constantCoeff (ψ f) = constantCoeff f := by
  obtain ⟨k, hk⟩ := exists_decomp f
  have hC : ψ (C (constantCoeff f)) = C (constantCoeff f) := ψ.commutes _
  conv_lhs => rw [hk]
  simp [hC, h]

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_decomp f`. Establish `hC : ψ (C (constantCoeff f)) = C (constantCoeff f)` using `ψ.commutes _`. Establish `h1 : ∀ j, coeff (Finsupp.single j 1) f = constantCoeff (k j)`. Introduce `j`. Use `conv_lhs => rw [hk]`.

Rewrite using `[map_add, coeff_single_C, zero_add, map_sum]`. Rewrite using `[Finset.sum_congr rfl fun i _ => coeff_single_mul j (X i) (k i) (by simp)]`. Simplify using `[coeff_single_X]`. Use `conv_lhs => rw [hk]`. Rewrite using `[map_add, hC, map_add, coeff_single_C, zero_add, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, coeff_single_mul _ _ _ (h j), const_hom ψ h, h1, _root_.mul_comm]`.
-/
theorem coeff_hom [Fintype σ] (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V)
    (h : ∀ j, constantCoeff (ψ (X j)) = 0) (f : MvPowerSeries σ V) (q : τ) :
    coeff (Finsupp.single q 1) (ψ f) = ∑ j, coeff (Finsupp.single j 1) f * coeff (Finsupp.single q 1) (ψ (X j)) := by
  classical
  obtain ⟨k, hk⟩ := exists_decomp f
  have hC : ψ (C (constantCoeff f)) = C (constantCoeff f) := ψ.commutes _
  have h1 : ∀ j, coeff (Finsupp.single j 1) f = constantCoeff (k j) := by
    intro j
    conv_lhs => rw [hk]
    rw [map_add, coeff_single_C, zero_add, map_sum]
    rw [Finset.sum_congr rfl fun i _ => coeff_single_mul j (X i) (k i) (by simp)]
    simp [coeff_single_X]
  conv_lhs => rw [hk]
  rw [map_add, hC, map_add, coeff_single_C, zero_add, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coeff_single_mul _ _ _ (h j), const_hom ψ h, h1, _root_.mul_comm]

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Establish `h : ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j` using `⟨substAlgHom hs, fun j => substAlgHom_X hs j⟩`. Conclude with `⟨h.choose, h.choose_spec, fun f => by unfold evC; rw [dif_pos h]⟩`.
-/
theorem evC_hom [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0) :
    ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (X j) = a j) ∧ ∀ f, evC a f = ψ f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h : ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j :=
    ⟨substAlgHom hs, fun j => substAlgHom_X hs j⟩
  exact ⟨h.choose, h.choose_spec, fun f => by unfold evC; rw [dif_pos h]⟩

/- English proof (translation)
Take `⟨ψ, h1, h2⟩` from `evC_hom a ha`. Rewrite using `[h2, const_hom ψ fun j => by rw [h1, ha]]`.
-/
theorem const_evC [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0)
    (f : MvPowerSeries σ V) : constantCoeff (evC a f) = constantCoeff f := by
  obtain ⟨ψ, h1, h2⟩ := evC_hom a ha
  rw [h2, const_hom ψ fun j => by rw [h1, ha]]

/- English proof (translation)
Take `⟨ψ, h1, h2⟩` from `evC_hom a ha`. Rewrite using `[h2, coeff_hom ψ fun j => by rw [h1, ha]]`. Simplify using `only [h1]`.
-/
theorem coeff_evC [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0)
    (f : MvPowerSeries σ V) (q : τ) :
    coeff (Finsupp.single q 1) (evC a f) = ∑ j, coeff (Finsupp.single j 1) f * coeff (Finsupp.single q 1) (a j) := by
  obtain ⟨ψ, h1, h2⟩ := evC_hom a ha
  rw [h2, coeff_hom ψ fun j => by rw [h1, ha]]
  simp only [h1]

variable {d m : ℕ}

/- English proof (translation)
Establish `ha : ∀ p : Fin 2 × Fin d, constantCoeff ((![x, y] : Fin 2 → Pt V m d) p.1 p.2) = 0`. Introduce and unpack `⟨a, j⟩`. Use `fin_cases a`. Conclude with `hx j`. Conclude with `hy j`.

Use `⟨(const_evC _ ha _).trans (G.const i), fun q => (coeff_evC _ ha _ q).trans ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, PullbackSections.Pf.EigA.formal_group_coeff_first_linear, PullbackSections.Pf.EigA.formal_group_coeff_second_linear, ite_mul, _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem addV_lin (G : FGLaw V d) (x y : Pt V m d) (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) :
    constantCoeff (addV G.F x y i) = 0 ∧ ∀ q, coeff (Finsupp.single q 1) (addV G.F x y i) =
      coeff (Finsupp.single q 1) (x i) + coeff (Finsupp.single q 1) (y i) := by
  have ha : ∀ p : Fin 2 × Fin d, constantCoeff ((![x, y] : Fin 2 → Pt V m d) p.1 p.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    · exact hx j
    · exact hy j
  refine ⟨(const_evC _ ha _).trans (G.const i), fun q => (coeff_evC _ ha _ q).trans ?_⟩
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PullbackSections.Pf.EigA.formal_group_coeff_first_linear, PullbackSections.Pf.EigA.formal_group_coeff_second_linear, ite_mul, _root_.one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons x l ih`. Take `⟨h1, h2⟩` from `ih fun y hy => hl y (List.mem_cons_of_mem _ hy)`. Establish `hx` using `hl x List.mem_cons_self`.

Use `⟨fun i => (addV_lin G x _ hx h1 i).1, fun i q => ?_⟩` and prove the remaining obligations. Rewrite using `[List.foldr_cons, (addV_lin G x _ hx h1 i).2, h2, List.map_cons, List.sum_cons]`.
-/
theorem fold_lin (G : FGLaw V d) (l : List (Pt V m d)) (hl : ∀ x ∈ l, ∀ i, constantCoeff (x i) = 0) :
    (∀ i, constantCoeff (l.foldr (addV G.F) 0 i) = 0) ∧ ∀ i q, coeff (Finsupp.single q 1) (l.foldr (addV G.F) 0 i) =
      (l.map fun x => coeff (Finsupp.single q 1) (x i)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hx := hl x List.mem_cons_self
    refine ⟨fun i => (addV_lin G x _ hx h1 i).1, fun i q => ?_⟩
    rw [List.foldr_cons, (addV_lin G x _ hx h1 i).2, h2, List.map_cons, List.sum_cons]

/- English proof (translation)
Establish `ha : ∀ p : Fin 1 × Fin d, constantCoeff ((![pt V d j] : Fin 1 → Pt V m d) p.1 p.2) = 0`. Introduce and unpack `⟨a, j⟩`. Use `fin_cases a`. Simplify using `[pt]`. Use `⟨const_evC _ ha _, fun q => (coeff_evC _ ha _ q).trans ?_⟩` and prove the remaining obligations.

Take `⟨a, b⟩` from `q`. Rewrite using `[Fintype.sum_prod_type, Fin.sum_univ_one]`. Apply the tactic sequence `by_cases h : a = j <;> simp [pt, coeff_single_X, h]`.
-/
theorem compV_pt (φ : Pt V 1 d) (j : Fin m) (i : Fin d) :
    constantCoeff (compV φ (pt V d j) i) = constantCoeff (φ i) ∧
      ∀ q : Fin m × Fin d, coeff (Finsupp.single q 1) (compV φ (pt V d j) i) =
        if q.1 = j then coeff (Finsupp.single ((0 : Fin 1), q.2) 1) (φ i) else 0 := by
  have ha : ∀ p : Fin 1 × Fin d, constantCoeff ((![pt V d j] : Fin 1 → Pt V m d) p.1 p.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    simp [pt]
  refine ⟨const_evC _ ha _, fun q => (coeff_evC _ ha _ q).trans ?_⟩
  obtain ⟨a, b⟩ := q
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  by_cases h : a = j <;> simp [pt, coeff_single_X, h]

variable {O : Type} [CommRing O] [StarRing O]

/- English proof (translation)
Unfold `matV`. Rewrite using `[(fold_lin B.G _ ?_).2, List.map_ofFn, List.sum_ofFn]`. Simplify using `only [Function.comp, (compV_pt _ _ _).2]`. Simplify using the standard rewrite rules. Introduce `y hy i`.

Take `⟨j, rfl⟩` from `List.mem_ofFn.1 hy`. Rewrite using `[(compV_pt _ _ _).1, B.A.const]`.
-/
theorem coeff_matV (B : FB V d O) {n : ℕ} (p : Matrix (Fin n) (Fin n) O) (x q : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (matV B p (fun j => pt V (n := n) d j) x.1 x.2) =
      coeff (Finsupp.single ((0 : Fin 1), q.2) 1) (B.A.act (p x.1 q.1) x.2) := by
  unfold matV
  rw [(fold_lin B.G _ ?_).2, List.map_ofFn, List.sum_ofFn]
  · simp only [Function.comp, (compV_pt _ _ _).2]
    simp
  · intro y hy i
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    rw [(compV_pt _ _ _).1, B.A.const]

end Series

/- English proof (translation)
Set `U : Matrix (Fin d) L K` to `Matrix.of fun j ℓ => u ℓ j`. Set `W : Matrix L (Fin d) K` to `Matrix.of fun ℓ t => (hb (Pi.single t 1)).exists.choose ℓ`. Establish `hUW : U * W = 1`. Use extensionality with `j t`. Use `(hb (Pi.single t 1)).exists.choose_spec j` as an intermediate fact.

Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [U, W, Matrix.of_apply]`. Rewrite using `[Finset.sum_congr rfl fun ℓ _ => _root_.mul_comm _ _, this, Pi.single_apply]`. Establish `hWU : W * U = 1`. Establish `h3 : U * (W * U) = U * (1 : Matrix L L K)` using `by rw [← Matrix.mul_assoc, hUW, Matrix.one_mul, Matrix.mul_one]`.

Use extensionality with `ℓ ℓ'`. Use `(hb fun j => (U * (1 : Matrix L L K)) j ℓ').unique (y₁ := fun ℓ => (W * U) ℓ ℓ') (y₂ := fun ℓ => (1 : Matrix L L K) ℓ ℓ') (fun j => by` as an intermediate fact. Rewrite using `[← h3, Matrix.mul_apply (M := U)]`. Conclude with `Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _)`. Use the proof step `(fun j => by`.

Rewrite using `[Matrix.mul_apply (M := U)]`. Conclude with `Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _)`. Conclude with `congrFun this ℓ`. Establish `h1 : ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) = 1`. Rewrite using `[← Matrix.mul_kronecker_mul, hUW, Matrix.mul_one, Matrix.one_kronecker_one]`.

Establish `h2 : ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) = 1`. Rewrite using `[← Matrix.mul_kronecker_mul, hWU, Matrix.mul_one, Matrix.one_kronecker_one]`. Establish `h3 : (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) = ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * Matrix.blockDiagonal fun ℓ => (s ℓ).mapMatrix p`. Use extensionality with `⟨i, a⟩ ⟨j, ℓ⟩`. Use `congrFun (he ℓ (p i j)) a` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this`. Simplify using `only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply, U, Matrix.blockDiagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero, _root_.one_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Fi …`. Rewrite using `[this, _root_.mul_comm]`. Both sides reduce to the same expression. Establish `h4 : (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2) = ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * (Matrix.blockDiagonal fun ℓ => (s ℓ).mapMatrix p) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W)`.

Rewrite using `[← h3, Matrix.mul_assoc, h1, Matrix.mul_one]`. Rewrite using `[h4, Matrix.det_conj_of_mul_eq_one h1 h2, Matrix.det_blockDiagonal]`. Conclude with `Finset.prod_congr rfl fun ℓ _ => ((s ℓ).map_det p).symm`.
-/
theorem det_blocks {K O L : Type} [CommRing K] [CommRing O] [Fintype L] {d n : ℕ} (M : O → Matrix (Fin d) (Fin d) K)
    (p : Matrix (Fin n) (Fin n) O) (s : L → O →+* K) (u : L → Fin d → K)
    (he : ∀ ℓ a, (M a).mulVec (u ℓ) = s ℓ a • u ℓ)
    (hb : ∀ v : Fin d → K, ∃! a : L → K, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) :
    (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2).det = ∏ ℓ, s ℓ p.det := by
  classical
  let U : Matrix (Fin d) L K := Matrix.of fun j ℓ => u ℓ j
  let W : Matrix L (Fin d) K := Matrix.of fun ℓ t => (hb (Pi.single t 1)).exists.choose ℓ
  have hUW : U * W = 1 := by
    ext j t
    have := (hb (Pi.single t 1)).exists.choose_spec j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [U, W, Matrix.of_apply]
    rw [Finset.sum_congr rfl fun ℓ _ => _root_.mul_comm _ _, this, Pi.single_apply]
  have hWU : W * U = 1 := by
    have h3 : U * (W * U) = U * (1 : Matrix L L K) := by rw [← Matrix.mul_assoc, hUW, Matrix.one_mul, Matrix.mul_one]
    ext ℓ ℓ'
    have := (hb fun j => (U * (1 : Matrix L L K)) j ℓ').unique (y₁ := fun ℓ => (W * U) ℓ ℓ')
      (y₂ := fun ℓ => (1 : Matrix L L K) ℓ ℓ')
      (fun j => by
        rw [← h3, Matrix.mul_apply (M := U)]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _)
      (fun j => by
        rw [Matrix.mul_apply (M := U)]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _)
    exact congrFun this ℓ
  have h1 : ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hUW, Matrix.mul_one, Matrix.one_kronecker_one]
  have h2 : ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hWU, Matrix.mul_one, Matrix.one_kronecker_one]
  have h3 : (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) =
      ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * Matrix.blockDiagonal fun ℓ => (s ℓ).mapMatrix p := by
    ext ⟨i, a⟩ ⟨j, ℓ⟩
    have := congrFun (he ℓ (p i j)) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply, U,
      Matrix.blockDiagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero, _root_.one_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [this, _root_.mul_comm]
    rfl
  have h4 : (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2) =
      ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * (Matrix.blockDiagonal fun ℓ => (s ℓ).mapMatrix p) *
        ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) := by
    rw [← h3, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [h4, Matrix.det_conj_of_mul_eq_one h1 h2, Matrix.det_blockDiagonal]
  exact Finset.prod_congr rfl fun ℓ _ => ((s ℓ).map_det p).symm

/- English proof (translation)
Introduce `V _ _ _ _ _ d O _ _ B K _ _ _ n p Ty _ r σ u he hb`. Establish `h` using `det_blocks (dAct K B) p (fun ℓ : Σ τ : Ty, Fin (r τ) => σ ℓ.1) u he hb`. Rewrite `h` using `[Fintype.prod_sigma]`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h`. Rewrite using `[← h, jacM, RingHom.map_det]`.

Use `congr 1`. Use extensionality with `x q`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, coeff_matV]`. Use `show _ = coeff _ (MvPowerSeries.map (algebraMap V K) _)`. Rewrite using `[coeff_map]`.
-/
theorem jacM_eq_prod : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (n : ℕ) (p : Matrix (Fin n) (Fin n) O) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ v : Fin d → K, ∃! a : (Σ τ : Ty, Fin (r τ)) → K, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) → algebraMap V K (jacM B p) = ∏ τ, σ τ p.det ^ r τ := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ n p Ty _ r σ u he hb
  have h := det_blocks (dAct K B) p (fun ℓ : Σ τ : Ty, Fin (r τ) => σ ℓ.1) u he hb
  rw [Fintype.prod_sigma] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h, jacM, RingHom.map_det]
  congr 1
  ext x q
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, coeff_matV]
  show _ = coeff _ (MvPowerSeries.map (algebraMap V K) _)
  rw [coeff_map]

end GlobalTheory.JacVal
