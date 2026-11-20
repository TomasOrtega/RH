import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PeriodMapPresentation
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

noncomputable section

namespace GlobalTheory.PeriodCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Use `forall_congr' fun τ => ?_` and prove the remaining obligations. Unfold `sigMult`. Apply the tactic sequence `by_cases h : τ (H.rt : E) = H.rt0 <;> simp [h]`.
-/
theorem isTypeFn_iff (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) :
    Tor.IsTypeFn H D.p D.q ty ↔ IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D ty := by
  refine forall_congr' fun τ => ?_
  unfold sigMult
  by_cases h : τ (H.rt : E) = H.rt0 <;> simp [h]

/- English proof (translation)
Set `κ` to `Σ τ : E →+* ℂ, Fin (sigMult D τ)`. Set `ε` to `Fintype.equivFin κ`. Establish `h0 : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D (fun k => (ε.symm k).1)` using `fun τ => by`. Rewrite using `[Nat.card_congr (ε.symm.subtypeEquiv (q := fun x : κ => x.1 = τ) fun _ => Iff.rfl), Nat.card_congr (Equiv.sigmaSubtype τ)]`. Simplify using the standard rewrite rules.

Take `⟨e, he⟩` from `PeriodNonempty.exists_equiv_of_sum_eq ty (fun k => (ε.symm k).1) fun a => by`. Rewrite using `[h, PeriodNonempty.sum_type H ((isTypeFn_iff D _).2 h0)]`. Both sides reduce to the same expression. Introduce `τ`. Rewrite using `[← h0 τ]`.

Conclude with `Nat.card_congr (e.subtypeEquiv fun i => by rw [← he i])`.
-/
theorem isTypeFn_of_sum (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = sigTrace D a) : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D ty := by
  classical
  let κ := Σ τ : E →+* ℂ, Fin (sigMult D τ)
  let ε := Fintype.equivFin κ
  have h0 : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D (fun k => (ε.symm k).1) := fun τ => by
    rw [Nat.card_congr (ε.symm.subtypeEquiv (q := fun x : κ => x.1 = τ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype τ)]
    simp
  obtain ⟨e, he⟩ := PeriodNonempty.exists_equiv_of_sum_eq ty (fun k => (ε.symm k).1) fun a => by
    rw [h, PeriodNonempty.sum_type H ((isTypeFn_iff D _).2 h0)]
    rfl
  intro τ
  rw [← h0 τ]
  exact Nat.card_congr (e.subtypeEquiv fun i => by rw [← he i])

/- English proof (translation)
Use `haveI := D.fin`. Use `haveI := D.proj`. Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Use `haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem finiteDimensional (D : Datum H) : Module.Finite ℤ D.La ∧ Module.Free ℤ D.La := by
  haveI := D.fin
  haveI := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Establish `hinj : Function.Injective (J + J')`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Establish `h1` using `hp x h0`.

Establish `h2` using `hp' x h0`. Establish `h3 : B ((J + J') x) x = 0` using `by rw [hx]; simp`. Simplify using `only [LinearMap.add_apply, map_add] at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Set `T` to `LinearEquiv.ofInjectiveEndo _ hinj`.

Establish `hT : ∀ x, T x = J x + J' x` using `fun _ => rfl`. Establish `hA1 : ∀ x, J (A x) = A (J x)` using `fun x => LinearMap.congr_fun hA x`. Establish `hA2 : ∀ x, J' (A x) = A (J' x)` using `fun x => LinearMap.congr_fun hA' x`. Rewrite using `[← LinearMap.trace_conj' (J ∘ₗ A) T]`. Use `congr 1`.

Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `T.surjective y`. Rewrite using `[LinearEquiv.conj_apply_apply, T.symm_apply_apply, hT, hT]`. Simplify using `only [LinearMap.comp_apply, map_add, ← hA1, ← hA2, hJ, hJ']`. Normalize the expressions using the abelian group laws.
-/
theorem trace_eq_of_pos {W : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : LinearMap.BilinForm ℝ W) (J J' A : W →ₗ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (hJ' : ∀ x, J' (J' x) = -x)
    (hp : ∀ x, x ≠ 0 → 0 < B (J x) x) (hp' : ∀ x, x ≠ 0 → 0 < B (J' x) x)
    (hA : J ∘ₗ A = A ∘ₗ J) (hA' : J' ∘ₗ A = A ∘ₗ J') :
    LinearMap.trace ℝ W (J ∘ₗ A) = LinearMap.trace ℝ W (J' ∘ₗ A) := by
  have hinj : Function.Injective (J + J') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 := hp' x h0
    have h3 : B ((J + J') x) x = 0 := by rw [hx]; simp
    simp only [LinearMap.add_apply, map_add] at h3
    linarith
  let T := LinearEquiv.ofInjectiveEndo _ hinj
  have hT : ∀ x, T x = J x + J' x := fun _ => rfl
  have hA1 : ∀ x, J (A x) = A (J x) := fun x => LinearMap.congr_fun hA x
  have hA2 : ∀ x, J' (A x) = A (J' x) := fun x => LinearMap.congr_fun hA' x
  rw [← LinearMap.trace_conj' (J ∘ₗ A) T]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := T.surjective y
  rw [LinearEquiv.conj_apply_apply, T.symm_apply_apply, hT, hT]
  simp only [LinearMap.comp_apply, map_add, ← hA1, ← hA2, hJ, hJ']
  abel

/- English proof (translation)
Take `⟨_, _⟩` from `finiteDimensional D`. Take `⟨J', k1, k2, -, k4, k5⟩` from `domain_nonempty D`. Use `⟨h1, h2, h3, h4, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[trace_eq_of_pos _ J J' _ h1 k1 h4 k4 (h2 a) (k2 a), k5]`.
-/
theorem mem_domain (D : Datum H) {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h1 : ∀ x, J (J x) = -x)
    (h2 : ∀ a : 𝓞 E, J ∘ₗ actR D a = actR D a ∘ₗ J)
    (h3 : ∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y)
    (h4 : ∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) : J ∈ domain D := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨J', k1, k2, -, k4, k5⟩ := domain_nonempty D
  refine ⟨h1, h2, h3, h4, fun a => ?_⟩
  rw [trace_eq_of_pos _ J J' _ h1 k1 h4 k4 (h2 a) (k2 a), k5]

/- English proof (translation)
Take `⟨_, _⟩` from `finiteDimensional D`. Take `⟨φ, -, h2, h3⟩` from `h`. Set `f : Module.End ℂ (Fin g → ℂ)` to `Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E))`. Establish `hf : ∀ z, f z = tyAct ty a z` using `fun z => by`. Use function extensionality and compare the values at `i`.

Simplify using `[f, tyAct, Matrix.mulVec_diagonal]`. Establish `ht : LinearMap.trace ℂ _ f = ∑ i, ty i (a : E)` using `by simp [f]`. Establish `e1 : φ.conj (actR D a) = f.restrictScalars ℝ`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearEquiv.conj_apply_apply, h3, φ.apply_symm_apply]`.

Conclude with `(hf y).symm`. Establish `e2 : φ.conj (J ∘ₗ actR D a) = (Complex.I • f).restrictScalars ℝ`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearEquiv.conj_apply_apply, LinearMap.comp_apply, h2, h3, φ.apply_symm_apply, ← hf]`. Both sides reduce to the same expression.

Rewrite using `[← LinearMap.trace_conj' _ φ, ← LinearMap.trace_conj' (J ∘ₗ actR D a) φ, e1, e2, PeriodNonempty.trace_real, PeriodNonempty.trace_real, map_smul, ht]`. Generalize the expression as in `∑ i, ty i (a : E) = t`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_of_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h : Presents D ty P J) (a : 𝓞 E) :
    ((LinearMap.trace ℝ _ (actR D a) : ℝ) : ℂ) / 2 -
      Complex.I * ((LinearMap.trace ℝ _ (J ∘ₗ actR D a) : ℝ) : ℂ) / 2 = ∑ i, ty i (a : E) := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨φ, -, h2, h3⟩ := h
  let f : Module.End ℂ (Fin g → ℂ) := Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E))
  have hf : ∀ z, f z = tyAct ty a z := fun z => by
    funext i; simp [f, tyAct, Matrix.mulVec_diagonal]
  have ht : LinearMap.trace ℂ _ f = ∑ i, ty i (a : E) := by simp [f]
  have e1 : φ.conj (actR D a) = f.restrictScalars ℝ := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, h3, φ.apply_symm_apply]
    exact (hf y).symm
  have e2 : φ.conj (J ∘ₗ actR D a) = (Complex.I • f).restrictScalars ℝ := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, h2, h3, φ.apply_symm_apply, ← hf]
    rfl
  rw [← LinearMap.trace_conj' _ φ, ← LinearMap.trace_conj' (J ∘ₗ actR D a) φ, e1, e2, PeriodNonempty.trace_real,
    PeriodNonempty.trace_real, map_smul, ht]
  generalize ∑ i, ty i (a : E) = t
  apply Complex.ext
  · simp
  · simp; ring

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun a b c => by simp [hermForm, add_dotProduct])
    (fun r a b => by simp [hermForm, smul_dotProduct])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun r a b => by
      simp only [hermForm, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul]
      simp)

/- English proof (translation)
Take `⟨_, _⟩` from `finiteDimensional D`. Take `⟨hlin, hinj, hdisc, hspan, Hm, -, hpos, hE⟩` from `h`. Set `ψ : ℝ ⊗[ℤ] D.La →ₗ[ℝ] (Fin g → ℂ)` to `P.toIntLinearMap.liftBaseChange ℝ`. Establish `hψ : ∀ (r : ℝ) x, ψ (r ⊗ₜ x) = r • P x` using `fun r x => by simp [ψ]`. Establish `hsurj : Function.Surjective ψ`.

Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨1 ⊗ₜ x, by simp [hψ]⟩`. Establish `hrk : Module.finrank ℝ (ℝ ⊗[ℤ] D.La) = Module.finrank ℝ (Fin g → ℂ)` using `by haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩`. Rewrite using `[Module.finrank_baseChange, (LinearEquiv.ofInjective P.toIntLinearMap hinj).finrank_eq, ZLattice.rank ℝ]`.

Set `φ` to `LinearEquiv.ofBijective ψ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj, hsurj⟩`. Establish `hφ : ∀ (r : ℝ) x, φ (r ⊗ₜ x) = r • P x` using `hψ`. Set `J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La` to `φ.symm.conj ((Complex.I • (LinearMap.id : Module.End ℂ (Fin g → ℂ))).restrictScalars ℝ)`. Establish `hJ : ∀ v, φ (J v) = Complex.I • φ v` using `fun v => by simp [J, LinearEquiv.conj_apply_apply]`. Establish `hact : ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v)` using `fun a v => by`.

Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => funext i`. Simplify using `[tyAct]`. Consider the case `add u v hu hv => funext i`. Simplify using `[tyAct, hu, hv, mul_add]`.

Consider the case `tmul r x`. Use function extensionality and compare the values at `i`. Establish `: actR D a (r ⊗ₜ x) = r ⊗ₜ (a • x)` using `rfl`. Simplify using `[this, hφ, tyAct, hlin, mul_left_comm]`. Establish `hB : ∀ x y, D.EF.baseChange ℝ x y = imForm Hm (φ x) (φ y)` using `fun x y => by`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']`. Consider the case `tmul r x`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y y' h h' => simp only [map_add, h, h']`. Consider the case `tmul r' y`. Establish `: imForm Hm (P x) (P y) = D.EF x y` using `hE x y`. Simplify using `only [hφ, map_smul, LinearMap.smul_apply, this, LinearMap.BilinForm.baseChange_tmul, smul_eq_mul, zsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨J, mem_domain D (fun x => φ.injective ?_) (fun a => LinearMap.ext fun v => φ.injective ?_) (fun x y => ?_) (fun x hx => ?_), φ, fun x => by simp [hφ], hJ, hact⟩` and prove the remaining obligations. Rewrite using `[hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]`. Simplify using `only [LinearMap.comp_apply, hJ, hact]`. Use function extensionality and compare the values at `i`.

Simplify using `[tyAct, mul_left_comm]`. Rewrite using `[hB, hB, hJ, hJ]`. Express the relevant statement in the definitionally equal form `(hermForm _ _ _).im = (hermForm _ _ _).im`. Simplify using `[hermForm, star_smul, Matrix.mulVec_smul, Matrix.mulVec_neg, ← mul_assoc]`. Rewrite using `[hB, hJ]`.

Use `hpos (φ x) (by simpa using hx)` as an intermediate fact. Express the relevant statement in the definitionally equal form `0 < (hermForm _ _ _).im`. Simplify `this` using `[hermForm, smul_dotProduct]`.
-/
theorem exists_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriod D ty P) : ∃ J ∈ domain D, Presents D ty P J := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, -, hpos, hE⟩ := h
  let ψ : ℝ ⊗[ℤ] D.La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hψ : ∀ (r : ℝ) x, ψ (r ⊗ₜ x) = r • P x := fun r x => by simp [ψ]
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [hψ]⟩
  have hrk : Module.finrank ℝ (ℝ ⊗[ℤ] D.La) = Module.finrank ℝ (Fin g → ℂ) := by
    haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc
    haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩
    rw [Module.finrank_baseChange, (LinearEquiv.ofInjective P.toIntLinearMap hinj).finrank_eq, ZLattice.rank ℝ]
  let φ := LinearEquiv.ofBijective ψ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj, hsurj⟩
  have hφ : ∀ (r : ℝ) x, φ (r ⊗ₜ x) = r • P x := hψ
  let J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
    φ.symm.conj ((Complex.I • (LinearMap.id : Module.End ℂ (Fin g → ℂ))).restrictScalars ℝ)
  have hJ : ∀ v, φ (J v) = Complex.I • φ v := fun v => by simp [J, LinearEquiv.conj_apply_apply]
  have hact : ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v) := fun a v => by
    induction v using TensorProduct.induction_on with
    | zero => funext i; simp [tyAct]
    | add u v hu hv => funext i; simp [tyAct, hu, hv, mul_add]
    | tmul r x =>
      funext i
      have : actR D a (r ⊗ₜ x) = r ⊗ₜ (a • x) := rfl
      simp [this, hφ, tyAct, hlin, mul_left_comm]
  have hB : ∀ x y, D.EF.baseChange ℝ x y = imForm Hm (φ x) (φ y) := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, h, h']
      | tmul r' y =>
        have : imForm Hm (P x) (P y) = D.EF x y := hE x y
        simp only [hφ, map_smul, LinearMap.smul_apply, this, LinearMap.BilinForm.baseChange_tmul, smul_eq_mul,
          zsmul_eq_mul]
        ring
  refine ⟨J, mem_domain D (fun x => φ.injective ?_) (fun a => LinearMap.ext fun v => φ.injective ?_)
    (fun x y => ?_) (fun x hx => ?_), φ, fun x => by simp [hφ], hJ, hact⟩
  · rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · simp only [LinearMap.comp_apply, hJ, hact]
    funext i; simp [tyAct, mul_left_comm]
  · rw [hB, hB, hJ, hJ]
    change (hermForm _ _ _).im = (hermForm _ _ _).im
    simp [hermForm, star_smul, Matrix.mulVec_smul, Matrix.mulVec_neg, ← mul_assoc]
  · rw [hB, hJ]
    have := hpos (φ x) (by simpa using hx)
    change 0 < (hermForm _ _ _).im
    simpa [hermForm, smul_dotProduct] using this

/- English proof (translation)
Take `⟨_, _⟩` from `finiteDimensional D`. Take `⟨-, -, hinv, hpos, -⟩` from `hJ`. Take `⟨e, hP, heJ, heρ⟩` from `h`. Set `b` to `Module.Free.chooseBasis ℤ D.La`. Set `c` to `(b.baseChange ℝ).map e`.

Establish `hc : ∀ i, c i = P (b i)` using `fun i => by simp [c, hP]`. Establish `hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup`. Establish `h1 : Set.range c = P.toIntLinearMap '' Set.range b`. Rewrite using `[← Set.range_comp]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `hc i`. Rewrite using `[h1, ← Submodule.map_span, b.span_eq]`. Use extensionality with `z`. Simplify using the standard rewrite rules.

Use `⟨fun a x i => ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hP, ← hP]`. Conclude with `congrFun (heρ a (1 ⊗ₜ x)) i`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Rewrite `hx` using `[← hP, e.map_eq_zero_iff]`. Apply `b.ext_elem` to reduce the goal to its premises. Introduce `i`. Use `congrArg (fun v => (b.baseChange ℝ).repr v i) hx` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hrange]`. Use `infer_instance`. Rewrite using `[eq_top_iff, ← c.span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `⟨b i, (hc i).symm⟩`. Establish `halt0 : ∀ x y, D.EF x y = -D.EF y x` using `fun x y => by`. Use `D.alt (x + y)` as an intermediate fact. Simplify using `only [map_add, LinearMap.add_apply, D.alt] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x` using `fun x y => by`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `tmul r x`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `tmul r' y => simp [halt0 x y, mul_comm]`. Establish `hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z)` using `fun z => by`. Rewrite using `[e.symm_apply_eq, heJ, e.apply_symm_apply]`. Take `⟨Hm, h1, h2, h3⟩` from `PeriodNonempty.exists_herm ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap) (fun x y => halt _ _) (fun x y => by simp [hs, hinv]) (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))`. Use `⟨Hm, h1, h2, fun x y => ?_⟩` and prove the remaining obligations.

Rewrite using `[h3]`. Simplify using `[← hP]`.
-/
theorem isPeriod_of_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (hJ : J ∈ domain D) (h : Presents D ty P J) : IsPeriod D ty P := by
  classical
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨-, -, hinv, hpos, -⟩ := hJ
  obtain ⟨e, hP, heJ, heρ⟩ := h
  let b := Module.Free.chooseBasis ℤ D.La
  let c := (b.baseChange ℝ).map e
  have hc : ∀ i, c i = P (b i) := fun i => by simp [c, hP]
  have hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
    have h1 : Set.range c = P.toIntLinearMap '' Set.range b := by
      rw [← Set.range_comp]; congr 1; funext i; exact hc i
    rw [h1, ← Submodule.map_span, b.span_eq]
    ext z; simp
  refine ⟨fun a x i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP, ← hP]
    exact congrFun (heρ a (1 ⊗ₜ x)) i
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← hP, e.map_eq_zero_iff] at hx
    apply b.ext_elem
    intro i
    have := congrArg (fun v => (b.baseChange ℝ).repr v i) hx
    simpa using this
  · rw [hrange]; infer_instance
  · rw [eq_top_iff, ← c.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · have halt0 : ∀ x y, D.EF x y = -D.EF y x := fun x y => by
      have := D.alt (x + y)
      simp only [map_add, LinearMap.add_apply, D.alt] at this
      linarith
    have halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x := fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
      | tmul r x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
        | tmul r' y => simp [halt0 x y, mul_comm]
    have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
      rw [e.symm_apply_eq, heJ, e.apply_symm_apply]
    obtain ⟨Hm, h1, h2, h3⟩ := PeriodNonempty.exists_herm
      ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap)
      (fun x y => halt _ _) (fun x y => by simp [hs, hinv])
      (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
    refine ⟨Hm, h1, h2, fun x y => ?_⟩
    rw [h3]
    simp [← hP]

/- English proof (translation)
Take `⟨J, hJ, hP⟩` from `exists_presents h`. Conclude with `(isTypeFn_iff D ty).2 (isTypeFn_of_sum D ty fun a => (trace_of_presents hP a).symm.trans (hJ.2.2.2.2 a))`.
-/
theorem isTypeFn_of_isPeriod {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriod D ty P) : Tor.IsTypeFn H D.p D.q ty := by
  obtain ⟨J, hJ, hP⟩ := exists_presents h
  exact (isTypeFn_iff D ty).2 (isTypeFn_of_sum D ty fun a => (trace_of_presents hP a).symm.trans (hJ.2.2.2.2 a))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨(isTypeFn_iff D ty).1 (isTypeFn_of_isPeriod h), exists_presents h⟩, fun ⟨_, _, hJ, hP⟩ => isPeriod_of_presents hJ hP⟩`.
-/
theorem isPeriod_iff (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) :
    IsPeriod D ty P ↔ IsPeriodMap D ty P :=
  ⟨fun h => ⟨(isTypeFn_iff D ty).1 (isTypeFn_of_isPeriod h), exists_presents h⟩,
    fun ⟨_, _, hJ, hP⟩ => isPeriod_of_presents hJ hP⟩

/- English proof (translation)
Simplify using `only [IsHolPeriods, IsHolFamily, isPeriod_iff]`.
-/
theorem isHolPeriods_iff (D : Datum H) {g m : ℕ} (ty : Fin g → (E →+* ℂ)) (B : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) : IsHolPeriods D ty B P ↔ IsHolFamily D ty B P := by
  simp only [IsHolPeriods, IsHolFamily, isPeriod_iff]

end Period

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨by simpa using (h ⊤ 0).1, fun U b hb hU => ?_⟩` and prove the remaining obligations. Establish `hn : {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∈ 𝓝 b` using `(h U 0).1.mem_nhds ⟨hb, hU⟩`. Conclude with `⟨Filter.Eventually.filter_mono nhdsWithin_le_nhds (Filter.mem_of_superset hn fun _ hx => hx.2), fun f => ((h U f).2.differentiableAt hn).differentiableWithinAt⟩`.

Introduce and unpack `⟨hB, h⟩ U f`. Use `⟨isOpen_iff_mem_nhds.2 fun b hb => ?_, fun b hb => ((h U b hb.1 hb.2).2 f).mono fun _ hx => hx.1⟩` and prove the remaining obligations. Use `(h U b hb.1 hb.2).1` as an intermediate fact. Rewrite `this` using `[hB.nhdsWithin_eq hb.1]`. Conclude with `Filter.inter_mem (hB.mem_nhds hb.1) this`.
-/
theorem isHolTo_iff (B : Set V) (y : V → (Sp ℂ ⟶ X)) : IsHolTo B y ↔ IsOpen B ∧ HolOn B y := by
  constructor
  · intro h
    refine ⟨by simpa using (h ⊤ 0).1, fun U b hb hU => ?_⟩
    have hn : {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∈ 𝓝 b := (h U 0).1.mem_nhds ⟨hb, hU⟩
    exact ⟨Filter.Eventually.filter_mono nhdsWithin_le_nhds (Filter.mem_of_superset hn fun _ hx => hx.2),
      fun f => ((h U f).2.differentiableAt hn).differentiableWithinAt⟩
  · rintro ⟨hB, h⟩ U f
    refine ⟨isOpen_iff_mem_nhds.2 fun b hb => ?_, fun b hb => ((h U b hb.1 hb.2).2 f).mono fun _ hx => hx.1⟩
    have := (h U b hb.1 hb.2).1
    rw [hB.nhdsWithin_eq hb.1] at this
    exact Filter.inter_mem (hB.mem_nhds hb.1) this

/- English proof (translation)
Rewrite using `[isHolTo_iff, and_iff_right hB]`.
-/
theorem isHolTo_iff_of_isOpen {B : Set V} (hB : IsOpen B) (y : V → (Sp ℂ ⟶ X)) : IsHolTo B y ↔ HolOn B y := by
  rw [isHolTo_iff, and_iff_right hB]

/- English proof (translation)
Use `and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => ?_` and prove the remaining obligations. Establish `hU0 : ⊤ ≤ F 0 ⁻¹ᵁ U`. Rewrite using `[← h0]`. Conclude with `fun x _ => hU (x := _) trivial`. Take `⟨h1, h2⟩` from `hF U 0 (mem_of_mem_nhds hB) hU0`.

Rewrite `h1` using `[nhdsWithin_eq_nhds.2 hB]`. Establish `hl : HasDerivAt (fun t : ℂ => t • w) w 0` using `by simpa using (hasDerivAt_id (0 : ℂ)).smul_const w`. Establish `hd : ∀ f : Γ(X, U), HasDerivAt (fun t : ℂ => valAt' (F (t • w)) U f) (fderiv ℂ (fun z => valAt' (F z) U f) 0 w) 0` using `fun f => HasFDerivAt.comp_hasDerivAt_of_eq (l := fun z => valAt' (F z) U f) (f := fun t : ℂ => t • w) 0 ((h2 f).differentiableAt hB).hasFDerivAt hl (zero_smul ℂ w).symm`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨Filter.Tendsto.eventually (f := fun t : ℂ => t • w) (by simpa using hl.continuousAt.tendsto) h1, fun f => ?_⟩` and prove the remaining obligations. Use `hd f` as an intermediate fact. Rewrite `this` using `[← h f]`. Then use the resulting hypothesis. Conclude with `fun h f => (h.2 f).unique (hd f)`.
-/
theorem isDerivAt0_iff {g : ℕ} {F : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {B : Set (Fin g → ℂ)} (hB : B ∈ 𝓝 0) (hF : HolOn B F)
    (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 F w v ↔ IsDerivAlong F w v := by
  refine and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => ?_
  have hU0 : ⊤ ≤ F 0 ⁻¹ᵁ U := by
    rw [← h0]
    exact fun x _ => hU (x := _) trivial
  obtain ⟨h1, h2⟩ := hF U 0 (mem_of_mem_nhds hB) hU0
  rw [nhdsWithin_eq_nhds.2 hB] at h1
  have hl : HasDerivAt (fun t : ℂ => t • w) w 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
  have hd : ∀ f : Γ(X, U), HasDerivAt (fun t : ℂ => valAt' (F (t • w)) U f)
      (fderiv ℂ (fun z => valAt' (F z) U f) 0 w) 0 := fun f =>
    HasFDerivAt.comp_hasDerivAt_of_eq (l := fun z => valAt' (F z) U f) (f := fun t : ℂ => t • w) 0
      ((h2 f).differentiableAt hB).hasFDerivAt hl (zero_smul ℂ w).symm
  constructor
  · intro h
    refine ⟨Filter.Tendsto.eventually (f := fun t : ℂ => t • w) (by simpa using hl.continuousAt.tendsto) h1,
      fun f => ?_⟩
    have := hd f
    rwa [← h f] at this
  · exact fun h f => (h.2 f).unique (hd f)

/- English proof (translation)
Establish `h1 : (spMap φ).appLE ⊤ ⊤ h = (spMap φ).appTop` using `Scheme.Hom.appLE_eq_app _`. Rewrite using `[h1]`. Conclude with `congrArg (fun k => k.hom f) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))`.
-/
theorem val_spMap {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (f : Γ(Sp A, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (((spMap φ).appLE ⊤ ⊤ h).hom f) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom f) := by
  have h1 : (spMap φ).appLE ⊤ ⊤ h = (spMap φ).appTop := Scheme.Hom.appLE_eq_app _
  rw [h1]
  exact congrArg (fun k => k.hom f) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

open Classical in

def jump (z : Fin 1 → ℂ) : Sp ℂ ⟶ Sp ℂ := spMap (if z = 0 then RingHom.id ℂ else starRingEnd ℂ)

end Hol

section Theta

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {g m : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩`.
-/
theorem le_pull_iff {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (x : Sp ℂ ⟶ Y) (j : (L.pull f).ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) :=
  ⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

/- English proof (translation)
Establish `hf : ∀ b z, fibrePt (ex b z) ≫ pullback.fst G.hom (y b) = (ex b z).left` using `fun b z => pullback.lift_fst ..`. Establish `hs : ∀ b z, fibrePt (ex b z) ≫ pullback.snd G.hom (y b) = 𝟙 _` using `fun b z => pullback.lift_snd ..`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨fr, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩`. Use `⟨h1, h2, fun j p => fr j p.1 p.2, h3, fun j b z hb => h4 j b hb z, fun j j' b z hb => h5 j j' b hb z, fun j b hb hj => h6 (fun _ => j) b hb ((le_pull_iff _ _ _ _).2 (by rw [← h2 b hb]; exact hj)), fun b hb => ?_⟩` and prove the remaining obligations.

Take `⟨s, hsec⟩` from `h7 b hb`. Use `⟨s, fun j z x hx hx' hj => ?_⟩` and prove the remaining obligations. Take `rfl : x = fibrePt (ex b z)` from `pullback.hom_ext (hx.trans (hf b z).symm) (hx'.trans (hs b z).symm)`. Conclude with `hsec (fun _ => j) z ((le_pull_iff _ _ _ _).2 (by rw [hf]; exact hj))`. Introduce and unpack `⟨h1, h2, fr, h3, h4, h5, h6, h7⟩`.

Use `⟨fun j b z => fr j (b, z), ⟨h1, h2, h3, fun j b hb z => h4 j b z hb, fun j j' b hb z => h5 j j' b z hb, fun j b hb hj => h6 (j PUnit.unit) b hb ?_⟩, fun b hb => ?_⟩` and prove the remaining obligations. Use `(le_pull_iff _ _ _ _).1 hj` as an intermediate fact. Rewrite `this` using `[← h2 b hb]`. Conclude with `this`. Take `⟨s, hsec⟩` from `h7 b hb`.

Use `⟨s, fun j z hj => hsec (j PUnit.unit) z _ (hf b z) (hs b z) ?_⟩` and prove the remaining obligations. Use `(le_pull_iff _ _ _ _).1 hj` as an intermediate fact. Rewrite `this` using `[hf]`. Conclude with `this`.
-/
theorem isThetaFamily_iff (L : RigLB G) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ S))
    (ex : ∀ b : Fin m → ℂ, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) :
    IsThetaFamily L B y ex θ ↔
      HolOn (B ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun p => ((ex p.1 p.2).left : Sp ℂ ⟶ G.left)) ∧
      (∀ b ∈ B, (ex b 0).left = y b ≫ eSec G) ∧ Tor.IsThetaFrame L B y (fun b z => (ex b z).left) θ := by
  have hf : ∀ b z, fibrePt (ex b z) ≫ pullback.fst G.hom (y b) = (ex b z).left := fun b z => pullback.lift_fst ..
  have hs : ∀ b z, fibrePt (ex b z) ≫ pullback.snd G.hom (y b) = 𝟙 _ := fun b z => pullback.lift_snd ..
  constructor
  · rintro ⟨fr, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
    refine ⟨h1, h2, fun j p => fr j p.1 p.2, h3, fun j b z hb => h4 j b hb z, fun j j' b z hb => h5 j j' b hb z,
      fun j b hb hj => h6 (fun _ => j) b hb ((le_pull_iff _ _ _ _).2 (by rw [← h2 b hb]; exact hj)), fun b hb => ?_⟩
    obtain ⟨s, hsec⟩ := h7 b hb
    refine ⟨s, fun j z x hx hx' hj => ?_⟩
    obtain rfl : x = fibrePt (ex b z) := pullback.hom_ext (hx.trans (hf b z).symm) (hx'.trans (hs b z).symm)
    exact hsec (fun _ => j) z ((le_pull_iff _ _ _ _).2 (by rw [hf]; exact hj))
  · rintro ⟨h1, h2, fr, h3, h4, h5, h6, h7⟩
    refine ⟨fun j b z => fr j (b, z), ⟨h1, h2, h3, fun j b hb z => h4 j b z hb, fun j j' b hb z => h5 j j' b z hb,
      fun j b hb hj => h6 (j PUnit.unit) b hb ?_⟩, fun b hb => ?_⟩
    · have := (le_pull_iff _ _ _ _).1 hj
      rw [← h2 b hb] at this
      exact this
    · obtain ⟨s, hsec⟩ := h7 b hb
      refine ⟨s, fun j z hj => hsec (j PUnit.unit) z _ (hf b z) (hs b z) ?_⟩
      have := (le_pull_iff _ _ _ _).1 hj
      rw [hf] at this
      exact this

end Theta

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)

/- English proof (translation)
Establish `h` using `(Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2`. Use `isDerivAt0_iff Filter.univ_mem ((isHolTo_iff _ _).1 fun U f => ⟨?_, ?_⟩).2 w v` and prove the remaining obligations. Simplify using `using (h U f).1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)`. Conclude with `(h U f).2.comp (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop) fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩`.
-/
theorem isDerivAt0_ex_iff {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left) :
    IsDerivAt0 (fun z => (Fu.ex i P z).left) w v ↔ IsDerivAlong (fun z => (Fu.ex i P z).left) w v := by
  have h := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  refine isDerivAt0_iff Filter.univ_mem ((isHolTo_iff _ _).1 fun U f => ⟨?_, ?_⟩).2 w v
  · simpa using (h U f).1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
  · exact (h U f).2.comp (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
      fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩

end Family

end GlobalTheory.PeriodCompare
