import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.SplitJump

open Module TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
/- English proof (translation)
Proceed by induction on `b, h using Int.le_induction with`. Consider the case `base => exact le_rfl`. Consider the case `succ b _ ih => exact (PD.Fil_anti b).trans ih`.
-/
theorem _root_.GlobalTheory.SplitJump.fil_mono {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  induction b, h using Int.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact (PD.Fil_anti b).trans ih

open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h1 : (1 : BdR) ∈ PD.Fil 1`. Use `(PD.Fil 1).smul_mem k⁻¹ hk` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hne, map_one]`. Then use the resulting hypothesis. Use `PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h1` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Conclude with `PD.not_mem_filtration_two (by simpa using this)`.
-/
theorem _root_.GlobalTheory.SplitJump.eq_zero_of_mem_fil_one (k : K) (hk : algebraMap K BdR k ∈ PD.Fil 1) :
    k = 0 := by
  by_contra hne
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem k⁻¹ hk
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hne, map_one] at this
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h1
  rw [mul_one] at this
  exact PD.not_mem_filtration_two (by simpa using this)

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)

def coord (BdR : Type) [CommRing BdR] [Algebra Qp BdR] : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin n → BdR) :=
  (TensorProduct.comm Qp V BdR).trans ((Algebra.TensorProduct.basis BdR e).equivFun.restrictScalars Qp)

open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V) in
omit [Field LL] [Algebra Qp LL] [Module LL V] [IsScalarTower Qp LL V] in
/- English proof (translation)
Simplify using `[_root_.GlobalTheory.SplitJump.coord, Algebra.TensorProduct.basis_repr_tmul, mul_comm]`.
-/
private lemma coord_tmul_eq_repr_mul (v : V) (b : BdR) (i : Fin n) :
    _root_.GlobalTheory.SplitJump.coord e BdR (v ⊗ₜ b) i = algebraMap Qp BdR (e.repr v i) * b := by
  simp [_root_.GlobalTheory.SplitJump.coord, Algebra.TensorProduct.basis_repr_tmul, mul_comm]

open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V) in
omit [Field LL] [Algebra Qp LL] [Module LL V] [IsScalarTower Qp LL V] in
/- English proof (translation)
Apply `(_root_.GlobalTheory.SplitJump.coord e BdR).injective` to reduce the goal to its premises. Use extensionality with `j`. Simplify using `[map_sum, coord_tmul_eq_repr_mul, Finsupp.single_apply, Pi.single_apply]`.
-/
private lemma sum_basis_tmul_coord_eq (y : V ⊗[Qp] BdR) :
    ∑ i, e i ⊗ₜ[Qp] _root_.GlobalTheory.SplitJump.coord e BdR y i = y := by
  apply (_root_.GlobalTheory.SplitJump.coord e BdR).injective
  ext j
  simp [map_sum, coord_tmul_eq_repr_mul, Finsupp.single_apply, Pi.single_apply]

open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V) in
/- English proof (translation)
Unfold `_root_.Formalism.WeaklyAdmissibleFiltrations.FilV`. Rewrite using `[LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩ i`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v f`. Rewrite using `[AlgebraTensorModule.map_tmul, LinearMap.id_apply, coord_tmul_eq_repr_mul]`. Rewrite using `[IsScalarTower.algebraMap_apply Qp K BdR, ← Algebra.smul_def]`. Conclude with `(PD.Fil a).smul_mem _ f.2`.

Consider the case `add z₁ z₂ h₁ h₂`. Rewrite using `[map_add, map_add]`. Conclude with `(PD.Fil a).add_mem h₁ h₂`. Introduce `h`. Use `⟨∑ i, e i ⊗ₜ[Qp] (⟨_root_.GlobalTheory.SplitJump.coord e BdR y i, h i⟩ : (PD.Fil a).restrictScalars Qp), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `conv_rhs => rw [← sum_basis_tmul_coord_eq e y]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.SplitJump.mem_filV (a : ℤ) (y : V ⊗[Qp] BdR) :
    y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a ↔ ∀ i, _root_.GlobalTheory.SplitJump.coord e BdR y i ∈ PD.Fil a := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨z, rfl⟩ i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      rw [AlgebraTensorModule.map_tmul, LinearMap.id_apply, coord_tmul_eq_repr_mul]
      rw [IsScalarTower.algebraMap_apply Qp K BdR, ← Algebra.smul_def]
      exact (PD.Fil a).smul_mem _ f.2
    | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact (PD.Fil a).add_mem h₁ h₂
  · intro h
    refine ⟨∑ i, e i ⊗ₜ[Qp]
      (⟨_root_.GlobalTheory.SplitJump.coord e BdR y i, h i⟩ : (PD.Fil a).restrictScalars Qp), ?_⟩
    rw [map_sum]
    conv_rhs => rw [← sum_basis_tmul_coord_eq e y]
    rfl

open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V) in
/- English proof (translation)
Unfold `_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => ext i`. Simplify using `[Matrix.mulVec, dotProduct]`. Consider the case `tmul v b`.

Use extensionality with `i`. Establish `hv : ρ g v = ∑ j, e.repr v j • ρ g (e j)` using `by conv_lhs => rw [← e.sum_repr v]`. Rewrite using `[map_sum]`. Simplify using `[LinearMap.map_smul_of_tower]`. Establish `hσ : ∀ r : Qp, PD.actdR g (algebraMap Qp BdR r) = algebraMap Qp BdR r`.

Introduce `r`. Rewrite using `[IsScalarTower.algebraMap_apply Qp K BdR, AlgEquiv.commutes]`. Simplify using `only [AlgebraTensorModule.map_tmul, coord_tmul_eq_repr_mul, Matrix.mulVec, dotProduct, Matrix.of_apply]`. Rewrite using `[hv, map_sum, Finset.sum_apply', map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hσ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]`. Express the relevant statement in the definitionally equal form `_ * PD.actdR g b = _`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x₁ x₂ h₁ h₂`. Rewrite using `[map_add, map_add, h₁, h₂, ← Matrix.mulVec_add]`.

Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.SplitJump.coord_act (g : G) (x : V ⊗[Qp] BdR) :
    _root_.GlobalTheory.SplitJump.coord e BdR (_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g x) =
      (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)).mulVec
        fun i => PD.actdR g (_root_.GlobalTheory.SplitJump.coord e BdR x i) := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR
  induction x using TensorProduct.induction_on with
  | zero => ext i; simp [Matrix.mulVec, dotProduct]
  | tmul v b =>
    ext i
    have hv : ρ g v = ∑ j, e.repr v j • ρ g (e j) := by
      conv_lhs => rw [← e.sum_repr v]
      rw [map_sum]
      simp [LinearMap.map_smul_of_tower]
    have hσ : ∀ r : Qp, PD.actdR g (algebraMap Qp BdR r) = algebraMap Qp BdR r := by
      intro r
      rw [IsScalarTower.algebraMap_apply Qp K BdR, AlgEquiv.commutes]
    simp only [AlgebraTensorModule.map_tmul, coord_tmul_eq_repr_mul, Matrix.mulVec, dotProduct,
      Matrix.of_apply]
    rw [hv, map_sum, Finset.sum_apply', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hσ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
    change _ * PD.actdR g b = _
    ring
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, ← Matrix.mulVec_add]
    congr 1
    ext i
    simp

open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V) in

/- English proof (translation)
Unfold `_root_.Formalism.WeaklyAdmissibleFiltrations.DdR at hy`. Establish `hfix : ∀ g, _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g y = y`. Introduce `g`. Use `(Submodule.mem_iInf _).1 hy g` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.

Conclude with `this`. Establish `hinv : ∀ i g, PD.actdR g ((W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y)) i) = (W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y)) i`. Introduce `i g`. Use `set M : Matrix (Fin n) (Fin n) BdR := Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)`. Use `set σ : BdR →+* BdR := (PD.actdR g : BdR ≃ₐ[K] BdR).toRingEquiv.toRingHom`.

Establish `hW'W : W' * W = 1` using `mul_eq_one_comm.1 hWW`. Establish `hmap : W'.map σ = W' * M`. Establish `h1 : W.map σ * W'.map σ = 1`. Rewrite using `[← Matrix.map_mul, hWW, Matrix.map_one _ (map_zero σ) (map_one σ)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc : M.mulVec (fun j => σ (_root_.GlobalTheory.SplitJump.coord e BdR y j)) = _root_.GlobalTheory.SplitJump.coord e BdR y`. Use `_root_.GlobalTheory.SplitJump.coord_act PD ρ e g y` as an intermediate fact. Rewrite `this` using `[hfix g]`. Conclude with `this.symm`. Express the relevant statement in the definitionally equal form `σ _ = _`.

Rewrite using `[RingHom.map_mulVec, hmap]`. Express the relevant statement in the definitionally equal form `(W' * M).mulVec (σ ∘ _root_.GlobalTheory.SplitJump.coord e BdR y) i = _`. Rewrite using `[← Matrix.mulVec_mulVec]`. Use `congr 2`. Use `choose k hk using fun i => PD.invdR _ fun g => hinv i g`.

Conclude with `⟨k, funext hk⟩`.
-/
theorem _root_.GlobalTheory.SplitJump.exists_coord (W W' : Matrix (Fin n) (Fin n) BdR) (hWW : W * W' = 1)
    (hg : ∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) *
      W.map (PD.actdR g) = W)
    (y : V ⊗[Qp] BdR) (hy : y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :
    ∃ k : Fin n → K, (fun i => algebraMap K BdR (k i)) =
      W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y) := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.DdR at hy
  have hfix : ∀ g, _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g y = y := by
    intro g
    have := (Submodule.mem_iInf _).1 hy g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  have hinv : ∀ i g, PD.actdR g ((W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y)) i) =
      (W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y)) i := by
    intro i g
    set M : Matrix (Fin n) (Fin n) BdR :=
      Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)
    set σ : BdR →+* BdR := (PD.actdR g : BdR ≃ₐ[K] BdR).toRingEquiv.toRingHom
    have hW'W : W' * W = 1 := mul_eq_one_comm.1 hWW
    have hmap : W'.map σ = W' * M := by
      have h1 : W.map σ * W'.map σ = 1 := by
        rw [← Matrix.map_mul, hWW, Matrix.map_one _ (map_zero σ) (map_one σ)]
      calc W'.map σ = (W' * W) * W'.map σ := by rw [hW'W, Matrix.one_mul]
        _ = W' * (M * W.map σ) * W'.map σ := by rw [show M * W.map σ = W from hg g]
        _ = W' * M * (W.map σ * W'.map σ) := by simp only [Matrix.mul_assoc]
        _ = W' * M := by rw [h1, Matrix.mul_one]
    have hc : M.mulVec (fun j => σ (_root_.GlobalTheory.SplitJump.coord e BdR y j)) =
        _root_.GlobalTheory.SplitJump.coord e BdR y := by
      have := _root_.GlobalTheory.SplitJump.coord_act PD ρ e g y
      rw [hfix g] at this
      exact this.symm
    change σ _ = _
    rw [RingHom.map_mulVec, hmap]
    change (W' * M).mulVec (σ ∘ _root_.GlobalTheory.SplitJump.coord e BdR y) i = _
    rw [← Matrix.mulVec_mulVec]
    congr 2
  choose k hk using fun i => PD.invdR _ fun g => hinv i g
  exact ⟨k, funext hk⟩

open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V) in

/- English proof (translation)
Establish `hK0 : ∀ c : K, algebraMap K BdR c ∈ PD.Fil 0` using `fun c => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `(PD.Fil 0).smul_mem c PD.one_mem`. Establish `hrec : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∃ k : Fin n → K, _root_.GlobalTheory.SplitJump.coord e BdR y = W.mulVec (fun i => algebraMap K BdR (k i)) ∧ (fun i => algebraMap K BdR (k i)) = W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y)`. Introduce `y hy`.

Take `⟨k, hk⟩` from `_root_.GlobalTheory.SplitJump.exists_coord PD ρ e W W' hWW hg y hy`. Use `⟨k, ?_, hk⟩` and prove the remaining obligations. Rewrite using `[hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]`. Establish `hlow : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∀ b : ℤ, b ≤ 0 → y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL` using `LL) (V := V) b := by`. Introduce `y hy b hb`.

Take `⟨k, hc, -⟩` from `hrec y hy`. Rewrite using `[_root_.GlobalTheory.SplitJump.mem_filV PD e]`. Introduce `i`. Apply `_root_.GlobalTheory.SplitJump.fil_mono PD hb` to reduce the goal to its premises. Rewrite using `[hc]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Simplify using `using PD.Fil_mul 0 0 _ _ (hW i j) (hK0 (k j))`. Establish `hhigh : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∀ b : ℤ, 1 ≤ b → y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL` using `LL) (V := V) b → y = 0 := by`. Introduce `y hy b hb hyb`.

Take `⟨k, hc, hk⟩` from `hrec y hy`. Rewrite `hyb` using `[_root_.GlobalTheory.SplitJump.mem_filV PD e]`. Establish `hk0 : k = 0`. Use function extensionality and compare the values at `i`. Apply `_root_.GlobalTheory.SplitJump.eq_zero_of_mem_fil_one PD` to reduce the goal to its premises.

Use `congrFun hk i` as an intermediate fact. Rewrite using `[this]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Simplify using `using PD.Fil_mul 0 1 _ _ (hW' i j) (_root_.GlobalTheory.SplitJump.fil_mono PD hb (hyb j))`.

Apply `(_root_.GlobalTheory.SplitJump.coord e BdR).injective` to reduce the goal to its premises. Rewrite using `[hc, hk0, map_zero]`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct]`. Unfold `_root_.Formalism.WeaklyAdmissibleFiltrations.IsJumpV _root_.Formalism.WeaklyAdmissibleFiltrations.FildR at h`.

Establish `hL : _root_.Formalism.WeaklyAdmissibleFiltrations.DdRE PD ρ τ ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ`. Unfold `_root_.Formalism.WeaklyAdmissibleFiltrations.DdRE`. Conclude with `inf_le_left`. Assume the negation of the conclusion as `ha`. Apply `h` to reduce the goal to its premises.

Break down `lt_or_gt_of_ne ha with ha | ha` into its components or cases. Rewrite using `[inf_eq_left.2 fun y hy => hlow y (hL hy) _ (by omega), inf_eq_left.2 fun y hy => hlow y (hL hy) _ (by omega)]`. Establish `hbot : ∀ b : ℤ, 1 ≤ b → _root_.Formalism.WeaklyAdmissibleFiltrations.DdRE PD ρ τ ⊓ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL` using `LL) (V := V) b = ⊥ := by`. Introduce `b hb`. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Conclude with `(Submodule.mem_bot _).2 (hhigh y (hL hy.1) b hb hy.2)`. Rewrite using `[hbot _ (by omega), hbot _ (by omega)]`.
-/
theorem _root_.GlobalTheory.SplitJump.jump_eq_zero (W W' : Matrix (Fin n) (Fin n) BdR)
    (hWW : W * W' = 1)
    (hW : ∀ i j, W i j ∈ PD.Fil 0) (hW' : ∀ i j, W' i j ∈ PD.Fil 0)
    (hg : ∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) *
      W.map (PD.actdR g) = W)
    (τ : K →ₐ[Qp] LL) (a : ℤ) (h : _root_.Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a) : a = 0 := by
  have hK0 : ∀ c : K, algebraMap K BdR c ∈ PD.Fil 0 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (PD.Fil 0).smul_mem c PD.one_mem
  have hrec : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∃ k : Fin n → K,
      _root_.GlobalTheory.SplitJump.coord e BdR y = W.mulVec (fun i => algebraMap K BdR (k i)) ∧
      (fun i => algebraMap K BdR (k i)) = W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y) := by
    intro y hy
    obtain ⟨k, hk⟩ := _root_.GlobalTheory.SplitJump.exists_coord PD ρ e W W' hWW hg y hy
    refine ⟨k, ?_, hk⟩
    rw [hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
  have hlow : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∀ b : ℤ, b ≤ 0 → y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b := by
    intro y hy b hb
    obtain ⟨k, hc, -⟩ := hrec y hy
    rw [_root_.GlobalTheory.SplitJump.mem_filV PD e]
    intro i
    apply _root_.GlobalTheory.SplitJump.fil_mono PD hb
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    simpa using PD.Fil_mul 0 0 _ _ (hW i j) (hK0 (k j))
  have hhigh : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∀ b : ℤ, 1 ≤ b →
      y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b → y = 0 := by
    intro y hy b hb hyb
    obtain ⟨k, hc, hk⟩ := hrec y hy
    rw [_root_.GlobalTheory.SplitJump.mem_filV PD e] at hyb
    have hk0 : k = 0 := by
      funext i
      apply _root_.GlobalTheory.SplitJump.eq_zero_of_mem_fil_one PD
      have := congrFun hk i
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      refine Submodule.sum_mem _ fun j _ => ?_
      simpa using PD.Fil_mul 0 1 _ _ (hW' i j) (_root_.GlobalTheory.SplitJump.fil_mono PD hb (hyb j))
    apply (_root_.GlobalTheory.SplitJump.coord e BdR).injective
    rw [hc, hk0, map_zero]
    funext i
    simp [Matrix.mulVec, dotProduct]
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.IsJumpV _root_.Formalism.WeaklyAdmissibleFiltrations.FildR at h
  have hL : _root_.Formalism.WeaklyAdmissibleFiltrations.DdRE PD ρ τ ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ := by
    unfold _root_.Formalism.WeaklyAdmissibleFiltrations.DdRE
    exact inf_le_left
  by_contra ha
  apply h
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [inf_eq_left.2 fun y hy => hlow y (hL hy) _ (by omega),
      inf_eq_left.2 fun y hy => hlow y (hL hy) _ (by omega)]
  · have hbot : ∀ b : ℤ, 1 ≤ b →
        _root_.Formalism.WeaklyAdmissibleFiltrations.DdRE PD ρ τ ⊓ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b = ⊥ := by
      intro b hb
      rw [eq_bot_iff]
      intro y hy
      exact (Submodule.mem_bot _).2 (hhigh y (hL hy.1) b hb hy.2)
    rw [hbot _ (by omega), hbot _ (by omega)]

end GlobalTheory.SplitJump
