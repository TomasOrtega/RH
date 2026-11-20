import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.TripleSumIndep
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.RightMoveTrianglesOfUnit
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JArith
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Mu

open Formalism.L2.PairingIndexBounds.Eq.Mu Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car}

/- English proof (translation)
Establish `hH : TaylorLogMetric.homL D M M' ≤ (TaylorLogMetric.homL D M M').comap f` using `Submodule.span_le.2 fun B hB => Submodule.subset_span (hgen B hB)`. Establish `hY : TaylorLogMetric.YYl D M M' ≤ (TaylorLogMetric.YYl D M M').comap f`. Use `Submodule.span_le.2 fun B hB => ?_` and prove the remaining obligations. Take `⟨a, ha, A', hA', rfl⟩` from `hB`. Use `show f (a • A') ∈ TaylorLogMetric.YYl D M M'`.

Rewrite using `[hfE]`. Conclude with `Submodule.subset_span ⟨a, ha, f A', hH hA', rfl⟩`. Conclude with `hY hA`.
-/
theorem yy_stab {N N' : ℕ} {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (f : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E)
    (hfE : ∀ (a : D.host.E) A, f (a • A) = a • f A)
    (hgen : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ M, A *ᵥ x ∈ M') → ∀ x ∈ M, f A *ᵥ x ∈ M')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.YYl D M M') : f A ∈ TaylorLogMetric.YYl D M M' := by
  have hH : TaylorLogMetric.homL D M M' ≤ (TaylorLogMetric.homL D M M').comap f :=
    Submodule.span_le.2 fun B hB => Submodule.subset_span (hgen B hB)
  have hY : TaylorLogMetric.YYl D M M' ≤ (TaylorLogMetric.YYl D M M').comap f := by
    refine Submodule.span_le.2 fun B hB => ?_
    obtain ⟨a, ha, A', hA', rfl⟩ := hB
    show f (a • A') ∈ TaylorLogMetric.YYl D M M'
    rw [hfE]
    exact Submodule.subset_span ⟨a, ha, f A', hH hA', rfl⟩
  exact hY hA

/- English proof (translation)
Unfold `TaylorLogMetric.La at hz ⊢`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem v hv`. Take `⟨w, hw, A, hA, rfl⟩` from `hv`. Rewrite using `[hΦ]`.

Conclude with `AddSubgroup.subset_closure ⟨w, hw, f A, hf A hA, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `AddSubgroup.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `AddSubgroup.add_mem _ hx hy`.

Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `AddSubgroup.neg_mem _ hx`.
-/
theorem la_stab {N N' : ℕ} (T : TaylorLogMetric.Tor D) {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (Φ : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N')
    (f : Matrix (Fin N') (Fin N) D.host.E → Matrix (Fin N') (Fin N) D.host.E)
    (hΦ : ∀ (w : ℂ) A, Φ (w • TaylorLogMetric.embV D T A) = w • TaylorLogMetric.embV D T (f A))
    (hf : ∀ A ∈ TaylorLogMetric.YYl D M M', f A ∈ TaylorLogMetric.YYl D M M') {z : TaylorLogMetric.VC D N N'} (hz : z ∈ TaylorLogMetric.La D T M M') :
    Φ z ∈ TaylorLogMetric.La D T M M' := by
  unfold TaylorLogMetric.La at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hv
    rw [hΦ]
    exact AddSubgroup.subset_closure ⟨w, hw, f A, hf A hA, rfl⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulO_apply {N N' : ℕ} (r : D.host.E) (x : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    J.mulO N N' r x τ i j = TaylorLogMetric.embT D τ r * x τ i j := rfl

/- English proof (translation)
Use `la_stab T (J.mulO N N' (r : D.host.E)).toAddMonoidHom (fun A => (r : D.host.E) • A) ?_ ?_ hz` and prove the remaining obligations. Introduce `w A`. Use function extensionality and compare the values at `τ i j`. Simplify using `only [LinearMap.toAddMonoidHom_coe, mulO_apply, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, hT]`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `A hA`. Rewrite using `[show (r : D.host.E) • A = r • A from algebraMap_smul D.host.E r A]`. Conclude with `Submodule.smul_mem _ r hA`.
-/
theorem mulO_la {N N' : ℕ} (T : TaylorLogMetric.Tor D) (hT : ∀ τ x, T.emb τ x = TaylorLogMetric.embT D τ x)
    {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (r : 𝓞 D.host.E) {z : TaylorLogMetric.VC D N N'} (hz : z ∈ TaylorLogMetric.La D T M M') :
    J.mulO N N' (r : D.host.E) z ∈ TaylorLogMetric.La D T M M' := by
  refine la_stab T (J.mulO N N' (r : D.host.E)).toAddMonoidHom (fun A => (r : D.host.E) • A) ?_ ?_ hz
  · intro w A
    funext τ i j
    simp only [LinearMap.toAddMonoidHom_coe, mulO_apply, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, hT]
    rw [map_mul]; ring
  · intro A hA
    rw [show (r : D.host.E) • A = r • A from algebraMap_smul D.host.E r A]
    exact Submodule.smul_mem _ r hA

/- English proof (translation)
Simplify using `[StandardLatticesGL3.stdL, Submodule.mem_pi]`.
-/
theorem mem_stdL {n : ℕ} {v : Fin n → D.host.E} :
    v ∈ StandardLatticesGL3.stdL D n ↔ ∀ i, v i ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [StandardLatticesGL3.stdL, Submodule.mem_pi]

def swp (n : ℕ) (i : Fin n) : Fin n :=
  ⟨if i.val < n / 2 then i.val + n / 2 else i.val - n / 2, by have := i.isLt; split_ifs <;> omega⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swp_val (n : ℕ) (i : Fin n) :
    (swp n i).val = if i.val < n / 2 then i.val + n / 2 else i.val - n / 2 := rfl

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[swp_val, swp_val]`. Use `i.isLt` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem swp_swp {n : ℕ} (h : Even n) (i : Fin n) : swp n (swp n i) = i := by
  obtain ⟨k, hk⟩ := h
  apply Fin.ext
  rw [swp_val, swp_val]
  have := i.isLt
  split_ifs <;> omega

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Rewrite using `[swp_val]`. Use `i.isLt` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem swp_lt {n : ℕ} (h : Even n) (i : Fin n) : (swp n i).val < n / 2 ↔ ¬ i.val < n / 2 := by
  obtain ⟨k, hk⟩ := h
  rw [swp_val]; have := i.isLt
  split_ifs <;> omega

def swpE {n : ℕ} (h : Even n) : Equiv.Perm (Fin n) := Function.Involutive.toPerm (swp n) (swp_swp h)

def rowP (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => if i.val < N' / 2 then z τ i j else 0
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp only [Pi.add_apply]; split_ifs <;> simp

def rowSw (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => z τ (swp N' i) j
  map_zero' := rfl
  map_add' _ _ := rfl

def colP (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => if j.val < N / 2 then z τ i j else 0
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp only [Pi.add_apply]; split_ifs <;> simp

def colSw (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => z τ i (swp N j)
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rowP_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    rowP N N' z τ i j = if i.val < N' / 2 then z τ i j else 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rowSw_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    rowSw N N' z τ i j = z τ (swp N' i) j := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colP_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    colP N N' z τ i j = if j.val < N / 2 then z τ i j else 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colSw_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    colSw N N' z τ i j = z τ i (swp N j) := rfl

section Facts

variable {N N' : ℕ}

/- English proof (translation)
Apply the tactic sequence `funext τ i j; simp only [rowP_apply]; split_ifs <;> rfl`.
-/
theorem rowProjection_rowProjection (x : TaylorLogMetric.VC D N N') : rowP N N' (rowP N N' x) = rowP N N' x := by
  funext τ i j; simp only [rowP_apply]; split_ifs <;> rfl
/- English proof (translation)
Apply the tactic sequence `funext τ i j; simp only [colP_apply]; split_ifs <;> rfl`.
-/
theorem colP_colP (x : TaylorLogMetric.VC D N N') : colP N N' (colP N N' x) = colP N N' x := by
  funext τ i j; simp only [colP_apply]; split_ifs <;> rfl

/- English proof (translation)
Rewrite using `[Cd.formV_apply, Finset.sum_eq_zero, zero_div]`. Introduce `τ _`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `simp only [rowP_apply, Pi.sub_apply]; split_ifs <;> simp`.
-/
theorem rowProjection_orthogonal (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (rowP N N' x) (y - rowP N N' y) = 0 := by
  rw [Cd.formV_apply, Finset.sum_eq_zero, zero_div]
  intro τ _; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp only [rowP_apply, Pi.sub_apply]; split_ifs <;> simp
/- English proof (translation)
Rewrite using `[Cd.formV_apply, Finset.sum_eq_zero, zero_div]`. Introduce `τ _`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `simp only [colP_apply, Pi.sub_apply]; split_ifs <;> simp`.
-/
theorem colP_orth (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (colP N N' x) (y - colP N N' y) = 0 := by
  rw [Cd.formV_apply, Finset.sum_eq_zero, zero_div]
  intro τ _; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp only [colP_apply, Pi.sub_apply]; split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [rowSw_apply, swp_swp h]`.
-/
theorem rowSw_sw (h : Even N') (x : TaylorLogMetric.VC D N N') : rowSw N N' (rowSw N N' x) = x := by
  funext τ i j; simp only [rowSw_apply, swp_swp h]
/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [colSw_apply, swp_swp h]`.
-/
theorem colSw_sw (h : Even N) (x : TaylorLogMetric.VC D N N') : colSw N N' (colSw N N' x) = x := by
  funext τ i j; simp only [colSw_apply, swp_swp h]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [rowP_apply, rowSw_apply, Pi.sub_apply]`. Use `swp_lt h i` as an intermediate fact. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem rowSw_p (h : Even N') (x : TaylorLogMetric.VC D N N') :
    rowP N N' (rowSw N N' x) = rowSw N N' x - rowSw N N' (rowP N N' x) := by
  funext τ i j
  simp only [rowP_apply, rowSw_apply, Pi.sub_apply]
  have := swp_lt h i
  split_ifs <;> simp_all
/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [colP_apply, colSw_apply, Pi.sub_apply]`. Use `swp_lt h j` as an intermediate fact. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem colSw_p (h : Even N) (x : TaylorLogMetric.VC D N N') :
    colP N N' (colSw N N' x) = colSw N N' x - colSw N N' (colP N N' x) := by
  funext τ i j
  simp only [colP_apply, colSw_apply, Pi.sub_apply]
  have := swp_lt h j
  split_ifs <;> simp_all

/- English proof (translation)
Rewrite using `[Cd.formV_apply, Cd.formV_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Conclude with `Equiv.sum_comp (swpE h) (fun i => ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j))`.
-/
theorem rowSw_form (h : Even N') (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (rowSw N N' x) (rowSw N N' y) = Ker.formV A D.what₂.Tau N N' x y := by
  rw [Cd.formV_apply, Cd.formV_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact Equiv.sum_comp (swpE h) (fun i => ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j))
/- English proof (translation)
Rewrite using `[Cd.formV_apply, Cd.formV_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Equiv.sum_comp (swpE h) (fun j => x τ i j * (starRingEnd ℂ) (y τ i j))`.
-/
theorem colSw_form (h : Even N) (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (colSw N N' x) (colSw N N' y) = Ker.formV A D.what₂.Tau N N' x y := by
  rw [Cd.formV_apply, Cd.formV_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (swpE h) (fun j => x τ i j * (starRingEnd ℂ) (y τ i j))

/- English proof (translation)
Unfold `TaylorLogMetric.al`. Rewrite using `[Cd.Hf_eq, Cd.Hf_eq, hf]`.
-/
theorem al_form (T : TaylorLogMetric.Tor D) (f : TaylorLogMetric.VC D N N' → TaylorLogMetric.VC D N N')
    (hf : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (f x) (f y) = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' x y)
    (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (f x) = TaylorLogMetric.al D T x := by
  unfold TaylorLogMetric.al
  rw [Cd.Hf_eq, Cd.Hf_eq, hf]

/- English proof (translation)
Apply the tactic sequence `funext τ i j; simp only [mulO_apply, rowP_apply]; split_ifs <;> simp`.
-/
theorem mulO_rowP (r : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (rowP N N' x) = rowP N N' (J.mulO N N' r x) := by
  funext τ i j; simp only [mulO_apply, rowP_apply]; split_ifs <;> simp
/- English proof (translation)
Apply the tactic sequence `funext τ i j; simp only [mulO_apply, colP_apply]; split_ifs <;> simp`.
-/
theorem mulO_colP (r : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (colP N N' x) = colP N N' (J.mulO N N' r x) := by
  funext τ i j; simp only [mulO_apply, colP_apply]; split_ifs <;> simp

end Facts

section Lat

variable {N N' : ℕ}

def rowPM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => if i.val < N' / 2 then A i j else 0
  map_add' A B := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c A := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def rowSwM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => A (swp N' i) j
  map_add' A B := by ext i j; simp
  map_smul' c A := by ext i j; simp

def colPM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => if j.val < N / 2 then A i j else 0
  map_add' A B := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c A := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def colSwM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => A i (swp N j)
  map_add' A B := by ext i j; simp
  map_smul' c A := by ext i j; simp

variable (T : TaylorLogMetric.Tor D) (hT : ∀ τ x, T.emb τ x = TaylorLogMetric.embT D τ x)
include hT

/- English proof (translation)
Use `la_stab T (rowP N N') (rowPM N N') ?_ (fun A hA => yy_stab (rowPM N N') ?_ ?_ hA) hz` and prove the remaining obligations. Introduce `w A`. Use function extensionality and compare the values at `τ i j`. Simplify using `only [rowP_apply, rowPM, LinearMap.coe_mk, AddHom.coe_mk, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, of_apply, hT]`. Apply the tactic sequence `split_ifs <;> simp`.

Introduce `a A`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp`. Introduce `A hA x hx`. Establish `h` using `mem_stdL.1 (hA x hx)`.

Use `mem_stdL.2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < N' / 2`. Establish `e : (rowPM N N' A *ᵥ x) i = (A *ᵥ x) i`. Simplify using `only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply, if_pos hi]`. Rewrite using `[e]`.

Conclude with `h i`. Establish `e : (rowPM N N' A *ᵥ x) i = 0`. Simplify using `only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply, if_neg hi, zero_mul, Finset.sum_const_zero]`. Rewrite using `[e]`. Conclude with `Submodule.zero_mem _`.
-/
theorem rowProjection_mem_lattice {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N')) : rowP N N' z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N') := by
  refine la_stab T (rowP N N') (rowPM N N') ?_ (fun A hA => yy_stab (rowPM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j
    simp only [rowP_apply, rowPM, LinearMap.coe_mk, AddHom.coe_mk, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, of_apply, hT]
    split_ifs <;> simp
  · intro a A; refine Matrix.ext fun i j => ?_
    simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  · intro A hA x hx
    have h := mem_stdL.1 (hA x hx)
    refine mem_stdL.2 fun i => ?_
    by_cases hi : i.val < N' / 2
    · have e : (rowPM N N' A *ᵥ x) i = (A *ᵥ x) i := by
        simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply, if_pos hi]
      rw [e]; exact h i
    · have e : (rowPM N N' A *ᵥ x) i = 0 := by
        simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply, if_neg hi, zero_mul,
          Finset.sum_const_zero]
      rw [e]; exact Submodule.zero_mem _

/- English proof (translation)
Use `la_stab T (rowSw N N') (rowSwM N N') ?_ (fun A hA => yy_stab (rowSwM N N') ?_ ?_ hA) hz` and prove the remaining obligations. Introduce `w A`. Use function extensionality and compare the values at `τ i j`. Both sides reduce to the same expression. Introduce `a A`.

Use extensionality with `i j`. Both sides reduce to the same expression. Introduce `A hA x hx`. Establish `h` using `mem_stdL.1 (hA x hx)`. Conclude with `mem_stdL.2 fun i => h (swp N' i)`.
-/
theorem rowSw_la {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N')) : rowSw N N' z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N') := by
  refine la_stab T (rowSw N N') (rowSwM N N') ?_ (fun A hA => yy_stab (rowSwM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j; rfl
  · intro a A; ext i j; rfl
  · intro A hA x hx
    have h := mem_stdL.1 (hA x hx)
    exact mem_stdL.2 fun i => h (swp N' i)

/- English proof (translation)
Use `la_stab T (colP N N') (colPM N N') ?_ (fun A hA => yy_stab (colPM N N') ?_ ?_ hA) hz` and prove the remaining obligations. Introduce `w A`. Use function extensionality and compare the values at `τ i j`. Simplify using `only [colP_apply, colPM, LinearMap.coe_mk, AddHom.coe_mk, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, of_apply, hT]`. Apply the tactic sequence `split_ifs <;> simp`.

Introduce `a A`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `simp only [colPM, LinearMap.coe_mk, AddHom.coe_mk, of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp`. Introduce `A hA x hx`. Establish `hx' : (fun j : Fin N => if j.val < N / 2 then x j else 0) ∈ StandardLatticesGL3.stdL D N`.

Use `mem_stdL.2 fun j => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `mem_stdL.1 hx j`. Conclude with `Submodule.zero_mem _`. Establish `e : colPM N N' A *ᵥ x = A *ᵥ (fun j : Fin N => if j.val < N / 2 then x j else 0)`.

Use function extensionality and compare the values at `i`. Simplify using `only [colPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e]`.

Conclude with `hA _ hx'`.
-/
theorem colP_mem_la {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M') : colP N N' z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M' := by
  refine la_stab T (colP N N') (colPM N N') ?_ (fun A hA => yy_stab (colPM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j
    simp only [colP_apply, colPM, LinearMap.coe_mk, AddHom.coe_mk, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, of_apply, hT]
    split_ifs <;> simp
  · intro a A; refine Matrix.ext fun i j => ?_
    simp only [colPM, LinearMap.coe_mk, AddHom.coe_mk, of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  · intro A hA x hx
    have hx' : (fun j : Fin N => if j.val < N / 2 then x j else 0) ∈ StandardLatticesGL3.stdL D N := by
      refine mem_stdL.2 fun j => ?_
      split_ifs
      · exact mem_stdL.1 hx j
      · exact Submodule.zero_mem _
    have e : colPM N N' A *ᵥ x = A *ᵥ (fun j : Fin N => if j.val < N / 2 then x j else 0) := by
      funext i
      simp only [colPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [e]; exact hA _ hx'

/- English proof (translation)
Use `la_stab T (colSw N N') (colSwM N N') ?_ (fun A hA => yy_stab (colSwM N N') ?_ ?_ hA) hz` and prove the remaining obligations. Introduce `w A`. Use function extensionality and compare the values at `τ i j`. Both sides reduce to the same expression. Introduce `a A`.

Use extensionality with `i j`. Both sides reduce to the same expression. Introduce `A hA x hx`. Establish `hx' : (fun j : Fin N => x (swp N j)) ∈ StandardLatticesGL3.stdL D N` using `mem_stdL.2 fun j => mem_stdL.1 hx (swp N j)`. Establish `e : colSwM N N' A *ᵥ x = A *ᵥ (fun j : Fin N => x (swp N j))`.

Use function extensionality and compare the values at `i`. Simplify using `only [colSwM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply]`. Use `Equiv.sum_comp (swpE hN) (fun j => A i j * x (swp N j))` as an intermediate fact. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `show A i (swp N j) * x j = A i (swp N j) * x (swp N (swp N j))`. Rewrite using `[swp_swp hN]`. Rewrite using `[e]`. Conclude with `hA _ hx'`.
-/
theorem colSw_la (hN : Even N) {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M') : colSw N N' z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M' := by
  refine la_stab T (colSw N N') (colSwM N N') ?_ (fun A hA => yy_stab (colSwM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j; rfl
  · intro a A; ext i j; rfl
  · intro A hA x hx
    have hx' : (fun j : Fin N => x (swp N j)) ∈ StandardLatticesGL3.stdL D N := mem_stdL.2 fun j => mem_stdL.1 hx (swp N j)
    have e : colSwM N N' A *ᵥ x = A *ᵥ (fun j : Fin N => x (swp N j)) := by
      funext i
      simp only [colSwM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply]
      have := Equiv.sum_comp (swpE hN) (fun j => A i j * x (swp N j))
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A i (swp N j) * x j = A i (swp N j) * x (swp N (swp N j))
      rw [swp_swp hN]
    rw [e]; exact hA _ hx'

end Lat

section Mult

variable {N N' : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [mulO_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulO_mul (r r' : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (J.mulO N N' r' x) = J.mulO N N' (r * r') x := by
  funext τ i j; simp only [mulO_apply, map_mul]; ring

/- English proof (translation)
Rewrite using `[J.mulO_adj, mulO_mul, hl]`. Establish `: J.mulO N N' (-1 + (n : D.host.E) * s) y = -y + n • J.mulO N N' s y`. Use function extensionality and compare the values at `τ i j`. Simplify using `only [mulO_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add, map_neg, map_one, map_mul, map_natCast]`. Simplify using `only [nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_add, map_neg, map_nsmul, nsmul_eq_mul]`.
-/
theorem form_mul (A : ℝ) (l s : D.host.E) (n : ℕ) (hl : star l * l = -1 + (n : D.host.E) * s)
    (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (J.mulO N N' l x) (J.mulO N N' l y)
      = -Ker.formV A D.what₂.Tau N N' x y + (n : ℂ) * Ker.formV A D.what₂.Tau N N' x (J.mulO N N' s y) := by
  rw [J.mulO_adj, mulO_mul, hl]
  have : J.mulO N N' (-1 + (n : D.host.E) * s) y = -y + n • J.mulO N N' s y := by
    funext τ i j
    simp only [mulO_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add, map_neg, map_one, map_mul, map_natCast]
    simp only [nsmul_eq_mul]
    ring
  rw [this, map_add, map_neg, map_nsmul, nsmul_eq_mul]

/- English proof (translation)
Take `⟨m0, h0re, h0r⟩` from `Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.self_int T hI hx`. Take `⟨m1, h1re, h1r⟩` from `Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.self_int T hI hmx`. Take `⟨a, b, -, hab⟩` from `hI x hx _ hsx`. Establish `hf : TaylorLogMetric.Hf D T (J.mulO N N' l x) (J.mulO N N' l x) = -TaylorLogMetric.Hf D T x x + ((4 * e : ℕ) : ℂ) * TaylorLogMetric.Hf D T x (J.mulO N N' s x)` using `form_mul (TaylorLogMetric.area T.abelian₂) l s (4 * e) hl x x`. Rewrite `hf` using `[hab]`.

Establish `hre : (TaylorLogMetric.Hf D T (J.mulO N N' l x) (J.mulO N N' l x)).re = -(TaylorLogMetric.Hf D T x x).re + ((4 * e : ℕ) : ℝ) * (a / Real.sqrt D.host.d)`. Rewrite using `[hf, Complex.add_re, Complex.neg_re, show ((4 * e : ℕ) : ℂ) = (((4 * e : ℕ) : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]`. Simplify using the standard rewrite rules. Establish `key : (m1 : ℝ) = -m0 + 2 * e * a`. Rewrite `hre` using `[h1re, h0re]`.

Establish `hs` using `Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.sqrt_d_pos D`. Clear denominators, using `at hre` for the nonvanishing conditions. Move the coercions through the operations in `at hre`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key' : m1 = -m0 + 2 * e * a` using `by exact_mod_cast key`.

Unfold `TaylorLogMetric.al`. Rewrite using `[h1r, h0r]`. Apply `Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.neg_one_zpow_congr` to reduce the goal to its premises. Rewrite using `[key']`. Conclude with `⟨-m0 + e * a, by ring⟩`.
-/
theorem al_mul (T : TaylorLogMetric.Tor D) {La' : AddSubgroup (TaylorLogMetric.VC D N N')} (hI : Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.HfInt T La')
    (l s : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s) {x : TaylorLogMetric.VC D N N'}
    (hx : x ∈ La') (hmx : J.mulO N N' l x ∈ La') (hsx : J.mulO N N' s x ∈ La') :
    TaylorLogMetric.al D T (J.mulO N N' l x) = TaylorLogMetric.al D T x := by
  obtain ⟨m0, h0re, h0r⟩ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.self_int T hI hx
  obtain ⟨m1, h1re, h1r⟩ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.self_int T hI hmx
  obtain ⟨a, b, -, hab⟩ := hI x hx _ hsx
  have hf : TaylorLogMetric.Hf D T (J.mulO N N' l x) (J.mulO N N' l x)
      = -TaylorLogMetric.Hf D T x x + ((4 * e : ℕ) : ℂ) * TaylorLogMetric.Hf D T x (J.mulO N N' s x) :=
    form_mul (TaylorLogMetric.area T.abelian₂) l s (4 * e) hl x x
  rw [hab] at hf
  have hre : (TaylorLogMetric.Hf D T (J.mulO N N' l x) (J.mulO N N' l x)).re
      = -(TaylorLogMetric.Hf D T x x).re + ((4 * e : ℕ) : ℝ) * (a / Real.sqrt D.host.d) := by
    rw [hf, Complex.add_re, Complex.neg_re,
      show ((4 * e : ℕ) : ℂ) = (((4 * e : ℕ) : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]
    simp
  have key : (m1 : ℝ) = -m0 + 2 * e * a := by
    rw [h1re, h0re] at hre
    have hs := Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.sqrt_d_pos D
    field_simp at hre
    push_cast at hre
    linarith
  have key' : m1 = -m0 + 2 * e * a := by exact_mod_cast key
  unfold TaylorLogMetric.al
  rw [h1r, h0r]
  apply Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.neg_one_zpow_congr
  rw [key']
  exact ⟨-m0 + e * a, by ring⟩

/- English proof (translation)
Take `⟨a, b, -, hab⟩` from `hI _ hez _ hsy`. Establish `hb : (e : ℝ) * (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z (J.mulO N N' s y)).im = b`. Establish `h1 : Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (e • z) (J.mulO N N' s y) = ((e : ℝ) : ℂ) * Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z (J.mulO N N' s y)`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `congrArg Complex.im hab`. Rewrite `h2` using `[show TaylorLogMetric.Hf D T (e • z) (J.mulO N N' s y) = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (e • z) (J.mulO N N' s y) from rfl, h1, Complex.im_ofReal_mul]`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.

Establish `hf` using `form_mul (TaylorLogMetric.area T.abelian₂) l s (4 * e) hl z y`. Use `⟨2 * b, ?_⟩` and prove the remaining obligations. Unfold `altE`. Rewrite using `[hf, Complex.add_im, Complex.neg_im, show ((4 * e : ℕ) : ℂ) = (((4 * e : ℕ) : ℝ) : ℂ) by norm_cast, Complex.im_ofReal_mul]`. Use `push_cast`.

Combine the linear relations using `[hb]`.
-/
theorem altE_mul (T : TaylorLogMetric.Tor D) {La' : AddSubgroup (TaylorLogMetric.VC D N N')} (hI : Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.HfInt T La')
    (l s : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s) {z y : TaylorLogMetric.VC D N N'}
    (hez : e • z ∈ La') (hsy : J.mulO N N' s y ∈ La') :
    ∃ k : ℤ, altE (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (J.mulO N N' l z) (J.mulO N N' l y)
      = -altE (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') z y + 2 * k := by
  obtain ⟨a, b, -, hab⟩ := hI _ hez _ hsy
  have hb : (e : ℝ) * (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z (J.mulO N N' s y)).im = b := by
    have h1 : Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (e • z) (J.mulO N N' s y)
        = ((e : ℝ) : ℂ) * Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z (J.mulO N N' s y) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, map_smul, LinearMap.smul_apply, smul_eq_mul]; push_cast; ring
    have h2 := congrArg Complex.im hab
    rw [show TaylorLogMetric.Hf D T (e • z) (J.mulO N N' s y)
        = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (e • z) (J.mulO N N' s y) from rfl, h1,
      Complex.im_ofReal_mul] at h2
    rw [h2]; simp
  have hf := form_mul (TaylorLogMetric.area T.abelian₂) l s (4 * e) hl z y
  refine ⟨2 * b, ?_⟩
  unfold altE
  rw [hf, Complex.add_im, Complex.neg_im,
    show ((4 * e : ℕ) : ℂ) = (((4 * e : ℕ) : ℝ) : ℂ) by norm_cast, Complex.im_ofReal_mul]
  push_cast
  linarith [hb]

/- English proof (translation)
Establish `hE : -l' * l = 1 + (e : D.host.E) * (-4 * s)`. Rewrite using `[hl', neg_mul, hl]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion.

Use function extensionality and compare the values at `τ i j`. Use `congrArg (TaylorLogMetric.embT D τ) hE` as an intermediate fact. Simplify using `only [map_mul, map_add, map_one, map_natCast, map_neg, map_ofNat] at this`. Simplify using `only [mulO_apply, Pi.add_apply, Pi.smul_apply]`. Simplify using `only [nsmul_eq_mul, map_mul, map_neg, map_ofNat]`.

Take the linear combination `x τ i j * this`. Use function extensionality and compare the values at `τ i j`. Use `congrArg (TaylorLogMetric.embT D τ) hE` as an intermediate fact. Simplify using `only [map_mul, map_add, map_one, map_natCast, map_neg, map_ofNat] at this`. Simplify using `only [mulO_apply, Pi.add_apply, Pi.smul_apply]`.

Simplify using `only [nsmul_eq_mul, map_mul, map_neg, map_ofNat]`. Take the linear combination `x τ i j * this`.
-/
theorem mulO_inv (l s l' : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s)
    (hl' : l' = star l) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' (-l') (J.mulO N N' l x) = x + e • J.mulO N N' (-4 * s) x ∧
    J.mulO N N' l (J.mulO N N' (-l') x) = x + e • J.mulO N N' (-4 * s) x := by
  have hE : -l' * l = 1 + (e : D.host.E) * (-4 * s) := by
    rw [hl', neg_mul, hl]; push_cast; ring
  constructor
  · funext τ i j
    have := congrArg (TaylorLogMetric.embT D τ) hE
    simp only [map_mul, map_add, map_one, map_natCast, map_neg, map_ofNat] at this
    simp only [mulO_apply, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, map_mul, map_neg, map_ofNat]
    linear_combination x τ i j * this
  · funext τ i j
    have := congrArg (TaylorLogMetric.embT D τ) hE
    simp only [map_mul, map_add, map_one, map_natCast, map_neg, map_ofNat] at this
    simp only [mulO_apply, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, map_mul, map_neg, map_ofNat]
    linear_combination x τ i j * this

/- English proof (translation)
Rewrite using `[← hr]`. Conclude with `mulO_la T hT r hz`.
-/
theorem mulO_la' (T : TaylorLogMetric.Tor D) (hT : ∀ τ x, T.emb τ x = TaylorLogMetric.embT D τ x)
    {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (r : 𝓞 D.host.E) {r' : D.host.E} (hr : (r : D.host.E) = r') {z : TaylorLogMetric.VC D N N'} (hz : z ∈ TaylorLogMetric.La D T M M') :
    J.mulO N N' r' z ∈ TaylorLogMetric.La D T M M' := by
  rw [← hr]; exact mulO_la T hT r hz

end Mult

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Mu
