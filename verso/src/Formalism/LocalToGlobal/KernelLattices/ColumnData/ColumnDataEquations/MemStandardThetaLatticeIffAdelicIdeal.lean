import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ConstCopies
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car}

def rowE (D : Car) (N N' : ℕ) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (Fin N' → TaylorLogMetric.VC D N 1) where
  toFun z := fun i τ _ j => z τ i j
  invFun w := fun τ i j => w i τ 0 j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by
    funext i τ a j
    rw [Subsingleton.elim a 0]

def colE (D : Car) (N N' : ℕ) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (Fin N → TaylorLogMetric.VC D N' 1) where
  toFun z := fun j τ _ i => z τ i j
  invFun w := fun τ i j => w j τ 0 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by
    funext i τ a j
    rw [Subsingleton.elim a 0]

/- English proof (translation)
Simplify using `only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, rowE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Finset.univ_unique, Finset.sum_singleton]`. Rewrite using `[← Finset.sum_div, Finset.sum_comm]`.
-/
theorem form_row (A : ℝ) (N N' : ℕ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' x y = ∑ i, Ker.formV A D.what₂.Tau N 1 (rowE D N N' x i) (rowE D N N' y i) := by
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, rowE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_div, Finset.sum_comm]

/- English proof (translation)
Simplify using `only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, colE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Finset.univ_unique, Finset.sum_singleton]`. Rewrite using `[← Finset.sum_div]`. Use `congr 1`. Use `symm`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun τ _ => Finset.sum_comm`.
-/
theorem form_col (A : ℝ) (N N' : ℕ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' x y = ∑ j, Ker.formV A D.what₂.Tau N' 1 (colE D N N' x j) (colE D N N' y j) := by
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, colE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_div]
  congr 1
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_comm

/- English proof (translation)
Introduce `x hx`. Establish `e : (Ker.formV A n N N' x x).re = (∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A`. Simplify using `only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]`. Rewrite using `[← Complex.ofReal_re ((∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A)]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[e]`. Use `div_pos ?_ hA` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨τ, i, j, h⟩ : ∃ τ i j, x τ i j ≠ 0 := by`. Assume the negation of the conclusion as `hno`.

Use `push Not at hno`. Conclude with `hx (funext fun τ => funext fun i => funext fun j => hno τ i j)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem formV_pos {A : ℝ} (hA : 0 < A) (n : Type) [Fintype n] (N N' : ℕ) : IsPosDef (Ker.formV A n N N') := by
  intro x hx
  have e : (Ker.formV A n N N' x x).re = (∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A := by
    simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [← Complex.ofReal_re ((∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A)]
    push_cast
    rfl
  rw [e]
  refine div_pos ?_ hA
  obtain ⟨τ, i, j, h⟩ : ∃ τ i j, x τ i j ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hx (funext fun τ => funext fun i => funext fun j => hno τ i j)
  calc 0 < Complex.normSq (x τ i j) := Complex.normSq_pos.mpr h
    _ ≤ ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (x τ i j)) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (x τ i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, Complex.normSq (x τ i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

include B in
/- English proof (translation)
Use `B.areaOK` as an intermediate fact. Unfold `Cd.Base.AreaOK at this`. Use `show 0 < TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)`. Rewrite using `[this]`. Conclude with `Formalism.L2.Th1.F.areaPos_thm B.L`.
-/
theorem area_pos' : 0 < TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂ := by
  have := B.areaOK
  unfold Cd.Base.AreaOK at this
  show 0 < TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)
  rw [this]
  exact Formalism.L2.Th1.F.areaPos_thm B.L

abbrev La0 (_B : Cd.Base D cc δ) (N N' : ℕ) : AddSubgroup (TaylorLogMetric.VC D N N') :=
  TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')

/- English proof (translation)
Use `B.lat0OK N N'` as an intermediate fact. Unfold `Cd.Base.Lat0OK at this`. Use `show x ∈ TaylorLogMetric.La D B.tor _ _ ↔ _`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem mem_standardThetaLattice_iff_adelicIdeal (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ i j, (fun τ => x τ i j) ∈ B.lamM := by
  have := B.lat0OK N N'
  unfold Cd.Base.Lat0OK at this
  show x ∈ TaylorLogMetric.La D B.tor _ _ ↔ _
  rw [this]
  rfl

/- English proof (translation)
Simplify using `only [mem_standardThetaLattice_iff_adelicIdeal]`. Conclude with `⟨fun h i _ j => h i j, fun h i j => h i 0 j⟩`.
-/
theorem lat_row (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ i, rowE D N N' x i ∈ La0 B N 1 := by
  simp only [mem_standardThetaLattice_iff_adelicIdeal]
  exact ⟨fun h i _ j => h i j, fun h i j => h i 0 j⟩

/- English proof (translation)
Simplify using `only [mem_standardThetaLattice_iff_adelicIdeal]`. Conclude with `⟨fun h j _ i => h i j, fun h i j => h j 0 i⟩`.
-/
theorem lat_col (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ j, colE D N N' x j ∈ La0 B N' 1 := by
  simp only [mem_standardThetaLattice_iff_adelicIdeal]
  exact ⟨fun h j _ i => h i j, fun h i j => h j 0 i⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]`.
-/
theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) : (-1 : ℂ) ^ (∑ i ∈ s, m i) = ∏ i ∈ s, (-1 : ℂ) ^ m i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

/- English proof (translation)
Use `choose m hm using hq`. Establish `h : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x).re = ((∑ i, m i : ℤ) : ℝ)`. Rewrite using `[hf, Complex.re_sum, Finset.mul_sum]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun i _ => hm i`.

Unfold `TaylorLogMetric.al`. Rewrite using `[h, round_intCast, neg_one_zpow_sum]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hm i, round_intCast]`.
-/
theorem al_prod {ι : Type} [Fintype ι] {N N' M M' : ℕ} (x : TaylorLogMetric.VC D N N') (y : ι → TaylorLogMetric.VC D M M')
    (hf : TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x = ∑ i, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (y i) (y i))
    (hq : ∀ i, ∃ m : ℤ, Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (y i) (y i)).re = (m : ℝ)) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ i, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (y i) := by
  choose m hm using hq
  have h : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x).re = ((∑ i, m i : ℤ) : ℝ) := by
    rw [hf, Complex.re_sum, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hm i
  unfold TaylorLogMetric.al
  rw [h, round_intCast, neg_one_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hm i, round_intCast]

/- English proof (translation)
The claim follows from `al_prod x _ (form_row _ N N' x x) fun i => B.qInt0 hS N 1 _ ((lat_row B N N' x).1 hx i)`.
-/
theorem al_row (hS : B.StdOK) (N N' : ℕ) (x : TaylorLogMetric.VC D N N') (hx : x ∈ La0 B N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ i, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (rowE D N N' x i) :=
  al_prod x _ (form_row _ N N' x x) fun i => B.qInt0 hS N 1 _ ((lat_row B N N' x).1 hx i)

/- English proof (translation)
The claim follows from `al_prod x _ (form_col _ N N' x x) fun j => B.qInt0 hS N' 1 _ ((lat_col B N N' x).1 hx j)`.
-/
theorem al_col (hS : B.StdOK) (N N' : ℕ) (x : TaylorLogMetric.VC D N N') (hx : x ∈ La0 B N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ j, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (colE D N N' x j) :=
  al_prod x _ (form_col _ N N' x x) fun j => B.qInt0 hS N' 1 _ ((lat_col B N N' x).1 hx j)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
