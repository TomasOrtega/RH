import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatPtsUnn

def blkD {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  fun i k => M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr k))

def blkA' {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  fun i k => M (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl k))

/- English proof (translation)
Rewrite using `[← Matrix.det_submatrix_equiv_self finSumFinEquiv M, ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]`. Establish `h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0`. Use extensionality with `i j`. Conclude with `h i j`. Rewrite using `[h0, Matrix.det_fromBlocks_zero₂₁]`.

Both sides reduce to the same expression.
-/
theorem det_eq_of_lowerLeft_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (h : ∀ i j : Fin n, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    M.det = (blkA' M).det * (blkD M).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j; exact h i j
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  rfl

/- English proof (translation)
Unfold `upperHalf`. Rewrite using `[LinearMap.mem_ker]`. Conclude with `funext_iff`.
-/
theorem mem_upperHalf {D : D7} {n : ℕ} (x : Fin (n + n) → AE D) :
    x ∈ upperHalf D n ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i)) = 0 := by
  unfold upperHalf
  rw [LinearMap.mem_ker]
  exact funext_iff

end GlobalTheory.CompanionTheory.RatPtsUnn

namespace GlobalTheory.CompanionTheory.RatPtsUnn

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]`. Both sides reduce to the same expression.
-/
theorem mulVec_inr {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (x : Fin (n + n) → R) (i : Fin n) :
    (M *ᵥ x) (finSumFinEquiv (Sum.inr i)) =
      (∑ j, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) +
        (blkD M *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  rfl

variable {D : D7} {n : ℕ}

/- English proof (translation)
Establish `h : γ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range` using `by rw [range_ratEmb]; exact hγ`. Conclude with `h`.
-/
theorem exists_ratEmb_of_mem {γ : G D n} (hγ : γ ∈ GF D n) :
    ∃ g0 : GRat D.sp.cm.sig (Jst D n), ratEmb _ _ g0 = γ := by
  have h : γ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range := by rw [range_ratEmb]; exact hγ
  exact h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_ratEmb (g0 : GRat D.sp.cm.sig (Jst D n)) :
    mat (ratEmb _ _ g0) = (g0.1 : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E).map (incA D) := rfl

/- English proof (translation)
Introduce `γ hγ`. Take `⟨g0, rfl⟩` from `exists_ratEmb_of_mem hγ`. Conclude with `⟨g0.1.1, (Matrix.isUnit_iff_isUnit_det _).1 g0.1.isUnit, g0.2, mat_ratEmb g0⟩`.
-/
theorem clause1 : ∀ γ ∈ GF D n, ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det ∧
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g ∧ mat γ = g.map (incA D) := by
  intro γ hγ
  obtain ⟨g0, rfl⟩ := exists_ratEmb_of_mem hγ
  exact ⟨g0.1.1, (Matrix.isUnit_iff_isUnit_det _).1 g0.1.isUnit, g0.2, mat_ratEmb g0⟩

/- English proof (translation)
Introduce `g hg hu`. Set `u : GL (Fin (n + n)) D.host.E` to `((Matrix.isUnit_iff_isUnit_det g).2 hg).unit`. Establish `hu' : u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n)` using `hu`. Use `⟨ratEmb _ _ ⟨u, hu'⟩, ?_, rfl⟩` and prove the remaining obligations. Establish `h : ratEmb D.sp.cm.sig (Jst D n) ⟨u, hu'⟩ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range` using `⟨_, rfl⟩`.

Rewrite `h` using `[range_ratEmb]`. Conclude with `h`.
-/
theorem clause2 : ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det →
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g → ∃ γ ∈ GF D n, mat γ = g.map (incA D) := by
  intro g hg hu
  let u : GL (Fin (n + n)) D.host.E := ((Matrix.isUnit_iff_isUnit_det g).2 hg).unit
  have hu' : u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := hu
  refine ⟨ratEmb _ _ ⟨u, hu'⟩, ?_, rfl⟩
  have h : ratEmb D.sp.cm.sig (Jst D n) ⟨u, hu'⟩ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range := ⟨_, rfl⟩
  rw [range_ratEmb] at h
  exact h

/- English proof (translation)
Unfold `P`. Rewrite using `[Subgroup.mem_comap]`. Conclude with `Iff.rfl`.
-/
theorem mem_P_iff (γ : G D n) :
    γ ∈ P D n ↔ ∀ x : Fin (n + n) → AE D, x ∈ upperHalf D n ↔ mat γ *ᵥ x ∈ upperHalf D n := by
  unfold P
  rw [Subgroup.mem_comap]
  exact Iff.rfl

/- English proof (translation)
Introduce `γ _ g hg`. Rewrite using `[mem_P_iff, hg]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `hx : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈ upperHalf D n`.

Rewrite using `[mem_upperHalf]`. Introduce `k`. Conclude with `Pi.single_eq_of_ne (fun e => Sum.inr_ne_inl (finSumFinEquiv.injective e)) _`. Establish `h2` using `(mem_upperHalf _).1 ((h _).1 hx) i`. Rewrite `h2` using `[Matrix.mulVec_single_one]`.

Express the relevant statement in the definitionally equal form `incA D (g _ _) = 0 at h2`. Conclude with `incA_injective (h2.trans (map_zero _).symm)`. Introduce `hS`. Establish `hM : ∀ i j : Fin n, g.map (incA D) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0`. Introduce `i j`.

Rewrite using `[Matrix.map_apply, hS i j, map_zero]`. Establish `hdet : IsUnit (blkD (g.map (incA D))).det`. Establish `h1 : IsUnit (mat γ).det`. Unfold `mat`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)`.

Rewrite `h1` using `[hg]`. Rewrite `h1` using `[det_eq_of_lowerLeft_zero _ hM]`. Conclude with `isUnit_of_mul_isUnit_right h1`. Establish `hinj : ∀ y : Fin n → AE D, blkD (g.map (incA D)) *ᵥ y = 0 → y = 0`. Introduce `y hy`.

Rewrite using `[← Matrix.one_mulVec y, ← Matrix.nonsing_inv_mul _ hdet, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]`. Establish `hsum : ∀ (x : Fin (n + n) → AE D) (i : Fin n), (∑ j, g.map (incA D) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) = 0` using `fun x i => Finset.sum_eq_zero fun j _ => by rw [hM i j, zero_mul]`. Introduce `x`. Rewrite using `[mem_upperHalf, mem_upperHalf]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx i`. Rewrite using `[mulVec_inr]`. Establish `h0 : (fun k => x (finSumFinEquiv (Sum.inr k))) = 0` using `funext hx`. Rewrite using `[hsum, h0, Matrix.mulVec_zero, zero_add]`. Both sides reduce to the same expression.

Introduce `hx`. Establish `h0 : (blkD (g.map (incA D)) *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) = 0`. Use function extensionality and compare the values at `i`. Use `hx i` as an intermediate fact. Rewrite `this` using `[mulVec_inr, hsum, zero_add]`.

Conclude with `this`. Establish `h1` using `hinj _ h0`. Conclude with `fun i => congrFun h1 i`.
-/
theorem clause3 : ∀ γ ∈ GF D n, ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = g.map (incA D) →
      (γ ∈ P D n ↔ IsSiegelP g) := by
  intro γ _ g hg
  rw [mem_P_iff, hg]
  constructor
  · intro h i j
    have hx : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
      rw [mem_upperHalf]
      intro k
      exact Pi.single_eq_of_ne (fun e => Sum.inr_ne_inl (finSumFinEquiv.injective e)) _
    have h2 := (mem_upperHalf _).1 ((h _).1 hx) i
    rw [Matrix.mulVec_single_one] at h2
    change incA D (g _ _) = 0 at h2
    exact incA_injective (h2.trans (map_zero _).symm)
  · intro hS
    have hM : ∀ i j : Fin n, g.map (incA D) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
      intro i j; rw [Matrix.map_apply, hS i j, map_zero]
    have hdet : IsUnit (blkD (g.map (incA D))).det := by
      have h1 : IsUnit (mat γ).det := by
        unfold mat
        exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
      rw [hg] at h1
      rw [det_eq_of_lowerLeft_zero _ hM] at h1
      exact isUnit_of_mul_isUnit_right h1
    have hinj : ∀ y : Fin n → AE D, blkD (g.map (incA D)) *ᵥ y = 0 → y = 0 := by
      intro y hy
      rw [← Matrix.one_mulVec y, ← Matrix.nonsing_inv_mul _ hdet, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
    have hsum : ∀ (x : Fin (n + n) → AE D) (i : Fin n), (∑ j, g.map (incA D) (finSumFinEquiv (Sum.inr i))
        (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) = 0 := fun x i =>
      Finset.sum_eq_zero fun j _ => by rw [hM i j, zero_mul]
    intro x
    rw [mem_upperHalf, mem_upperHalf]
    constructor
    · intro hx i
      rw [mulVec_inr]
      have h0 : (fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := funext hx
      rw [hsum, h0, Matrix.mulVec_zero, zero_add]
      rfl
    · intro hx
      have h0 : (blkD (g.map (incA D)) *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := by
        funext i
        have := hx i
        rw [mulVec_inr, hsum, zero_add] at this
        exact this
      have h1 := hinj _ h0
      exact fun i => congrFun h1 i

/- English proof (translation)
Introduce `_ _` and use `⟨clause1, clause2, clause3⟩`.
-/
theorem ratPtsUnn : RatPts := fun _ _ => ⟨clause1, clause2, clause3⟩

end GlobalTheory.CompanionTheory.RatPtsUnn
