import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.UnitaryDetClass

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ColumnMapShift

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

/- English proof (translation)
Rewrite using `[φ.as_sum, map_sum]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial]`. Establish `hdeg : (Finsupp.weight w) d = m` using `hφ (mem_support_iff.mp hd)`. Establish `h1 : IsWeightedHomogeneous w' (d.prod fun i k => v i ^ k) (∑ i ∈ d.support, d i • w i)` using `IsWeightedHomogeneous.prod _ _ _ fun i _ => (hv i).pow (d i)`.

Establish `h2 : (∑ i ∈ d.support, d i • w i) = m`. Rewrite using `[← hdeg, Finsupp.weight_apply, Finsupp.sum]`. Rewrite `h1` using `[h2]`. Establish `h3` using `(isWeightedHomogeneous_C w' (coeff d φ)).mul h1`. Rewrite `h3` using `[zero_add]`.

Rewrite using `[MvPolynomial.algebraMap_eq]`. Conclude with `h3`.
-/
theorem aeval_weightedHomogeneous {K σ τ : Type} [CommRing K] {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ K} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (v : σ → MvPolynomial τ K) (hv : ∀ i, IsWeightedHomogeneous w' (v i) (w i)) :
    IsWeightedHomogeneous w' (aeval v φ) m := by
  classical
  rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : (Finsupp.weight w) d = m := hφ (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (d.prod fun i k => v i ^ k) (∑ i ∈ d.support, d i • w i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hv i).pow (d i)
  have h2 : (∑ i ∈ d.support, d i • w i) = m := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w' (coeff d φ)).mul h1
  rw [zero_add] at h3
  rw [MvPolynomial.algebraMap_eq]
  exact h3

section Col

variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]

def colMap (r : T → ℕ) (g : T → Fin n → Fin n → k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ : Letter T r n => ∑ b, C (g ℓ.1 b ℓ.2.2) * X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter T r n)

/- English proof (translation)
Rewrite using `[rowShift, aeval_X, if_pos ⟨b, rfl⟩]`.
-/
theorem rowShift_X_self (σ : T) (i i' : Fin (r σ)) (t : k) (b : Fin n) :
    rowShift r n k σ i i' t (X ⟨σ, i, b⟩) = X ⟨σ, i, b⟩ + C t * X ⟨σ, i', b⟩ := by
  rw [rowShift, aeval_X, if_pos ⟨b, rfl⟩]

/- English proof (translation)
Rewrite using `[rowShift, aeval_X, if_neg]`. Introduce and unpack `⟨b', hb⟩`. Apply `h` to reduce the goal to its premises. Conclude with `congrArg (fun ℓ : Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s))) hb`.
-/
theorem rowShift_X_ne (σ : T) (i i' : Fin (r σ)) (t : k) (τ : T) (j : Fin (r τ))
    (h : (⟨τ, j⟩ : Σ s, Fin (r s)) ≠ ⟨σ, i⟩) (b : Fin n) :
    rowShift r n k σ i i' t (X ⟨τ, j, b⟩) = X ⟨τ, j, b⟩ := by
  rw [rowShift, aeval_X, if_neg]
  rintro ⟨b', hb⟩
  apply h
  exact congrArg (fun ℓ : Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s))) hb

/- English proof (translation)
Rewrite using `[colMap, aeval_X]`.
-/
theorem colMap_X (g : T → Fin n → Fin n → k) (τ : T) (j : Fin (r τ)) (b : Fin n) :
    colMap r g (X ⟨τ, j, b⟩) = ∑ b', C (g τ b' b) * X (⟨τ, j, b'⟩ : Letter T r n) := by
  rw [colMap, aeval_X]

/- English proof (translation)
Establish `h : (rowShift r n k σ i i' t).comp (colMap r g) = (colMap r g).comp (rowShift r n k σ i i' t)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨τ, j, b⟩`. Simplify using `only [AlgHom.comp_apply]`. Distinguish the cases in `h : (⟨τ, j⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩`.

Consider the cases of `h`. Simplify using `only [rowShift_X_self, colMap_X, map_sum, map_mul, map_add, algHom_C, algebraMap_eq, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `only [rowShift_X_ne σ i i' t τ j h, colMap_X, map_sum, map_mul, algHom_C, algebraMap_eq]`. Conclude with `DFunLike.congr_fun h P`.
-/
theorem rowShift_colMap (g : T → Fin n → Fin n → k) (σ : T) (i i' : Fin (r σ)) (t : k)
    (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k σ i i' t (colMap r g P) = colMap r g (rowShift r n k σ i i' t P) := by
  have h : (rowShift r n k σ i i' t).comp (colMap r g) = (colMap r g).comp (rowShift r n k σ i i' t) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, j, b⟩
    simp only [AlgHom.comp_apply]
    by_cases h : (⟨τ, j⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩
    · cases h
      simp only [rowShift_X_self, colMap_X, map_sum, map_mul, map_add, algHom_C, algebraMap_eq,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp only [rowShift_X_ne σ i i' t τ j h, colMap_X, map_sum, map_mul, algHom_C, algebraMap_eq]
  exact DFunLike.congr_fun h P

/- English proof (translation)
Introduce `σ i i' hi t`. Rewrite using `[rowShift_colMap, hP σ i i' hi t]`.
-/
theorem rowInv_colMap (g : T → Fin n → Fin n → k) {P : MvPolynomial (Letter T r n) k}
    (hP : RowInv r n k P) : RowInv r n k (colMap r g P) := by
  intro σ i i' hi t
  rw [rowShift_colMap, hP σ i i' hi t]

open Classical in

def rowWt (n : ℕ) (σ : T) (i : Fin (r σ)) (ℓ : Letter T r n) : ℕ :=
  if (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩ then 1 else 0

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]`. Simplify using `[rowWt]`. Introduce `j _ hj`. Simplify using `[rowWt, hj]`. Simplify using the standard rewrite rules.

Introduce `σ' _ hσ`. Simplify using `[rowWt, hσ]`. Simplify using the standard rewrite rules.
-/
theorem weight_rowWt [Fintype T] (σ : T) (i : Fin (r σ)) (m : Letter T r n →₀ ℕ) :
    Finsupp.weight (rowWt n σ i) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
    Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [rowWt]
  · intro j _ hj
    simp [rowWt, hj]
  · simp
  · intro σ' _ hσ
    simp [rowWt, hσ]
  · simp

/- English proof (translation)
Introduce `m hm σ i`. Establish `h1 : IsWeightedHomogeneous (rowWt n σ i) P (a σ i)`. Introduce `d hd`. Rewrite using `[weight_rowWt]`. Conclude with `hP d (mem_support_iff.2 hd) σ i`.

Establish `h2 : IsWeightedHomogeneous (rowWt n σ i) (colMap r g P) (a σ i)`. Use `aeval_weightedHomogeneous h1 _ fun ℓ => ?_` and prove the remaining obligations. Use `IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_` and prove the remaining obligations. Conclude with `IsWeightedHomogeneous.C_mul (isWeightedHomogeneous_X k (rowWt n σ i) ⟨ℓ.1, ℓ.2.1, b⟩) _`. Rewrite using `[← weight_rowWt]`.

Conclude with `h2 (mem_support_iff.1 hm)`.
-/
theorem rowDeg_colMap [Fintype T] (g : T → Fin n → Fin n → k) {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) : RowDeg r n k a (colMap r g P) := by
  intro m hm σ i
  have h1 : IsWeightedHomogeneous (rowWt n σ i) P (a σ i) := by
    intro d hd
    rw [weight_rowWt]
    exact hP d (mem_support_iff.2 hd) σ i
  have h2 : IsWeightedHomogeneous (rowWt n σ i) (colMap r g P) (a σ i) := by
    refine aeval_weightedHomogeneous h1 _ fun ℓ => ?_
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    exact IsWeightedHomogeneous.C_mul (isWeightedHomogeneous_X k (rowWt n σ i) ⟨ℓ.1, ℓ.2.1, b⟩) _
  rw [← weight_rowWt]
  exact h2 (mem_support_iff.1 hm)

end Col

/- English proof (translation)
Introduce `E _ _ _ H Dw l c n γ P a`. Establish `e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw` using `Dw) c γ = colMap Dw.mult fun σ b j => embF c σ (γ b j) := rfl`. Rewrite using `[e]`. Conclude with `⟨rowInv_colMap _, rowDeg_colMap _⟩`.
-/
theorem push_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F), ∀ (a : (E →+* ℂ) → ℕ → ℕ), (RowInv Dw.mult n c.F P → RowInv Dw.mult n c.F (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P)) ∧ (RowDeg Dw.mult n c.F a P → RowDeg Dw.mult n c.F a (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P)) := by
  intro E _ _ _ H Dw l c n γ P a
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ = colMap Dw.mult fun σ b j => embF c σ (γ b j) := rfl
  rw [e]
  exact ⟨rowInv_colMap _, rowDeg_colMap _⟩

end GlobalTheory.Proof.ColumnMapShift
