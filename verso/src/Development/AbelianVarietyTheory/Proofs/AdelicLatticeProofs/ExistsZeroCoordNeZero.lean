import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate

open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.LocalQuad

namespace HermClass

section Congr

variable {E : Type*} [Field E] {c : E →+* E} {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

def Congr (c : E →+* E) (G G' : Matrix n n E) : Prop :=
  ∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by simp, by simp [Matrix.map_one _ (map_zero c) (map_one c)]⟩`.
-/
theorem Congr.refl (G : Matrix n n E) : Congr c G G :=
  ⟨1, by simp, by simp [Matrix.map_one _ (map_zero c) (map_one c)]⟩

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Take `⟨Q, hQ, rfl⟩` from `h'`. Use `⟨P * Q, by rw [Matrix.det_mul]; exact mul_ne_zero hP hQ, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem Congr.trans {G G' G'' : Matrix n n E} (h : Congr c G G') (h' : Congr c G' G'') :
    Congr c G G'' := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨Q, hQ, rfl⟩ := h'
  refine ⟨P * Q, by rw [Matrix.det_mul]; exact mul_ne_zero hP hQ, ?_⟩
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Establish `hu : IsUnit P.det` using `isUnit_iff_ne_zero.mpr hP`. Use `⟨P⁻¹, (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero, ?_⟩` and prove the remaining obligations. Establish `e1 : P⁻¹ᵀ * Pᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]`.

Establish `e2 : P.map c * P⁻¹.map c = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2, Matrix.one_mul, Matrix.mul_one]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem Congr.symm {G G' : Matrix n n E} (h : Congr c G G') : Congr c G' G := by
  obtain ⟨P, hP, rfl⟩ := h
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine ⟨P⁻¹, (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero, ?_⟩
  have e1 : P⁻¹ᵀ * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
  have e2 : P.map c * P⁻¹.map c = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  calc G = (P⁻¹ᵀ * Pᵀ) * G * (P.map c * P⁻¹.map c) := by
        rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Use `⟨P.det, hP, ?_⟩` and prove the remaining obligations. Establish `: (P.map c).det = c P.det` using `(RingHom.map_det c P).symm`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Congr.det {G G' : Matrix n n E} (h : Congr c G G') :
    ∃ x : E, x ≠ 0 ∧ G'.det = x * c x * G.det := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.det, hP, ?_⟩
  have : (P.map c).det = c P.det := (RingHom.map_det c P).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, this]
  ring

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Use `⟨P.submatrix e e, by rwa [Matrix.det_submatrix_equiv_self], ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`.
-/
theorem Congr.submatrix {G G' : Matrix n n E} (h : Congr c G G') (e : m ≃ n) :
    Congr c (G.submatrix e e) (G'.submatrix e e) := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.submatrix e e, by rwa [Matrix.det_submatrix_equiv_self], ?_⟩
  rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Use `⟨Matrix.fromBlocks P 0 0 1, by simpa using hP, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_zero _ (map_zero c)]`.
-/
theorem Congr.fromBlocks {G G' : Matrix n n E} (h : Congr c G G') (D : Matrix m m E) :
    Congr c (Matrix.fromBlocks G 0 0 D) (Matrix.fromBlocks G' 0 0 D) := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨Matrix.fromBlocks P 0 0 1, by simpa using hP, ?_⟩
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_zero _ (map_zero c)]

/- English proof (translation)
Set `e : Fin (r + 1) ≃ Fin r ⊕ PUnit.{1}` to `(finSuccEquiv r).trans (Equiv.optionEquivSumPUnit _)`. Establish `key : ∀ k : Fin (r + 1) → E, Matrix.diagonal k = (Matrix.fromBlocks (Matrix.diagonal fun i : Fin r => k i.succ) 0 0 (Matrix.diagonal fun _ : PUnit.{1} => k 0)).submatrix e e`. Introduce `k`. Rewrite using `[Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp [e]`. Rewrite using `[key g, key g', h0]`. Conclude with `(h.fromBlocks _).submatrix e`.
-/
theorem congr_diagonal_of_tail {r : ℕ} {g g' : Fin (r + 1) → E} (h0 : g 0 = g' 0)
    (h : Congr c (Matrix.diagonal fun i : Fin r => g i.succ)
      (Matrix.diagonal fun i : Fin r => g' i.succ)) :
    Congr c (Matrix.diagonal g) (Matrix.diagonal g') := by
  let e : Fin (r + 1) ≃ Fin r ⊕ PUnit.{1} := (finSuccEquiv r).trans (Equiv.optionEquivSumPUnit _)
  have key : ∀ k : Fin (r + 1) → E, Matrix.diagonal k =
      (Matrix.fromBlocks (Matrix.diagonal fun i : Fin r => k i.succ) 0 0
        (Matrix.diagonal fun _ : PUnit.{1} => k 0)).submatrix e e := by
    intro k
    rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [e]
  rw [key g, key g', h0]
  exact (h.fromBlocks _).submatrix e

end Congr

/- English proof (translation)
Distinguish the cases in `hi : z i = 0`. Use `swap`. Conclude with `⟨z, hi, h⟩`. Take `⟨j, hj⟩` from `Function.ne_iff.mp hz`. Establish `hj : z j ≠ 0` using `hj`.

Establish `hij : i ≠ j`. Introduce and unpack `rfl`. Conclude with `hj hi`. Establish `haj` using `ha j`. Use `set t : F := -(a i + a j) / (2 * a j * z j) with ht`.

Use `⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hij, hi]`. Establish `: ∀ k, a k * ((if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k) ^ 2 = (if k = i then a i else 0) + (if k = j then a j + 2 * t * a j * z j else 0) + t ^ 2 * (a k * z k ^ 2)`. Introduce `k`. Distinguish the cases in `h1 : k = i`.

Substitute `h1` using the available equality. Simplify using `[hij, hi]`. Distinguish the cases in `h2 : k = j`. Substitute `h2` using the available equality. Simplify using `only [h1, if_false, if_true]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1, h2, if_false]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[ht]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_zero_coord_ne_zero {F : Type*} [Field F] [CharZero F] {ι : Type*} [Fintype ι]
    {a : ι → F} (ha : ∀ i, a i ≠ 0) {z : ι → F} (hz : z ≠ 0) (h : ∑ i, a i * z i ^ 2 = 0)
    (i : ι) : ∃ w : ι → F, w i ≠ 0 ∧ ∑ k, a k * w k ^ 2 = 0 := by
  classical
  by_cases hi : z i = 0
  swap
  · exact ⟨z, hi, h⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
  have hj : z j ≠ 0 := hj
  have hij : i ≠ j := by
    rintro rfl
    exact hj hi
  have haj := ha j
  set t : F := -(a i + a j) / (2 * a j * z j) with ht
  refine ⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k, ?_, ?_⟩
  · simp [hij, hi]
  · have : ∀ k, a k * ((if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k) ^ 2 =
        (if k = i then a i else 0) + (if k = j then a j + 2 * t * a j * z j else 0) +
          t ^ 2 * (a k * z k ^ 2) := by
      intro k
      by_cases h1 : k = i
      · subst h1
        simp [hij, hi]
      · by_cases h2 : k = j
        · subst h2
          simp only [h1, if_false, if_true]
          ring
        · simp only [h1, h2, if_false]
          ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [ht]
    field_simp
    ring

def Isotropy : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (a : ι → F),
    5 ≤ Fintype.card ι → (∀ i, a i ≠ 0) → (∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) →
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `(IsCMField.complexConj_eq_self_iff E _).mp hx`.
-/
theorem mem_real {x : E} (hx : cc x = x) : x ∈ maximalRealSubfield E :=
  (IsCMField.complexConj_eq_self_iff E _).mp hx

/- English proof (translation)
Introduce `h`. Establish `h1` using `GlobalTheory.Published.embedding_cc τ x`. Rewrite `h1` using `[hx]`. Establish `h2 : (τ x).im = 0` using `Complex.conj_eq_iff_im.mp h1.symm`. Conclude with `(map_ne_zero τ).mpr h0 (Complex.ext h h2)`.
-/
theorem re_ne_zero (τ : E →+* ℂ) {x : E} (hx : cc x = x) (h0 : x ≠ 0) : (τ x).re ≠ 0 := by
  intro h
  have h1 := GlobalTheory.Published.embedding_cc τ x
  rw [hx] at h1
  have h2 : (τ x).im = 0 := Complex.conj_eq_iff_im.mp h1.symm
  exact (map_ne_zero τ).mpr h0 (Complex.ext h h2)

/- English proof (translation)
Take `⟨θ, h0, hθ⟩` from `GlobalTheory.Published.exists_cc_eq_neg E`. Take `⟨d, hd⟩` from `GlobalTheory.Published.exists_sq_real hθ`. Set `γ : Fin r → maximalRealSubfield E` to `fun i => ⟨g i, mem_real (hg i)⟩`. Set `κ : maximalRealSubfield E` to `⟨c, mem_real hc⟩`. Establish `hγ : ∀ i, γ i ≠ 0` using `fun i h => hg0 i (congrArg Subtype.val h)`.

Establish `hκ : κ ≠ 0` using `fun h => hc0 (congrArg Subtype.val h)`. Establish `hd0 : d ≠ 0` using `fun h => mul_ne_zero h0 h0 (hd.symm.trans (congrArg Subtype.val h))`. Set `a : Option (Fin r ⊕ Fin r) → maximalRealSubfield E` to `fun o => o.elim (-κ) (Sum.elim γ fun i => -d * γ i)`. Establish `ha : ∀ o, a o ≠ 0`. Introduce and unpack `(_ | i | i)`.

Conclude with `neg_ne_zero.mpr hκ`. Conclude with `hγ i`. Conclude with `mul_ne_zero (neg_ne_zero.mpr hd0) (hγ i)`. Take `⟨x, hx, hx0⟩` from `H (maximalRealSubfield E) (Option (Fin r ⊕ Fin r)) a (by simp; omega) ha (by`. Introduce `σ`.

Set `τ` to `ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)`. Establish `hτ : ∀ y : maximalRealSubfield E, (τ (y : E)).re = σ y` using `fun y => by`. Establish `: τ (y : E) = (Complex.ofRealHom.comp σ) y` using `ComplexEmbedding.lift_algebraMap_apply E _ y`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Take `⟨i, hi⟩` from `hs τ`. Establish `e1 : (τ (g i)).re = σ (γ i)` using `hτ (γ i)`. Establish `e2 : (τ c).re = σ κ` using `hτ κ`. Rewrite `hi` using `[e1, e2]`. Establish `n1 : σ (γ i) ≠ 0` using `(map_ne_zero σ).mpr (hγ i)`.

Establish `n2 : σ κ ≠ 0` using `(map_ne_zero σ).mpr hκ`. Break down `lt_or_gt_of_ne n2 with h | h` into its components or cases. Use `⟨some (Sum.inl i), none, ?_, ?_⟩` and prove the remaining obligations. Conclude with `lt_of_le_of_ne (not_lt.mp fun h' => absurd (hi.mp h') h.not_gt) n1`. Simplify `h` using `[a]`.

Use `⟨none, some (Sum.inl i), ?_, hi.mpr h⟩` and prove the remaining obligations. Simplify `h)` using `[a]`. Take `⟨w, hw, hw0⟩` from `exists_zero_coord_ne_zero ha hx hx0 none`. Rewrite `hw0` using `[Fintype.sum_option, Fintype.sum_sum_type]`. Establish `hw1` using `congrArg (Subtype.val : maximalRealSubfield E → E) hw0`.

Establish `hw2 : (w none : E) ≠ 0` using `fun h => hw (Subtype.ext h)`. Simplify using `[a, γ, κ, hd] at hw1`. Use `⟨fun i => ((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none, ?_⟩` and prove the remaining obligations. Establish `hcc : ∀ i, cc (((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none) = ((w (some (Sum.inl i)) : E) - w (some (Sum.inr i)) * θ) / w none`. Introduce `i`.

Establish `: IsCMField.complexConj E θ = -θ` using `hθ`. Simplify using `[cc, this, sub_eq_add_neg]`. Simplify using `only [herm, hcc, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `: ∀ i, ((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none * g i * (((w (some (Sum.inl i)) : E) - w (some (Sum.inr i)) * θ) / w none) = (g i * (w (some (Sum.inl i)) : E) ^ 2 - θ * θ * g i * (w (some (Sum.inr i)) : E) ^ 2) / (w none : E) ^ 2`. Introduce `i`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this, ← Finset.sum_div, Finset.sum_sub_distrib]`. Rewrite using `[div_eq_iff (pow_ne_zero 2 hw2)]`. Take the linear combination `hw1`.
-/
theorem exists_represent (H : Isotropy) {r : ℕ} (hr : 2 ≤ r) {g : Fin r → E}
    (hg : ∀ i, cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0) {c : E} (hc : cc c = c) (hc0 : c ≠ 0)
    (hs : ∀ τ : E →+* ℂ, ∃ i, (0 < (τ (g i)).re ↔ 0 < (τ c).re)) :
    ∃ z : Fin r → E, herm (Matrix.diagonal g) z z = c := by
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  obtain ⟨d, hd⟩ := GlobalTheory.Published.exists_sq_real hθ
  let γ : Fin r → maximalRealSubfield E := fun i => ⟨g i, mem_real (hg i)⟩
  let κ : maximalRealSubfield E := ⟨c, mem_real hc⟩
  have hγ : ∀ i, γ i ≠ 0 := fun i h => hg0 i (congrArg Subtype.val h)
  have hκ : κ ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (hd.symm.trans (congrArg Subtype.val h))
  let a : Option (Fin r ⊕ Fin r) → maximalRealSubfield E :=
    fun o => o.elim (-κ) (Sum.elim γ fun i => -d * γ i)
  have ha : ∀ o, a o ≠ 0 := by
    rintro (_ | i | i)
    · exact neg_ne_zero.mpr hκ
    · exact hγ i
    · exact mul_ne_zero (neg_ne_zero.mpr hd0) (hγ i)
  obtain ⟨x, hx, hx0⟩ := H (maximalRealSubfield E) (Option (Fin r ⊕ Fin r)) a
    (by simp; omega) ha (by
      intro σ
      let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)
      have hτ : ∀ y : maximalRealSubfield E, (τ (y : E)).re = σ y := fun y => by
        have : τ (y : E) = (Complex.ofRealHom.comp σ) y :=
          ComplexEmbedding.lift_algebraMap_apply E _ y
        rw [this]
        simp
      obtain ⟨i, hi⟩ := hs τ
      have e1 : (τ (g i)).re = σ (γ i) := hτ (γ i)
      have e2 : (τ c).re = σ κ := hτ κ
      rw [e1, e2] at hi
      have n1 : σ (γ i) ≠ 0 := (map_ne_zero σ).mpr (hγ i)
      have n2 : σ κ ≠ 0 := (map_ne_zero σ).mpr hκ
      rcases lt_or_gt_of_ne n2 with h | h
      · refine ⟨some (Sum.inl i), none, ?_, ?_⟩
        · exact lt_of_le_of_ne (not_lt.mp fun h' => absurd (hi.mp h') h.not_gt) n1
        · simpa [a] using h
      · refine ⟨none, some (Sum.inl i), ?_, hi.mpr h⟩
        simpa [a] using h)
  obtain ⟨w, hw, hw0⟩ := exists_zero_coord_ne_zero ha hx hx0 none
  rw [Fintype.sum_option, Fintype.sum_sum_type] at hw0
  have hw1 := congrArg (Subtype.val : maximalRealSubfield E → E) hw0
  have hw2 : (w none : E) ≠ 0 := fun h => hw (Subtype.ext h)
  simp [a, γ, κ, hd] at hw1
  refine ⟨fun i => ((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none, ?_⟩
  have hcc : ∀ i, cc (((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none) =
      ((w (some (Sum.inl i)) : E) - w (some (Sum.inr i)) * θ) / w none := by
    intro i
    have : IsCMField.complexConj E θ = -θ := hθ
    simp [cc, this, sub_eq_add_neg]
  simp only [herm, hcc, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have : ∀ i, ((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none * g i *
      (((w (some (Sum.inl i)) : E) - w (some (Sum.inr i)) * θ) / w none) =
      (g i * (w (some (Sum.inl i)) : E) ^ 2 -
        θ * θ * g i * (w (some (Sum.inr i)) : E) ^ 2) / (w none : E) ^ 2 := by
    intro i
    field_simp
    ring
  simp only [this, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [div_eq_iff (pow_ne_zero 2 hw2)]
  linear_combination hw1

noncomputable def posCount (τ : E →+* ℂ) {r : ℕ} (g : Fin r → E) : ℕ :=
  (Finset.univ.filter fun k => 0 < (τ (g k)).re).card

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Simplify using `only [posCount, Finset.card_filter, Fin.sum_univ_succ]`.
-/
theorem posCount_succ (τ : E →+* ℂ) {r : ℕ} (g : Fin (r + 1) → E) :
    posCount τ g = (if 0 < (τ (g 0)).re then 1 else 0) + posCount τ fun i : Fin r => g i.succ := by
  simp only [posCount, Finset.card_filter, Fin.sum_univ_succ]

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite using `[Matrix.diagonal_map (map_zero τ), GlobalTheory.Inertia.posIndex_diagonal]`. Both sides reduce to the same expression.
-/
theorem posIndex_diagonal_map (τ : E →+* ℂ) {r : ℕ} (g : Fin r → E) :
    GlobalTheory.Inertia.posIndex ((Matrix.diagonal g).map τ) = posCount τ g := by
  rw [Matrix.diagonal_map (map_zero τ), GlobalTheory.Inertia.posIndex_diagonal]
  rfl

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Conclude with `GlobalTheory.Inertia.posIndex_map_congr τ G hP`.
-/
theorem posIndex_of_congr (τ : E →+* ℂ) {r : ℕ} {G G' : Matrix (Fin r) (Fin r) E}
    (h : Congr (IsCMField.complexConj E : E →+* E) G G') :
    GlobalTheory.Inertia.posIndex (G'.map τ) = GlobalTheory.Inertia.posIndex (G.map τ) := by
  obtain ⟨P, hP, rfl⟩ := h
  exact GlobalTheory.Inertia.posIndex_map_congr τ G hP

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Distinguish the cases in `hj : 0 < (τ (g' j)).re`. Establish `h1 : posCount τ g = 0`. Rewrite using `[posCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]`.

Introduce `i _ hi`. Break down `hne i with h | h` into its components or cases. Conclude with `absurd hj (not_lt.mpr h.2)`. Conclude with `absurd hi (not_lt.mpr h.1)`. Rewrite `h1` using `[h, posCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]`.

Conclude with `h1 (Finset.mem_univ j) hj`. Establish `h1 : posCount τ g = Fintype.card (Fin r)`. Rewrite using `[posCount, Finset.card_eq_iff_eq_univ, Finset.filter_eq_self]`. Introduce `i _`. Break down `hne i with h | h` into its components or cases.

Conclude with `h.1`. Conclude with `absurd h.2 hj`. Rewrite `h1` using `[h, posCount, Finset.card_eq_iff_eq_univ, Finset.filter_eq_self]`. Conclude with `hj (h1 j (Finset.mem_univ j))`.
-/
theorem exists_sign_iff (τ : E →+* ℂ) {r : ℕ} {g g' : Fin r → E}
    (h : posCount τ g = posCount τ g') (j : Fin r) :
    ∃ i, (0 < (τ (g i)).re ↔ 0 < (τ (g' j)).re) := by
  by_contra hne
  push Not at hne
  by_cases hj : 0 < (τ (g' j)).re
  · have h1 : posCount τ g = 0 := by
      rw [posCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      rcases hne i with h | h
      · exact absurd hj (not_lt.mpr h.2)
      · exact absurd hi (not_lt.mpr h.1)
    rw [h, posCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    exact h1 (Finset.mem_univ j) hj
  · have h1 : posCount τ g = Fintype.card (Fin r) := by
      rw [posCount, Finset.card_eq_iff_eq_univ, Finset.filter_eq_self]
      intro i _
      rcases hne i with h | h
      · exact h.1
      · exact absurd h.2 hj
    rw [h, posCount, Finset.card_eq_iff_eq_univ, Finset.filter_eq_self] at h1
    exact hj (h1 j (Finset.mem_univ j))

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Introduce `g g' _ _ _ _ _ _`. Conclude with `GlobalTheory.Published.Landherr.size_zero _ _`. Consider the case `succ r ih`.

Introduce `g g' hg hg' h0 h0' hs ⟨x, hx⟩`. Establish `hp : ∏ i, g i ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => h0 i`. Establish `hp' : ∏ i, g' i ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => h0' i`. Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Use `GlobalTheory.Published.Landherr.size_one _ _ (by rwa [Matrix.det_diagonal]) (by rwa [Matrix.det_diagonal]) ⟨x, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_diagonal, Matrix.det_diagonal, hx, mul_div_cancel_right₀ _ hp']`. Take `⟨z, hz⟩` from `exists_represent H (by omega) hg h0 (hg' 0) (h0' 0) fun τ => exists_sign_iff τ (hs τ) 0`. Establish `hG : ∀ a b, cc (Matrix.diagonal g a b) = Matrix.diagonal g b a`. Introduce `a b`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `using hg a`. Simplify using `[Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), cc]`. Take `⟨P, k, hP, hPk, hk, hk0, -, hk1⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal_herm_col_eq hG (x := z) (hz ▸ h0' 0) 0`. Establish `hk0` using `hk0 (by rwa [Matrix.det_diagonal])`.

Establish `hc : Congr (IsCMField.complexConj E : E →+* E) (Matrix.diagonal g) (Matrix.diagonal k)` using `⟨P, hP, hPk.symm⟩`. Establish `hk2 : k 0 = g' 0` using `hk1.trans hz`. Use `hc.trans (congr_diagonal_of_tail hk2 (ih _ _ (fun i => hk _) (fun i => hg' _) (fun i => hk0 _) (fun i => h0' _) (fun τ => ?_) ?_))` and prove the remaining obligations. Establish `h1` using `posIndex_of_congr τ hc`. Rewrite `h1` using `[posIndex_diagonal_map, posIndex_diagonal_map, hs τ, posCount_succ, posCount_succ τ g', hk2]`.

Conclude with `Nat.add_left_cancel h1`. Take `⟨y, -, hy⟩` from `hc.det`. Rewrite `hy` using `[Matrix.det_diagonal, Matrix.det_diagonal, hx, Fin.prod_univ_succ, Fin.prod_univ_succ, hk2]`. Use `⟨y * x, mul_left_cancel₀ (h0' 0) ?_⟩` and prove the remaining obligations. Rewrite using `[hy]`.

Simplify using `only [cc, map_mul, RingHom.coe_coe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem congr_diagonal (H : Isotropy) (r : ℕ) : ∀ g g' : Fin r → E,
    (∀ i, cc (g i) = g i) → (∀ i, cc (g' i) = g' i) → (∀ i, g i ≠ 0) → (∀ i, g' i ≠ 0) →
    (∀ τ : E →+* ℂ, posCount τ g = posCount τ g') →
    (∃ x : E, ∏ i, g i = x * cc x * ∏ i, g' i) →
    Congr (IsCMField.complexConj E : E →+* E) (Matrix.diagonal g) (Matrix.diagonal g') := by
  induction r with
  | zero =>
    intro g g' _ _ _ _ _ _
    exact GlobalTheory.Published.Landherr.size_zero _ _
  | succ r ih =>
    intro g g' hg hg' h0 h0' hs ⟨x, hx⟩
    have hp : ∏ i, g i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0 i
    have hp' : ∏ i, g' i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0' i
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · refine GlobalTheory.Published.Landherr.size_one _ _ (by rwa [Matrix.det_diagonal])
        (by rwa [Matrix.det_diagonal]) ⟨x, ?_⟩
      rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, mul_div_cancel_right₀ _ hp']
    obtain ⟨z, hz⟩ := exists_represent H (by omega) hg h0 (hg' 0) (h0' 0)
      fun τ => exists_sign_iff τ (hs τ) 0
    have hG : ∀ a b, cc (Matrix.diagonal g a b) = Matrix.diagonal g b a := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simpa using hg a
      · simp [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), cc]
    obtain ⟨P, k, hP, hPk, hk, hk0, -, hk1⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal_herm_col_eq hG (x := z) (hz ▸ h0' 0) 0
    have hk0 := hk0 (by rwa [Matrix.det_diagonal])
    have hc : Congr (IsCMField.complexConj E : E →+* E) (Matrix.diagonal g) (Matrix.diagonal k) :=
      ⟨P, hP, hPk.symm⟩
    have hk2 : k 0 = g' 0 := hk1.trans hz
    refine hc.trans (congr_diagonal_of_tail hk2 (ih _ _ (fun i => hk _) (fun i => hg' _)
      (fun i => hk0 _) (fun i => h0' _) (fun τ => ?_) ?_))
    · have h1 := posIndex_of_congr τ hc
      rw [posIndex_diagonal_map, posIndex_diagonal_map, hs τ, posCount_succ, posCount_succ τ g',
        hk2] at h1
      exact Nat.add_left_cancel h1
    · obtain ⟨y, -, hy⟩ := hc.det
      rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, Fin.prod_univ_succ, Fin.prod_univ_succ,
        hk2] at hy
      refine ⟨y * x, mul_left_cancel₀ (h0' 0) ?_⟩
      rw [hy]
      simp only [cc, map_mul, RingHom.coe_coe]
      ring

end HermClass

open HermClass in

/- English proof (translation)
Introduce `E _ _ _ r G G' hG hG' hd hd' hs ⟨x, hx⟩`. Take `⟨P, g, hP, hPg, hg, hg0⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal_herm hG`. Take `⟨P', g', hP', hPg', hg', hg0'⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal_herm hG'`. Establish `hc : Congr (IsCMField.complexConj E : E →+* E) G (Matrix.diagonal g)` using `⟨P, hP, hPg.symm⟩`. Establish `hc' : Congr (IsCMField.complexConj E : E →+* E) G' (Matrix.diagonal g')` using `⟨P', hP', hPg'.symm⟩`.

Use `(hc.trans (congr_diagonal H r g g' hg hg' (hg0 hd) (hg0' hd') (fun τ => ?_) ?_)).trans hc'.symm` and prove the remaining obligations. Take `⟨Q, hQ, h⟩` from `hs τ`. Rewrite using `[← posIndex_diagonal_map, ← posIndex_diagonal_map, posIndex_of_congr τ hc, posIndex_of_congr τ hc', h, GlobalTheory.Inertia.posIndex_congr _ hQ]`. Take `⟨y, -, hy⟩` from `hc.det`. Take `⟨y', -, hy'⟩` from `hc'.symm.det`.

Rewrite `hx` using `[div_eq_iff hd']`. Rewrite `hy`, `hy'` using `[Matrix.det_diagonal]`. Use `⟨y * x * y', ?_⟩` and prove the remaining obligations. Rewrite using `[hy, hx, hy']`. Simplify using `only [cc, map_mul, RingHom.coe_coe]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem landherr_of_isotropy
    (H : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (a : ι → F),
      5 ≤ Fintype.card ι → (∀ i, a i ≠ 0) → (∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) →
      ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) :
    GlobalTheory.Published.Landherr := by
  intro E _ _ _ r G G' hG hG' hd hd' hs ⟨x, hx⟩
  obtain ⟨P, g, hP, hPg, hg, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  obtain ⟨P', g', hP', hPg', hg', hg0'⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG'
  have hc : Congr (IsCMField.complexConj E : E →+* E) G (Matrix.diagonal g) := ⟨P, hP, hPg.symm⟩
  have hc' : Congr (IsCMField.complexConj E : E →+* E) G' (Matrix.diagonal g') :=
    ⟨P', hP', hPg'.symm⟩
  refine (hc.trans (congr_diagonal H r g g' hg hg' (hg0 hd) (hg0' hd') (fun τ => ?_) ?_)).trans
    hc'.symm
  · obtain ⟨Q, hQ, h⟩ := hs τ
    rw [← posIndex_diagonal_map, ← posIndex_diagonal_map, posIndex_of_congr τ hc,
      posIndex_of_congr τ hc', h, GlobalTheory.Inertia.posIndex_congr _ hQ]
  · obtain ⟨y, -, hy⟩ := hc.det
    obtain ⟨y', -, hy'⟩ := hc'.symm.det
    rw [div_eq_iff hd'] at hx
    rw [Matrix.det_diagonal] at hy hy'
    refine ⟨y * x * y', ?_⟩
    rw [hy, hx, hy']
    simp only [cc, map_mul, RingHom.coe_coe]
    ring

end GlobalTheory.LocalQuad
