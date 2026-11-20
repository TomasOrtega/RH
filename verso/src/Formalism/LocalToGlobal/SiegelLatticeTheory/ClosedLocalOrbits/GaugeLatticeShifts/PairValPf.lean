import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellBru

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def CellPointUniq : Prop :=
  ∀ (K : Type) [Field K] (N : ℕ) (p p' : Point K N) (L U L' U' : Matrix (Fin N) (Fin N) K),
    IsLoUni L → IsUpUni U → IsLoUni L' → IsUpUni U' → L * ptMat p * U = L' * ptMat p' * U' → p = p'

def DecompSimple : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (p : Point K N) (L U L' U' : Matrix (Fin N) (Fin N) K),
    IsLoUni L → IsUpUni U → IsLoUni L' → IsUpUni U' → L * ptMat p * U = L' * ptMat p * U' →
      sgLo L + sgUp U = sgLo L' + sgUp U'

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Take `⟨p₁, e₁⟩` from `h₁`. Take `⟨p₂, e₂⟩` from `h₂`. Use `const_of_mk (fun y : Carrier P => IsInCell (ZhatOM (ZhatL F y.1)) w) (fun a b hab => propext (hC a b hab w)) (e₁.trans e₂.symm)` as an intermediate fact. Conclude with `Iff.of_eq this`.
-/
theorem cell_rep_iff {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {P : LFlag S r T' → Prop}
    (hC : CellFun Λ F P) {t : TermQ Λ F P} {F₁ F₂ : LFlag S r T'} (h₁ : TermDef.Rep Λ F P t F₁)
    (h₂ : TermDef.Rep Λ F P t F₂) (w : Point E (r + 1)) :
    IsInCell (ZhatOM (ZhatL F F₁)) w ↔ IsInCell (ZhatOM (ZhatL F F₂)) w := by
  obtain ⟨p₁, e₁⟩ := h₁
  obtain ⟨p₂, e₂⟩ := h₂
  have := const_of_mk (fun y : Carrier P => IsInCell (ZhatOM (ZhatL F y.1)) w)
    (fun a b hab => propext (hC a b hab w)) (e₁.trans e₂.symm)
  exact Iff.of_eq this

end Gen

section Mat

variable {K : Type} [Field K] [NumberField K] {N : ℕ}

/- English proof (translation)
Unfold `psiInf`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Rewrite using `[map_add]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem psiInf_add (g : ℕ) (x y : K) : psiInf g (x + y) = psiInf g x * psiInf g y := by
  unfold psiInf
  rw [← Complex.exp_add]
  congr 1
  rw [map_add]
  push_cast
  ring

/- English proof (translation)
Unfold `sgLo`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Matrix.mul_apply]`.

Establish `hne : (⟨a.val + 1, h⟩ : Fin N) ≠ a` using `fun e => by have := congrArg Fin.val e; simp at this`. Establish `h0 : ∀ c ∈ (Finset.univ : Finset (Fin N)), c ≠ ⟨a.val + 1, h⟩ ∧ c ≠ a → A ⟨a.val + 1, h⟩ c * B c a = 0`. Introduce `c _ hc`. Break down `lt_trichotomy c.val a.val with h1 | h1 | h1` into its components or cases. Rewrite using `[(hB c a).1 (by exact h1), mul_zero]`.

Conclude with `absurd (Fin.ext h1) hc.2`. Break down `lt_or_eq_of_le (Nat.succ_le_of_lt h1) with h2 | h2` into its components or cases. Rewrite using `[(hA ⟨a.val + 1, h⟩ c).1 (by show a.val + 1 < c.val; omega), zero_mul]`. Conclude with `absurd (Fin.ext (by simp; omega)) hc.1`. Rewrite using `[Finset.sum_eq_add _ _ hne h0 (by simp) (by simp)]`.

Rewrite using `[(hA _ _).2 rfl, (hB _ _).2 rfl]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem sgLo_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsLoUni A) (hB : IsLoUni B) :
    sgLo (A * B) = sgLo A + sgLo B := by
  unfold sgLo
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [Matrix.mul_apply]
    have hne : (⟨a.val + 1, h⟩ : Fin N) ≠ a := fun e => by have := congrArg Fin.val e; simp at this
    have h0 : ∀ c ∈ (Finset.univ : Finset (Fin N)), c ≠ ⟨a.val + 1, h⟩ ∧ c ≠ a →
        A ⟨a.val + 1, h⟩ c * B c a = 0 := by
      intro c _ hc
      rcases lt_trichotomy c.val a.val with h1 | h1 | h1
      · rw [(hB c a).1 (by exact h1), mul_zero]
      · exact absurd (Fin.ext h1) hc.2
      · rcases lt_or_eq_of_le (Nat.succ_le_of_lt h1) with h2 | h2
        · rw [(hA ⟨a.val + 1, h⟩ c).1 (by show a.val + 1 < c.val; omega), zero_mul]
        · exact absurd (Fin.ext (by simp; omega)) hc.1
    rw [Finset.sum_eq_add _ _ hne h0 (by simp) (by simp)]
    rw [(hA _ _).2 rfl, (hB _ _).2 rfl]; ring
  · simp

/- English proof (translation)
Unfold `sgUp`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Matrix.mul_apply]`.

Establish `hne : (⟨a.val + 1, h⟩ : Fin N) ≠ a` using `fun e => by have := congrArg Fin.val e; simp at this`. Establish `h0 : ∀ c ∈ (Finset.univ : Finset (Fin N)), c ≠ ⟨a.val + 1, h⟩ ∧ c ≠ a → A a c * B c ⟨a.val + 1, h⟩ = 0`. Introduce `c _ hc`. Break down `lt_trichotomy c.val a.val with h1 | h1 | h1` into its components or cases. Rewrite using `[(hA a c).1 (by exact h1), zero_mul]`.

Conclude with `absurd (Fin.ext h1) hc.2`. Break down `lt_or_eq_of_le (Nat.succ_le_of_lt h1) with h2 | h2` into its components or cases. Rewrite using `[(hB c ⟨a.val + 1, h⟩).1 (by show a.val + 1 < c.val; omega), mul_zero]`. Conclude with `absurd (Fin.ext (by simp; omega)) hc.1`. Rewrite using `[Finset.sum_eq_add _ _ hne h0 (by simp) (by simp)]`.

Rewrite using `[(hA _ _).2 rfl, (hB _ _).2 rfl]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem sgUp_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A) (hB : IsUpUni B) :
    sgUp (A * B) = sgUp A + sgUp B := by
  unfold sgUp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [Matrix.mul_apply]
    have hne : (⟨a.val + 1, h⟩ : Fin N) ≠ a := fun e => by have := congrArg Fin.val e; simp at this
    have h0 : ∀ c ∈ (Finset.univ : Finset (Fin N)), c ≠ ⟨a.val + 1, h⟩ ∧ c ≠ a →
        A a c * B c ⟨a.val + 1, h⟩ = 0 := by
      intro c _ hc
      rcases lt_trichotomy c.val a.val with h1 | h1 | h1
      · rw [(hA a c).1 (by exact h1), zero_mul]
      · exact absurd (Fin.ext h1) hc.2
      · rcases lt_or_eq_of_le (Nat.succ_le_of_lt h1) with h2 | h2
        · rw [(hB c ⟨a.val + 1, h⟩).1 (by show a.val + 1 < c.val; omega), mul_zero]
        · exact absurd (Fin.ext (by simp; omega)) hc.1
    rw [Finset.sum_eq_add _ _ hne h0 (by simp) (by simp)]
    rw [(hA _ _).2 rfl, (hB _ _).2 rfl]; ring
  · simp

/- English proof (translation)
Rewrite using `[phasePair, psiInf_add, mul_inv]`.
-/
theorem phasePair_eq (g : ℕ) (L U : Matrix (Fin N) (Fin N) K) :
    phasePair g L U = (psiInf g (sgLo L + sgUp U))⁻¹ := by
  rw [phasePair, psiInf_add, mul_inv]

end Mat

section PtStruct

variable {K : Type*} [Field K]

def pσ : List (K × ℕ) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < s then s - 1 - i else s + pσ bs (i - s)

def pv : List (K × ℕ) → ℕ → K
  | [], _ => 0
  | (t, s) :: bs, i => if i < s then t else pv bs (i - s)

/- English proof (translation)
The claim follows from `| [], i, j, h => by simp at h | (t, s) :: bs, i, j, h => by simp only [List.map_cons, List.sum_cons] at h by_cases hi : i < s · have e1 : pσ ((t, s) :: bs) i = s - 1 - i := by simp [pσ, hi] have e2 : pv ((t, s) :: bs) i = t := by simp [pv, hi] rw [e1, e2] simp only [ptEntry] by_c …`.
-/
theorem ptEntry_eq_pv : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum →
    ptEntry bs i j = if j = pσ bs i then pv bs i else 0
  | [], i, j, h => by simp at h
  | (t, s) :: bs, i, j, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · have e1 : pσ ((t, s) :: bs) i = s - 1 - i := by simp [pσ, hi]
      have e2 : pv ((t, s) :: bs) i = t := by simp [pv, hi]
      rw [e1, e2]
      simp only [ptEntry]
      by_cases hj : j < s
      · rw [if_pos ⟨hi, hj⟩]
        by_cases e : i + j + 1 = s
        · rw [if_pos e, if_pos (by omega)]
        · rw [if_neg e, if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · have e1 : pσ ((t, s) :: bs) i = s + pσ bs (i - s) := by simp [pσ, hi]
      have e2 : pv ((t, s) :: bs) i = pv bs (i - s) := by simp [pv, hi]
      rw [e1, e2]
      simp only [ptEntry]
      by_cases hj : j < s
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg (by omega), if_pos (by omega), ptEntry_eq_pv bs (i - s) (j - s) (by omega)]
        by_cases e : j - s = pσ bs (i - s)
        · rw [if_pos e, if_pos (by omega)]
        · rw [if_neg e, if_neg (by omega)]

/- English proof (translation)
The claim follows from `| [], i, h => by simp at h | (t, s) :: bs, i, h => by simp only [List.map_cons, List.sum_cons] at h ⊢ simp only [pσ] split_ifs with hi · omega · have := pσ_lt bs (i - s) (by omega); omega`.
-/
theorem pσ_lt : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum → pσ bs i < (bs.map Prod.snd).sum
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    simp only [pσ]
    split_ifs with hi
    · omega
    · have := pσ_lt bs (i - s) (by omega); omega

/- English proof (translation)
The claim follows from `| [], i, h => by simp at h | (t, s) :: bs, i, h => by simp only [List.map_cons, List.sum_cons] at h by_cases hi : i < s · simp only [pσ, if_pos hi] rw [if_pos (by omega)]; omega · simp only [pσ, if_neg hi] rw [if_neg (by omega), show s + pσ bs (i - s) - s = pσ bs (i - s) by omega …`.
-/
theorem pσ_inv : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum → pσ bs (pσ bs i) = i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pσ, if_pos hi]
      rw [if_pos (by omega)]; omega
    · simp only [pσ, if_neg hi]
      rw [if_neg (by omega), show s + pσ bs (i - s) - s = pσ bs (i - s) by omega, pσ_inv bs (i - s) (by omega)]
      omega

/- English proof (translation)
The claim follows from `| [], _, i, h => by simp at h | (t, s) :: bs, hv, i, h => by simp only [List.map_cons, List.sum_cons] at h simp only [pv] split_ifs with hi · exact (hv (t, s) (by simp)).1 · exact pv_ne bs (fun b hb => hv b (by simp [hb])) (i - s) (by omega)`.
-/
theorem pv_ne : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i < (bs.map Prod.snd).sum →
    pv bs i ≠ 0
  | [], _, i, h => by simp at h
  | (t, s) :: bs, hv, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [pv]
    split_ifs with hi
    · exact (hv (t, s) (by simp)).1
    · exact pv_ne bs (fun b hb => hv b (by simp [hb])) (i - s) (by omega)

/- English proof (translation)
The claim follows from `| [], _, i, h => by simp at h | (t, s) :: bs, hv, i, h => by simp only [List.map_cons, List.sum_cons] at h by_cases h1 : i + 1 < s · left have a1 : pσ ((t, s) :: bs) (i + 1) = s - 1 - (i + 1) := by simp [pσ, h1] have a2 : pσ ((t, s) :: bs) i = s - 1 - i := by simp [pσ, show i < s …`.
-/
theorem pσ_nb : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i + 1 < (bs.map Prod.snd).sum →
    (pσ bs (i + 1) + 1 = pσ bs i ∧ pv bs (i + 1) = pv bs i) ∨ pσ bs i < pσ bs (i + 1)
  | [], _, i, h => by simp at h
  | (t, s) :: bs, hv, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases h1 : i + 1 < s
    · left
      have a1 : pσ ((t, s) :: bs) (i + 1) = s - 1 - (i + 1) := by simp [pσ, h1]
      have a2 : pσ ((t, s) :: bs) i = s - 1 - i := by simp [pσ, show i < s by omega]
      have a3 : pv ((t, s) :: bs) (i + 1) = t := by simp [pv, h1]
      have a4 : pv ((t, s) :: bs) i = t := by simp [pv, show i < s by omega]
      rw [a1, a2, a3, a4]; exact ⟨by omega, rfl⟩
    · by_cases h2 : i < s
      · right
        simp only [pσ, if_pos h2, if_neg h1]
        omega
      · simp only [pσ, pv, if_neg h1, if_neg h2]
        have e : i + 1 - s = (i - s) + 1 := by omega
        rw [e]
        rcases pσ_nb bs (fun b hb => hv b (by simp [hb])) (i - s) (by omega) with ⟨a, b⟩ | c
        · left; exact ⟨by omega, b⟩
        · right; omega

end PtStruct

section Tri

variable {K : Type} [Field K] {N : ℕ}

/- English proof (translation)
Establish `hB : L.BlockTriangular OrderDual.toDual` using `fun i j hij => (h i j).1 hij`. Establish `hdet : L.det = 1`. Rewrite using `[Matrix.det_of_isLowerTriangular L hB]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`. Establish `hu : IsUnit L.det` using `by rw [hdet]; exact isUnit_one`.

Establish `h1` using `Matrix.nonsing_inv_mul L hu`. Establish `h2` using `Matrix.mul_nonsing_inv L hu`. Use `letI : Invertible L := Matrix.invertibleOfIsUnitDet L hu`. Establish `hBi` using `Matrix.blockTriangular_inv_of_blockTriangular hB`. Use `⟨fun i j => ⟨fun hij => hBi hij, fun hij => ?_⟩, h1, h2⟩` and prove the remaining obligations.

Substitute `hij` using the available equality. Use `congrFun (congrFun h1 i) i` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `this` using `[(h i i).2 rfl, mul_one]`. Simplify using `using this`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases. Rewrite using `[(h k i).1 hk, mul_zero]`. Rewrite using `[hBi (show OrderDual.toDual k < OrderDual.toDual i from hk), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem loUni_inv {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) :
    IsLoUni L⁻¹ ∧ L⁻¹ * L = 1 ∧ L * L⁻¹ = 1 := by
  have hB : L.BlockTriangular OrderDual.toDual := fun i j hij => (h i j).1 hij
  have hdet : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L hB]
    exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  have hu : IsUnit L.det := by rw [hdet]; exact isUnit_one
  have h1 := Matrix.nonsing_inv_mul L hu
  have h2 := Matrix.mul_nonsing_inv L hu
  letI : Invertible L := Matrix.invertibleOfIsUnitDet L hu
  have hBi := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun i j => ⟨fun hij => hBi hij, fun hij => ?_⟩, h1, h2⟩
  subst hij
  have := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at this
  · rw [(h i i).2 rfl, mul_one] at this; simpa using this
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [(h k i).1 hk, mul_zero]
    · rw [hBi (show OrderDual.toDual k < OrderDual.toDual i from hk), zero_mul]
  · simp

/- English proof (translation)
Establish `hB : U.BlockTriangular id` using `fun i j hij => (h i j).1 hij`. Establish `hdet : U.det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular hB]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`. Establish `hu : IsUnit U.det` using `by rw [hdet]; exact isUnit_one`.

Establish `h1` using `Matrix.nonsing_inv_mul U hu`. Establish `h2` using `Matrix.mul_nonsing_inv U hu`. Use `letI : Invertible U := Matrix.invertibleOfIsUnitDet U hu`. Establish `hBi` using `Matrix.blockTriangular_inv_of_blockTriangular hB`. Use `⟨fun i j => ⟨fun hij => hBi hij, fun hij => ?_⟩, h1, h2⟩` and prove the remaining obligations.

Substitute `hij` using the available equality. Use `congrFun (congrFun h1 i) i` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `this` using `[(h i i).2 rfl, mul_one]`. Simplify using `using this`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases. Rewrite using `[hBi (show id k < id i from hk), zero_mul]`. Rewrite using `[(h k i).1 hk, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem upUni_inv {U : Matrix (Fin N) (Fin N) K} (h : IsUpUni U) :
    IsUpUni U⁻¹ ∧ U⁻¹ * U = 1 ∧ U * U⁻¹ = 1 := by
  have hB : U.BlockTriangular id := fun i j hij => (h i j).1 hij
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hB]
    exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  have hu : IsUnit U.det := by rw [hdet]; exact isUnit_one
  have h1 := Matrix.nonsing_inv_mul U hu
  have h2 := Matrix.mul_nonsing_inv U hu
  letI : Invertible U := Matrix.invertibleOfIsUnitDet U hu
  have hBi := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun i j => ⟨fun hij => hBi hij, fun hij => ?_⟩, h1, h2⟩
  subst hij
  have := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at this
  · rw [(h i i).2 rfl, mul_one] at this; simpa using this
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hBi (show id k < id i from hk), zero_mul]
    · rw [(h k i).1 hk, mul_zero]
  · simp

/- English proof (translation)
Take `⟨hLi, hL1, hL2⟩` from `loUni_inv hL'`. Take `⟨hUi, hU1, hU2⟩` from `upUni_inv hU`. Use `⟨Formalism.MainNotions.BridgeLemma.bru_lo_mul hLi hL, Formalism.MainNotions.BridgeLemma.bru_up_mul hU' hUi, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: L'⁻¹ * (L * P * U) * U⁻¹ = L'⁻¹ * (L' * P' * U') * U⁻¹` using `by rw [e]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc, hU2, Matrix.mul_one]`. Use `_ = L'⁻¹ * (L' * P' * U') * U⁻¹ := this`. Use `_ = P' * (U' * U⁻¹) := by`. Simplify using `only [← Matrix.mul_assoc, hL1, Matrix.one_mul]`. Rewrite using `[← Matrix.mul_assoc, hL2, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, hU1, Matrix.mul_one]`.
-/
theorem cell_move {L U L' U' P P' : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) (hU : IsUpUni U)
    (hL' : IsLoUni L') (hU' : IsUpUni U') (e : L * P * U = L' * P' * U') :
    IsLoUni (L'⁻¹ * L) ∧ IsUpUni (U' * U⁻¹) ∧ (L'⁻¹ * L) * P = P' * (U' * U⁻¹) ∧
      L' * (L'⁻¹ * L) = L ∧ (U' * U⁻¹) * U = U' := by
  obtain ⟨hLi, hL1, hL2⟩ := loUni_inv hL'
  obtain ⟨hUi, hU1, hU2⟩ := upUni_inv hU
  refine ⟨Formalism.MainNotions.BridgeLemma.bru_lo_mul hLi hL, Formalism.MainNotions.BridgeLemma.bru_up_mul hU' hUi, ?_, ?_, ?_⟩
  · have : L'⁻¹ * (L * P * U) * U⁻¹ = L'⁻¹ * (L' * P' * U') * U⁻¹ := by rw [e]
    calc (L'⁻¹ * L) * P = L'⁻¹ * (L * P * U) * U⁻¹ := by
            simp only [Matrix.mul_assoc, hU2, Matrix.mul_one]
      _ = L'⁻¹ * (L' * P' * U') * U⁻¹ := this
      _ = P' * (U' * U⁻¹) := by
            simp only [← Matrix.mul_assoc, hL1, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, hL2, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hU1, Matrix.mul_one]

end Tri

section PtMat

variable {K : Type} [Field K] {N : ℕ}

/- English proof (translation)
Unfold `ptMat`. Conclude with `ptEntry_eq_pv p.1 a b (by rw [p.2.2]; exact a.isLt)`.
-/
theorem ptMat_apply'_pv (p : Point K N) (a b : Fin N) :
    ptMat p a b = if b.val = pσ p.1 a.val then pv p.1 a.val else 0 := by
  unfold ptMat
  exact ptEntry_eq_pv p.1 a b (by rw [p.2.2]; exact a.isLt)

/- English proof (translation)
The claim follows from `| [], [], _, _, _, _ => rfl | [], (t, s) :: _, _, hv', hs, _ => by have := (hv' (t, s) (by simp)).2 simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hs; omega | (t, s) :: _, [], hv, _, hs, _ => by have := (hv (t, s) (by simp)).2 simp only [List.map_nil, Lis …`.
-/
theorem pts_inj : ∀ (bs bs' : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (∀ b ∈ bs', b.1 ≠ 0 ∧ 1 ≤ b.2) →
    (bs.map Prod.snd).sum = (bs'.map Prod.snd).sum →
    (∀ i, i < (bs.map Prod.snd).sum → pσ bs i = pσ bs' i ∧ pv bs i = pv bs' i) → bs = bs'
  | [], [], _, _, _, _ => rfl
  | [], (t, s) :: _, _, hv', hs, _ => by
    have := (hv' (t, s) (by simp)).2
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hs; omega
  | (t, s) :: _, [], hv, _, hs, _ => by
    have := (hv (t, s) (by simp)).2
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hs; omega
  | (t, s) :: b1, (t', s') :: b1', hv, hv', hs, h => by
    simp only [List.map_cons, List.sum_cons] at hs h
    have hs1 := (hv (t, s) (by simp)).2
    have hs1' := (hv' (t', s') (by simp)).2
    obtain ⟨e1, e2⟩ := h 0 (by omega)
    simp only [pσ, pv, if_pos (show 0 < s by omega), if_pos (show 0 < s' by omega)] at e1 e2
    have ess : s = s' := by omega
    subst ess e2
    have := pts_inj b1 b1' (fun b hb => hv b (by simp [hb])) (fun b hb => hv' b (by simp [hb])) (by omega)
      (fun i hi => by
        obtain ⟨a, b⟩ := h (s + i) (by omega)
        simp only [pσ, pv, if_neg (show ¬ (s + i < s) by omega), Nat.add_sub_cancel_left] at a b
        exact ⟨by omega, b⟩)
    rw [this]

/- English proof (translation)
The claim follows from `Subtype.ext (pts_inj p.1 p'.1 p.2.1 p'.2.1 (by rw [p.2.2, p'.2.2]) (fun i hi => h i (by rw [← p.2.2]; exact hi)))`.
-/
theorem pt_eq_of_struct (p p' : Point K N) (h : ∀ i, i < N → pσ p.1 i = pσ p'.1 i ∧ pv p.1 i = pv p'.1 i) :
    p = p' :=
  Subtype.ext (pts_inj p.1 p'.1 p.2.1 p'.2.1 (by rw [p.2.2, p'.2.2]) (fun i hi => h i (by rw [← p.2.2]; exact hi)))

def fσ (p : Point K N) (a : Fin N) : Fin N :=
  ⟨pσ p.1 a, by have := pσ_lt p.1 a (by rw [p.2.2]; exact a.isLt); rw [p.2.2] at this; exact this⟩

/- English proof (translation)
The claim follows from `Fin.ext (pσ_inv p.1 a (by rw [p.2.2]; exact a.isLt))`.
-/
theorem fσ_fσ (p : Point K N) (a : Fin N) : fσ p (fσ p a) = a :=
  Fin.ext (pσ_inv p.1 a (by rw [p.2.2]; exact a.isLt))

/- English proof (translation)
Rewrite using `[ptMat_apply'_pv]`. Simplify using `only [fσ, Fin.ext_iff]`.
-/
theorem ptMat_fσ (p : Point K N) (a b : Fin N) : ptMat p a b = if b = fσ p a then pv p.1 a else 0 := by
  rw [ptMat_apply'_pv]
  simp only [fσ, Fin.ext_iff]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (fσ p j)]`. Rewrite using `[ptMat_fσ, if_pos (fσ_fσ p j).symm]`. Introduce `k _ hk`. Rewrite using `[ptMat_fσ, if_neg (fun hj => hk (by rw [hj, fσ_fσ])), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem mul_ptMat (p : Point K N) (n : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (n * ptMat p) i j = n i (fσ p j) * pv p.1 (fσ p j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (fσ p j)]
  · rw [ptMat_fσ, if_pos (fσ_fσ p j).symm]
  · intro k _ hk
    rw [ptMat_fσ, if_neg (fun hj => hk (by rw [hj, fσ_fσ])), mul_zero]
  · simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (fσ p i)]`. Rewrite using `[ptMat_fσ, if_pos rfl]`. Introduce `k _ hk`. Rewrite using `[ptMat_fσ, if_neg hk, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem ptMat_mul (p : Point K N) (m : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (ptMat p * m) i j = pv p.1 i * m (fσ p i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (fσ p i)]
  · rw [ptMat_fσ, if_pos rfl]
  · intro k _ hk
    rw [ptMat_fσ, if_neg hk, zero_mul]
  · simp

/- English proof (translation)
The claim follows from `pv_ne p.1 p.2.1 a (by rw [p.2.2]; exact a.isLt)`.
-/
theorem pv_ne' (p : Point K N) (a : Fin N) : pv p.1 a ≠ 0 :=
  pv_ne p.1 p.2.1 a (by rw [p.2.2]; exact a.isLt)

/- English proof (translation)
Establish `key : ∀ i j, n i (fσ p j) * pv p.1 (fσ p j) = pv p'.1 i * m (fσ p' i) j` using `fun i j => by`. Rewrite using `[← mul_ptMat, ← ptMat_mul, h]`. Establish `hle : ∀ i : Fin N, (fσ p' i : ℕ) ≤ (fσ p i : ℕ)`. Introduce `i`. Establish `k` using `key i (fσ p i)`.

Rewrite `k` using `[fσ_fσ, (hn i i).2 rfl, one_mul]`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Rewrite `k` using `[(hm _ _).1 hlt, mul_zero]`. Conclude with `pv_ne' p i k`.

Establish `hsum : ∀ q : Point K N, ∑ i : Fin N, ((fσ q i : Fin N) : ℕ) = ∑ i : Fin N, (i : ℕ)`. Introduce `q`. Establish `hinv : Function.Involutive (fσ q)` using `fσ_fσ q`. Conclude with `Equiv.sum_comp hinv.toPerm (fun i : Fin N => (i : ℕ))`. Establish `heq : ∀ i : Fin N, (fσ p' i : ℕ) = (fσ p i : ℕ)`.

Use `(Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hle i)).mp (by rw [hsum, hsum])` as an intermediate fact. Conclude with `fun i => this i (Finset.mem_univ _)`. Establish `heqF : ∀ i, fσ p' i = fσ p i` using `fun i => Fin.ext (heq i)`. Use `pt_eq_of_struct p p' fun i hi => ?_` and prove the remaining obligations. Establish `e1` using `heq ⟨i, hi⟩`.

Establish `k` using `key ⟨i, hi⟩ (fσ p ⟨i, hi⟩)`. Rewrite `k` using `[fσ_fσ, (hn _ _).2 rfl, one_mul, heqF, (hm _ _).2 rfl, mul_one]`. Conclude with `⟨e1.symm, k⟩`.
-/
theorem pt_eq_of_move (p p' : Point K N) {n m : Matrix (Fin N) (Fin N) K} (hn : IsLoUni n) (hm : IsUpUni m)
    (h : n * ptMat p = ptMat p' * m) : p = p' := by
  have key : ∀ i j, n i (fσ p j) * pv p.1 (fσ p j) = pv p'.1 i * m (fσ p' i) j := fun i j => by
    rw [← mul_ptMat, ← ptMat_mul, h]
  have hle : ∀ i : Fin N, (fσ p' i : ℕ) ≤ (fσ p i : ℕ) := by
    intro i
    have k := key i (fσ p i)
    rw [fσ_fσ, (hn i i).2 rfl, one_mul] at k
    by_contra hlt
    push Not at hlt
    rw [(hm _ _).1 hlt, mul_zero] at k
    exact pv_ne' p i k
  have hsum : ∀ q : Point K N, ∑ i : Fin N, ((fσ q i : Fin N) : ℕ) = ∑ i : Fin N, (i : ℕ) := by
    intro q
    have hinv : Function.Involutive (fσ q) := fσ_fσ q
    exact Equiv.sum_comp hinv.toPerm (fun i : Fin N => (i : ℕ))
  have heq : ∀ i : Fin N, (fσ p' i : ℕ) = (fσ p i : ℕ) := by
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hle i)).mp (by rw [hsum, hsum])
    exact fun i => this i (Finset.mem_univ _)
  have heqF : ∀ i, fσ p' i = fσ p i := fun i => Fin.ext (heq i)
  refine pt_eq_of_struct p p' fun i hi => ?_
  have e1 := heq ⟨i, hi⟩
  have k := key ⟨i, hi⟩ (fσ p ⟨i, hi⟩)
  rw [fσ_fσ, (hn _ _).2 rfl, one_mul, heqF, (hm _ _).2 rfl, mul_one] at k
  exact ⟨e1.symm, k⟩

end PtMat

/- English proof (translation)
Introduce `K _ N p p' L U L' U' hL hU hL' hU' e`. Take `⟨hn, hm, hnm, -, -⟩` from `cell_move hL hU hL' hU' e`. Conclude with `pt_eq_of_move p p' hn hm hnm`.
-/
theorem cell_point_uniqueness : CellPointUniq := by
  intro K _ N p p' L U L' U' hL hU hL' hU' e
  obtain ⟨hn, hm, hnm, -, -⟩ := cell_move hL hU hL' hU' e
  exact pt_eq_of_move p p' hn hm hnm

section Simple

variable {K : Type} [Field K] [NumberField K] {N : ℕ}

def sameB (bs : List (K × ℕ)) (N a : ℕ) : Prop :=
  a + 1 < N ∧ pσ bs (a + 1) + 1 = pσ bs a ∧ pv bs (a + 1) = pv bs a

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hs`. Establish `hN` using `p.2.2`. Establish `i1 : pσ p.1 (pσ p.1 (a + 1)) = a + 1` using `pσ_inv p.1 (a + 1) (by omega)`. Establish `i2 : pσ p.1 (pσ p.1 a) = a` using `pσ_inv p.1 a (by omega)`. Establish `l2 : pσ p.1 a < N` using `by have := pσ_lt p.1 a (by omega); omega`.

Establish `e1 : pσ p.1 (pσ p.1 (a + 1) + 1) = a` using `by rw [h2, i2]`. Use `⟨⟨by omega, by rw [e1, i1], ?_⟩, e1⟩` and prove the remaining obligations. Break down `pσ_nb p.1 p.2.1 (pσ p.1 (a + 1)) (by omega) with ⟨_, hh⟩ | hh` into its components or cases. Conclude with `hh`. Rewrite `hh` using `[e1, i1]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem same_phi (p : Point K N) {a : ℕ} (hs : sameB p.1 N a) :
    sameB p.1 N (pσ p.1 (a + 1)) ∧ pσ p.1 (pσ p.1 (a + 1) + 1) = a := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hN := p.2.2
  have i1 : pσ p.1 (pσ p.1 (a + 1)) = a + 1 := pσ_inv p.1 (a + 1) (by omega)
  have i2 : pσ p.1 (pσ p.1 a) = a := pσ_inv p.1 a (by omega)
  have l2 : pσ p.1 a < N := by have := pσ_lt p.1 a (by omega); omega
  have e1 : pσ p.1 (pσ p.1 (a + 1) + 1) = a := by rw [h2, i2]
  refine ⟨⟨by omega, by rw [e1, i1], ?_⟩, e1⟩
  rcases pσ_nb p.1 p.2.1 (pσ p.1 (a + 1)) (by omega) with ⟨_, hh⟩ | hh
  · exact hh
  · rw [e1, i1] at hh; omega

/- English proof (translation)
Establish `key : ∀ i j, n i (fσ p j) * pv p.1 (fσ p j) = pv p.1 i * m (fσ p i) j` using `fun i j => by`. Rewrite using `[← mul_ptMat, ← ptMat_mul, h]`. Establish `hN : (p.1.map Prod.snd).sum = N` using `p.2.2`. Set `F : ℕ → K` to `fun a => if h : a + 1 < N then n ⟨a + 1, h⟩ ⟨a, by omega⟩ else 0`. Set `G : ℕ → K` to `fun a => if h : a + 1 < N then m ⟨a, by omega⟩ ⟨a + 1, h⟩ else 0`.

Establish `eLo : sgLo n = ∑ a ∈ Finset.range N, F a` using `Fin.sum_univ_eq_sum_range F N`. Establish `eUp : sgUp m = ∑ a ∈ Finset.range N, G a` using `Fin.sum_univ_eq_sum_range G N`. Establish `cross : ∀ a (ha : a + 1 < N), ¬ sameB p.1 N a → pσ p.1 a < pσ p.1 (a + 1)`. Introduce `a ha hs`. Break down `pσ_nb p.1 p.2.1 a (by omega) with ⟨h1, h2⟩ | h1` into its components or cases.

Conclude with `absurd ⟨ha, h1, h2⟩ hs`. Conclude with `h1`. Establish `hF : ∀ a ∈ Finset.range N, F a ≠ 0 → sameB p.1 N a`. Introduce `a _ hne`. Assume the negation of the conclusion as `hs`.

Distinguish the cases in `ha : a + 1 < N`. Apply `hne` to reduce the goal to its premises. Establish `hc` using `cross a ha hs`. Establish `k` using `key ⟨a + 1, ha⟩ (fσ p ⟨a, by omega⟩)`. Rewrite `k` using `[fσ_fσ, (hm _ _).1 (show fσ p ⟨a, by omega⟩ < fσ p ⟨a + 1, ha⟩ by exact hc), mul_zero]`.

Use `(mul_eq_zero.mp k).resolve_right (pv_ne' p _)` as an intermediate fact. Simplify using `only [F]`. Rewrite using `[dif_pos ha]`. Conclude with `this`. Conclude with `hne (by simp only [F]; rw [dif_neg ha])`.

Establish `hG : ∀ a ∈ Finset.range N, G a ≠ 0 → sameB p.1 N a`. Introduce `a _ hne`. Assume the negation of the conclusion as `hs`. Distinguish the cases in `ha : a + 1 < N`. Apply `hne` to reduce the goal to its premises.

Establish `hc` using `cross a ha hs`. Establish `k` using `key (fσ p ⟨a, by omega⟩) ⟨a + 1, ha⟩`. Rewrite `k` using `[fσ_fσ, (hn _ _).1 (show fσ p ⟨a, by omega⟩ < fσ p ⟨a + 1, ha⟩ by exact hc), zero_mul]`. Use `(mul_eq_zero.mp k.symm).resolve_left (pv_ne' p _)` as an intermediate fact. Simplify using `only [G]`.

Rewrite using `[dif_pos ha]`. Conclude with `this`. Conclude with `hne (by simp only [G]; rw [dif_neg ha])`. Establish `hGF : ∀ a ∈ (Finset.range N).filter (sameB p.1 N), G a = F (pσ p.1 (a + 1))`. Introduce `a ha`.

Take `⟨-, hs⟩` from `Finset.mem_filter.mp ha`. Take `⟨⟨hb1, -, hb3⟩, -⟩` from `same_phi p hs`. Take `⟨ha1, h2, -⟩` from `hs`. Establish `k` using `key (fσ p ⟨a, by omega⟩) ⟨a + 1, ha1⟩`. Rewrite `k` using `[fσ_fσ]`.

Establish `eA : fσ p ⟨a, by omega⟩ = ⟨pσ p.1 (a + 1) + 1, hb1⟩` using `Fin.ext (by show pσ p.1 a = pσ p.1 (a + 1) + 1; omega)`. Establish `orbitMap_conj_smul_one : fσ p ⟨a + 1, ha1⟩ = ⟨pσ p.1 (a + 1), by omega⟩` using `Fin.ext rfl`. Rewrite `k` using `[eA, orbitMap_conj_smul_one]`. Simplify using `only [Fin.val_mk] at k`. Rewrite `k` using `[hb3]`.

Establish `hv` using `pv_ne' p ⟨pσ p.1 (a + 1), by omega⟩`. Simplify using `only [Fin.val_mk] at hv`. Simplify using `only [F, G]`. Rewrite using `[dif_pos ha1, dif_pos hb1]`. Conclude with `mul_left_cancel₀ hv (k.symm.trans (mul_comm _ _))`.

Rewrite using `[eLo, eUp, ← Finset.sum_filter_of_ne hF, ← Finset.sum_filter_of_ne hG]`. Use `(Finset.sum_nbij' (fun a => pσ p.1 (a + 1)) (fun a => pσ p.1 (a + 1)) ?_ ?_ ?_ ?_ hGF).symm` and prove the remaining obligations. Introduce `a ha`. Take `⟨-, hs⟩` from `Finset.mem_filter.mp ha`. Take `⟨hs', -⟩` from `same_phi p hs`.

Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hs'.1; omega), hs'⟩`. Introduce `a ha`. Take `⟨-, hs⟩` from `Finset.mem_filter.mp ha`. Take `⟨hs', -⟩` from `same_phi p hs`. Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hs'.1; omega), hs'⟩`.

Introduce `a ha`. Conclude with `(same_phi p (Finset.mem_filter.mp ha).2).2`. Introduce `a ha`. Conclude with `(same_phi p (Finset.mem_filter.mp ha).2).2`.
-/
theorem simple_eq (p : Point K N) {n m : Matrix (Fin N) (Fin N) K} (hn : IsLoUni n) (hm : IsUpUni m)
    (h : n * ptMat p = ptMat p * m) : sgLo n = sgUp m := by
  have key : ∀ i j, n i (fσ p j) * pv p.1 (fσ p j) = pv p.1 i * m (fσ p i) j := fun i j => by
    rw [← mul_ptMat, ← ptMat_mul, h]
  have hN : (p.1.map Prod.snd).sum = N := p.2.2
  let F : ℕ → K := fun a => if h : a + 1 < N then n ⟨a + 1, h⟩ ⟨a, by omega⟩ else 0
  let G : ℕ → K := fun a => if h : a + 1 < N then m ⟨a, by omega⟩ ⟨a + 1, h⟩ else 0
  have eLo : sgLo n = ∑ a ∈ Finset.range N, F a := Fin.sum_univ_eq_sum_range F N
  have eUp : sgUp m = ∑ a ∈ Finset.range N, G a := Fin.sum_univ_eq_sum_range G N
  have cross : ∀ a (ha : a + 1 < N), ¬ sameB p.1 N a → pσ p.1 a < pσ p.1 (a + 1) := by
    intro a ha hs
    rcases pσ_nb p.1 p.2.1 a (by omega) with ⟨h1, h2⟩ | h1
    · exact absurd ⟨ha, h1, h2⟩ hs
    · exact h1
  have hF : ∀ a ∈ Finset.range N, F a ≠ 0 → sameB p.1 N a := by
    intro a _ hne
    by_contra hs
    by_cases ha : a + 1 < N
    · apply hne
      have hc := cross a ha hs
      have k := key ⟨a + 1, ha⟩ (fσ p ⟨a, by omega⟩)
      rw [fσ_fσ, (hm _ _).1 (show fσ p ⟨a, by omega⟩ < fσ p ⟨a + 1, ha⟩ by exact hc), mul_zero] at k
      have := (mul_eq_zero.mp k).resolve_right (pv_ne' p _)
      simp only [F]; rw [dif_pos ha]; exact this
    · exact hne (by simp only [F]; rw [dif_neg ha])
  have hG : ∀ a ∈ Finset.range N, G a ≠ 0 → sameB p.1 N a := by
    intro a _ hne
    by_contra hs
    by_cases ha : a + 1 < N
    · apply hne
      have hc := cross a ha hs
      have k := key (fσ p ⟨a, by omega⟩) ⟨a + 1, ha⟩
      rw [fσ_fσ, (hn _ _).1 (show fσ p ⟨a, by omega⟩ < fσ p ⟨a + 1, ha⟩ by exact hc), zero_mul] at k
      have := (mul_eq_zero.mp k.symm).resolve_left (pv_ne' p _)
      simp only [G]; rw [dif_pos ha]; exact this
    · exact hne (by simp only [G]; rw [dif_neg ha])
  have hGF : ∀ a ∈ (Finset.range N).filter (sameB p.1 N), G a = F (pσ p.1 (a + 1)) := by
    intro a ha
    obtain ⟨-, hs⟩ := Finset.mem_filter.mp ha
    obtain ⟨⟨hb1, -, hb3⟩, -⟩ := same_phi p hs
    obtain ⟨ha1, h2, -⟩ := hs
    have k := key (fσ p ⟨a, by omega⟩) ⟨a + 1, ha1⟩
    rw [fσ_fσ] at k
    have eA : fσ p ⟨a, by omega⟩ = ⟨pσ p.1 (a + 1) + 1, hb1⟩ :=
      Fin.ext (by show pσ p.1 a = pσ p.1 (a + 1) + 1; omega)
    have orbitMap_conj_smul_one : fσ p ⟨a + 1, ha1⟩ = ⟨pσ p.1 (a + 1), by omega⟩ := Fin.ext rfl
    rw [eA, orbitMap_conj_smul_one] at k
    simp only [Fin.val_mk] at k
    rw [hb3] at k
    have hv := pv_ne' p ⟨pσ p.1 (a + 1), by omega⟩
    simp only [Fin.val_mk] at hv
    simp only [F, G]; rw [dif_pos ha1, dif_pos hb1]
    exact mul_left_cancel₀ hv (k.symm.trans (mul_comm _ _))
  rw [eLo, eUp, ← Finset.sum_filter_of_ne hF, ← Finset.sum_filter_of_ne hG]
  refine (Finset.sum_nbij' (fun a => pσ p.1 (a + 1)) (fun a => pσ p.1 (a + 1)) ?_ ?_ ?_ ?_ hGF).symm
  · intro a ha
    obtain ⟨-, hs⟩ := Finset.mem_filter.mp ha
    obtain ⟨hs', -⟩ := same_phi p hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hs'.1; omega), hs'⟩
  · intro a ha
    obtain ⟨-, hs⟩ := Finset.mem_filter.mp ha
    obtain ⟨hs', -⟩ := same_phi p hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hs'.1; omega), hs'⟩
  · intro a ha
    exact (same_phi p (Finset.mem_filter.mp ha).2).2
  · intro a ha
    exact (same_phi p (Finset.mem_filter.mp ha).2).2

end Simple

/- English proof (translation)
Introduce `K _ _ N p L U L' U' hL hU hL' hU' e`. Take `⟨hn, hm, hnm, eL, eU⟩` from `cell_move hL hU hL' hU' e`. Establish `hs` using `simple_eq p hn hm hnm`. Rewrite using `[← eL, ← eU, sgLo_mul hL' hn, sgUp_mul hm hU, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem simple_decomposition_holds : DecompSimple := by
  intro K _ _ N p L U L' U' hL hU hL' hU' e
  obtain ⟨hn, hm, hnm, eL, eU⟩ := cell_move hL hU hL' hU' e
  have hs := simple_eq p hn hm hnm
  rw [← eL, ← eU, sgLo_mul hL' hn, sgUp_mul hm hU, hs]; ring

section Frame

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Unfold `FlagG.Xa at hx`. Take `⟨l, hl, rfl⟩` from `(Finsupp.mem_span_image_iff_linearCombination E).mp hx`. Use `⟨fun i => l i, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `(Finsupp.mem_supported E l).mp hl (Finsupp.mem_support_iff.mpr h)` as an intermediate fact.

Simplify using `only [Set.mem_setOf_eq] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype]`. Introduce `i`. Simplify using the standard rewrite rules.
-/
theorem mem_Xa_coef {T : E} (F : FlagG S r T) {j : ℕ} {x : S.V} (hx : x ∈ F.Xa j) :
    ∃ c : Fin r → E, (∀ i : Fin r, j ≤ i.val → c i = 0) ∧ x = ∑ i, c i • F.e i := by
  unfold FlagG.Xa at hx
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).mp hx
  refine ⟨fun i => l i, fun i hi => ?_, ?_⟩
  · by_contra h
    have := (Finsupp.mem_supported E l).mp hl (Finsupp.mem_support_iff.mpr h)
    simp only [Set.mem_setOf_eq] at this
    omega
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp

/- English proof (translation)
Unfold `FlagG.X at hx`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun E).mp hx`. Conclude with `⟨c, hc.symm⟩`.
-/
theorem mem_X_coef {T : E} (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) :
    ∃ c : Fin r → E, x = ∑ i, c i • F.e i := by
  unfold FlagG.X at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hx
  exact ⟨c, hc.symm⟩

/- English proof (translation)
Take `⟨-, hflag, horth⟩` from `hs`. Establish `he : ∀ i : Fin r, ∃ c : Fin r → E, (∀ k : Fin r, i.val ≤ k.val → c k = 0) ∧ s (F.fl.e i) = F.fl.e i + ∑ k, c k • F.fl.e k`. Introduce `i`. Establish `hmem : F.fl.e i ∈ Xflag F (i.val + 1)` using `Submodule.subset_span ⟨i, by simp, rfl⟩`. Take `⟨c, hc0, hc⟩` from `mem_Xa_coef F.fl (hflag i.val _ hmem)`.

Conclude with `⟨c, hc0, by rw [← hc]; abel⟩`. Establish `hz : ∃ c : Fin r → E, s F.fl.z = F.fl.z + ∑ k, c k • F.fl.e k`. Establish `hmem : F.fl.z ∈ orth S (Xsp F)` using `Formalism.MainNotions.S.Inh.tie_mem_orth F.fl F.fl.z_orth`. Take `⟨c, hc⟩` from `mem_X_coef F.fl (horth _ hmem)`. Conclude with `⟨c, by rw [← hc]; abel⟩`.

Use `choose ce hce0 hce using he`. Take `⟨cz, hcz⟩` from `hz`. Set `col : Fin (r + 1) → Fin r → E` to `fun b => Fin.lastCases cz ce b`. Use `⟨fun c b => if c = b then 1 else Fin.lastCases (0 : E) (fun k => col b k) c, ?_, ?_⟩` and prove the remaining obligations. Introduce `c b`.

Use `⟨fun hbc => ?_, fun hcb => by simp [hcb]⟩` and prove the remaining obligations. Simplify using `only [if_neg (ne_of_gt hbc)]`. Proceed by induction on `c using Fin.lastCases with`. Consider the case `last => simp`. Consider the case `cast k`.

Simplify using `only [Fin.lastCases_castSucc]`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => exact absurd hbc (not_lt.mpr (Fin.le_last _))`. Consider the case `cast i`. Simplify using `only [col, Fin.lastCases_castSucc]`.

Conclude with `hce0 i k (le_of_lt (Fin.castSucc_lt_castSucc_iff.mp hbc))`. Introduce `b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Simplify using `only [frame, FlagG.fvec, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc, if_pos rfl, one_smul, col, Fin.lastCases_last, Fin.lastCases_castSucc, if_neg (Fin.castSucc_lt_last _).ne]`.

Rewrite using `[hcz, add_comm]`. Simplify using the standard rewrite rules. Consider the case `cast i`. Simplify using `only [frame, FlagG.fvec, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc, if_neg (Fin.castSucc_lt_last i).ne', Fin.lastCases_last, zero_smul, add_zero, Fin.castSucc_inj, col, Fin.lastCases_castSucc]`. Rewrite using `[hce i]`.

Establish `: ∀ k : Fin r, (if k = i then (1 : E) else ce i k) = ce i k + if k = i then 1 else 0`. Introduce `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[hce0 k k le_rfl]`.

Simplify using `[hk]`. Simplify using `only [this, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Normalize the expressions using the abelian group laws.
-/
theorem nlam_frame (Λ : Submodule (𝓞 E) S.V) {T : E} (F : LFlag S r T) {s : S.V ≃ₗ[E] S.V}
    (hs : s ∈ NLam Λ F) : ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni u ∧
      ∀ b, s (frame F b) = ∑ c, u c b • frame F c := by
  obtain ⟨-, hflag, horth⟩ := hs
  have he : ∀ i : Fin r, ∃ c : Fin r → E, (∀ k : Fin r, i.val ≤ k.val → c k = 0) ∧
      s (F.fl.e i) = F.fl.e i + ∑ k, c k • F.fl.e k := by
    intro i
    have hmem : F.fl.e i ∈ Xflag F (i.val + 1) := Submodule.subset_span ⟨i, by simp, rfl⟩
    obtain ⟨c, hc0, hc⟩ := mem_Xa_coef F.fl (hflag i.val _ hmem)
    exact ⟨c, hc0, by rw [← hc]; abel⟩
  have hz : ∃ c : Fin r → E, s F.fl.z = F.fl.z + ∑ k, c k • F.fl.e k := by
    have hmem : F.fl.z ∈ orth S (Xsp F) := Formalism.MainNotions.S.Inh.tie_mem_orth F.fl F.fl.z_orth
    obtain ⟨c, hc⟩ := mem_X_coef F.fl (horth _ hmem)
    exact ⟨c, by rw [← hc]; abel⟩
  choose ce hce0 hce using he
  obtain ⟨cz, hcz⟩ := hz
  let col : Fin (r + 1) → Fin r → E := fun b => Fin.lastCases cz ce b
  refine ⟨fun c b => if c = b then 1 else Fin.lastCases (0 : E) (fun k => col b k) c, ?_, ?_⟩
  · intro c b
    refine ⟨fun hbc => ?_, fun hcb => by simp [hcb]⟩
    simp only [if_neg (ne_of_gt hbc)]
    induction c using Fin.lastCases with
    | last => simp
    | cast k =>
      simp only [Fin.lastCases_castSucc]
      induction b using Fin.lastCases with
      | last => exact absurd hbc (not_lt.mpr (Fin.le_last _))
      | cast i =>
        simp only [col, Fin.lastCases_castSucc]
        exact hce0 i k (le_of_lt (Fin.castSucc_lt_castSucc_iff.mp hbc))
  · intro b
    induction b using Fin.lastCases with
    | last =>
      simp only [frame, FlagG.fvec, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc, if_pos rfl,
        one_smul, col, Fin.lastCases_last, Fin.lastCases_castSucc, if_neg (Fin.castSucc_lt_last _).ne]
      rw [hcz, add_comm]; simp
    | cast i =>
      simp only [frame, FlagG.fvec, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        if_neg (Fin.castSucc_lt_last i).ne', Fin.lastCases_last, zero_smul, add_zero, Fin.castSucc_inj, col,
        Fin.lastCases_castSucc]
      rw [hce i]
      have : ∀ k : Fin r, (if k = i then (1 : E) else ce i k) = ce i k + if k = i then 1 else 0 := by
        intro k; by_cases hk : k = i
        · subst hk; simp [hce0 k k le_rfl]
        · simp [hk]
      simp only [this, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      abel

/- English proof (translation)
Use extensionality with `a b`. Establish `hiso : S.hT (s (frame F a)) (s (frame F' b)) = S.hT (frame F a) (frame F' b)` using `hs _ _`. Establish `lhs : ZhatL F F' a b = S.hT (frame F a) (frame F' b)` using `rfl`. Rewrite using `[lhs, ← hiso, h1, h2]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, Matrix.mul_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `only [show ∀ x y, ZhatL F F' x y = S.hT (frame F x) (frame F' y) from fun _ _ => rfl, starRingEnd_apply, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zhat_move {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') {s : S.V ≃ₗ[E] S.V}
    (hs : s ∈ Formalism.HermitianLatticesTheory.isom S.hT) {uu u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (h1 : ∀ b, s (frame F b) = ∑ c, uu c b • frame F c) (h2 : ∀ b, s (frame F' b) = ∑ c, u' c b • frame F' c) :
    ZhatL F F' = uu.conjTranspose * ZhatL F F' * u' := by
  ext a b
  have hiso : S.hT (s (frame F a)) (s (frame F' b)) = S.hT (frame F a) (frame F' b) := hs _ _
  have lhs : ZhatL F F' a b = S.hT (frame F a) (frame F' b) := rfl
  rw [lhs, ← hiso, h1, h2]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [show ∀ x y, ZhatL F F' x y = S.hT (frame F x) (frame F' y) from fun _ _ => rfl, starRingEnd_apply,
    RingHom.id_apply]
  ring

/- English proof (translation)
Establish `hz : ∀ d, ∑ c, star (x c - y c) * ZhatL F F' c d = 0`. Introduce `d`. Establish `h0 : ∑ c, (x c - y c) • frame F c = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, h, sub_self]`. Establish `: S.hT (∑ c, (x c - y c) • frame F c) (frame F' d) = 0` using `by rw [h0]; simp`.

Rewrite `this` using `[map_sum, LinearMap.sum_apply]`. Simplify using `only [LinearMap.map_smulₛₗ₂, smul_eq_mul] at this`. Conclude with `this`. Establish `hv : Matrix.vecMul (fun c => star (x c - y c)) (ZhatL F F') = 0`. Use extensionality with `d`.

Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply]`. Conclude with `hz d`. Use `Matrix.eq_zero_of_vecMul_eq_zero hdet hv` as an intermediate fact. Use function extensionality and compare the values at `c`. Establish `hc` using `congrFun this c`.

Simplify using `only [Pi.zero_apply, star_eq_zero] at hc`. Conclude with `sub_eq_zero.mp hc`.
-/
theorem frame_coef_unique {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hdet : (ZhatL F F').det ≠ 0)
    {x y : Fin (r + 1) → E} (h : ∑ c, x c • frame F c = ∑ c, y c • frame F c) : x = y := by
  have hz : ∀ d, ∑ c, star (x c - y c) * ZhatL F F' c d = 0 := by
    intro d
    have h0 : ∑ c, (x c - y c) • frame F c = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
    have : S.hT (∑ c, (x c - y c) • frame F c) (frame F' d) = 0 := by rw [h0]; simp
    rw [map_sum, LinearMap.sum_apply] at this
    simp only [LinearMap.map_smulₛₗ₂, smul_eq_mul] at this
    exact this
  have hv : Matrix.vecMul (fun c => star (x c - y c)) (ZhatL F F') = 0 := by
    ext d; simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]; exact hz d
  have := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  funext c
  have hc := congrFun this c
  simp only [Pi.zero_apply, star_eq_zero] at hc
  exact sub_eq_zero.mp hc

end Frame

section Big

variable {K : Type} [Field K] {N : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular L (fun i j hij => (h i j).1 hij)]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`.
-/
theorem det_loUni {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j hij => (h i j).1 hij)]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`.
-/
theorem det_upUni {U : Matrix (Fin N) (Fin N) K} (h : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[ptMat_mul, ptMat_fσ, fσ_fσ, Matrix.diagonal_apply]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, if_neg (Ne.symm h), mul_zero]`.
-/
theorem ptMat_sq (p : Point K N) :
    ptMat p * ptMat p = Matrix.diagonal (fun i : Fin N => pv p.1 i * pv p.1 (fσ p i)) := by
  ext i j
  rw [ptMat_mul, ptMat_fσ, fσ_fσ, Matrix.diagonal_apply]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

/- English proof (translation)
Introduce `h0`. Use `congrArg Matrix.det (ptMat_sq p)` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_diagonal]`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (pv_ne' p i) (pv_ne' p _)) this.symm`.
-/
theorem det_ptMat_ne (p : Point K N) : (ptMat p).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (ptMat_sq p)
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_diagonal] at this
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (pv_ne' p i) (pv_ne' p _)) this.symm

/- English proof (translation)
The claim follows from `| [], _, _ => rfl | (t, s) :: bs, h, i => by have hs : s = 1 := h (t, s) (by simp) subst hs simp only [pσ] split_ifs with hi · omega · rw [pσ_big bs (fun b hb => h b (by simp [hb])) (i - 1)]; omega`.
-/
theorem pσ_big : ∀ bs : List (K × ℕ), (∀ b ∈ bs, b.2 = 1) → ∀ i, pσ bs i = i
  | [], _, _ => rfl
  | (t, s) :: bs, h, i => by
    have hs : s = 1 := h (t, s) (by simp)
    subst hs
    simp only [pσ]
    split_ifs with hi
    · omega
    · rw [pσ_big bs (fun b hb => h b (by simp [hb])) (i - 1)]; omega

/- English proof (translation)
The claim follows from `Fin.ext (pσ_big p.1 h a)`.
-/
theorem fσ_big (p : Point K N) (h : ∀ b ∈ p.1, b.2 = 1) (a : Fin N) : fσ p a = a :=
  Fin.ext (pσ_big p.1 h a)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[ZhatOM, Matrix.mul_diagonal, mul_comm]`.
-/
theorem zhatOM_eq_pv {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * Matrix.diagonal (fun b : Fin (r + 1) => (-1 : K) ^ (r - b.val)) := by
  ext a b
  simp [ZhatOM, Matrix.mul_diagonal, mul_comm]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.conjTranspose_apply]`. Conclude with `⟨fun hij => by rw [(h j i).1 hij, star_zero], fun hij => by subst hij; rw [(h i i).2 rfl, star_one]⟩`.
-/
theorem conjT_loUni [StarRing K] {u : Matrix (Fin N) (Fin N) K} (h : IsUpUni u) : IsLoUni u.conjTranspose := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ⟨fun hij => by rw [(h j i).1 hij, star_zero], fun hij => by subst hij; rw [(h i i).2 rfl, star_one]⟩

end Big

section Steps

variable (D : D7) (u u' : D.what₂.Word)

def NormRepStep : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ t : TermsOf D u' F0 Λ,
      IsRel Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F t → IsGen Λ (lf D F0) (PD D Λ (lf D F0) u') (gS D) t →
        ∃ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E),
          TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F' ∧ AdmWit Λ (gS D) (lf D F0) F' 1

def NormRepMove : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ t : TermsOf D u' F0 Λ, IsRel Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F t →
      ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E),
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₁ → AdmWit Λ (gS D) (lf D F0) F₁ 1 →
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₂ → AdmWit Λ (gS D) (lf D F0) F₂ 1 →
        ∀ w : Point D.host.E (D.R.rS + 1), IsInCell (ZhatOM (ZhatL (lf D F0) F₁)) w →
          ∃ A B : MatR D, IsLoUni A ∧ IsUpUni B ∧
            ZhatOM (ZhatL (lf D F0) F₂) = A * ZhatOM (ZhatL (lf D F0) F₁) * B ∧ psiInf (gS D) (sgLo A + sgUp B) = 1

def AutLzFin : Prop :=
  (VS D).SigOK → ∀ (Tn : ℕ), 0 < Tn → ∀ (F0 : FlagG (VS D) D.R.rS ((Tn : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → (autLz D F0 Λ).Finite

variable (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def BigCellIdx : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
      (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
      t.relevant → t.generic → NormRep t w F' L U → BigCell w → volIdx D u u' F0 what₂ δ M t w F' L = 1

def VolOrbit : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∃ wt : MatR D → ℝ, ∀ (t : Term D u u' F0 what₂)
      (w : Point D.host.E (D.R.rS + 1)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
      t.relevant → t.generic → NormRep t w F' L U →
        vRdef D u u' F0 what₂ δ M t = ((orbT D u u' F0 what₂ t (ZhatL (lf D F0) F')).ncard : ℝ) * wt (ZhatL (lf D F0) F')

def VolIdxRep : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
      (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
      t.relevant → t.generic → NormRep t w F₁ L₁ U₁ → NormRep t w F₂ L₂ U₂ →
        volIdx D u u' F0 what₂ δ M t w F₁ L₁ = volIdx D u u' F0 what₂ δ M t w F₂ L₂

end Steps

section Proofs

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Establish `hC` using `(hTF F0 t.lam (hrows.1 _ t.mem)).2.1`. Establish `c₂'` using `(cell_rep_iff hC h₁ h₂ w').mpr c₂`. Take `⟨L, U, hL, hU, e⟩` from `c₁`. Take `⟨L', U', hL', hU', e'⟩` from `c₂'`. Conclude with `hCP _ _ w w' L U L' U' hL hU hL' hU' (e.symm.trans e')`.
-/
theorem pt_eq_of_cells (hCP : CellPointUniq) (hTF : TermFun D u u') (hrows : IsRowReps D F0 what₂)
    (t : Term D u u' F0 what₂) {F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (h₁ : TermDef.Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F₁)
    (h₂ : TermDef.Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F₂) {w w' : Point D.host.E (D.R.rS + 1)}
    (c₁ : IsInCell (ZhatOM (ZhatL (lf D F0) F₁)) w) (c₂ : IsInCell (ZhatOM (ZhatL (lf D F0) F₂)) w') : w = w' := by
  have hC := (hTF F0 t.lam (hrows.1 _ t.mem)).2.1
  have c₂' := (cell_rep_iff hC h₁ h₂ w').mpr c₂
  obtain ⟨L, U, hL, hU, e⟩ := c₁
  obtain ⟨L', U', hL', hU', e'⟩ := c₂'
  exact hCP _ _ w w' L U L' U' hL hU hL' hU' (e.symm.trans e')

/- English proof (translation)
Introduce `t w w' hw hw'`. Take `⟨F₁, hR₁, -, hc₁⟩` from `hw`. Take `⟨F₂, hR₂, -, hc₂⟩` from `hw'`. Conclude with `pt_eq_of_cells hCP hTF hrows t hR₁ hR₂ hc₁ hc₂`.
-/
theorem cellPtUnique_of (hCP : CellPointUniq) (hTF : TermFun D u u') (hrows : IsRowReps D F0 what₂) :
    CellPtUnique D u u' F0 what₂ := by
  intro t w w' hw hw'
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hw
  obtain ⟨F₂, hR₂, -, hc₂⟩ := hw'
  exact pt_eq_of_cells hCP hTF hrows t hR₁ hR₂ hc₁ hc₂

/- English proof (translation)
Introduce `t w hw hrel hgen`. Establish `hΛ` using `hrows.1 _ t.mem`. Take `⟨F', hR', hA⟩` from `hN F0 t.lam hΛ t.cls hrel hgen`. Take `⟨F₁, hR₁, -, hc₁⟩` from `hw`. Take `⟨L, U, hL, hU, e⟩` from `(cell_rep_iff (hTF F0 t.lam hΛ).2.1 hR₁ hR' w).mp hc₁`.

Conclude with `⟨(F', L, U), hR', hA, hL, hU, e⟩`.
-/
theorem normRepExists_of (hN : NormRepStep D u u') (hTF : TermFun D u u') (hrows : IsRowReps D F0 what₂) :
    NormRepExists D u u' F0 what₂ := by
  intro t w hw hrel hgen
  have hΛ := hrows.1 _ t.mem
  obtain ⟨F', hR', hA⟩ := hN F0 t.lam hΛ t.cls hrel hgen
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hw
  obtain ⟨L, U, hL, hU, e⟩ := (cell_rep_iff (hTF F0 t.lam hΛ).2.1 hR₁ hR' w).mp hc₁
  exact ⟨(F', L, U), hR', hA, hL, hU, e⟩

/- English proof (translation)
Introduce `t w hrel F₁ F₂ L₁ U₁ L₂ U₂ h₁ h₂`. Take `⟨hR₁, hA₁, hL₁, hU₁, e₁⟩` from `h₁`. Take `⟨hR₂, hA₂, hL₂, hU₂, e₂⟩` from `h₂`. Take `⟨A, B, hA, hB, eZ, hψ⟩` from `hM F0 t.lam (hrows.1 _ t.mem) t.cls hrel F₁ F₂ hR₁ hA₁ hR₂ hA₂ w ⟨L₁, U₁, hL₁, hU₁, e₁⟩`. Establish `hAL` using `Formalism.MainNotions.BridgeLemma.bru_lo_mul hA hL₁`.

Establish `hUB` using `Formalism.MainNotions.BridgeLemma.bru_up_mul hU₁ hB`. Establish `key : (A * L₁) * ptMat w * (U₁ * B) = L₂ * ptMat w * U₂`. Rewrite using `[← e₂, eZ, e₁]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hs` using `hDS D.host.E _ w (A * L₁) (U₁ * B) L₂ U₂ hAL hUB hL₂ hU₂ key`.

Rewrite `hs` using `[sgLo_mul hA hL₁, sgUp_mul hU₁ hB]`. Rewrite using `[phasePair_eq, phasePair_eq, ← hs]`. Establish `: sgLo A + sgLo L₁ + (sgUp U₁ + sgUp B) = (sgLo A + sgUp B) + (sgLo L₁ + sgUp U₁)` using `by ring`. Rewrite using `[this, psiInf_add (gS D) (sgLo A + sgUp B), hψ, one_mul]`.
-/
theorem phaseWellDef_of (hDS : DecompSimple) (hM : NormRepMove D u u') (hrows : IsRowReps D F0 what₂) :
    PhaseWellDef D u u' F0 what₂ := by
  intro t w hrel F₁ F₂ L₁ U₁ L₂ U₂ h₁ h₂
  obtain ⟨hR₁, hA₁, hL₁, hU₁, e₁⟩ := h₁
  obtain ⟨hR₂, hA₂, hL₂, hU₂, e₂⟩ := h₂
  obtain ⟨A, B, hA, hB, eZ, hψ⟩ :=
    hM F0 t.lam (hrows.1 _ t.mem) t.cls hrel F₁ F₂ hR₁ hA₁ hR₂ hA₂ w ⟨L₁, U₁, hL₁, hU₁, e₁⟩
  have hAL := Formalism.MainNotions.BridgeLemma.bru_lo_mul hA hL₁
  have hUB := Formalism.MainNotions.BridgeLemma.bru_up_mul hU₁ hB
  have key : (A * L₁) * ptMat w * (U₁ * B) = L₂ * ptMat w * U₂ := by
    rw [← e₂, eZ, e₁]; simp only [Matrix.mul_assoc]
  have hs := hDS D.host.E _ w (A * L₁) (U₁ * B) L₂ U₂ hAL hUB hL₂ hU₂ key
  rw [sgLo_mul hA hL₁, sgUp_mul hU₁ hB] at hs
  rw [phasePair_eq, phasePair_eq, ← hs]
  have : sgLo A + sgLo L₁ + (sgUp U₁ + sgUp B) = (sgLo A + sgUp B) + (sgLo L₁ + sgUp U₁) := by ring
  rw [this, psiInf_add (gS D) (sgLo A + sgUp B), hψ, one_mul]

/- English proof (translation)
Introduce `Λ hΛ` and use `hAF hsig _ hT F0 Λ (hrows.1 Λ hΛ)`.
-/
theorem autFin_of (hAF : AutLzFin D) (hsig : (VS D).SigOK) (hT : 0 < Tu D u) (hrows : IsRowReps D F0 what₂) :
    AutFin D F0 what₂ :=
  fun Λ hΛ => hAF hsig _ hT F0 Λ (hrows.1 Λ hΛ)

end Proofs

section VolProofs

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  {δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp}
  {M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

end VolProofs

section Final

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
The claim follows from `cellPtUnique_of cell_point_uniqueness hTF hrows`.
-/
theorem cell_point_unique_of_term_fun (hTF : TermFun D u u') (hrows : IsRowReps D F0 what₂) : CellPtUnique D u u' F0 what₂ :=
  cellPtUnique_of cell_point_uniqueness hTF hrows

/- English proof (translation)
The claim follows from `phaseWellDef_of simple_decomposition_holds hM hrows`.
-/
theorem phase_well_defined (hM : NormRepMove D u u') (hrows : IsRowReps D F0 what₂) : PhaseWellDef D u u' F0 what₂ :=
  phaseWellDef_of simple_decomposition_holds hM hrows

end Final

end Formalism.L2.SG.Pf
