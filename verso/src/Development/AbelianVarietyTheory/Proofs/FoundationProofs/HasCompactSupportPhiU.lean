import Mathlib
import Formalism.DoubleCosetMeasures.LatticeCoset
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL

noncomputable section

open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL

namespace GlobalTheory.SingleBlock

section Alg

variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}

def suppSet (t : ℕ) (O : Subring F) (ϖ : F) (P : Subgroup (GL (Fin r) F)) :
    Set (Matrix (Fin r ⊕ Fin t) (Fin r) F) :=
  {x | toRows₁ x ∈ Jset P ∧ toRows₂ x ∈ IIset O ϖ}

/- English proof (translation)
Establish `h1 : (∃ k : P, ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = toRows₁ x) ∧ toRows₂ x ∈ IIset O ϖ` using `⟨⟨k, hk⟩, h2⟩`. Unfold `phiU`. Rewrite using `[dif_pos h1, LemmaU.choose_eq h1.1 k hk]`.
-/
theorem phiU_of_mem (ρ : P →* ℂˣ) {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (k : P)
    (hk : ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = toRows₁ x)
    (h2 : toRows₂ x ∈ IIset O ϖ) : phiU O ϖ P ρ x = ((ρ k : ℂˣ) : ℂ) := by
  have h1 : (∃ k : P, ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = toRows₁ x) ∧
      toRows₂ x ∈ IIset O ϖ := ⟨⟨k, hk⟩, h2⟩
  unfold phiU
  rw [dif_pos h1, LemmaU.choose_eq h1.1 k hk]

/- English proof (translation)
Unfold `phiU`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨⟨k, ek⟩, h2⟩`. Conclude with `hx ⟨⟨k, k.2, ek⟩, h2⟩`.
-/
theorem phiU_of_notMem (ρ : P →* ℂˣ) {x : Matrix (Fin r ⊕ Fin t) (Fin r) F}
    (hx : x ∉ suppSet t O ϖ P) : phiU O ϖ P ρ x = 0 := by
  unfold phiU
  rw [dif_neg]
  rintro ⟨⟨k, ek⟩, h2⟩
  exact hx ⟨⟨k, k.2, ek⟩, h2⟩

/- English proof (translation)
Introduce `i j`. Take `⟨a, ha, e⟩` from `hy i j`. Take `⟨b, hb, e'⟩` from `hz i j`. Conclude with `⟨a + b, O.add_mem ha hb, by rw [Matrix.add_apply, e, e', mul_add]⟩`.
-/
theorem II_add {m n : ℕ} {y z : Matrix (Fin m) (Fin n) F} (hy : y ∈ IIset O ϖ)
    (hz : z ∈ IIset O ϖ) : y + z ∈ IIset O ϖ := by
  intro i j
  obtain ⟨a, ha, e⟩ := hy i j
  obtain ⟨b, hb, e'⟩ := hz i j
  exact ⟨a + b, O.add_mem ha hb, by rw [Matrix.add_apply, e, e', mul_add]⟩

/- English proof (translation)
Introduce `i j`. Use `choose o ho he using hy`. Use `⟨∑ k, A i k * o k j, Subring.sum_mem _ (fun k _ => O.mul_mem (hA i k) (ho k j)), ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, he, Finset.mul_sum, mul_left_comm]`.
-/
theorem mul_II {l m n : ℕ} {A : Matrix (Fin l) (Fin m) F} (hA : ∀ i j, A i j ∈ O)
    {y : Matrix (Fin m) (Fin n) F} (hy : y ∈ IIset O ϖ) : A * y ∈ IIset O ϖ := by
  intro i j
  choose o ho he using hy
  refine ⟨∑ k, A i k * o k j, Subring.sum_mem _ (fun k _ => O.mul_mem (hA i k) (ho k j)), ?_⟩
  simp only [Matrix.mul_apply, he, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Take `⟨κ, hκ, e⟩` from `Vol.piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hP k.2) (Vol.mem_piece.2 hm)`. Conclude with `⟨k * ⟨κ, hKP hκ⟩, e, by rw [map_mul, hρ κ hκ, mul_one]⟩`.
-/
theorem exists_of_congr (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1) (k : P)
    {m : Matrix (Fin r) (Fin r) F}
    (hm : m - ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ IIset O ϖ) :
    ∃ k' : P, ((k' : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = m ∧ ρ k' = ρ k := by
  obtain ⟨κ, hκ, e⟩ := Vol.piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hP k.2) (Vol.mem_piece.2 hm)
  exact ⟨k * ⟨κ, hKP hκ⟩, e, by rw [map_mul, hρ κ hκ, mul_one]⟩

/- English proof (translation)
Take `⟨⟨k, hk, ek⟩, h2⟩` from `hx`. Establish `e : (((⟨k, hk⟩ * g : P) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = toRows₁ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))`. Rewrite using `[LemmaU.toRows₁_mul, ← ek]`. Both sides reduce to the same expression. Establish `h3 : toRows₂ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) ∈ IIset O ϖ`.

Rewrite using `[LemmaU.toRows₂_mul]`. Conclude with `LemmaU.II_mul O ϖ _ h2 _ (hP g.2).1`. Use `⟨⟨⟨_, (⟨k, hk⟩ * g : P).2, e⟩, h3⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[phiU_of_mem ρ _ e h3, phiU_of_mem ρ ⟨k, hk⟩ ek h2, map_mul, Units.val_mul, mul_comm]`.
-/
theorem mul_right_mem (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) (g : P)
    {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hx : x ∈ suppSet t O ϖ P) :
    x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ suppSet t O ϖ P ∧
      phiU O ϖ P ρ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) =
        ((ρ g : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by
  obtain ⟨⟨k, hk, ek⟩, h2⟩ := hx
  have e : (((⟨k, hk⟩ * g : P) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      toRows₁ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) := by
    rw [LemmaU.toRows₁_mul, ← ek]; rfl
  have h3 : toRows₂ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) ∈ IIset O ϖ := by
    rw [LemmaU.toRows₂_mul]; exact LemmaU.II_mul O ϖ _ h2 _ (hP g.2).1
  refine ⟨⟨⟨_, (⟨k, hk⟩ * g : P).2, e⟩, h3⟩, ?_⟩
  rw [phiU_of_mem ρ _ e h3, phiU_of_mem ρ ⟨k, hk⟩ ek h2, map_mul, Units.val_mul, mul_comm]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ suppSet t O ϖ P`. Conclude with `(mul_right_mem hP ρ g hx).2`. Rewrite using `[phiU_of_notMem ρ hx, mul_zero, phiU_of_notMem]`. Introduce `h`. Use `(mul_right_mem hP ρ g⁻¹ h).1` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_assoc, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Conclude with `hx this`.
-/
theorem phiU_mul_right (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) (g : P)
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) :
    phiU O ϖ P ρ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) =
      ((ρ g : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by
  by_cases hx : x ∈ suppSet t O ϖ P
  · exact (mul_right_mem hP ρ g hx).2
  · rw [phiU_of_notMem ρ hx, mul_zero, phiU_of_notMem]
    intro h
    have := (mul_right_mem hP ρ g⁻¹ h).1
    rw [Matrix.mul_assoc, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at this
    exact hx this

/- English proof (translation)
Take `⟨⟨p, hp, ep⟩, h2⟩` from `hx`. Establish `e : h * x = fromRows (h.toBlocks₁₁ * toRows₁ x + h.toBlocks₁₂ * toRows₂ x) (h.toBlocks₂₁ * toRows₁ x + h.toBlocks₂₂ * toRows₂ x)`. Rewrite using `[← fromBlocks_mul_fromRows, fromBlocks_toBlocks, fromRows_toRows]`. Establish `h3 : toRows₂ (h * x) ∈ IIset O ϖ`. Rewrite using `[e, toRows₂_fromRows]`.

Use `II_add (LemmaU.II_mul O ϖ _ hc _ ?_) (mul_II (fun i j => hh _ _) h2)` and prove the remaining obligations. Rewrite using `[← ep]`. Conclude with `(hP hp).1`. Take `⟨k', ek', hk'⟩` from `exists_of_congr hϖ hϖ0 hloc hKP hP ρ hρ (k * ⟨p, hp⟩) (m := toRows₁ (h * x)) (by`. Rewrite using `[e, toRows₁_fromRows, ← hk, ← ep]`.

Establish `: (((k * ⟨p, hp⟩ : P) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (p : Matrix (Fin r) (Fin r) F)` using `rfl`. Rewrite using `[this, add_sub_cancel_left]`. Conclude with `mul_II (fun i j => hh _ _) h2)`. Use `⟨⟨⟨_, k'.2, ek'⟩, h3⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[phiU_of_mem ρ _ ek' h3, phiU_of_mem ρ ⟨p, hp⟩ ep h2, hk', map_mul, Units.val_mul]`.
-/
theorem mul_left_mem (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1)
    {h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F} (hh : ∀ i j, h i j ∈ O) (k : P)
    (hk : ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = h.toBlocks₁₁)
    (hc : h.toBlocks₂₁ ∈ IIset O ϖ)
    {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hx : x ∈ suppSet t O ϖ P) :
    h * x ∈ suppSet t O ϖ P ∧ phiU O ϖ P ρ (h * x) = ((ρ k : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by
  obtain ⟨⟨p, hp, ep⟩, h2⟩ := hx
  have e : h * x = fromRows (h.toBlocks₁₁ * toRows₁ x + h.toBlocks₁₂ * toRows₂ x)
      (h.toBlocks₂₁ * toRows₁ x + h.toBlocks₂₂ * toRows₂ x) := by
    rw [← fromBlocks_mul_fromRows, fromBlocks_toBlocks, fromRows_toRows]
  have h3 : toRows₂ (h * x) ∈ IIset O ϖ := by
    rw [e, toRows₂_fromRows]
    refine II_add (LemmaU.II_mul O ϖ _ hc _ ?_) (mul_II (fun i j => hh _ _) h2)
    rw [← ep]; exact (hP hp).1
  obtain ⟨k', ek', hk'⟩ := exists_of_congr hϖ hϖ0 hloc hKP hP ρ hρ (k * ⟨p, hp⟩)
    (m := toRows₁ (h * x)) (by
      rw [e, toRows₁_fromRows, ← hk, ← ep]
      have : (((k * ⟨p, hp⟩ : P) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
        ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (p : Matrix (Fin r) (Fin r) F) := rfl
      rw [this, add_sub_cancel_left]
      exact mul_II (fun i j => hh _ _) h2)
  refine ⟨⟨⟨_, k'.2, ek'⟩, h3⟩, ?_⟩
  rw [phiU_of_mem ρ _ ek' h3, phiU_of_mem ρ ⟨p, hp⟩ ep h2, hk', map_mul, Units.val_mul]

/- English proof (translation)
Take `⟨⟨p, hp, ep⟩, h2⟩` from `hx`. Establish `h3 : toRows₂ y ∈ IIset O ϖ`. Establish `: toRows₂ y = toRows₂ x + (toRows₂ y - toRows₂ x)` using `by abel`. Rewrite using `[this]`. Use `II_add h2 ?_` and prove the remaining obligations.

Rewrite using `[Vol.iiset_eq O ϖ hϖ0]`. Conclude with `fun i j => hy _ _`. Take `⟨k', ek', hk'⟩` from `exists_of_congr hϖ hϖ0 hloc hKP hP ρ hρ ⟨p, hp⟩ (m := toRows₁ y) (by`. Rewrite using `[Vol.iiset_eq O ϖ hϖ0]`. Introduce `i j`.

Use `hy (Sum.inl i) j` as an intermediate fact. Establish `e2 : (p : Matrix (Fin r) (Fin r) F) i j = x (Sum.inl i) j` using `congrFun (congrFun ep i) j`. Simplify `this)` using `[← e2]`. Use `⟨⟨⟨_, k'.2, ek'⟩, h3⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[phiU_of_mem ρ _ ek' h3, phiU_of_mem ρ ⟨p, hp⟩ ep h2, hk']`.
-/
theorem add_mem_supp (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1)
    {x y : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hy : ∀ i j, ϖ⁻¹ * (y i j - x i j) ∈ O)
    (hx : x ∈ suppSet t O ϖ P) :
    y ∈ suppSet t O ϖ P ∧ phiU O ϖ P ρ y = phiU O ϖ P ρ x := by
  obtain ⟨⟨p, hp, ep⟩, h2⟩ := hx
  have h3 : toRows₂ y ∈ IIset O ϖ := by
    have : toRows₂ y = toRows₂ x + (toRows₂ y - toRows₂ x) := by abel
    rw [this]
    refine II_add h2 ?_
    rw [Vol.iiset_eq O ϖ hϖ0]
    exact fun i j => hy _ _
  obtain ⟨k', ek', hk'⟩ := exists_of_congr hϖ hϖ0 hloc hKP hP ρ hρ ⟨p, hp⟩
    (m := toRows₁ y) (by
      rw [Vol.iiset_eq O ϖ hϖ0]
      intro i j
      have := hy (Sum.inl i) j
      have e2 : (p : Matrix (Fin r) (Fin r) F) i j = x (Sum.inl i) j := congrFun (congrFun ep i) j
      simpa [← e2] using this)
  refine ⟨⟨⟨_, k'.2, ek'⟩, h3⟩, ?_⟩
  rw [phiU_of_mem ρ _ ek' h3, phiU_of_mem ρ ⟨p, hp⟩ ep h2, hk']

/- English proof (translation)
Distinguish the cases in `hx : x ∈ suppSet t O ϖ P`. Conclude with `(add_mem_supp hϖ hϖ0 hloc hKP hP ρ hρ hy hx).2`. Rewrite using `[phiU_of_notMem ρ hx, phiU_of_notMem]`. Introduce `h`. Use `hx (add_mem_supp hϖ hϖ0 hloc hKP hP ρ hρ (fun i j => ?_) h).1` and prove the remaining obligations.

Use `O.neg_mem (hy i j)` as an intermediate fact. Rewrite `this` using `[← mul_neg, neg_sub]`. Then use the resulting hypothesis.
-/
theorem phiU_congr (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1)
    {x y : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hy : ∀ i j, ϖ⁻¹ * (y i j - x i j) ∈ O) :
    phiU O ϖ P ρ y = phiU O ϖ P ρ x := by
  by_cases hx : x ∈ suppSet t O ϖ P
  · exact (add_mem_supp hϖ hϖ0 hloc hKP hP ρ hρ hy hx).2
  · rw [phiU_of_notMem ρ hx, phiU_of_notMem]
    intro h
    refine hx (add_mem_supp hϖ hϖ0 hloc hKP hP ρ hρ (fun i j => ?_) h).1
    have := O.neg_mem (hy i j)
    rwa [← mul_neg, neg_sub] at this

/- English proof (translation)
Introduce and unpack `x ⟨⟨p, hp, ep⟩, h2⟩ (i | i) j`. Establish `e2 : (p : Matrix (Fin r) (Fin r) F) i j = x (Sum.inl i) j` using `congrFun (congrFun ep i) j`. Rewrite using `[← e2]`. Conclude with `(hP hp).1 i j`. Take `⟨o, ho, e⟩` from `h2 i j`.

Establish `e2 : x (Sum.inr i) j = ϖ * o` using `e`. Rewrite using `[e2]`. Conclude with `O.mul_mem hϖ ho`.
-/
theorem suppSet_subset (hϖ : ϖ ∈ O) (hP : P ≤ GLint O r) :
    suppSet t O ϖ P ⊆ intMatrices O (Fin r ⊕ Fin t) (Fin r) := by
  rintro x ⟨⟨p, hp, ep⟩, h2⟩ (i | i) j
  · have e2 : (p : Matrix (Fin r) (Fin r) F) i j = x (Sum.inl i) j := congrFun (congrFun ep i) j
    rw [← e2]; exact (hP hp).1 i j
  · obtain ⟨o, ho, e⟩ := h2 i j
    have e2 : x (Sum.inr i) j = ϖ * o := e
    rw [e2]; exact O.mul_mem hϖ ho

end Alg

section Top

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨⋂ i, ⋂ j, (fun y : Matrix (Fin r ⊕ Fin t) (Fin r) F => ϖ⁻¹ * (y i j - x i j)) ⁻¹' O, isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (continuous_const.mul ((continuous_id.matrix_elem i j).sub continuous_const)), by simp [O.zero_mem], fun y hy => ?_⟩` and prove the remaining obligations. Conclude with `phiU_congr hϖ hϖ0 hloc hKP hP ρ hρ (by simpa using hy)`.
-/
theorem isLocallyConstant_phiU (hO : IsOpen (O : Set F)) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1) :
    IsLocallyConstant (phiU (t := t) O ϖ P ρ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨⋂ i, ⋂ j, (fun y : Matrix (Fin r ⊕ Fin t) (Fin r) F => ϖ⁻¹ * (y i j - x i j)) ⁻¹' O,
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage
      (continuous_const.mul ((continuous_id.matrix_elem i j).sub continuous_const)),
    by simp [O.zero_mem], fun y hy => ?_⟩
  exact phiU_congr hϖ hϖ0 hloc hKP hP ρ hρ (by simpa using hy)

/- English proof (translation)
Establish `hS : IsCompact (Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (O : Set F))) : Set (Matrix (Fin r ⊕ Fin t) (Fin r) F))` using `isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hO))`. Use `HasCompactSupport.intro hS fun x hx => phiU_of_notMem ρ fun h => hx ?_` and prove the remaining obligations. Conclude with `fun i _ j _ => suppSet_subset hϖ hP h i j`.
-/
theorem hasCompactSupport_phiU [T2Space F] (hO : IsCompact (O : Set F)) (hϖ : ϖ ∈ O)
    (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) : HasCompactSupport (phiU (t := t) O ϖ P ρ) := by
  have hS : IsCompact (Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (O : Set F))) :
      Set (Matrix (Fin r ⊕ Fin t) (Fin r) F)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hO))
  refine HasCompactSupport.intro hS fun x hx => phiU_of_notMem ρ fun h => hx ?_
  exact fun i _ j _ => suppSet_subset hϖ hP h i j

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `e : Jset P = ⋃ c : {c : Fin r → Fin r → kF O ϖ hϖ // Vol.piece O ϖ (Vol.repM O ϖ hϖ c) ⊆ Jset P}, Vol.piece O ϖ (Vol.repM O ϖ hϖ c.1)`. Use `Set.Subset.antisymm ?_ (Set.iUnion_subset fun c => c.2)` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Establish `h1 : (p : Matrix (Fin r) (Fin r) F) ∈ intMat O r r` using `(hP hp).1`. Rewrite `h1` using `[Vol.intMat_eq_iUnion O ϖ hϖ]`.

Take `⟨c, hc⟩` from `Set.mem_iUnion.1 h1`. Use `Set.mem_iUnion.2 ⟨⟨c, fun z hz => ?_⟩, hc⟩` and prove the remaining obligations. Establish `hz' : z ∈ Vol.piece O ϖ (p : Matrix (Fin r) (Fin r) F)`. Rewrite `hz`, `hc`, the goal using `[Vol.mem_piece]`. Introduce `i j`.

Take `⟨o1, ho1, e1⟩` from `hz i j`. Take `⟨o2, ho2, e2⟩` from `hc i j`. Conclude with `⟨o1 - o2, O.sub_mem ho1 ho2, by rw [mul_sub, ← e1, ← e2]; ring⟩`. Take `⟨κ, hκ, e⟩` from `Vol.piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hP hp) hz'`. Conclude with `⟨_, P.mul_mem hp (hKP hκ), e⟩`.

Rewrite using `[e]`. Conclude with `MeasurableSet.iUnion fun c => Vol.meas_piece O hO ϖ hϖ0 _`.
-/
theorem measurableSet_Jset (hO : IsOpen (O : Set F)) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) :
    MeasurableSet (Jset P) := by
  have e : Jset P = ⋃ c : {c : Fin r → Fin r → kF O ϖ hϖ //
      Vol.piece O ϖ (Vol.repM O ϖ hϖ c) ⊆ Jset P}, Vol.piece O ϖ (Vol.repM O ϖ hϖ c.1) := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun c => c.2)
    rintro _ ⟨p, hp, rfl⟩
    have h1 : (p : Matrix (Fin r) (Fin r) F) ∈ intMat O r r := (hP hp).1
    rw [Vol.intMat_eq_iUnion O ϖ hϖ] at h1
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 h1
    refine Set.mem_iUnion.2 ⟨⟨c, fun z hz => ?_⟩, hc⟩
    have hz' : z ∈ Vol.piece O ϖ (p : Matrix (Fin r) (Fin r) F) := by
      rw [Vol.mem_piece] at hz hc ⊢
      intro i j
      obtain ⟨o1, ho1, e1⟩ := hz i j
      obtain ⟨o2, ho2, e2⟩ := hc i j
      exact ⟨o1 - o2, O.sub_mem ho1 ho2, by rw [mul_sub, ← e1, ← e2]; ring⟩
    obtain ⟨κ, hκ, e⟩ := Vol.piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hP hp) hz'
    exact ⟨_, P.mul_mem hp (hKP hκ), e⟩
  rw [e]
  exact MeasurableSet.iUnion fun c => Vol.meas_piece O hO ϖ hϖ0 _

omit [TopologicalSpace F] [IsTopologicalRing F] [BorelSpace F] [Field F] in
/- English proof (translation)
The claim follows from `measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inl i)`.
-/
theorem measurable_toRows₁ :
    Measurable (fun x : Matrix (Fin r ⊕ Fin t) (Fin r) F => toRows₁ x) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inl i)

omit [TopologicalSpace F] [IsTopologicalRing F] [BorelSpace F] [Field F] in
/- English proof (translation)
The claim follows from `measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inr i)`.
-/
theorem measurable_toRows₂ :
    Measurable (fun x : Matrix (Fin r ⊕ Fin t) (Fin r) F => toRows₂ x) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inr i)

/- English proof (translation)
Use `Vol.meas_ii O hO 1 one_ne_zero n a` as an intermediate fact. Rewrite `this` using `[Vol.iiset_eq O 1 one_ne_zero]`. Simplify `this` using `[intMat]`.
-/
theorem measurableSet_intMat (hO : IsOpen (O : Set F)) (n a : ℕ) :
    MeasurableSet (intMat O n a) := by
  have := Vol.meas_ii O hO 1 one_ne_zero n a
  rw [Vol.iiset_eq O 1 one_ne_zero] at this
  simpa [intMat] using this

/- English proof (translation)
The claim follows from `inferInstanceAs (MeasurableAdd (Fin r ⊕ Fin t → Fin r → F))`.
-/
theorem measurableAdd_rows : MeasurableAdd (Matrix (Fin r ⊕ Fin t) (Fin r) F) :=
  inferInstanceAs (MeasurableAdd (Fin r ⊕ Fin t → Fin r → F))

/- English proof (translation)
Use `measurableAdd_rows (F := F) (r := r) (t := t)` as an intermediate fact. Use `⟨fun g => Measure.ext fun A hA => ?_⟩` and prove the remaining obligations. Establish `hg` using `Vol.meas_add r r g`. Rewrite using `[Measure.map_apply hg hA, Measure.map_apply measurable_toRows₁ (hg hA), Measure.map_apply measurable_toRows₁ hA, Measure.restrict_apply (measurable_toRows₁ (hg hA)), Measure.restrict_apply (measurable_toRows₁ hA), ← measure_preimage_add ν (fromRows g 0) (_ ⁻¹' A ∩ _)]`. Use `congr 1`.

Use extensionality with `x`. Establish `e1 : toRows₁ (fromRows g 0 + x) = g + toRows₁ x` using `by ext i j; simp`. Establish `e2 : toRows₂ (fromRows g 0 + x) = toRows₂ x` using `by ext i j; simp`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, e1, e2]`.
-/
theorem invariant_top (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) [ν.IsAddLeftInvariant]
    (B : Set (Matrix (Fin t) (Fin r) F)) :
    ((ν.restrict (toRows₂ ⁻¹' B)).map toRows₁).IsAddLeftInvariant := by
  have := measurableAdd_rows (F := F) (r := r) (t := t)
  refine ⟨fun g => Measure.ext fun A hA => ?_⟩
  have hg := Vol.meas_add r r g
  rw [Measure.map_apply hg hA, Measure.map_apply measurable_toRows₁ (hg hA),
    Measure.map_apply measurable_toRows₁ hA, Measure.restrict_apply (measurable_toRows₁ (hg hA)),
    Measure.restrict_apply (measurable_toRows₁ hA),
    ← measure_preimage_add ν (fromRows g 0) (_ ⁻¹' A ∩ _)]
  congr 1
  ext x
  have e1 : toRows₁ (fromRows g 0 + x) = g + toRows₁ x := by ext i j; simp
  have e2 : toRows₂ (fromRows g 0 + x) = toRows₂ x := by ext i j; simp
  simp only [Set.mem_inter_iff, Set.mem_preimage, e1, e2]

/- English proof (translation)
Use `measurableAdd_rows (F := F) (r := r) (t := t)` as an intermediate fact. Use `⟨fun g => Measure.ext fun B hB => ?_⟩` and prove the remaining obligations. Establish `hg` using `Vol.meas_add t r g`. Rewrite using `[Measure.map_apply hg hB, Measure.map_apply measurable_toRows₂ (hg hB), Measure.map_apply measurable_toRows₂ hB, Measure.restrict_apply (measurable_toRows₂ (hg hB)), Measure.restrict_apply (measurable_toRows₂ hB), ← measure_preimage_add ν (fromRows 0 g) (_ ⁻¹' B ∩ _)]`. Use `congr 1`.

Use extensionality with `x`. Establish `e1 : toRows₁ (fromRows 0 g + x) = toRows₁ x` using `by ext i j; simp`. Establish `e2 : toRows₂ (fromRows 0 g + x) = g + toRows₂ x` using `by ext i j; simp`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, e1, e2]`.
-/
theorem invariant_bot (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) [ν.IsAddLeftInvariant]
    (A : Set (Matrix (Fin r) (Fin r) F)) :
    ((ν.restrict (toRows₁ ⁻¹' A)).map toRows₂).IsAddLeftInvariant := by
  have := measurableAdd_rows (F := F) (r := r) (t := t)
  refine ⟨fun g => Measure.ext fun B hB => ?_⟩
  have hg := Vol.meas_add t r g
  rw [Measure.map_apply hg hB, Measure.map_apply measurable_toRows₂ (hg hB),
    Measure.map_apply measurable_toRows₂ hB, Measure.restrict_apply (measurable_toRows₂ (hg hB)),
    Measure.restrict_apply (measurable_toRows₂ hB),
    ← measure_preimage_add ν (fromRows 0 g) (_ ⁻¹' B ∩ _)]
  congr 1
  ext x
  have e1 : toRows₁ (fromRows 0 g + x) = toRows₁ x := by ext i j; simp
  have e2 : toRows₂ (fromRows 0 g + x) = g + toRows₂ x := by ext i j; simp
  simp only [Set.mem_inter_iff, Set.mem_preimage, e1, e2]

/- English proof (translation)
Establish `i1` using `invariant_top ν (IIset O ϖ)`. Establish `i2` using `invariant_bot ν (intMat O r r)`. Establish `h1` using `volJadd F O hO ϖ hϖ hϖ0 hloc inferInstance r ((ν.restrict (toRows₂ ⁻¹' IIset O ϖ)).map toRows₁) P hKP hP`. Establish `h2` using `volII F O hO ϖ hϖ hϖ0 inferInstance t r ((ν.restrict (toRows₁ ⁻¹' intMat O r r)).map toRows₂)`. Establish `mJ` using `measurableSet_Jset hO hϖ hϖ0 hloc hKP hP`.

Establish `mI` using `Vol.meas_ii O hO ϖ hϖ0 t r`. Rewrite `h1` using `[Measure.map_apply measurable_toRows₁ mJ, Measure.map_apply measurable_toRows₁ (measurableSet_intMat hO r r), Measure.restrict_apply (measurable_toRows₁ mJ), Measure.restrict_apply (measurable_toRows₁ (measurableSet_intMat hO r r))]`. Rewrite `h2` using `[Measure.map_apply measurable_toRows₂ mI, Measure.map_apply measurable_toRows₂ (measurableSet_intMat hO t r), Measure.restrict_apply (measurable_toRows₂ mI), Measure.restrict_apply (measurable_toRows₂ (measurableSet_intMat hO t r)), Set.inter_comm]`. Establish `e : intMatrices O (Fin r ⊕ Fin t) (Fin r) = toRows₂ ⁻¹' intMat O t r ∩ toRows₁ ⁻¹' intMat O r r`. Use extensionality with `x`.

Conclude with `⟨fun h => ⟨fun i j => h _ _, fun i j => h _ _⟩, fun h i j => by rcases i with i | i; exacts [h.2 i j, h.1 i j]⟩`. Rewrite using `[e, ← h2, ← mul_assoc]`. Use `congr 1`.
-/
theorem measure_suppSet (hO : IsOpen (O : Set F)) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r)
    (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) [ν.IsAddLeftInvariant] :
    ν (suppSet t O ϖ P) * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (r * r) *
        (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (t * r) =
      (Nat.card (P ⧸ (congSub O ϖ r).subgroupOf P) : ENNReal) *
        ν (intMatrices O (Fin r ⊕ Fin t) (Fin r)) := by
  have i1 := invariant_top ν (IIset O ϖ)
  have i2 := invariant_bot ν (intMat O r r)
  have h1 := volJadd F O hO ϖ hϖ hϖ0 hloc inferInstance r
    ((ν.restrict (toRows₂ ⁻¹' IIset O ϖ)).map toRows₁) P hKP hP
  have h2 := volII F O hO ϖ hϖ hϖ0 inferInstance t r
    ((ν.restrict (toRows₁ ⁻¹' intMat O r r)).map toRows₂)
  have mJ := measurableSet_Jset hO hϖ hϖ0 hloc hKP hP
  have mI := Vol.meas_ii O hO ϖ hϖ0 t r
  rw [Measure.map_apply measurable_toRows₁ mJ,
    Measure.map_apply measurable_toRows₁ (measurableSet_intMat hO r r),
    Measure.restrict_apply (measurable_toRows₁ mJ),
    Measure.restrict_apply (measurable_toRows₁ (measurableSet_intMat hO r r))] at h1
  rw [Measure.map_apply measurable_toRows₂ mI,
    Measure.map_apply measurable_toRows₂ (measurableSet_intMat hO t r),
    Measure.restrict_apply (measurable_toRows₂ mI),
    Measure.restrict_apply (measurable_toRows₂ (measurableSet_intMat hO t r)),
    Set.inter_comm] at h2
  have e : intMatrices O (Fin r ⊕ Fin t) (Fin r) =
      toRows₂ ⁻¹' intMat O t r ∩ toRows₁ ⁻¹' intMat O r r := by
    ext x
    exact ⟨fun h => ⟨fun i j => h _ _, fun i j => h _ _⟩,
      fun h i j => by rcases i with i | i; exacts [h.2 i j, h.1 i j]⟩
  rw [e, ← h2, ← mul_assoc]
  congr 1

/- English proof (translation)
The claim follows from `(measurable_toRows₁ (measurableSet_Jset hO hϖ hϖ0 hloc hKP hP)).inter (measurable_toRows₂ (Vol.meas_ii O hO ϖ hϖ0 t r))`.
-/
theorem measurableSet_suppSet (hO : IsOpen (O : Set F)) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) :
    MeasurableSet (suppSet t O ϖ P) :=
  (measurable_toRows₁ (measurableSet_Jset hO hϖ hϖ0 hloc hKP hP)).inter
    (measurable_toRows₂ (Vol.meas_ii O hO ϖ hϖ0 t r))

/- English proof (translation)
Establish `hpt : ∀ x, phiU O ϖ P ρ x * conj (phiU O ϖ P ρ x) = (suppSet t O ϖ P).indicator (fun _ => (1 : ℂ)) x`. Introduce `x`. Distinguish the cases in `hx : x ∈ suppSet t O ϖ P`. Rewrite using `[Set.indicator_of_mem hx]`. Take `⟨⟨k, hk, ek⟩, h2⟩` from `hx`.

Rewrite using `[phiU_of_mem ρ ⟨k, hk⟩ ek h2, Complex.mul_conj, Complex.normSq_eq_norm_sq, hρ]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hx, phiU_of_notMem ρ hx, zero_mul]`. Unfold `weilIP`. Repeatedly rewrite using `[hpt]`.

Rewrite using `[integral_indicator_const _ hS]`. Simplify using `[Measure.real]`.
-/
theorem weilPairing_self_eq_measure_support (hS : MeasurableSet (suppSet t O ϖ P)) (ρ : P →* ℂˣ)
    (hρ : ∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1) (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) :
    weilIP ν (phiU O ϖ P ρ) (phiU O ϖ P ρ) = ((ν (suppSet t O ϖ P)).toReal : ℂ) := by
  have hpt : ∀ x, phiU O ϖ P ρ x * conj (phiU O ϖ P ρ x) =
      (suppSet t O ϖ P).indicator (fun _ => (1 : ℂ)) x := by
    intro x
    by_cases hx : x ∈ suppSet t O ϖ P
    · rw [Set.indicator_of_mem hx]
      obtain ⟨⟨k, hk, ek⟩, h2⟩ := hx
      rw [phiU_of_mem ρ ⟨k, hk⟩ ek h2, Complex.mul_conj, Complex.normSq_eq_norm_sq, hρ]
      simp
    · rw [Set.indicator_of_notMem hx, phiU_of_notMem ρ hx, zero_mul]
  unfold weilIP
  simp_rw [hpt]
  rw [integral_indicator_const _ hS]
  simp [Measure.real]

end Top

end GlobalTheory.SingleBlock
