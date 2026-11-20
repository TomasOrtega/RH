import Mathlib

namespace PositivityTheory.ThKG.Tow.Levi

open Matrix

variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

def fr (ι : Matrix d e R) (x y : d → R) : Matrix d (e ⊕ Fin 2) R := fromCols ι (of fun i j => ![x i, y i] j)

def gr (J₁ : Matrix e e R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks J₁ 0 0 !![0, 1; -1, 0]

structure IsFr (c : R →+* R) (J : Matrix d d R) (J₁ : Matrix e e R) (ι : Matrix d e R) (x y : d → R) : Prop where
  gram : (fr ι x y)ᵀ * J * (fr ι x y).map c = gr J₁
  inv : ∃ A' : Matrix (e ⊕ Fin 2) d R, fr ι x y * A' = 1 ∧ A' * fr ι x y = 1

variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}

omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
/- English proof (translation)
Use extensionality with `i (j | j)`. Both sides reduce to the same expression. Apply the tactic sequence `fin_cases j <;> rfl`.
-/
theorem fr_map (f : R →+* S) : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := by
  ext i (j | j)
  · rfl
  · fin_cases j <;> rfl

omit [Fintype e] [DecidableEq e] in
/- English proof (translation)
Use extensionality with `(i | i) (j | j)`. Both sides reduce to the same expression. Simplify using `[gr]`. Simplify using `[gr]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [gr]`.
-/
theorem gr_map (f : R →+* S) : gr (J₁.map f) = (gr J₁).map f := by
  ext (i | i) (j | j)
  · rfl
  · simp [gr]
  · simp [gr]
  · fin_cases i <;> fin_cases j <;> simp [gr]

/- English proof (translation)
Take `⟨hg, A', h1, h2⟩` from `h`. Use `⟨?_, A'.map f, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[fr_map, gr_map, ← hg, Matrix.map_mul, Matrix.map_mul]`. Use `congr 1`. Conclude with `Matrix.ext fun i j => (hc _).symm`.

Rewrite using `[fr_map, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[fr_map, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem IsFr.map (h : IsFr c J J₁ ι x y) (f : R →+* S) {c' : S →+* S} (hc : ∀ a, f (c a) = c' (f a)) :
    IsFr c' (J.map f) (J₁.map f) (ι.map f) (fun i => f (x i)) (fun i => f (y i)) := by
  obtain ⟨hg, A', h1, h2⟩ := h
  refine ⟨?_, A'.map f, ?_, ?_⟩
  · rw [fr_map, gr_map, ← hg, Matrix.map_mul, Matrix.map_mul]
    congr 1
    exact Matrix.ext fun i j => (hc _).symm
  · rw [fr_map, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [fr_map, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Take `⟨hg, A', h1, h2⟩` from `h`. Establish `e1 : (fr ι x y).map c * A'.map c = 1`. Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `e2 : gr J₁ * (A'.map c * J⁻¹ * A'ᵀ) = 1`. Rewrite using `[← hg]`.

Combine the equalities or inequalities in the displayed calculation. Establish `e3` using `Matrix.isUnit_det_of_right_inverse e2`. Rewrite `e3` using `[gr, det_fromBlocks_zero₂₁]`. Conclude with `isUnit_of_mul_isUnit_left e3`.
-/
theorem IsFr.isUnit_det (h : IsFr c J J₁ ι x y) (hJ : IsUnit J.det) : IsUnit J₁.det := by
  obtain ⟨hg, A', h1, h2⟩ := h
  have e1 : (fr ι x y).map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : gr J₁ * (A'.map c * J⁻¹ * A'ᵀ) = 1 := by
    rw [← hg]
    calc _ = (fr ι x y)ᵀ * (J * ((fr ι x y).map c * A'.map c) * J⁻¹) * A'ᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, mul_nonsing_inv _ hJ, Matrix.mul_one, ← transpose_mul, h2, transpose_one]
  have e3 := Matrix.isUnit_det_of_right_inverse e2
  rw [gr, det_fromBlocks_zero₂₁] at e3
  exact isUnit_of_mul_isUnit_left e3

omit [DecidableEq d] [DecidableEq e] in
/- English proof (translation)
Rewrite `h` using `[fr, mul_fromCols, fromCols_mul_fromBlocks, fromCols_ext_iff]`. Use `⟨h.1, funext fun i => ?_, funext fun i => ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun h.2 i) 0` as an intermediate fact. Simplify `this` using `[mul_apply, mulVec, dotProduct, add_assoc, mul_comm]`. Use `congrFun (congrFun h.2 i) 1` as an intermediate fact.

Simplify `this` using `[mul_apply, mulVec, dotProduct, add_assoc, mul_comm]`.
-/
theorem cols_of_mul {m : Matrix d d R} {g : Matrix e e R} {b : Matrix e (Fin 2) R} {a : Matrix (Fin 2) e R}
    {s : Matrix (Fin 2) (Fin 2) R} (h : m * fr ι x y = fr ι x y * fromBlocks g b a s) :
    m * ι = ι * g + of (fun i j => ![x i, y i] j) * a ∧
      m *ᵥ x = ι *ᵥ (fun j => b j 0) + s 0 0 • x + s 1 0 • y ∧ m *ᵥ y = ι *ᵥ (fun j => b j 1) + s 0 1 • x + s 1 1 • y := by
  rw [fr, mul_fromCols, fromCols_mul_fromBlocks, fromCols_ext_iff] at h
  refine ⟨h.1, funext fun i => ?_, funext fun i => ?_⟩
  · have := congrFun (congrFun h.2 i) 0
    simpa [mul_apply, mulVec, dotProduct, add_assoc, mul_comm] using this
  · have := congrFun (congrFun h.2 i) 1
    simpa [mul_apply, mulVec, dotProduct, add_assoc, mul_comm] using this

/- English proof (translation)
Take `⟨hG, A', h1, h2⟩` from `h`. Use `set A := fr ι x y with hA`. Set `D : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R` to `fromBlocks g 0 0 !![t, 0; 0, c t']`. Set `D' : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R` to `fromBlocks g' 0 0 !![t', 0; 0, c t]`. Establish `hct : c t' * c t = 1` using `by rw [← map_mul, mul_comm, ht, map_one]`.

Establish `hD : D * D' = 1`. Rewrite using `[fromBlocks_multiply, ← fromBlocks_one]`. Use `congr 1`. Simplify using `using hg'`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [ht, hct]`. Establish `hDG : Dᵀ * gr J₁ * D.map c = gr J₁`. Rewrite using `[gr, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]`. Use `congr 1`.

Simplify using `using hg`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [mul_apply, ht, hct, hcc]`. Establish `e1 : A.map c * A'.map c = 1`.

Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `e2 : A * D * A' * A = A * D` using `by rw [Matrix.mul_assoc, h2, Matrix.mul_one]`. Take `⟨c1, c2, c3⟩` from `cols_of_mul e2`. Use `⟨A * D * A', A * D' * A', ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]`. Use `_ = (A * A')ᵀ * J * (A.map c * A'.map c) := by`. Rewrite using `[hG, hDG, ← hG]`. Simplify using `only [transpose_mul, Matrix.mul_assoc]`.

Use `_ = J := by rw [h1, e1, transpose_one, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[c2]`. Use extensionality with `i`. Simplify using `[mulVec, dotProduct]`. Rewrite using `[c3]`.

Use extensionality with `i`. Simplify using `[mulVec, dotProduct]`. Simplify using `using c1`.
-/
theorem IsFr.levi (h : IsFr c J J₁ ι x y) (hcc : ∀ a, c (c a) = a) {t t' : R} (ht : t * t' = 1) {g g' : Matrix e e R}
    (hg' : g * g' = 1) (hg : gᵀ * J₁ * g.map c = J₁) :
    ∃ m m' : Matrix d d R, m * m' = 1 ∧ mᵀ * J * m.map c = J ∧ m *ᵥ x = t • x ∧ m *ᵥ y = c t' • y ∧ m * ι = ι * g := by
  obtain ⟨hG, A', h1, h2⟩ := h
  set A := fr ι x y with hA
  let D : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g 0 0 !![t, 0; 0, c t']
  let D' : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g' 0 0 !![t', 0; 0, c t]
  have hct : c t' * c t = 1 := by rw [← map_mul, mul_comm, ht, map_one]
  have hD : D * D' = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simpa using hg'
    · simp
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [ht, hct]
  have hDG : Dᵀ * gr J₁ * D.map c = gr J₁ := by
    rw [gr, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    · simpa using hg
    · simp
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, ht, hct, hcc]
  have e1 : A.map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : A * D * A' * A = A * D := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  obtain ⟨c1, c2, c3⟩ := cols_of_mul e2
  refine ⟨A * D * A', A * D' * A', ?_, ?_, ?_, ?_, ?_⟩
  · calc _ = A * (D * (A' * A) * D') * A' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hD, Matrix.mul_one, h1]
  · calc _ = A'ᵀ * (Dᵀ * (Aᵀ * J * A.map c) * D.map c) * A'.map c := by
          simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]
      _ = (A * A')ᵀ * J * (A.map c * A'.map c) := by
          rw [hG, hDG, ← hG]; simp only [transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [h1, e1, transpose_one, Matrix.one_mul, Matrix.mul_one]
  · rw [c2]; ext i; simp [mulVec, dotProduct]
  · rw [c3]; ext i; simp [mulVec, dotProduct]
  · simpa using c1

/- English proof (translation)
Take `⟨hG, A', h1, h2⟩` from `h`. Use `set A := fr ι x y with hA`. Establish `hP : (A' * p * A)ᵀ * gr J₁ * (A' * p * A).map c = gr J₁`. Establish `e1 : A.map c * A'.map c = 1`. Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`.

Rewrite using `[← hG]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [h1, e1, transpose_one, Matrix.one_mul, Matrix.mul_one, hp]`. Establish `e2 : p * A = A * (A' * p * A)`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]`. Establish `e3 : ∀ i, (A' * p * A) i (Sum.inr 0) = t * (1 : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R) i (Sum.inr 0)` using `fun i => by`. Rewrite using `[← h2, Matrix.mul_assoc]`. Express the relevant statement in the definitionally equal form `(A' *ᵥ (p *ᵥ x)) i = t * (A' *ᵥ x) i`. Rewrite using `[hx, mulVec_smul]`.

Both sides reduce to the same expression. Generalize the expression as in `A' * p * A = P at hP e2 e3`. Establish `hct : c t * c t' = 1` using `by rw [← map_mul, ht, map_one]`. Establish `e4 : ∀ j, P (Sum.inr 1) (Sum.inl j) = 0` using `fun j => by`. Use `congrFun (congrFun hP (Sum.inl j)) (Sum.inr 0)` as an intermediate fact.

Simplify using `[mul_apply, e3, gr, one_apply, Fintype.sum_sum_type, apply_ite c] at this`. Combine the equalities or inequalities in the displayed calculation. Rewrite `e2` using `[← fromBlocks_toBlocks P]`. Use `⟨P.toBlocks₁₁, fun j => P (Sum.inr 0) (Sum.inl j), ?_, fun z => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Use `congrFun (congrFun hP (Sum.inl i)) (Sum.inl j)` as an intermediate fact. Simplify `this` using `[mul_apply, e4, gr, Fintype.sum_sum_type, toBlocks₁₁]`. Rewrite using `[mulVec_mulVec, (cols_of_mul e2).1, add_mulVec, mulVec_mulVec]`. Use `congr 1`. Use extensionality with `i`.

Simplify using `[mulVec, dotProduct, mul_apply, toBlocks₂₁, e4, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm]`.
-/
theorem IsFr.stab (h : IsFr c J J₁ ι x y) {t t' : R} (ht : t * t' = 1) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = t • x) :
    ∃ (g : Matrix e e R) (α : e → R), gᵀ * J₁ * g.map c = J₁ ∧ ∀ z, p *ᵥ (ι *ᵥ z) = ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • x := by
  obtain ⟨hG, A', h1, h2⟩ := h
  set A := fr ι x y with hA
  have hP : (A' * p * A)ᵀ * gr J₁ * (A' * p * A).map c = gr J₁ := by
    have e1 : A.map c * A'.map c = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← hG]
    calc _ = Aᵀ * (pᵀ * ((A * A')ᵀ * J * (A.map c * A'.map c)) * p.map c) * A.map c := by
          simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1, e1, transpose_one, Matrix.one_mul, Matrix.mul_one, hp]
  have e2 : p * A = A * (A' * p * A) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e3 : ∀ i, (A' * p * A) i (Sum.inr 0) = t * (1 : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R) i (Sum.inr 0) := fun i => by
    rw [← h2, Matrix.mul_assoc]
    change (A' *ᵥ (p *ᵥ x)) i = t * (A' *ᵥ x) i
    rw [hx, mulVec_smul]; rfl
  generalize A' * p * A = P at hP e2 e3
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  have e4 : ∀ j, P (Sum.inr 1) (Sum.inl j) = 0 := fun j => by
    have := congrFun (congrFun hP (Sum.inl j)) (Sum.inr 0)
    simp [mul_apply, e3, gr, one_apply, Fintype.sum_sum_type, apply_ite c] at this
    calc _ = P (Sum.inr 1) (Sum.inl j) * c t * c t' := by rw [mul_assoc, hct, mul_one]
      _ = 0 := by rw [this, zero_mul]
  rw [← fromBlocks_toBlocks P] at e2
  refine ⟨P.toBlocks₁₁, fun j => P (Sum.inr 0) (Sum.inl j), ?_, fun z => ?_⟩
  · ext i j
    have := congrFun (congrFun hP (Sum.inl i)) (Sum.inl j)
    simpa [mul_apply, e4, gr, Fintype.sum_sum_type, toBlocks₁₁] using this
  · rw [mulVec_mulVec, (cols_of_mul e2).1, add_mulVec, mulVec_mulVec]
    congr 1
    ext i
    simp [mulVec, dotProduct, mul_apply, toBlocks₂₁, e4, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm]

end PositivityTheory.ThKG.Tow.Levi
