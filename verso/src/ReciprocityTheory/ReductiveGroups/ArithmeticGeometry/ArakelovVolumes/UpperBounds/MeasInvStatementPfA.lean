import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix

noncomputable section

/- English proof (translation)
Use `letI : LinearOrder m := LinearOrder.lift' (fun i => OrderDual.toDual (κ i)) (fun a b hab => hκ (OrderDual.toDual.injective hab))`. Conclude with `Matrix.det_of_upperTriangular (fun i j hij => h i j hij)`.
-/
theorem det_of_key {m α : Type*} [Fintype m] [DecidableEq m] [LinearOrder α] {R : Type*} [CommRing R]
    (M : Matrix m m R) (κ : m → α) (hκ : Function.Injective κ)
    (h : ∀ i j, κ i < κ j → M i j = 0) : M.det = ∏ i, M i i := by
  letI : LinearOrder m := LinearOrder.lift' (fun i => OrderDual.toDual (κ i))
    (fun a b hab => hκ (OrderDual.toDual.injective hab))
  exact Matrix.det_of_upperTriangular (fun i j hij => h i j hij)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev Ix (ι : Type*) (r : ℕ) : Type _ := ι × Fin r × Fin r

def sl (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then w (τ, a, b) else 0

def up (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then 0 else w (τ, a, b)

def lu (w : Ix ι r → ℂ) : Ix ι r → ℂ := fun i => ((1 + sl w i.1) * up w i.1) i.2.1 i.2.2

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [sl, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma sl_add (h h' : Ix ι r → ℂ) (τ : ι) : sl (h + h') τ = sl h τ + sl h' τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [up, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma up_add (h h' : Ix ι r → ℂ) (τ : ι) : up (h + h') τ = up h τ + up h' τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [sl, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma sl_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : sl (c • h) τ = c • sl h τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [up, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma up_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : up (c • h) τ = c • up h τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def luD (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun h i := (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2
  map_add' h h' := by
    funext i
    simp only [sl_add, up_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Pi.add_apply]
    ring
  map_smul' c h := by
    funext i
    simp only [sl_smul, up_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    ring

def key (e : ι ≃ Fin (Fintype.card ι)) (i : Ix ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.2.1 : ℕ) + i.2.2, toLex ((i.2.1 : ℕ), e i.1))

/- English proof (translation)
Introduce and unpack `⟨τ, a, b⟩ ⟨τ', a', b'⟩ h`. Simplify using `only [key, toLex_inj, Prod.mk.injEq] at h`. Take `⟨h1, h2, h3⟩` from `h`. Establish `ha : a = a'` using `Fin.ext h2`. Establish `hb : b = b'` using `Fin.ext (by omega)`.

Establish `hτ : τ = τ'` using `e.injective h3`. Substitute `ha hb hτ` using the available equality. Both sides reduce to the same expression.
-/
lemma key_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (key (r := r) e) := by
  rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : a = a' := Fin.ext h2
  have hb : b = b' := Fin.ext (by omega)
  have hτ : τ = τ' := e.injective h3
  subst ha hb hτ
  rfl

/- English proof (translation)
Rewrite using `[Prod.Lex.le_iff]`. Simplify using `only [key, ofLex_toLex]`. Break down `h1.lt_or_eq with h | h` into its components or cases. Conclude with `Or.inl h`. Use `Or.inr ⟨h, ?_⟩` and prove the remaining obligations.

Rewrite using `[Prod.Lex.le_iff]`. Simplify using `only [ofLex_toLex]`. Break down `h2.lt_or_eq with h' | h'` into its components or cases. Conclude with `Or.inl h'`. Conclude with `Or.inr ⟨h', le_rfl⟩`.
-/
lemma key_le_of (e : ι ≃ Fin (Fintype.card ι)) (τ : ι) {a b a' b' : Fin r} (h1 : (a' : ℕ) + b' ≤ a + b)
    (h2 : (a' : ℕ) ≤ a) : key e (τ, a', b') ≤ key e (τ, a, b) := by
  rw [Prod.Lex.le_iff]
  simp only [key, ofLex_toLex]
  rcases h1.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    rw [Prod.Lex.le_iff]
    simp only [ofLex_toLex]
    rcases h2.lt_or_eq with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', le_rfl⟩

/- English proof (translation)
Use `show (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2 = _`. Rewrite using `[Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]`.
-/
lemma luD_apply (w h : Ix ι r → ℂ) (i : Ix ι r) :
    luD w h i = ∑ k, sl h i.1 i.2.1 k * up w i.1 k i.2.2 + ∑ k, (1 + sl w i.1) i.2.1 k * up h i.1 k i.2.2 := by
  show (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2 = _
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne h.ne]`. Simplify using `[sl, not_lt.mpr h.le]`.
-/
lemma one_add_sl_zero (w : Ix ι r → ℂ) (τ : ι) {a k : Fin r} (h : a < k) : (1 + sl w τ) a k = 0 := by
  rw [Matrix.add_apply, Matrix.one_apply_ne h.ne]
  simp [sl, not_lt.mpr h.le]

/- English proof (translation)
Take `⟨τ, a, b⟩` from `i`. Rewrite using `[LinearMap.toMatrix'_apply, luD_apply]`. Establish `hne : ∀ a' b' : Fin r, (a' : ℕ) + b' ≤ a + b → (a' : ℕ) ≤ a → (τ, a', b') ≠ j`. Introduce and unpack `a' b' h1 h2 rfl`. Conclude with `absurd (key_le_of e τ h1 h2) (not_le.mpr hij)`.

Establish `hs1 : ∀ k : Fin r, sl (Pi.single j (1 : ℂ)) τ a k * up w τ k b = 0`. Introduce `k`. Distinguish the cases in `hka : k < a`. Distinguish the cases in `hbk : b < k`. Simplify using `[Pi.single_apply, up, hbk]`.

Use `hne a k (by omega) le_rfl` as an intermediate fact. Simplify using `[Pi.single_apply, sl, hka, this]`. Simplify using `[Pi.single_apply, sl, hka]`. Establish `hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single j (1 : ℂ)) τ k b = 0`. Introduce `k`.

Distinguish the cases in `hka : a < k`. Rewrite using `[one_add_sl_zero w τ hka, zero_mul]`. Distinguish the cases in `hbk : b < k`. Simplify using `[Pi.single_apply, up, hbk]`. Use `hne k b (by omega) (by omega)` as an intermediate fact.

Simplify using `[Pi.single_apply, up, hbk, this]`. Rewrite using `[Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]`. Simplify using the standard rewrite rules.
-/
lemma toMatrix_luD_zero (e : ι ≃ Fin (Fintype.card ι)) (w : Ix ι r → ℂ) (i j : Ix ι r)
    (hij : key e i < key e j) : LinearMap.toMatrix' (luD w) i j = 0 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hne : ∀ a' b' : Fin r, (a' : ℕ) + b' ≤ a + b → (a' : ℕ) ≤ a → (τ, a', b') ≠ j := by
    rintro a' b' h1 h2 rfl
    exact absurd (key_le_of e τ h1 h2) (not_le.mpr hij)
  have hs1 : ∀ k : Fin r, sl (Pi.single j (1 : ℂ)) τ a k * up w τ k b = 0 := by
    intro k
    by_cases hka : k < a
    · by_cases hbk : b < k
      · simp [Pi.single_apply, up, hbk]
      · have := hne a k (by omega) le_rfl
        simp [Pi.single_apply, sl, hka, this]
    · simp [Pi.single_apply, sl, hka]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single j (1 : ℂ)) τ k b = 0 := by
    intro k
    by_cases hka : a < k
    · rw [one_add_sl_zero w τ hka, zero_mul]
    · by_cases hbk : b < k
      · simp [Pi.single_apply, up, hbk]
      · have := hne k b (by omega) (by omega)
        simp [Pi.single_apply, up, hbk, this]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp

/- English proof (translation)
Take `⟨τ, a, b⟩` from `i`. Rewrite using `[LinearMap.toMatrix'_apply, luD_apply]`. Establish `hs1 : ∀ k : Fin r, sl (Pi.single (τ, a, b) (1 : ℂ)) τ a k * up w τ k b = if k = b then (if b < a then w (τ, b, b) else 0) else 0`. Introduce `k`. Distinguish the cases in `hkb : k = b`.

Substitute `hkb` using the available equality. Apply the tactic sequence `by_cases hka : k < a <;> simp [Pi.single_apply, sl, up, hka]`. Simplify using `[Pi.single_apply, sl, hkb]`. Establish `hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single (τ, a, b) (1 : ℂ)) τ k b = if k = a then (if b < a then 0 else 1) else 0`. Introduce `k`.

Distinguish the cases in `hka : k = a`. Substitute `hka` using the available equality. Apply the tactic sequence `by_cases hbk : b < k <;> simp [Pi.single_apply, sl, up, hbk]`. Simplify using `[Pi.single_apply, up, hka]`. Rewrite using `[Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]`.

Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma toMatrix_luD_diag (w : Ix ι r → ℂ) (i : Ix ι r) :
    LinearMap.toMatrix' (luD w) i i = if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hs1 : ∀ k : Fin r, sl (Pi.single (τ, a, b) (1 : ℂ)) τ a k * up w τ k b =
      if k = b then (if b < a then w (τ, b, b) else 0) else 0 := by
    intro k
    by_cases hkb : k = b
    · subst hkb
      by_cases hka : k < a <;> simp [Pi.single_apply, sl, up, hka]
    · simp [Pi.single_apply, sl, hkb]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single (τ, a, b) (1 : ℂ)) τ k b =
      if k = a then (if b < a then 0 else 1) else 0 := by
    intro k
    by_cases hka : k = a
    · subst hka
      by_cases hbk : b < k <;> simp [Pi.single_apply, sl, up, hbk]
    · simp [Pi.single_apply, up, hka]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix', det_of_key _ (key (r := r) (Fintype.equivFin ι)) (key_injective _) (fun i j h => toMatrix_luD_zero _ w i j h)]`. Conclude with `Finset.prod_congr rfl fun i _ => toMatrix_luD_diag w i`.
-/
theorem det_luD (w : Ix ι r → ℂ) :
    LinearMap.det (luD w) = ∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  rw [← LinearMap.det_toMatrix', det_of_key _ (key (r := r) (Fintype.equivFin ι))
    (key_injective _) (fun i j h => toMatrix_luD_zero _ w i j h)]
  exact Finset.prod_congr rfl fun i _ => toMatrix_luD_diag w i

def luD' (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →L[ℝ] (Ix ι r → ℂ) :=
  LinearMap.toContinuousLinearMap ((luD w).restrictScalars ℝ)

/- English proof (translation)
Distinguish the cases in `hk : k < a`. Rewrite using `[if_pos hk]`. Establish `hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) = fun v => (1 : Matrix (Fin r) (Fin r) ℂ) a k + v (τ, a, k)`. Use function extensionality and compare the values at `v`. Simplify using `[sl, hk]`.

Rewrite using `[hf]`. Conclude with `(hasFDerivAt_apply (𝕜 := ℝ) (τ, a, k) w).const_add _`. Rewrite using `[if_neg hk]`. Establish `hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) = fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) a k`. Use function extensionality and compare the values at `v`.

Simplify using `[sl, hk]`. Rewrite using `[hf]`. Conclude with `hasFDerivAt_const _ _`.
-/
lemma hasFDerivAt_entry1 (w : Ix ι r → ℂ) (τ : ι) (a k : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => (1 + sl v τ) a k)
      (if k < a then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, a, k) else 0) w := by
  by_cases hk : k < a
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun v => (1 : Matrix (Fin r) (Fin r) ℂ) a k + v (τ, a, k) := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact (hasFDerivAt_apply (𝕜 := ℝ) (τ, a, k) w).const_add _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) a k := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact hasFDerivAt_const _ _

/- English proof (translation)
Distinguish the cases in `hk : b < k`. Rewrite using `[if_pos hk]`. Establish `hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun _ => (0 : ℂ)`. Use function extensionality and compare the values at `v`. Simplify using `[up, hk]`.

Rewrite using `[hf]`. Conclude with `hasFDerivAt_const _ _`. Rewrite using `[if_neg hk]`. Establish `hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun v => v (τ, k, b)`. Use function extensionality and compare the values at `v`.

Simplify using `[up, hk]`. Rewrite using `[hf]`. Conclude with `hasFDerivAt_apply (𝕜 := ℝ) (τ, k, b) w`.
-/
lemma hasFDerivAt_entry2 (w : Ix ι r → ℂ) (τ : ι) (k b : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => up v τ k b)
      (if b < k then 0 else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, k, b)) w := by
  by_cases hk : b < k
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun _ => (0 : ℂ) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_const _ _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun v => v (τ, k, b) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_apply (𝕜 := ℝ) (τ, k, b) w

/- English proof (translation)
Rewrite using `[hasFDerivAt_pi']`. Introduce and unpack `⟨τ, a, b⟩`. Establish `hf : (fun v : Ix ι r → ℂ => lu v (τ, a, b)) = fun v => ∑ k, (1 + sl v τ) a k * up v τ k b`. Use function extensionality and compare the values at `v`. Simplify using `only [lu, Matrix.mul_apply]`.

Rewrite using `[hf]`. Establish `hd` using `HasFDerivAt.sum (u := Finset.univ) (fun k _ => (hasFDerivAt_entry1 w τ a k).mul (hasFDerivAt_entry2 w τ k b))`. Use `hd using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`. Simplify using `only [Finset.sum_apply, Pi.mul_apply]`.

Apply `ContinuousLinearMap.ext` to reduce the goal to its premises. Introduce `h`. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply]`. Express the relevant statement in the definitionally equal form `luD w h (τ, a, b) = _`. Rewrite using `[luD_apply, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hka : k < a <;> by_cases hbk : b < k <;> simp [hka, hbk, sl, up] <;> ring`.
-/
theorem hasFDerivAt_lu (w : Ix ι r → ℂ) : HasFDerivAt lu (luD' w) w := by
  rw [hasFDerivAt_pi']
  rintro ⟨τ, a, b⟩
  have hf : (fun v : Ix ι r → ℂ => lu v (τ, a, b)) =
      fun v => ∑ k, (1 + sl v τ) a k * up v τ k b := by
    funext v
    simp only [lu, Matrix.mul_apply]
  rw [hf]
  have hd := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (hasFDerivAt_entry1 w τ a k).mul (hasFDerivAt_entry2 w τ k b))
  convert hd using 1
  · funext v
    simp only [Finset.sum_apply, Pi.mul_apply]
  · apply ContinuousLinearMap.ext
    intro h
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply]
    change luD w h (τ, a, b) = _
    rw [luD_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hka : k < a <;> by_cases hbk : b < k <;> simp [hka, hbk, sl, up] <;> ring

/- English proof (translation)
Rewrite using `[← det_luD w, ← Algebra.norm_complex_apply]`. Use `show LinearMap.det ((luD w).restrictScalars ℝ) = _`. Conclude with `LinearMap.det_restrictScalars`.
-/
theorem det_luD' (w : Ix ι r → ℂ) :
    (luD' w).det = Complex.normSq (∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1) := by
  rw [← det_luD w, ← Algebra.norm_complex_apply]
  show LinearMap.det ((luD w).restrictScalars ℝ) = _
  exact LinearMap.det_restrictScalars

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
