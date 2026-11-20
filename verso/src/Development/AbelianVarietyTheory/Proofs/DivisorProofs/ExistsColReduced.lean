import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.Bruhat

variable {F : Type} [Field F] {n : ℕ}

/- English proof (translation)
Establish `hs : ∑ i : Fin n, (τ i : ℕ) = ∑ i : Fin n, (i : ℕ)` using `Equiv.sum_comp τ (fun i => (i : ℕ))`. Use `(Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin n => (τ i : ℕ)) (g := fun i : Fin n => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)` as an intermediate fact. Conclude with `Fin.ext this`.
-/
theorem perm_eq_of_le (τ : Equiv.Perm (Fin n)) (h : ∀ b, τ b ≤ b) (b : Fin n) : τ b = b := by
  have hs : ∑ i : Fin n, (τ i : ℕ) = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin n => (τ i : ℕ))
    (g := fun i : Fin n => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

def mono (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0

/- English proof (translation)
Simplify using `[mono, Matrix.mul_apply]`.
-/
theorem mul_mono (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (A * mono m) a c = A a (m.1 c) * m.2 c := by
  simp [mono, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (m.1.symm a)]`. Simplify using `[mono]`. Introduce `k _ hk`. Establish `: a ≠ m.1 k` using `fun h => hk (by rw [h, Equiv.symm_apply_apply])`. Simplify using `[mono, this]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem mono_mul (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (mono m * A) a c = m.2 (m.1.symm a) * A (m.1.symm a) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (m.1.symm a)]
  · simp [mono]
  · intro k _ hk
    have : a ≠ m.1 k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [mono, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `key : ∀ b, (m.2 b : F) = m'.2 (m'.1.symm (m.1 b)) * (u' : Matrix (Fin n) (Fin n) F) (m'.1.symm (m.1 b)) b`. Introduce `b`. Establish `h1` using `congrFun (congrFun h (m.1 b)) b`. Rewrite `h1` using `[mul_mono, mono_mul, unip_diag hu, one_mul]`. Then use the resulting hypothesis. Establish `hle : ∀ b, (m.1.trans m'.1.symm) b ≤ b`.

Introduce `b`. Assume the negation of the conclusion as `hlt`. Establish `hlt' : b < m'.1.symm (m.1 b)` using `not_le.1 hlt`. Apply `(m.2 b).ne_zero` to reduce the goal to its premises. Rewrite using `[key b, unip_lower hu' hlt', mul_zero]`.

Establish `hfix : ∀ b, m'.1.symm (m.1 b) = b` using `fun b => perm_eq_of_le _ hle b`. Use `Prod.ext (Equiv.ext fun b => ?_) (funext fun b => Units.ext ?_)` and prove the remaining obligations. Use `congrArg m'.1 (hfix b)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis. Rewrite using `[key b, hfix b, unip_diag hu', mul_one]`.
-/
theorem mono_unique {m m' : Equiv.Perm (Fin n) × (Fin n → Fˣ)} {u u' : GL (Fin n) F} (hu : u ∈ unip F n)
    (hu' : u' ∈ unip F n)
    (h : (u : Matrix (Fin n) (Fin n) F) * mono m = mono m' * (u' : Matrix (Fin n) (Fin n) F)) : m = m' := by
  have key : ∀ b, (m.2 b : F) = m'.2 (m'.1.symm (m.1 b)) *
      (u' : Matrix (Fin n) (Fin n) F) (m'.1.symm (m.1 b)) b := by
    intro b
    have h1 := congrFun (congrFun h (m.1 b)) b
    rwa [mul_mono, mono_mul, unip_diag hu, one_mul] at h1
  have hle : ∀ b, (m.1.trans m'.1.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < m'.1.symm (m.1 b) := not_le.1 hlt
    apply (m.2 b).ne_zero
    rw [key b, unip_lower hu' hlt', mul_zero]
  have hfix : ∀ b, m'.1.symm (m.1 b) = b := fun b => perm_eq_of_le _ hle b
  refine Prod.ext (Equiv.ext fun b => ?_) (funext fun b => Units.ext ?_)
  · have := congrArg m'.1 (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  · rw [key b, hfix b, unip_diag hu', mul_one]

/- English proof (translation)
Establish `hdet : A.det ≠ 0`. Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => hl i j hij)]`. Simplify using `[hd]`. Conclude with `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, ⟨fun i j hij => hl i j hij, hd⟩, rfl⟩`.
-/
theorem mem_unip_of {A : Matrix (Fin n) (Fin n) F} (hl : ∀ i j, j < i → A i j = 0) (hd : ∀ i, A i i = 1) :
    ∃ u ∈ unip F n, (u : Matrix (Fin n) (Fin n) F) = A := by
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hl i j hij)]
    simp [hd]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, ⟨fun i j hij => hl i j hij, hd⟩, rfl⟩

/- English proof (translation)
Set `P : ℕ → Prop` to `fun N => ∃ u ∈ unip F n, ∃ f : Fin n → ℕ, ∑ c, f c = N ∧ ∀ a c : Fin n, f c ≤ a.val → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0`. Establish `hex : ∃ N, P N` using `⟨_, 1, Subgroup.one_mem _, fun _ => n, rfl, fun a c h => absurd a.2 (not_lt.2 h)⟩`. Take `⟨u, hu, f, hf, hz⟩` from `Nat.find_spec hex`. Establish `hpos : ∀ c, 0 < f c`. Introduce `c`.

Assume the negation of the conclusion as `h0`. Establish `h1 : (((g * u)⁻¹ * (g * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c c = 1`. Rewrite using `[inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]`. Rewrite `h1` using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero]`. Conclude with `zero_ne_one h1`.

Introduce `k _`. Rewrite using `[hz k c (by omega), mul_zero]`. Establish `hmin : ∀ v ∈ unip F n, (∀ a c : Fin n, f c ≤ a.val → ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0) → ∀ c, ∃ a : Fin n, a.val + 1 = f c ∧ ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c ≠ 0`. Introduce `v hv hzv c`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hlt : ∑ k, Function.update f c (f c - 1) k < Nat.find hex`. Rewrite using `[← hf]`. Use `Finset.sum_lt_sum (fun k _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = c`.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hk]`. Use `hpos c` as an intermediate fact. Rewrite using `[Function.update_self]`.

Use linear arithmetic over natural numbers and integers. Use `Nat.find_min hex hlt ⟨v, hv, _, rfl, fun a k hk => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hkc : k = c`. Substitute `hkc` using the available equality. Rewrite `hk` using `[Function.update_self]`.

Distinguish the cases in `h2 : f k ≤ a.val`. Conclude with `hzv a k h2`. Conclude with `hcon a (by omega)`. Rewrite `hk` using `[Function.update_of_ne hkc]`. Conclude with `hzv a k hk`.

Use `choose s hs hsne using hmin u hu hz`. Establish `hinj : ∀ k c, k < c → s k ≠ s c`. Introduce `k c hkc he`. Establish `hfe : f k = f c` using `by rw [← hs k, ← hs c, he]`. Use `set H := ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH`.

Take `⟨t, ht, htv⟩` from `mem_unip_of (A := Matrix.transvection k c (-(H (s c) c / H (s c) k))) (fun i j hij => by`. Establish `h1 : ¬ (k = i ∧ c = j)`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `absurd hkc (not_lt.2 hij.le)`. Simplify using `[Matrix.transvection, Matrix.one_apply_ne (ne_of_gt hij), Matrix.single_apply, h1])`.

Use the proof step `(fun i => by`. Establish `h1 : ¬ (k = i ∧ c = i)`. Introduce and unpack `⟨rfl, h⟩`. Conclude with `absurd h (ne_of_gt hkc)`. Simplify using `[Matrix.transvection, Matrix.single_apply, h1])`.

Establish `hval : ((g * (u * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = H * Matrix.transvection k c (-(H (s c) c / H (s c) k))`. Rewrite using `[← mul_assoc, Units.val_mul, htv]`. Take `⟨a, ha, hane⟩` from `hmin (u * t) (Subgroup.mul_mem _ hu ht) (fun a j hj => by`. Rewrite using `[hval]`. Distinguish the cases in `hjc : j = c`.

Substitute `hjc` using the available equality. Rewrite using `[Matrix.mul_transvection_apply_same, hz a j hj, hz a k (hfe ▸ hj)]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_transvection_apply_of_ne _ _ _ _ hjc]`. Conclude with `hz a j hj) c`.

Establish `hac : a = s c` using `Fin.ext (by have := hs c; omega)`. Apply `hane` to reduce the goal to its premises. Establish `hk0 : H (s c) k ≠ 0` using `he ▸ hsne k`. Rewrite using `[hval, Matrix.mul_transvection_apply_same, hac]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hinj' : Function.Injective s`. Introduce `k c he`. Break down `lt_trichotomy k c with h | h | h` into its components or cases. Conclude with `absurd he (hinj k c h)`.

Conclude with `h`. Conclude with `absurd he.symm (hinj c k h)`. Use `⟨u, hu, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj'), hsne, fun a c h => hz a c ?_⟩` and prove the remaining obligations. Establish `h1 : (s c).val < a.val` using `h`. Use `hs c` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_col_reduced (g : GL (Fin n) F) :
    ∃ u ∈ unip F n, ∃ σ : Equiv.Perm (Fin n),
      (∀ c, ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (σ c) c ≠ 0) ∧
      ∀ a c, σ c < a → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0 := by
  classical
  let P : ℕ → Prop := fun N => ∃ u ∈ unip F n, ∃ f : Fin n → ℕ, ∑ c, f c = N ∧
    ∀ a c : Fin n, f c ≤ a.val → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0
  have hex : ∃ N, P N := ⟨_, 1, Subgroup.one_mem _, fun _ => n, rfl,
    fun a c h => absurd a.2 (not_lt.2 h)⟩
  obtain ⟨u, hu, f, hf, hz⟩ := Nat.find_spec hex
  have hpos : ∀ c, 0 < f c := by
    intro c
    by_contra h0
    have h1 : (((g * u)⁻¹ * (g * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c c = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      rw [hz k c (by omega), mul_zero]
  have hmin : ∀ v ∈ unip F n,
      (∀ a c : Fin n, f c ≤ a.val → ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0) →
      ∀ c, ∃ a : Fin n, a.val + 1 = f c ∧ ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c ≠ 0 := by
    intro v hv hzv c
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ k, Function.update f c (f c - 1) k < Nat.find hex := by
      rw [← hf]
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
      · by_cases hk : k = c
        · subst hk; simp
        · rw [Function.update_of_ne hk]
      · have := hpos c
        rw [Function.update_self]; omega
    refine Nat.find_min hex hlt ⟨v, hv, _, rfl, fun a k hk => ?_⟩
    by_cases hkc : k = c
    · subst hkc
      rw [Function.update_self] at hk
      by_cases h2 : f k ≤ a.val
      · exact hzv a k h2
      · exact hcon a (by omega)
    · rw [Function.update_of_ne hkc] at hk
      exact hzv a k hk
  choose s hs hsne using hmin u hu hz
  have hinj : ∀ k c, k < c → s k ≠ s c := by
    intro k c hkc he
    have hfe : f k = f c := by rw [← hs k, ← hs c, he]
    set H := ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
    obtain ⟨t, ht, htv⟩ := mem_unip_of (A := Matrix.transvection k c (-(H (s c) c / H (s c) k)))
      (fun i j hij => by
        have h1 : ¬ (k = i ∧ c = j) := by
          rintro ⟨rfl, rfl⟩; exact absurd hkc (not_lt.2 hij.le)
        simp [Matrix.transvection, Matrix.one_apply_ne (ne_of_gt hij), Matrix.single_apply, h1])
      (fun i => by
        have h1 : ¬ (k = i ∧ c = i) := by
          rintro ⟨rfl, h⟩; exact absurd h (ne_of_gt hkc)
        simp [Matrix.transvection, Matrix.single_apply, h1])
    have hval : ((g * (u * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        H * Matrix.transvection k c (-(H (s c) c / H (s c) k)) := by
      rw [← mul_assoc, Units.val_mul, htv]
    obtain ⟨a, ha, hane⟩ := hmin (u * t) (Subgroup.mul_mem _ hu ht) (fun a j hj => by
      rw [hval]
      by_cases hjc : j = c
      · subst hjc
        rw [Matrix.mul_transvection_apply_same, hz a j hj, hz a k (hfe ▸ hj)]
        simp
      · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hjc]
        exact hz a j hj) c
    have hac : a = s c := Fin.ext (by have := hs c; omega)
    apply hane
    have hk0 : H (s c) k ≠ 0 := he ▸ hsne k
    rw [hval, Matrix.mul_transvection_apply_same, hac]
    field_simp
    ring
  have hinj' : Function.Injective s := by
    intro k c he
    rcases lt_trichotomy k c with h | h | h
    · exact absurd he (hinj k c h)
    · exact h
    · exact absurd he.symm (hinj c k h)
  refine ⟨u, hu, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj'), hsne, fun a c h => hz a c ?_⟩
  have h1 : (s c).val < a.val := h
  have := hs c
  omega

/- English proof (translation)
Take `⟨v, hv, σ, hne, hz⟩` from `exists_col_reduced g`. Use `set H := ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH`. Take `⟨u, hu, huv⟩` from `mem_unip_of (A := Matrix.of fun a b => H a (σ.symm b) / H b (σ.symm b)) (fun i j hij => by`. Rewrite using `[Matrix.of_apply, hz i _ (by simpa using hij), zero_div])`. Use the proof step `(fun i => by`.

Use `hne (σ.symm i)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Rewrite using `[Matrix.of_apply, div_self this])`. Use `⟨(σ, fun c => Units.mk0 _ (hne c)), u, hu, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩` and prove the remaining obligations. Establish `h1 : (u : Matrix (Fin n) (Fin n) F) * mono (σ, fun c => Units.mk0 _ (hne c)) = H`.

Use extensionality with `a c`. Rewrite using `[mul_mono, huv]`. Simplify using `[div_mul_cancel₀ _ (hne c)]`. Rewrite using `[h1, hH, ← Units.val_mul, mul_inv_cancel_right]`.
-/
theorem exists_decomp (g : GL (Fin n) F) : ∃ m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n,
    (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * mono m * (u' : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨v, hv, σ, hne, hz⟩ := exists_col_reduced g
  set H := ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
  obtain ⟨u, hu, huv⟩ := mem_unip_of (A := Matrix.of fun a b => H a (σ.symm b) / H b (σ.symm b))
    (fun i j hij => by
      rw [Matrix.of_apply, hz i _ (by simpa using hij), zero_div])
    (fun i => by
      have := hne (σ.symm i)
      rw [Equiv.apply_symm_apply] at this
      rw [Matrix.of_apply, div_self this])
  refine ⟨(σ, fun c => Units.mk0 _ (hne c)), u, hu, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
  have h1 : (u : Matrix (Fin n) (Fin n) F) * mono (σ, fun c => Units.mk0 _ (hne c)) = H := by
    ext a c
    rw [mul_mono, huv]
    simp [div_mul_cancel₀ _ (hne c)]
  rw [h1, hH, ← Units.val_mul, mul_inv_cancel_right]

/- English proof (translation)
Introduce `F _ n g`. Take `⟨m, u, hu, u', hu', h⟩` from `exists_decomp g`. Use `⟨m, ⟨u, hu, u', hu', h⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `m' ⟨v, hv, v', hv', h'⟩`. Establish `h2 : (v : Matrix (Fin n) (Fin n) F) * mono m' * v' = u * mono m * u'` using `h'.symm.trans h`.

Use `mono_unique (u := u⁻¹ * v) (u' := u' * v'⁻¹) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hv) (Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hv')) ?_` and prove the remaining obligations. Establish `h3` using `congrArg (fun X => ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X * ((v'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h2`. Simplify using `only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.inv_mul_cancel_left] at h3`. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Conclude with `h3`.
-/
theorem bruhat : ∀ (F : Type) [Field F] (n : ℕ) (g : GL (Fin n) F), ∃! m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n, (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * (Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0) * (u' : Matrix (Fin n) (Fin n) F) := by
  intro F _ n g
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  refine ⟨m, ⟨u, hu, u', hu', h⟩, ?_⟩
  rintro m' ⟨v, hv, v', hv', h'⟩
  have h2 : (v : Matrix (Fin n) (Fin n) F) * mono m' * v' = u * mono m * u' := h'.symm.trans h
  refine mono_unique (u := u⁻¹ * v) (u' := u' * v'⁻¹) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hv)
    (Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hv')) ?_
  have h3 := congrArg (fun X => ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X *
    ((v'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h2
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.inv_mul_cancel_left] at h3
  simp only [Units.val_mul, Matrix.mul_assoc]
  exact h3

end GlobalTheory.FinGL.Bruhat
