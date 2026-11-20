import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.RepPf

variable {C : Type} [Field C] {N n : ℕ}

section
variable (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N)

noncomputable def coef (a : Mat C N) (i j : Fin n) : C := by
  classical
  exact if h : ∃ c : C, E i j ≠ 0 ∧ p i * a * p j = c • E i j then h.choose else 0

/- English proof (translation)
Unfold `coef`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨c, hc, -⟩`. Conclude with `hc h`.
-/
lemma coef_zero {a : Mat C N} {i j : Fin n} (h : E i j = 0) : coef p E a i j = 0 := by
  unfold coef
  rw [dif_neg]
  rintro ⟨c, hc, -⟩
  exact hc h

variable {p E}

/- English proof (translation)
Take `⟨c, hc⟩` from `hM.2.2.2.2.2 a ha i j`. Distinguish the cases in `hE : E i j = 0`. Rewrite using `[hc, hE, smul_zero, smul_zero]`. Establish `h : ∃ c : C, E i j ≠ 0 ∧ p i * a * p j = c • E i j` using `⟨c, hE, hc⟩`. Unfold `coef`.

Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec.2`.
-/
lemma coef_spec {R : Subalgebra C (Mat C N)} (hM : MUnits R p E) {a : Mat C N} (ha : a ∈ R)
    (i j : Fin n) : p i * a * p j = coef p E a i j • E i j := by
  obtain ⟨c, hc⟩ := hM.2.2.2.2.2 a ha i j
  by_cases hE : E i j = 0
  · rw [hc, hE, smul_zero, smul_zero]
  · have h : ∃ c : C, E i j ≠ 0 ∧ p i * a * p j = c • E i j := ⟨c, hE, hc⟩
    unfold coef
    rw [dif_pos h]
    exact h.choose_spec.2

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma E_left {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    p i * E i j = E i j := by
  calc p i * E i j = p i * (p i * E i j * p j) := by rw [hM.2.2.1 i j]
    _ = (p i * p i) * E i j * p j := by simp only [mul_assoc]
    _ = E i j := by rw [(hp.1.idem i).eq, hM.2.2.1 i j]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma E_right {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    E i j * p j = E i j := by
  calc E i j * p j = (p i * E i j * p j) * p j := by rw [hM.2.2.1 i j]
    _ = p i * E i j * (p j * p j) := by simp only [mul_assoc]
    _ = E i j := by rw [(hp.1.idem j).eq, hM.2.2.1 i j]

/- English proof (translation)
Establish `h : ∀ j, (p i * a * p j) * (p j * b * p k) = p i * a * p j * b * p k`. Introduce `j`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [(hp.1.idem j).eq]`.

Simplify using `only [h]`. Rewrite using `[← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hp.1.complete, mul_one]`. Simplify using `only [mul_assoc]`.
-/
lemma expand (hp : Sys p) (a b : Mat C N) (i k : Fin n) :
    p i * (a * b) * p k = ∑ j, (p i * a * p j) * (p j * b * p k) := by
  have h : ∀ j, (p i * a * p j) * (p j * b * p k) = p i * a * p j * b * p k := by
    intro j
    calc (p i * a * p j) * (p j * b * p k) = p i * a * (p j * p j) * b * p k := by
          simp only [mul_assoc]
      _ = _ := by rw [(hp.1.idem j).eq]
  simp only [h]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hp.1.complete, mul_one]
  simp only [mul_assoc]

/- English proof (translation)
Distinguish the cases in `hik : E i k = 0`. Rewrite using `[coef_zero p E hik]`. Use `symm`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hij : E i j = 0`.

Rewrite using `[coef_zero p E hij, zero_mul]`. Distinguish the cases in `hjk : E j k = 0`. Rewrite using `[coef_zero p E hjk, mul_zero]`. Conclude with `absurd hik (hM.2.2.2.2.1 i j k hij hjk).2`. Apply `smul_left_injective C hik` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← coef_spec hM (R.mul_mem ha hb), expand hp, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[coef_spec hM ha, coef_spec hM hb, smul_mul_smul_comm]`. Distinguish the cases in `hij : E i j = 0`.

Simplify using `[hij, coef_zero p E hij]`. Distinguish the cases in `hjk : E j k = 0`. Simplify using `[hjk, coef_zero p E hjk]`. Rewrite using `[(hM.2.2.2.2.1 i j k hij hjk).1]`.
-/
lemma coef_mul {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a b : Mat C N}
    (ha : a ∈ R) (hb : b ∈ R) (i k : Fin n) :
    coef p E (a * b) i k = ∑ j, coef p E a i j * coef p E b j k := by
  by_cases hik : E i k = 0
  · rw [coef_zero p E hik]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : E i j = 0
    · rw [coef_zero p E hij, zero_mul]
    by_cases hjk : E j k = 0
    · rw [coef_zero p E hjk, mul_zero]
    exact absurd hik (hM.2.2.2.2.1 i j k hij hjk).2
  · apply smul_left_injective C hik
    simp only
    rw [← coef_spec hM (R.mul_mem ha hb), expand hp, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coef_spec hM ha, coef_spec hM hb, smul_mul_smul_comm]
    by_cases hij : E i j = 0
    · simp [hij, coef_zero p E hij]
    by_cases hjk : E j k = 0
    · simp [hjk, coef_zero p E hjk]
    rw [(hM.2.2.2.2.1 i j k hij hjk).1]

/- English proof (translation)
Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.one_apply_eq]`. Establish `hE : E i i ≠ 0` using `by rw [hM.2.1 i]; exact hp.2 i`. Apply `smul_left_injective C hE` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← coef_spec hM R.one_mem, one_smul, mul_one, (hp.1.idem i).eq, hM.2.1 i]`. Rewrite using `[Matrix.one_apply_ne hij]`. Distinguish the cases in `hE : E i j = 0`. Conclude with `coef_zero p E hE`.

Apply `smul_left_injective C hE` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← coef_spec hM R.one_mem, zero_smul, mul_one, hp.1.ortho hij]`.
-/
lemma coef_one {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    coef p E 1 i j = (1 : Matrix (Fin n) (Fin n) C) i j := by
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    have hE : E i i ≠ 0 := by rw [hM.2.1 i]; exact hp.2 i
    apply smul_left_injective C hE
    simp only
    rw [← coef_spec hM R.one_mem, one_smul, mul_one, (hp.1.idem i).eq, hM.2.1 i]
  · rw [Matrix.one_apply_ne hij]
    by_cases hE : E i j = 0
    · exact coef_zero p E hE
    apply smul_left_injective C hE
    simp only
    rw [← coef_spec hM R.one_mem, zero_smul, mul_one, hp.1.ortho hij]

end

section
variable {p : Fin n → Mat C N} {E : Fin n → Fin n → Mat C N}

variable (E) in

noncomputable def blk (j : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => E i j ≠ 0

variable (E) in

noncomputable def bb (j : Fin n) : Fin n :=
  if h : (blk E j).Nonempty then (blk E j).min' h else j

/- English proof (translation)
Unfold `blk`. Simplify using the standard rewrite rules.
-/
lemma mem_blk {i j : Fin n} : i ∈ blk E j ↔ E i j ≠ 0 := by
  classical
  unfold blk
  simp

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
lemma min'_congr {s t : Finset (Fin n)} (h : s.Nonempty) (h' : t.Nonempty) (e : s = t) :
    s.min' h = t.min' h' := by
  subst e; rfl

/- English proof (translation)
Establish `hne : (blk E j).Nonempty` using `⟨j, mem_blk.2 (by rw [hM.2.1 j]; exact hp.2 j)⟩`. Use `⟨hne, ?_⟩` and prove the remaining obligations. Unfold `bb`. Rewrite using `[dif_pos hne]`. Conclude with `mem_blk.1 (Finset.min'_mem _ hne)`.
-/
lemma bb_spec {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (j : Fin n) :
    (blk E j).Nonempty ∧ E (bb E j) j ≠ 0 := by
  have hne : (blk E j).Nonempty := ⟨j, mem_blk.2 (by rw [hM.2.1 j]; exact hp.2 j)⟩
  refine ⟨hne, ?_⟩
  unfold bb
  rw [dif_pos hne]
  exact mem_blk.1 (Finset.min'_mem _ hne)

/- English proof (translation)
The claim follows from `hM.2.2.2.1 _ _ (bb_spec hp hM j).2`.
-/
lemma bb_ne {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (j : Fin n) :
    E j (bb E j) ≠ 0 := hM.2.2.2.1 _ _ (bb_spec hp hM j).2

/- English proof (translation)
Establish `e : blk E i = blk E j`. Use extensionality with `k`. Rewrite using `[mem_blk, mem_blk]`. Prove the components needed by the constructor for the conclusion. Introduce `hki`.

Conclude with `(hM.2.2.2.2.1 k i j hki hij).2`. Introduce `hkj`. Conclude with `(hM.2.2.2.2.1 k j i hkj (hM.2.2.2.1 i j hij)).2`. Unfold `bb`. Rewrite using `[dif_pos (bb_spec hp hM i).1, dif_pos (bb_spec hp hM j).1]`.

Conclude with `min'_congr _ _ e`.
-/
lemma bb_congr {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {i j : Fin n}
    (hij : E i j ≠ 0) : bb E i = bb E j := by
  have e : blk E i = blk E j := by
    ext k
    rw [mem_blk, mem_blk]
    constructor
    · intro hki; exact (hM.2.2.2.2.1 k i j hki hij).2
    · intro hkj; exact (hM.2.2.2.2.1 k j i hkj (hM.2.2.2.1 i j hij)).2
  unfold bb
  rw [dif_pos (bb_spec hp hM i).1, dif_pos (bb_spec hp hM j).1]
  exact min'_congr _ _ e

/- English proof (translation)
Establish `h1 : a * E j (bb E j) = ∑ i, (p i * a * p j) * E j (bb E j)`. Rewrite using `[← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hp.1.complete, one_mul, mul_assoc, E_left hp hM]`. Rewrite using `[h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[coef_spec hM ha, smul_mul_assoc]`.

Distinguish the cases in `hij : E i j = 0`. Simplify using `[hij, coef_zero p E hij]`. Rewrite using `[(hM.2.2.2.2.1 i j (bb E j) hij (bb_ne hp hM j)).1, bb_congr hp hM hij]`.
-/
lemma mul_E {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a : Mat C N}
    (ha : a ∈ R) (j : Fin n) : a * E j (bb E j) = ∑ i, coef p E a i j • E i (bb E i) := by
  have h1 : a * E j (bb E j) = ∑ i, (p i * a * p j) * E j (bb E j) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hp.1.complete, one_mul, mul_assoc,
      E_left hp hM]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coef_spec hM ha, smul_mul_assoc]
  by_cases hij : E i j = 0
  · simp [hij, coef_zero p E hij]
  rw [(hM.2.2.2.2.1 i j (bb E j) hij (bb_ne hp hM j)).1, bb_congr hp hM hij]

variable (E) in

noncomputable def T (w : Fin N → C) : Matrix (Fin N) (Fin n) C := Matrix.of fun x j => (E j (bb E j) *ᵥ w) x

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec]`. Simplify using `[T, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
lemma mul_T (M : Mat C N) (w : Fin N → C) (x : Fin N) (j : Fin n) :
    (M * T E w) x j = ((M * E j (bb E j)) *ᵥ w) x := by
  rw [← Matrix.mulVec_mulVec]
  simp [T, Matrix.mul_apply, Matrix.mulVec, dotProduct]

variable (p E) in

noncomputable def rmat (a : Mat C N) : Matrix (Fin n) (Fin n) C := Matrix.of fun i j => coef p E a i j

/- English proof (translation)
Simplify using `[T, rmat, Matrix.mul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, mul_comm]`.
-/
lemma T_mul (w : Fin N → C) (a : Mat C N) (x : Fin N) (j : Fin n) :
    (T E w * rmat p E a) x j = ((∑ i, coef p E a i j • E i (bb E i)) *ᵥ w) x := by
  simp [T, rmat, Matrix.mul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, mul_comm]

/- English proof (translation)
Use extensionality with `x j`. Rewrite using `[mul_T, T_mul, mul_E hp hM ha]`.
-/
lemma intertw {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a : Mat C N}
    (ha : a ∈ R) (w : Fin N → C) : a * T E w = T E w * rmat p E a := by
  ext x j
  rw [mul_T, T_mul, mul_E hp hM ha]

end

/- English proof (translation)
Introduce `Γ C _ _ N n ρ R p E hp hM hρ`. Set `f : Γ →* Matrix (Fin n) (Fin n) C` to `{ toFun := fun g => rmat p E (ρ g : Mat C N) map_one' := by`. Use extensionality with `i j`. Simplify using `only [map_one, Units.val_one]`. Conclude with `coef_one hp hM i j`.

Use the proof step `map_mul' := by`. Introduce `g h`. Use extensionality with `i k`. Simplify using `only [map_mul, Units.val_mul]`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `coef_mul hp hM (hρ g) (hρ h) i k }`. Set `r : Γ →* GL (Fin n) C` to `f.toHomUnits`. Establish `hcol : ∀ k, ∃ v : Fin N → C, p k *ᵥ v = v ∧ v ≠ 0`. Introduce `k`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hp.2 k` to reduce the goal to its premises. Use extensionality with `x c`. Establish `h1` using `hcon (p k *ᵥ Pi.single c 1) (by rw [Matrix.mulVec_mulVec, (hp.1.idem k).eq])`. Establish `h2` using `congrFun h1 x`.

Simplify `h2` using `[Matrix.mulVec_single_one]`. Use `choose v hv using hcol`. Set `w0` to `∑ k, v k`. Establish `hw : ∀ k, p k *ᵥ w0 = v k`. Introduce `k`.

Simplify using `only [w0, Matrix.mulVec_sum]`. Rewrite using `[Finset.sum_eq_single k]`. Conclude with `(hv k).1`. Introduce `m _ hmk`. Rewrite using `[← (hv m).1, Matrix.mulVec_mulVec, hp.1.ortho (Ne.symm hmk), Matrix.zero_mulVec]`.

Simplify using the standard rewrite rules. Establish `hu : ∀ k, ∃ u : Fin N → C, u ⬝ᵥ v k = 1`. Introduce `k`. Take `⟨x, hx⟩` from `Function.ne_iff.1 (hv k).2`. Establish `hx' : v k x ≠ 0` using `hx`.

Conclude with `⟨Pi.single x (v k x)⁻¹, by simp [hx']⟩`. Use `choose u hu using hu`. Set `A` to `T E w0`. Set `B : Matrix (Fin n) (Fin N) C` to `Matrix.of fun j x => (u (bb E j) ᵥ* E (bb E j) j) x`. Use `⟨r, A, B, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `j k`. Establish `hprod : E (bb E j) j * E k (bb E k) = if j = k then p (bb E j) else 0` using `by split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[(hM.2.2.2.2.1 _ j _ (bb_spec hp hM j).2 (bb_ne hp hM j)).1, hM.2.1]`. Rewrite using `[← E_right hp hM (bb E j) j, ← E_left hp hM k (bb E k)]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hBA : (B * A) j k = (u (bb E j) ᵥ* E (bb E j) j) ⬝ᵥ (E k (bb E k) *ᵥ w0)` using `rfl`. Rewrite using `[hBA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hprod]`. Use `split_ifs with h`. Rewrite using `[hw, hu, h, Matrix.one_apply_eq]`.

Rewrite using `[Matrix.zero_mulVec, dotProduct_zero, Matrix.one_apply_ne h]`. Introduce `g`. Conclude with `intertw hp hM (hρ g) w0`. Introduce `Z hZ`. Establish `hZE : ∀ j, Z * E j (bb E j) = 0`.

Introduce `j`. Rewrite using `[Matrix.ext_iff_mulVec]`. Introduce `w`. Establish `h1` using `hZ (T E w) (fun g => intertw hp hM (hρ g) w)`. Use extensionality with `x`.

Establish `h2` using `congrFun (congrFun h1 x) j`. Rewrite `h2` using `[mul_T]`. Simplify using `using h2`. Establish `hZp : ∀ j, Z * p j = 0`. Introduce `j`.

Establish `h3 : E j (bb E j) * E (bb E j) j = p j`. Rewrite using `[(hM.2.2.2.2.1 j (bb E j) j (bb_ne hp hM j) (bb_spec hp hM j).2).1, hM.2.1 j]`. Rewrite using `[← h3, ← mul_assoc, hZE j, zero_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_eq_zero fun j _ => hZp j`.
-/
theorem Rep_of : Rep := by
  classical
  intro Γ C _ _ N n ρ R p E hp hM hρ
  let f : Γ →* Matrix (Fin n) (Fin n) C :=
    { toFun := fun g => rmat p E (ρ g : Mat C N)
      map_one' := by
        ext i j
        simp only [map_one, Units.val_one]
        exact coef_one hp hM i j
      map_mul' := by
        intro g h
        ext i k
        simp only [map_mul, Units.val_mul]
        rw [Matrix.mul_apply]
        exact coef_mul hp hM (hρ g) (hρ h) i k }
  let r : Γ →* GL (Fin n) C := f.toHomUnits
  have hcol : ∀ k, ∃ v : Fin N → C, p k *ᵥ v = v ∧ v ≠ 0 := by
    intro k
    by_contra hcon
    push_neg at hcon
    apply hp.2 k
    ext x c
    have h1 := hcon (p k *ᵥ Pi.single c 1) (by rw [Matrix.mulVec_mulVec, (hp.1.idem k).eq])
    have h2 := congrFun h1 x
    simpa [Matrix.mulVec_single_one] using h2
  choose v hv using hcol
  let w0 := ∑ k, v k
  have hw : ∀ k, p k *ᵥ w0 = v k := by
    intro k
    simp only [w0, Matrix.mulVec_sum]
    rw [Finset.sum_eq_single k]
    · exact (hv k).1
    · intro m _ hmk
      rw [← (hv m).1, Matrix.mulVec_mulVec, hp.1.ortho (Ne.symm hmk), Matrix.zero_mulVec]
    · simp
  have hu : ∀ k, ∃ u : Fin N → C, u ⬝ᵥ v k = 1 := by
    intro k
    obtain ⟨x, hx⟩ := Function.ne_iff.1 (hv k).2
    have hx' : v k x ≠ 0 := hx
    exact ⟨Pi.single x (v k x)⁻¹, by simp [hx']⟩
  choose u hu using hu
  let A := T E w0
  let B : Matrix (Fin n) (Fin N) C := Matrix.of fun j x => (u (bb E j) ᵥ* E (bb E j) j) x
  refine ⟨r, A, B, ?_, ?_, ?_⟩
  · ext j k
    have hprod : E (bb E j) j * E k (bb E k) = if j = k then p (bb E j) else 0 := by
      split_ifs with h
      · subst h
        rw [(hM.2.2.2.2.1 _ j _ (bb_spec hp hM j).2 (bb_ne hp hM j)).1, hM.2.1]
      · rw [← E_right hp hM (bb E j) j, ← E_left hp hM k (bb E k)]
        calc E (bb E j) j * p j * (p k * E k (bb E k))
            = E (bb E j) j * (p j * p k) * E k (bb E k) := by simp only [mul_assoc]
          _ = 0 := by rw [hp.1.ortho h, mul_zero, zero_mul]
    have hBA : (B * A) j k = (u (bb E j) ᵥ* E (bb E j) j) ⬝ᵥ (E k (bb E k) *ᵥ w0) := rfl
    rw [hBA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hprod]
    split_ifs with h
    · rw [hw, hu, h, Matrix.one_apply_eq]
    · rw [Matrix.zero_mulVec, dotProduct_zero, Matrix.one_apply_ne h]
  · intro g
    exact intertw hp hM (hρ g) w0
  · intro Z hZ
    have hZE : ∀ j, Z * E j (bb E j) = 0 := by
      intro j
      rw [Matrix.ext_iff_mulVec]
      intro w
      have h1 := hZ (T E w) (fun g => intertw hp hM (hρ g) w)
      ext x
      have h2 := congrFun (congrFun h1 x) j
      rw [mul_T] at h2
      simpa using h2
    have hZp : ∀ j, Z * p j = 0 := by
      intro j
      have h3 : E j (bb E j) * E (bb E j) j = p j := by
        rw [(hM.2.2.2.2.1 j (bb E j) j (bb_ne hp hM j) (bb_spec hp hM j).2).1, hM.2.1 j]
      rw [← h3, ← mul_assoc, hZE j, zero_mul]
    calc Z = Z * ∑ j, p j := by rw [hp.1.complete, mul_one]
      _ = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun j _ => hZp j

end LateralTheory.DivDb.RepPf
