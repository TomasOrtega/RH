import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

noncomputable section

open ValuativeRel GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V.Hi Matrix

namespace UpperTheory.V.Z.Desc.V0

section Rank

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun x _ => by ring)` and prove the remaining obligations.
-/
private theorem vv_sq (y w : Fin n → R) : vecMulVec y w * vecMulVec y w = (w ⬝ᵥ y) • vecMulVec y w := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => by ring)

/- English proof (translation)
Rewrite using `[mul_sub, mul_one, add_mul, one_mul, mul_smul_comm, vv_sq, smul_smul, ← add_smul, show c + c * (w ⬝ᵥ y) = c * (1 + w ⬝ᵥ y) by ring, h, one_smul]`. Normalize the expressions using the abelian group laws.
-/
private theorem tv_mul (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) :
    (1 + vecMulVec y w) * (1 - c • vecMulVec y w) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, mul_smul_comm, vv_sq, smul_smul, ← add_smul,
    show c + c * (w ⬝ᵥ y) = c * (1 + w ⬝ᵥ y) by ring, h, one_smul]
  abel

/- English proof (translation)
Rewrite using `[sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, vv_sq, smul_smul]`. Rewrite using `[show (c * (w ⬝ᵥ y)) = c * (1 + w ⬝ᵥ y) - c by ring, h, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
private theorem tv_mul' (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) :
    (1 - c • vecMulVec y w) * (1 + vecMulVec y w) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, vv_sq, smul_smul]
  rw [show (c * (w ⬝ᵥ y)) = c * (1 + w ⬝ᵥ y) - c by ring, h, sub_smul, one_smul]
  abel

private def tv (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) : GL (Fin n) R where
  val := 1 + vecMulVec y w
  inv := 1 - c • vecMulVec y w
  val_inv := tv_mul y w c h
  inv_val := tv_mul' y w c h

/- English proof (translation)
Simplify using `[tv, vecMulVec_apply]`.
-/
private theorem tv_apply (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) (a b : Fin n) :
    (tv y w c h : Matrix (Fin n) (Fin n) R) a b = (1 : Matrix (Fin n) (Fin n) R) a b + y a * w b := by
  simp [tv, vecMulVec_apply]

end Rank

section Loc

variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Simplify using `only [chr]`. Use `congr 2`. Establish `hic : i ≠ c`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_eq_single_of_mem (i, c) (by simp [hc])]`. Rewrite using `[hg, Matrix.one_apply_ne hic, hwc]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨a, b⟩ hab hne`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hab`. Establish `hab' : a ≠ b`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hg, Matrix.one_apply_ne hab']`. Break down `lt_trichotomy a i with h | h | h` into its components or cases. Establish `h1` using `Fin.lt_def.1 h`. Rewrite using `[hw b (by rw [Fin.le_def]; omega)]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `h` using the available equality. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Establish `: b = c`. Use `ext`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this]`. Rewrite using `[hy a h]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem chr_of (ψ : AddChar k Circle) (t : Fin n → k) (g : GL (Fin n) k) (y w : Fin n → k) (i c : Fin n)
    (hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b + y a * w b)
    (hy : ∀ a, i < a → y a = 0) (hw : ∀ b, b ≤ i → w b = 0) (hc : (c : ℕ) = i + 1) (hwc : w c = 1) :
    chr ψ t g = (ψ (t i * y i) : ℂ) := by
  simp only [chr]
  congr 2
  have hic : i ≠ c := by
    intro h
    have := congrArg Fin.val h
    omega
  rw [Finset.sum_eq_single_of_mem (i, c) (by simp [hc])]
  · rw [hg, Matrix.one_apply_ne hic, hwc]
    ring
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    have hab' : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [hg, Matrix.one_apply_ne hab']
    rcases lt_trichotomy a i with h | h | h
    · have h1 := Fin.lt_def.1 h
      rw [hw b (by rw [Fin.le_def]; omega)]
      ring
    · subst h
      exfalso
      apply hne
      have : b = c := by
        ext
        omega
      rw [this]
    · rw [hy a h]
      ring

/- English proof (translation)
Rewrite using `[mem_unipB]`. Use `⟨fun a b hba => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hg, Matrix.one_apply_ne hba.ne']`. Distinguish the cases in `ha : i < a`. Rewrite using `[hy a ha]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hw b (le_trans hba.le (not_lt.1 ha))]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hg]`. Distinguish the cases in `ha : i < a`.

Simplify using `[hy a ha]`. Simplify using `[hw a (not_lt.1 ha)]`.
-/
private theorem unip_of (g : GL (Fin n) k) (y w : Fin n → k) (i : Fin n)
    (hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b + y a * w b)
    (hy : ∀ a, i < a → y a = 0) (hw : ∀ b, b ≤ i → w b = 0) : g ∈ unipB k (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [hg, Matrix.one_apply_ne hba.ne']
    by_cases ha : i < a
    · rw [hy a ha]
      ring
    · rw [hw b (le_trans hba.le (not_lt.1 ha))]
      ring
  · rw [hg]
    by_cases ha : i < a
    · simp [hy a ha]
    · simp [hw a (not_lt.1 ha)]

/- English proof (translation)
Establish `hq : (p : Matrix (Fin n) (Fin n) k) * ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1` using `Units.mul_inv p`. Introduce `a`. Proceed by induction on `h : n - (a : ℕ) using Nat.strong_induction_on generalizing a with`. Consider the case `_ d ih`. Introduce `ha j hj`.

Establish `e` using `congrFun (congrFun hq a) j`. Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite `e` using `[(hp a ha).2, one_mul]`. Conclude with `e`. Introduce `m _ hma`.

Break down `lt_or_gt_of_ne hma with hlt | hgt` into its components or cases. Rewrite using `[(hp a ha).1 m hlt, zero_mul]`. Establish `hjm : j < m` using `lt_of_le_of_lt hj hgt`. Establish `h1` using `Fin.lt_def.1 hgt`. Establish `h2` using `m.isLt`.

Rewrite using `[ih (n - (m : ℕ)) (by omega) m rfl (lt_trans ha hgt) j hjm.le, Matrix.one_apply_ne (ne_of_gt hjm)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
private theorem inv_rows (p : GL (Fin n) k) (i : Fin n)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1) :
    ∀ a, i < a → ∀ j, j ≤ a →
      ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = (1 : Matrix (Fin n) (Fin n) k) a j := by
  have hq : (p : Matrix (Fin n) (Fin n) k) * ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 :=
    Units.mul_inv p
  intro a
  induction h : n - (a : ℕ) using Nat.strong_induction_on generalizing a with
  | _ d ih =>
    intro ha j hj
    have e := congrFun (congrFun hq a) j
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at e
    · rw [(hp a ha).2, one_mul] at e
      exact e
    · intro m _ hma
      rcases lt_or_gt_of_ne hma with hlt | hgt
      · rw [(hp a ha).1 m hlt, zero_mul]
      · have hjm : j < m := lt_of_le_of_lt hj hgt
        have h1 := Fin.lt_def.1 hgt
        have h2 := m.isLt
        rw [ih (n - (m : ℕ)) (by omega) m rfl (lt_trans ha hgt) j hjm.le, Matrix.one_apply_ne (ne_of_gt hjm)]
        ring
    · simp

/- English proof (translation)
Establish `hrow : ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c ᵥ* (p : Matrix (Fin n) (Fin n) k) = Pi.single c 1`. Use function extensionality and compare the values at `b`. Establish `e` using `congrFun (congrFun (Units.inv_mul p) c) b`. Rewrite `e` using `[Matrix.mul_apply]`. Rewrite using `[Matrix.vecMul, dotProduct, e]`.

Break down `eq_or_ne b c with rfl | hb` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[hb, Matrix.one_apply_ne hb.symm]`. Rewrite using `[Matrix.mul_add, mul_one, Matrix.mul_vecMulVec, Matrix.add_mul, one_mul, Matrix.vecMulVec_mul, hrow]`.
-/
private theorem conj_eq (p : GL (Fin n) k) (x : Fin n → k) (c : Fin n) :
    (p : Matrix (Fin n) (Fin n) k) * (1 + vecMulVec x (Pi.single c 1)) =
      (1 + vecMulVec ((p : Matrix (Fin n) (Fin n) k) *ᵥ x) (((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c)) *
        (p : Matrix (Fin n) (Fin n) k) := by
  have hrow : ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c ᵥ* (p : Matrix (Fin n) (Fin n) k) = Pi.single c 1 := by
    funext b
    have e := congrFun (congrFun (Units.inv_mul p) c) b
    rw [Matrix.mul_apply] at e
    rw [Matrix.vecMul, dotProduct, e]
    rcases eq_or_ne b c with rfl | hb
    · simp
    · simp [hb, Matrix.one_apply_ne hb.symm]
  rw [Matrix.mul_add, mul_one, Matrix.mul_vecMulVec, Matrix.add_mul, one_mul, Matrix.vecMulVec_mul, hrow]

end Loc

section Val

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Assume the negation of the conclusion as `hy`. Establish `hy1 : 1 ≤ valuation k y` using `not_lt.1 hy`. Establish `hy0 : y ≠ 0` using `fun h0 => by`. Rewrite `hy1` using `[h0, map_zero]`. Conclude with `absurd hy1 (not_le.2 zero_lt_one)`.

Take `⟨x, hx, hne⟩` from `hψ.2.2`. Establish `hs : valuation k (x / y) ≤ 1`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ (hx.trans hy1) zero_le'`. Apply `hne` to reduce the goal to its premises.

Use `h ⟨x / y, hs⟩` as an intermediate fact. Establish `hyx : y * ((⟨x / y, hs⟩ : 𝒪[k]) : k) = x` using `by show y * (x / y) = x`. Clear the denominators using the available nonvanishing facts. Rewrite `this` using `[hyx]`. Then use the resulting hypothesis.
-/
private theorem lev_lt (ψ : AddChar k Circle) (hψ : Lev1 ψ) (y : k)
    (h : ∀ s : 𝒪[k], ψ (y * (s : k)) = 1) : valuation k y < 1 := by
  by_contra hy
  have hy1 : 1 ≤ valuation k y := not_lt.1 hy
  have hy0 : y ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hy1
    exact absurd hy1 (not_le.2 zero_lt_one)
  obtain ⟨x, hx, hne⟩ := hψ.2.2
  have hs : valuation k (x / y) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ (hx.trans hy1) zero_le'
  apply hne
  have := h ⟨x / y, hs⟩
  have hyx : y * ((⟨x / y, hs⟩ : 𝒪[k]) : k) = x := by
    show y * (x / y) = x
    field_simp
  rwa [hyx] at this

/- English proof (translation)
Establish `hci : i < c` using `by rw [Fin.lt_def, hc]; omega`. Establish `hjc : j ≠ c` using `fun h => absurd (lt_of_le_of_lt hj hci) (by rw [h]; exact lt_irrefl c)`. Use `set x : Fin n → k := Pi.single j (s : k) with hx`. Use `set e : Fin n → k := Pi.single c 1 with he`. Establish `hdot : e ⬝ᵥ x = 0`.

Simplify using `only [dotProduct, he, hx, Pi.single_apply]`. Use `Finset.sum_eq_zero (fun b _ => ?_)` and prove the remaining obligations. Use `split_ifs with h1 h2`. Conclude with `absurd (h2.symm.trans h1) hjc`. Apply the tactic sequence `all_goals simp`.

Establish `h0 : (1 : k) * (1 + e ⬝ᵥ x) = 1` using `by rw [hdot]; ring`. Establish `hy : ∀ a, i < a → x a = 0` using `fun a ha => by`. Rewrite using `[hx, Pi.single_eq_of_ne]`. Conclude with `fun h => absurd (lt_of_le_of_lt hj ha) (by rw [h]; exact lt_irrefl j)`. Establish `hw : ∀ b, b ≤ i → e b = 0` using `fun b hb => by`.

Rewrite using `[he, Pi.single_eq_of_ne]`. Conclude with `fun h => absurd (lt_of_le_of_lt hb hci) (by rw [h]; exact lt_irrefl c)`. Establish `hu` using `unip_of (tv x e 1 h0) x e i (tv_apply x e 1 h0) hy hw`. Establish `hcu` using `chr_of ψ t (tv x e 1 h0) x e i c (tv_apply x e 1 h0) hy hw hc (by rw [he, Pi.single_eq_same])`. Establish `hK : tv x e 1 h0 ∈ KO k (Fin n)`.

Establish `h00 : (1 : 𝒪[k]) * (1 + (Pi.single c 1 : Fin n → 𝒪[k]) ⬝ᵥ (Pi.single j s)) = 1`. Establish `hz : (Pi.single c 1 : Fin n → 𝒪[k]) ⬝ᵥ (Pi.single j s) = 0`. Simplify using `only [dotProduct, Pi.single_apply]`. Use `Finset.sum_eq_zero (fun b _ => ?_)` and prove the remaining obligations. Use `split_ifs with h1 h2`.

Conclude with `absurd (h2.symm.trans h1) hjc`. Apply the tactic sequence `all_goals simp`. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨tv (Pi.single j s) (Pi.single c 1) 1 h00, ?_⟩` and prove the remaining obligations.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Simplify using `[tv, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.single_apply, he, hx]`. Apply the tactic sequence `split_ifs <;> first | rfl | simp`. Use `set y : Fin n → k := (p : Matrix (Fin n) (Fin n) k) *ᵥ x with hyd`.

Use `set w : Fin n → k := ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c with hwd`. Establish `hyv : ∀ a, y a = (p : Matrix (Fin n) (Fin n) k) a j * (s : k)`. Introduce `a`. Simplify using `[hyd, hx, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]`. Establish `hinv` using `inv_rows p i hp`.

Establish `hy' : ∀ a, i < a → y a = 0` using `fun a ha => by`. Rewrite using `[hyv, (hp a ha).1 j (lt_of_le_of_lt hj ha), zero_mul]`. Establish `hw' : ∀ b, b ≤ i → w b = 0` using `fun b hb => by`. Rewrite using `[hwd, hinv c hci b (le_of_lt (lt_of_le_of_lt hb hci))]`. Conclude with `Matrix.one_apply_ne (fun h => absurd (lt_of_le_of_lt hb hci) (by rw [h]; exact lt_irrefl b))`.

Establish `hwc : w c = 1` using `by rw [hwd, hinv c hci c le_rfl, Matrix.one_apply_eq]`. Establish `hdot' : w ⬝ᵥ y = 0`. Rewrite using `[dotProduct]`. Use `Finset.sum_eq_zero (fun b _ => ?_)` and prove the remaining obligations. Break down `le_or_gt b i with hb | hb` into its components or cases.

Rewrite using `[hw' b hb, zero_mul]`. Rewrite using `[hy' b hb, mul_zero]`. Establish `h1 : (1 : k) * (1 + w ⬝ᵥ y) = 1` using `by rw [hdot']; ring`. Establish `hu'` using `unip_of (tv y w 1 h1) y w i (tv_apply y w 1 h1) hy' hw'`. Establish `hcu'` using `chr_of ψ t (tv y w 1 h1) y w i c (tv_apply y w 1 h1) hy' hw' hc hwc`.

Establish `hconj : p * tv x e 1 h0 = tv y w 1 h1 * p`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `conj_eq p x c`. Establish `eq1 : l (τ (p * tv x e 1 h0) v) = chr ψ t (tv x e 1 h0) * l (τ p v)`. Rewrite using `[map_mul, Module.End.mul_apply, hv _ hu hK, map_smul, map_smul, smul_eq_mul]`.

Establish `eq2 : l (τ (tv y w 1 h1 * p) v) = chr ψ t (tv y w 1 h1) * l (τ p v)`. Rewrite using `[map_mul, Module.End.mul_apply, hl _ hu' (τ p v)]`. Rewrite `eq1` using `[hconj, eq2]`. Establish `eq3` using `mul_right_cancel₀ hW eq1`. Rewrite `eq3` using `[hcu, hcu']`.

Establish `eq4 : ψ (t i * y i) = ψ (t i * x i)` using `Subtype.ext (by exact_mod_cast eq3)`. Rewrite `eq4` using `[hyv]`. Conclude with `eq4`.
-/
private theorem rowStep {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W)
    (ψ : AddChar k Circle) (t : Fin n → k) (l : W →ₗ[ℂ] ℂ)
    (hl : ∀ u ∈ unipB k (Fin n), ∀ v, l (τ u v) = chr ψ t u * l v) (v : W)
    (hv : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v)
    (p : GL (Fin n) k) (i c : Fin n) (hc : (c : ℕ) = i + 1)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1)
    (hW : l (τ p v) ≠ 0) (j : Fin n) (hj : j ≤ i) (s : 𝒪[k]) :
    ψ (t i * ((p : Matrix (Fin n) (Fin n) k) i j * (s : k))) = ψ (t i * (Pi.single j (s : k) : Fin n → k) i) := by
  have hci : i < c := by rw [Fin.lt_def, hc]; omega
  have hjc : j ≠ c := fun h => absurd (lt_of_le_of_lt hj hci) (by rw [h]; exact lt_irrefl c)
  set x : Fin n → k := Pi.single j (s : k) with hx
  set e : Fin n → k := Pi.single c 1 with he
  have hdot : e ⬝ᵥ x = 0 := by
    simp only [dotProduct, he, hx, Pi.single_apply]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    split_ifs with h1 h2
    · exact absurd (h2.symm.trans h1) hjc
    all_goals simp
  have h0 : (1 : k) * (1 + e ⬝ᵥ x) = 1 := by rw [hdot]; ring
  have hy : ∀ a, i < a → x a = 0 := fun a ha => by
    rw [hx, Pi.single_eq_of_ne]
    exact fun h => absurd (lt_of_le_of_lt hj ha) (by rw [h]; exact lt_irrefl j)
  have hw : ∀ b, b ≤ i → e b = 0 := fun b hb => by
    rw [he, Pi.single_eq_of_ne]
    exact fun h => absurd (lt_of_le_of_lt hb hci) (by rw [h]; exact lt_irrefl c)
  have hu := unip_of (tv x e 1 h0) x e i (tv_apply x e 1 h0) hy hw
  have hcu := chr_of ψ t (tv x e 1 h0) x e i c (tv_apply x e 1 h0) hy hw hc (by rw [he, Pi.single_eq_same])
  have hK : tv x e 1 h0 ∈ KO k (Fin n) := by
    have h00 : (1 : 𝒪[k]) * (1 + (Pi.single c 1 : Fin n → 𝒪[k]) ⬝ᵥ (Pi.single j s)) = 1 := by
      have hz : (Pi.single c 1 : Fin n → 𝒪[k]) ⬝ᵥ (Pi.single j s) = 0 := by
        simp only [dotProduct, Pi.single_apply]
        refine Finset.sum_eq_zero (fun b _ => ?_)
        split_ifs with h1 h2
        · exact absurd (h2.symm.trans h1) hjc
        all_goals simp
      rw [hz]; ring
    refine ⟨tv (Pi.single j s) (Pi.single c 1) 1 h00, ?_⟩
    apply Units.ext
    ext a b
    simp [tv, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.single_apply, he, hx]
    split_ifs <;> first | rfl | simp
  set y : Fin n → k := (p : Matrix (Fin n) (Fin n) k) *ᵥ x with hyd
  set w : Fin n → k := ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c with hwd
  have hyv : ∀ a, y a = (p : Matrix (Fin n) (Fin n) k) a j * (s : k) := by
    intro a
    simp [hyd, hx, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  have hinv := inv_rows p i hp
  have hy' : ∀ a, i < a → y a = 0 := fun a ha => by
    rw [hyv, (hp a ha).1 j (lt_of_le_of_lt hj ha), zero_mul]
  have hw' : ∀ b, b ≤ i → w b = 0 := fun b hb => by
    rw [hwd, hinv c hci b (le_of_lt (lt_of_le_of_lt hb hci))]
    exact Matrix.one_apply_ne (fun h => absurd (lt_of_le_of_lt hb hci) (by rw [h]; exact lt_irrefl b))
  have hwc : w c = 1 := by rw [hwd, hinv c hci c le_rfl, Matrix.one_apply_eq]
  have hdot' : w ⬝ᵥ y = 0 := by
    rw [dotProduct]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rcases le_or_gt b i with hb | hb
    · rw [hw' b hb, zero_mul]
    · rw [hy' b hb, mul_zero]
  have h1 : (1 : k) * (1 + w ⬝ᵥ y) = 1 := by rw [hdot']; ring
  have hu' := unip_of (tv y w 1 h1) y w i (tv_apply y w 1 h1) hy' hw'
  have hcu' := chr_of ψ t (tv y w 1 h1) y w i c (tv_apply y w 1 h1) hy' hw' hc hwc
  have hconj : p * tv x e 1 h0 = tv y w 1 h1 * p := by
    apply Units.ext
    exact conj_eq p x c
  have eq1 : l (τ (p * tv x e 1 h0) v) = chr ψ t (tv x e 1 h0) * l (τ p v) := by
    rw [map_mul, Module.End.mul_apply, hv _ hu hK, map_smul, map_smul, smul_eq_mul]
  have eq2 : l (τ (tv y w 1 h1 * p) v) = chr ψ t (tv y w 1 h1) * l (τ p v) := by
    rw [map_mul, Module.End.mul_apply, hl _ hu' (τ p v)]
  rw [hconj, eq2] at eq1
  have eq3 := mul_right_cancel₀ hW eq1
  rw [hcu, hcu'] at eq3
  have eq4 : ψ (t i * y i) = ψ (t i * x i) := Subtype.ext (by exact_mod_cast eq3)
  rw [hyv] at eq4
  exact eq4

set_option synthInstance.maxHeartbeats 200000 in
/- English proof (translation)
Use `set P := (p : Matrix (Fin n) (Fin n) k) with hP`. Set `d : Fin n → k` to `fun j => if j ≤ i then P i j - (1 : Matrix (Fin n) (Fin n) k) i j else 0`. Establish `hdv : ∀ j, valuation k (d j) < 1`. Introduce `j`. Distinguish the cases in `hj : j ≤ i`.

Simplify using `only [d, if_pos hj]`. Conclude with `hd j hj`. Simplify using `only [d, if_neg hj, map_zero]`. Conclude with `zero_lt_one`. Establish `hint : ∀ j, d j ∈ 𝒪[k]` using `fun j => (Valuation.mem_integer_iff _ _).2 (hdv j).le`.

Establish `hI` using `Valuation.integer.integers (valuation k)`. Establish `hmax : ∀ x : 𝒪[k], valuation k (x : k) < 1 → x ∈ 𝓂[k]`. Introduce `x hx`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]`. Conclude with `hx.ne`.

Set `d₀ : Fin n → 𝒪[k]` to `fun j => ⟨d j, hint j⟩`. Set `y₀ : Fin n → 𝒪[k]` to `Pi.single i 1`. Establish `hdot : d₀ ⬝ᵥ y₀ = d₀ i` using `by simp [y₀]`. Establish `hu : IsUnit (1 + d₀ ⬝ᵥ y₀)`. Rewrite using `[hdot, hI.isUnit_iff_valuation_eq_one, map_add, map_one]`.

Conclude with `Valuation.map_one_add_of_lt _ (hdv i)`. Take `⟨u, hu'⟩` from `hu`. Establish `hc : ((u⁻¹ : (𝒪[k])ˣ) : 𝒪[k]) * (1 + d₀ ⬝ᵥ y₀) = 1` using `by rw [← hu']; exact u.inv_mul`. Set `M₀ : GL (Fin n) 𝒪[k]` to `tv y₀ d₀ _ hc`. Set `M : GL (Fin n) k` to `GeneralLinearGroup.map (algebraMap 𝒪[k] k) M₀`.

Establish `hM : ∀ a b, (M : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b + (Pi.single i (1 : k) : Fin n → k) a * d b`. Introduce `a b`. Simplify using `only [M, GeneralLinearGroup.map_apply, M₀, tv_apply, map_add, map_mul]`. Use `congr 1`. Simplify using `[Matrix.one_apply]`.

Use `congr 1`. Simplify using `[y₀, Pi.single_apply]`. Use `⟨M⁻¹, ?_, ?_⟩` and prove the remaining obligations. Apply `Subgroup.inv_mem` to reduce the goal to its premises. Use `⟨M₀, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Apply `GeneralLinearGroup.ext` to reduce the goal to its premises. Introduce `a b`. Rewrite using `[GeneralLinearGroup.map_apply, tv_apply, map_add]`. Establish `hz : Ideal.Quotient.mk (𝓂[k] ^ 1) (y₀ a * d₀ b) = 0`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, pow_one]`. Conclude with `Ideal.mul_mem_left _ _ (hmax _ (hdv b))`. Rewrite using `[hz, add_zero]`. Simplify using `[Matrix.one_apply]`. Use `set Q := ((p * M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hQ`.

Establish `hq : ∀ a j, Q a j + Q a i * d j = P a j`. Introduce `a j`. Establish `h1 : ((p * M⁻¹ * M : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = P a j`. Rewrite using `[inv_mul_cancel_right]`. Rewrite `h1` using `[Units.val_mul, Matrix.mul_apply]`.

Rewrite `h1` using `[hM]`. Rewrite using `[← h1]`. Simplify using `[mul_add, Finset.sum_add_distrib, Matrix.one_apply, Pi.single_apply, Q]`. Establish `hdi : 1 + d i = P i i` using `by simp [d]`. Establish `hPii : P i i ≠ 0`.

Introduce `h0`. Use `hd i le_rfl` as an intermediate fact. Rewrite `this` using `[h0, zero_sub, Valuation.map_neg, Matrix.one_apply_eq, map_one]`. Conclude with `lt_irrefl _ this`. Establish `hQi : ∀ a, Q a i * P i i = P a i`.

Introduce `a`. Rewrite using `[← hdi, ← hq a i]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a ha`. Break down `ha.eq_or_lt with rfl | hlt` into its components or cases.

Establish `hii : Q i i = 1`. Use `hQi i` as an intermediate fact. Conclude with `(mul_eq_right₀ hPii).1 this`. Use `⟨fun j hj => ?_, hii⟩` and prove the remaining obligations. Establish `h2` using `hq i j`.

Rewrite `h2` using `[hii, one_mul]`. Establish `hdj : d j = P i j - (1 : Matrix (Fin n) (Fin n) k) i j` using `by simp [d, hj.le]`. Rewrite `h2` using `[hdj, Matrix.one_apply_ne hj.ne']`. Take the linear combination `h2`. Take `⟨hz, h1⟩` from `hp a hlt`.

Establish `hai : Q a i = 0`. Use `hQi a` as an intermediate fact. Rewrite `this` using `[hz i hlt]`. Conclude with `(mul_eq_zero.1 this).resolve_right hPii`. Establish `hrow : ∀ j, Q a j = P a j`.

Introduce `j`. Use `hq a j` as an intermediate fact. Rewrite `this` using `[hai, zero_mul, add_zero]`. Conclude with `this`. Conclude with `⟨fun j hj => by rw [hrow]; exact hz j hj, by rw [hrow]; exact h1⟩`.
-/
private theorem exists_mem_Kc_rows_unitriangular (p : GL (Fin n) k) (i : Fin n)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1)
    (hd : ∀ j, j ≤ i → valuation k ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1) :
    ∃ κ ∈ Kc k n 1, ∀ a, i ≤ a → (∀ j, j < a → ((p * κ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = 0) ∧
      ((p * κ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a a = 1 := by
  classical
  set P := (p : Matrix (Fin n) (Fin n) k) with hP
  let d : Fin n → k := fun j => if j ≤ i then P i j - (1 : Matrix (Fin n) (Fin n) k) i j else 0
  have hdv : ∀ j, valuation k (d j) < 1 := by
    intro j
    by_cases hj : j ≤ i
    · simp only [d, if_pos hj]
      exact hd j hj
    · simp only [d, if_neg hj, map_zero]
      exact zero_lt_one
  have hint : ∀ j, d j ∈ 𝒪[k] := fun j => (Valuation.mem_integer_iff _ _).2 (hdv j).le
  have hI := Valuation.integer.integers (valuation k)
  have hmax : ∀ x : 𝒪[k], valuation k (x : k) < 1 → x ∈ 𝓂[k] := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact hx.ne
  let d₀ : Fin n → 𝒪[k] := fun j => ⟨d j, hint j⟩
  let y₀ : Fin n → 𝒪[k] := Pi.single i 1
  have hdot : d₀ ⬝ᵥ y₀ = d₀ i := by simp [y₀]
  have hu : IsUnit (1 + d₀ ⬝ᵥ y₀) := by
    rw [hdot, hI.isUnit_iff_valuation_eq_one, map_add, map_one]
    exact Valuation.map_one_add_of_lt _ (hdv i)
  obtain ⟨u, hu'⟩ := hu
  have hc : ((u⁻¹ : (𝒪[k])ˣ) : 𝒪[k]) * (1 + d₀ ⬝ᵥ y₀) = 1 := by rw [← hu']; exact u.inv_mul
  let M₀ : GL (Fin n) 𝒪[k] := tv y₀ d₀ _ hc
  let M : GL (Fin n) k := GeneralLinearGroup.map (algebraMap 𝒪[k] k) M₀
  have hM : ∀ a b, (M : Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b + (Pi.single i (1 : k) : Fin n → k) a * d b := by
    intro a b
    simp only [M, GeneralLinearGroup.map_apply, M₀, tv_apply, map_add, map_mul]
    congr 1
    · simp [Matrix.one_apply]
    · congr 1
      simp [y₀, Pi.single_apply]
  refine ⟨M⁻¹, ?_, ?_⟩
  · apply Subgroup.inv_mem
    refine ⟨M₀, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply GeneralLinearGroup.ext
    intro a b
    rw [GeneralLinearGroup.map_apply, tv_apply, map_add]
    have hz : Ideal.Quotient.mk (𝓂[k] ^ 1) (y₀ a * d₀ b) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact Ideal.mul_mem_left _ _ (hmax _ (hdv b))
    rw [hz, add_zero]
    simp [Matrix.one_apply]
  · set Q := ((p * M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hQ
    have hq : ∀ a j, Q a j + Q a i * d j = P a j := by
      intro a j
      have h1 : ((p * M⁻¹ * M : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = P a j := by
        rw [inv_mul_cancel_right]
      rw [Units.val_mul, Matrix.mul_apply] at h1
      simp_rw [hM] at h1
      rw [← h1]
      simp [mul_add, Finset.sum_add_distrib, Matrix.one_apply, Pi.single_apply, Q]
    have hdi : 1 + d i = P i i := by simp [d]
    have hPii : P i i ≠ 0 := by
      intro h0
      have := hd i le_rfl
      rw [h0, zero_sub, Valuation.map_neg, Matrix.one_apply_eq, map_one] at this
      exact lt_irrefl _ this
    have hQi : ∀ a, Q a i * P i i = P a i := by
      intro a
      rw [← hdi, ← hq a i]
      ring
    intro a ha
    rcases ha.eq_or_lt with rfl | hlt
    · have hii : Q i i = 1 := by
        have := hQi i
        exact (mul_eq_right₀ hPii).1 this
      refine ⟨fun j hj => ?_, hii⟩
      have h2 := hq i j
      rw [hii, one_mul] at h2
      have hdj : d j = P i j - (1 : Matrix (Fin n) (Fin n) k) i j := by simp [d, hj.le]
      rw [hdj, Matrix.one_apply_ne hj.ne'] at h2
      linear_combination h2
    · obtain ⟨hz, h1⟩ := hp a hlt
      have hai : Q a i = 0 := by
        have := hQi a
        rw [hz i hlt] at this
        exact (mul_eq_zero.1 this).resolve_right hPii
      have hrow : ∀ j, Q a j = P a j := by
        intro j
        have := hq a j
        rw [hai, zero_mul, add_zero] at this
        exact this
      exact ⟨fun j hj => by rw [hrow]; exact hz j hj, by rw [hrow]; exact h1⟩

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Introduce `_ p hp`. Establish `hu : p ∈ unipB k (Fin n)` using `(mem_unipB k).2 ⟨fun a j h => (hp a (Nat.zero_le _)).1 j h, fun a => (hp a (Nat.zero_le _)).2⟩`. Rewrite using `[hl p hu v, hlv, mul_zero]`.

Consider the case `succ r ih`. Introduce `hr p hp`. Assume the negation of the conclusion as `hW`. Establish `hrn : r < n` using `by omega`. Establish `hcn : r + 1 < n` using `by omega`.

Set `i : Fin n` to `⟨r, hrn⟩`. Set `c : Fin n` to `⟨r + 1, hcn⟩`. Establish `hpi : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1` using `fun a ha => hp a (Fin.lt_def.1 ha)`. Establish `hd : ∀ j, j ≤ i → valuation k ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1`. Introduce `j hj`.

Establish `hs` using `rowStep τ ψ t l hl v hv p i c rfl hpi hW j hj`. Establish `h2 : ∀ s : 𝒪[k], ψ ((t i * ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)) * (s : k)) = 1`. Introduce `s`. Establish `e : t i * ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) * (s : k) = t i * ((p : Matrix (Fin n) (Fin n) k) i j * (s : k)) - t i * (Pi.single j (s : k) : Fin n → k) i`. Rewrite using `[Pi.single_apply]`.

Break down `eq_or_ne i j with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `only [Matrix.one_apply_eq, if_true]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h, Matrix.one_apply_ne h, if_false]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, AddChar.map_sub_eq_div, hs s, div_self']`. Establish `h3` using `lev_lt ψ hψ _ h2`. Rewrite `h3` using `[map_mul, ht i, one_mul]`. Conclude with `h3`.

Take `⟨κ, hκ, hpk⟩` from `exists_mem_Kc_rows_unitriangular p i hpi hd`. Apply `hW` to reduce the goal to its premises. Establish `e : τ (p * κ) v = τ p v`. Rewrite using `[map_mul, Module.End.mul_apply, hfix κ hκ]`. Rewrite using `[← e]`.

Conclude with `ih (by omega) (p * κ) (fun a ha => hpk a (Fin.le_def.2 ha))`.
-/
private theorem descent {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W)
    (ψ : AddChar k Circle) (t : Fin n → k) (l : W →ₗ[ℂ] ℂ) (hψ : Lev1 ψ) (ht : ∀ i, valuation k (t i) = 1)
    (hl : ∀ u ∈ unipB k (Fin n), ∀ v, l (τ u v) = chr ψ t u * l v) (v : W) (hlv : l v = 0)
    (hfix : ∀ κ ∈ Kc k n 1, τ κ v = v)
    (hv : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v) (r : ℕ) :
    r ≤ n - 1 → ∀ p : GL (Fin n) k,
      (∀ a : Fin n, r ≤ (a : ℕ) → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧
        (p : Matrix (Fin n) (Fin n) k) a a = 1) → l (τ p v) = 0 := by
  induction r with
  | zero =>
    intro _ p hp
    have hu : p ∈ unipB k (Fin n) :=
      (mem_unipB k).2 ⟨fun a j h => (hp a (Nat.zero_le _)).1 j h, fun a => (hp a (Nat.zero_le _)).2⟩
    rw [hl p hu v, hlv, mul_zero]
  | succ r ih =>
    intro hr p hp
    by_contra hW
    have hrn : r < n := by omega
    have hcn : r + 1 < n := by omega
    let i : Fin n := ⟨r, hrn⟩
    let c : Fin n := ⟨r + 1, hcn⟩
    have hpi : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧
        (p : Matrix (Fin n) (Fin n) k) a a = 1 := fun a ha => hp a (Fin.lt_def.1 ha)
    have hd : ∀ j, j ≤ i → valuation k ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := by
      intro j hj
      have hs := rowStep τ ψ t l hl v hv p i c rfl hpi hW j hj
      have h2 : ∀ s : 𝒪[k], ψ ((t i * ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)) * (s : k)) = 1 := by
        intro s
        have e : t i * ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) * (s : k) =
            t i * ((p : Matrix (Fin n) (Fin n) k) i j * (s : k)) - t i * (Pi.single j (s : k) : Fin n → k) i := by
          rw [Pi.single_apply]
          rcases eq_or_ne i j with h | h
          · subst h
            simp only [Matrix.one_apply_eq, if_true]
            ring
          · simp only [h, Matrix.one_apply_ne h, if_false]
            ring
        rw [e, AddChar.map_sub_eq_div, hs s, div_self']
      have h3 := lev_lt ψ hψ _ h2
      rw [map_mul, ht i, one_mul] at h3
      exact h3
    obtain ⟨κ, hκ, hpk⟩ := exists_mem_Kc_rows_unitriangular p i hpi hd
    apply hW
    have e : τ (p * κ) v = τ p v := by
      rw [map_mul, Module.End.mul_apply, hfix κ hκ]
    rw [← e]
    exact ih (by omega) (p * κ) (fun a ha => hpk a (Fin.le_def.2 ha))

end Val

/- English proof (translation)
Introduce `k _ _ _ _ n W _ _ τ ψ t l hψ ht hK v hv hlv`. Take `⟨hl, hsep⟩` from `hK`. Establish `hfix : ∀ κ ∈ Kc k n 1, τ κ v = v` using `(Submodule.mem_inf.1 hv).1`. Establish `heig : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v`. Introduce `u h1 h2`.

Establish `h3` using `(Submodule.mem_iInf _).1 (Submodule.mem_iInf _ |>.1 (Submodule.mem_inf.1 hv).2 u) ⟨h1, h2⟩`. Conclude with `Module.End.mem_eigenspace_iff.1 h3`. Use `hsep v fun p hp => descent τ ψ t l hψ ht hl v hlv hfix heig (n - 1) le_rfl p fun a ha => ?_` and prove the remaining obligations. Establish `hn : (a : ℕ) + 1 = n`. Use `a.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `⟨fun j hj => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hp a j hn, one_apply_ne (ne_of_gt hj)]`. Rewrite using `[hp a a hn, one_apply_eq]`.
-/
theorem isoLe : IsoLe := by
  intro k _ _ _ _ n W _ _ τ ψ t l hψ ht hK v hv hlv
  obtain ⟨hl, hsep⟩ := hK
  have hfix : ∀ κ ∈ Kc k n 1, τ κ v = v := (Submodule.mem_inf.1 hv).1
  have heig : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v := by
    intro u h1 h2
    have h3 := (Submodule.mem_iInf _).1 (Submodule.mem_iInf _ |>.1 (Submodule.mem_inf.1 hv).2 u) ⟨h1, h2⟩
    exact Module.End.mem_eigenspace_iff.1 h3
  refine hsep v fun p hp => descent τ ψ t l hψ ht hl v hlv hfix heig (n - 1) le_rfl p fun a ha => ?_
  have hn : (a : ℕ) + 1 = n := by
    have := a.2
    omega
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hp a j hn, one_apply_ne (ne_of_gt hj)]
  · rw [hp a a hn, one_apply_eq]

end UpperTheory.V.Z.Desc.V0
