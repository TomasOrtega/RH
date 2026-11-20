import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiagMemCongruencePairs

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob.Iota

variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

def formL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (w : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun v := form σ J v w
  map_add' a b := by simp [form, Matrix.mulVec_add]
  map_smul' a b := by simp [form, Matrix.mulVec_smul]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
/- English proof (translation)
Establish `h` using `FractionalIdeal.inv_anti_mono (K := E) (I := (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) (J := 1) (by simp [differentIdeal_ne_bot]) one_ne_zero FractionalIdeal.coeIdeal_le_one`. Simplify using `using h`.
-/
private theorem one_le_inv_differentIdeal :
    (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
  have h := FractionalIdeal.inv_anti_mono (K := E)
    (I := (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) (J := 1)
    (by simp [differentIdeal_ne_bot]) one_ne_zero FractionalIdeal.coeIdeal_le_one
  simpa using h

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in

/- English proof (translation)
Unfold `_root_.GlobalTheory.SgGlob.dInv`. Establish `hpow : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ ^ j`. Simplify using `using pow_le_pow_left' (one_le_inv_differentIdeal (E := E)) j`. Conclude with `hpow (FractionalIdeal.one_mem_one _)`.
-/
theorem _root_.GlobalTheory.SgGlob.Iota.one_mem_dInv (j : ℕ) : (1 : E) ∈ _root_.GlobalTheory.SgGlob.dInv E j := by
  unfold _root_.GlobalTheory.SgGlob.dInv
  have hpow : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ ^ j := by
    simpa using pow_le_pow_left' (one_le_inv_differentIdeal (E := E)) j
  exact hpow (FractionalIdeal.one_mem_one _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, a, ha, rfl⟩` from `hx`.

Use `⟨Pi.single b a, fun b' => ?_, by ext i; simp [mul_comm]⟩` and prove the remaining obligations. Distinguish the cases in `h : b' = b`. Substitute `h` using the available equality. Simplify using `using ha`. Rewrite using `[Pi.single_eq_of_ne h]`.

Conclude with `FractionalIdeal.zero_mem _`. Consider the case `zero => exact ⟨0, fun b => FractionalIdeal.zero_mem _, Matrix.mulVec_zero _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`.

Conclude with `⟨a + b, fun i => Submodule.add_mem (dInv E (r - (i : ℕ))).coeToSubmodule (ha i) (hb i), Matrix.mulVec_add _ _ _⟩`. Consider the case `smul t x _ hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `⟨t • a, fun i => Submodule.smul_mem (dInv E (r - (i : ℕ))).coeToSubmodule t (ha i), Matrix.mulVec_smul _ _ _⟩`. Introduce and unpack `⟨a, ha, rfl⟩`.

Establish `: P *ᵥ a = ∑ b, a b • fun i => P i b`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨b, a b, ha b, rfl⟩`.
-/
theorem mem_frameLat (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ frameLat P ↔ ∃ a : Fin (r + 1) → E, (∀ b : Fin (r + 1), a b ∈ dInv E (r - (b : ℕ))) ∧ P *ᵥ a = v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, a, ha, rfl⟩ := hx
      refine ⟨Pi.single b a, fun b' => ?_, by ext i; simp [mul_comm]⟩
      by_cases h : b' = b
      · subst h
        simpa using ha
      · rw [Pi.single_eq_of_ne h]
        exact FractionalIdeal.zero_mem _
    | zero => exact ⟨0, fun b => FractionalIdeal.zero_mem _, Matrix.mulVec_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, fun i => Submodule.add_mem (dInv E (r - (i : ℕ))).coeToSubmodule (ha i) (hb i),
        Matrix.mulVec_add _ _ _⟩
    | smul t x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨t • a, fun i => Submodule.smul_mem (dInv E (r - (i : ℕ))).coeToSubmodule t (ha i),
        Matrix.mulVec_smul _ _ _⟩
  · rintro ⟨a, ha, rfl⟩
    have : P *ᵥ a = ∑ b, a b • fun i => P i b := by
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨b, a b, ha b, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Use `(Submodule.span_le (p := LinearMap.range P.mulVecLin)).2 (fun w hw => ?_) hv` and prove the remaining obligations. Take `⟨a, -, rfl⟩` from `(mem_frameLat P w).1 hw`. Conclude with `⟨a, rfl⟩`.

Introduce and unpack `⟨a, rfl⟩`. Establish `: P *ᵥ a = ∑ b, a b • fun i => P i b`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨b, 1, one_mem_dInv _, (one_smul _ _).symm⟩))`.
-/
theorem mem_span_frameLat (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ Submodule.span E (frameLat P : Set (Fin n → E)) ↔ ∃ a, P *ᵥ a = v := by
  constructor
  · intro hv
    refine (Submodule.span_le (p := LinearMap.range P.mulVecLin)).2 (fun w hw => ?_) hv
    obtain ⟨a, -, rfl⟩ := (mem_frameLat P w).1 hw
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    have : P *ᵥ a = ∑ b, a b • fun i => P i b := by
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span
      (Submodule.subset_span ⟨b, 1, one_mem_dInv _, (one_smul _ _).symm⟩))

section Pair

variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}

omit [NumberField E] in

/- English proof (translation)
Rewrite using `[Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hg, one_smul, Matrix.sub_mulVec, add_sub_cancel]`.
-/
theorem mulVec_eq_add (hg : (g : E) ≠ 0) (P P' : Matrix (Fin n) (Fin (r + 1)) E) (a : Fin (r + 1) → E) :
    P' *ᵥ a = P *ᵥ a + (g : E) • (((g : E)⁻¹ • (P' - P)) *ᵥ a) := by
  rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hg, one_smul, Matrix.sub_mulVec, add_sub_cancel]

/- English proof (translation)
Establish `hs : P *ᵥ a + P' *ᵥ a' ∈ Submodule.span E (pairLat g P P' : Set (Fin n → E))`. Establish `h1 (c) : P *ᵥ c ∈ Submodule.span E (pairLat g P P' : Set (Fin n → E))` using `Submodule.span_mono (fun _ hx => Submodule.mem_sup_left hx) ((mem_span_frameLat P _).2 ⟨c, rfl⟩)`. Rewrite using `[mulVec_eq_add hg P P']`. Conclude with `add_mem (h1 _) (add_mem (h1 _) (Submodule.smul_mem _ _ (Submodule.span_mono (fun _ hx => Submodule.mem_sup_right hx) ((mem_span_frameLat _ _).2 ⟨a', rfl⟩))))`. Take `⟨x, hx, y, hy, e⟩` from `Submodule.mem_sup.1 (hΛ.2 _ h hs)`.

Take `⟨s, hs, rfl⟩` from `(mem_frameLat _ _).1 hx`. Take `⟨t, -, rfl⟩` from `(mem_frameLat _ _).1 hy`. Take `⟨e1, e2⟩` from `hind (s - (g : E)⁻¹ • t - a) ((g : E)⁻¹ • t - a') (by`. Rewrite `e` using `[Matrix.smul_mulVec, Matrix.sub_mulVec]`. Simplify using `only [Matrix.mulVec_sub, Matrix.mulVec_smul]`.

Rewrite using `[← sub_eq_zero.2 e, smul_sub]`. Use the proof step `abel)`. Establish `e3 : a b + a' b = s b`. Establish `f1` using `congrFun e1 b`. Establish `f2` using `congrFun e2 b`.

Simplify using `only [Pi.sub_apply, Pi.zero_apply] at f1 f2`. Take the linear combination `-f1 - f2`. Conclude with `e3 ▸ hs b`.
-/
theorem coeff_mem (hg : (g : E) ≠ 0) (hΛ : PrimIn (pairLat g P P') Λ)
    (hind : ∀ a a', P *ᵥ a + P' *ᵥ a' = 0 → a = 0 ∧ a' = 0) {a a' : Fin (r + 1) → E}
    (h : P *ᵥ a + P' *ᵥ a' ∈ Λ) (b : Fin (r + 1)) : a b + a' b ∈ dInv E (r - (b : ℕ)) := by
  have hs : P *ᵥ a + P' *ᵥ a' ∈ Submodule.span E (pairLat g P P' : Set (Fin n → E)) := by
    have h1 (c) : P *ᵥ c ∈ Submodule.span E (pairLat g P P' : Set (Fin n → E)) :=
      Submodule.span_mono (fun _ hx => Submodule.mem_sup_left hx) ((mem_span_frameLat P _).2 ⟨c, rfl⟩)
    rw [mulVec_eq_add hg P P']
    exact add_mem (h1 _) (add_mem (h1 _) (Submodule.smul_mem _ _
      (Submodule.span_mono (fun _ hx => Submodule.mem_sup_right hx)
        ((mem_span_frameLat _ _).2 ⟨a', rfl⟩))))
  obtain ⟨x, hx, y, hy, e⟩ := Submodule.mem_sup.1 (hΛ.2 _ h hs)
  obtain ⟨s, hs, rfl⟩ := (mem_frameLat _ _).1 hx
  obtain ⟨t, -, rfl⟩ := (mem_frameLat _ _).1 hy
  obtain ⟨e1, e2⟩ := hind (s - (g : E)⁻¹ • t - a) ((g : E)⁻¹ • t - a') (by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec] at e
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [← sub_eq_zero.2 e, smul_sub]
    abel)
  have e3 : a b + a' b = s b := by
    have f1 := congrFun e1 b
    have f2 := congrFun e2 b
    simp only [Pi.sub_apply, Pi.zero_apply] at f1 f2
    linear_combination -f1 - f2
  exact e3 ▸ hs b

/- English proof (translation)
Establish `h1 : P *ᵥ a ∈ Λ` using `hΛ (Submodule.mem_sup_left ((mem_frameLat _ _).2 ⟨a, ha, rfl⟩))`. Establish `h2 : P' *ᵥ a - P *ᵥ a ∈ mulLat g Λ` using `(mem_mulLat g Λ _).2 ⟨_, hΛ (Submodule.mem_sup_right ((mem_frameLat _ _).2 ⟨a, ha, rfl⟩)), by`. Rewrite using `[mulVec_eq_add hg P P' a, add_sub_cancel_left]⟩`. Use `⟨h1, ?_, h2⟩` and prove the remaining obligations. Rewrite using `[← add_sub_cancel (P *ᵥ a) (P' *ᵥ a)]`.

Conclude with `add_mem h1 (mulLat_le g Λ h2)`.
-/
theorem mulVec_mem (hg : (g : E) ≠ 0) (hΛ : pairLat g P P' ≤ Λ) {a : Fin (r + 1) → E}
    (ha : ∀ b : Fin (r + 1), a b ∈ dInv E (r - (b : ℕ))) :
    P *ᵥ a ∈ Λ ∧ P' *ᵥ a ∈ Λ ∧ P' *ᵥ a - P *ᵥ a ∈ mulLat g Λ := by
  have h1 : P *ᵥ a ∈ Λ := hΛ (Submodule.mem_sup_left ((mem_frameLat _ _).2 ⟨a, ha, rfl⟩))
  have h2 : P' *ᵥ a - P *ᵥ a ∈ mulLat g Λ :=
    (mem_mulLat g Λ _).2 ⟨_, hΛ (Submodule.mem_sup_right ((mem_frameLat _ _).2 ⟨a, ha, rfl⟩)), by
      rw [mulVec_eq_add hg P P' a, add_sub_cancel_left]⟩
  refine ⟨h1, ?_, h2⟩
  rw [← add_sub_cancel (P *ᵥ a) (P' *ᵥ a)]
  exact add_mem h1 (mulLat_le g Λ h2)

/- English proof (translation)
Use `⟨⟨fun v hv => ?_, fun v hv hs => ?_⟩, fun v hv => ?_, fun v hv hs => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(mem_frameLat _ _).1 hv`. Conclude with `(mulVec_mem hg hΛ.1 ha).1`. Take `⟨a, rfl⟩` from `(mem_span_frameLat _ _).1 hs`. Conclude with `(mem_frameLat _ _).2 ⟨a, fun b => by`.

Simplify `hv) b, rfl⟩` using `using coeff_mem hg hΛ hind (a := a) (a' := 0) (by simpa`. Take `⟨a, ha, rfl⟩` from `(mem_frameLat _ _).1 hv`. Conclude with `(mulVec_mem hg hΛ.1 ha).2.1`. Take `⟨a, rfl⟩` from `(mem_span_frameLat _ _).1 hs`. Conclude with `(mem_frameLat _ _).2 ⟨a, fun b => by`.

Simplify `hv) b, rfl⟩` using `using coeff_mem hg hΛ hind (a := 0) (a' := a) (by simpa`.
-/
theorem primIn_frameLat (hg : (g : E) ≠ 0) (hΛ : PrimIn (pairLat g P P') Λ)
    (hind : ∀ a a', P *ᵥ a + P' *ᵥ a' = 0 → a = 0 ∧ a' = 0) :
    PrimIn (frameLat P) Λ ∧ PrimIn (frameLat P') Λ := by
  refine ⟨⟨fun v hv => ?_, fun v hv hs => ?_⟩, fun v hv => ?_, fun v hv hs => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (mem_frameLat _ _).1 hv
    exact (mulVec_mem hg hΛ.1 ha).1
  · obtain ⟨a, rfl⟩ := (mem_span_frameLat _ _).1 hs
    exact (mem_frameLat _ _).2 ⟨a, fun b => by
      simpa using coeff_mem hg hΛ hind (a := a) (a' := 0) (by simpa using hv) b, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := (mem_frameLat _ _).1 hv
    exact (mulVec_mem hg hΛ.1 ha).2.1
  · obtain ⟨a, rfl⟩ := (mem_span_frameLat _ _).1 hs
    exact (mem_frameLat _ _).2 ⟨a, fun b => by
      simpa using coeff_mem hg hΛ hind (a := 0) (a' := a) (by simpa using hv) b, rfl⟩

omit [NumberField E] in

/- English proof (translation)
Use extensionality with `i`. Simplify using `[eOf, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]`.
-/
theorem eOf_mulVec (P : Matrix (Fin n) (Fin (r + 1)) E) (c : Fin r → E) :
    eOf P *ᵥ c = P *ᵥ (Fin.snoc c 0 : Fin (r + 1) → E) := by
  ext i
  simp [eOf, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

end Pair

section Gram

omit [NumberField E] in

/- English proof (translation)
Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, Even.neg_one_pow ⟨_, rfl⟩, one_mul, Fin.succAbove_last]`. Both sides reduce to the same expression.
-/
theorem adjugate_last (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Z.adjugate (Fin.last r) (Fin.last r) = lead Z r (Nat.le_succ r) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Even.neg_one_pow ⟨_, rfl⟩, one_mul, Fin.succAbove_last]
  rfl

omit [NumberField E] in

/- English proof (translation)
Establish `e` using `congrFun (congrArg (Z.adjugate *ᵥ ·) h) (Fin.last r)`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e`. Establish `e2 : ((Z.adjugate * TF r T) *ᵥ y) (Fin.last r) = -(T * lead Z r (Nat.le_succ r) * y (Fin.last r))`. Simplify using `[TF, Matrix.mulVec, dotProduct, Matrix.mul_diagonal, adjugate_last, mul_comm]`. Take the linear combination `e - e2`.
-/
theorem det_mul_last {T : E} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {x y : Fin (r + 1) → E}
    (h : TF r T *ᵥ y + Z *ᵥ x = 0) :
    Z.det * x (Fin.last r) = T * lead Z r (Nat.le_succ r) * y (Fin.last r) := by
  have e := congrFun (congrArg (Z.adjugate *ᵥ ·) h) (Fin.last r)
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
  have e2 : ((Z.adjugate * TF r T) *ᵥ y) (Fin.last r) =
      -(T * lead Z r (Nat.le_succ r) * y (Fin.last r)) := by
    simp [TF, Matrix.mulVec, dotProduct, Matrix.mul_diagonal, adjugate_last, mul_comm]
  linear_combination e - e2

omit [NumberField E] in

/- English proof (translation)
Take `⟨⟨⟨L, hL⟩, h1⟩, ⟨-, h2⟩, h3⟩` from `h`. Simplify using `only at hL h1 h2 h3`. Establish `h4 : pairM σ J P P' = cT σ Z`. Rewrite using `[← h3, pairM, pairM]`. Use `conv_rhs => rw [cT, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]`.

Establish `: ((cT σ P).map σ)ᵀ = P`. Use extensionality with `i j`. Simplify using `[cT, hσ]`. Rewrite using `[this, Matrix.mul_assoc]`. Conclude with `congrArg (fun M => cT σ P' * (M * P)) hJ.symm`.

Establish `e1 : TF r T *ᵥ a + Z *ᵥ a' = 0`. Rewrite using `[← h1, ← h3, pairM, pairM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec a', ← Matrix.mulVec_add, e, Matrix.mulVec_zero]`. Establish `e2 : TF r T' *ᵥ a' + cT σ Z *ᵥ a = 0`. Rewrite using `[← h2, ← h4, pairM, pairM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec a, ← Matrix.mulVec_add, add_comm (P' *ᵥ a'), e, Matrix.mulVec_zero]`. Establish `d1` using `det_mul_last e1`.

Establish `d2` using `det_mul_last e2`. Establish `c1 : (cT σ Z).det = σ Z.det` using `by rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl`. Establish `c2 : lead (cT σ Z) r (Nat.le_succ r) = σ (lead Z r (Nat.le_succ r))`. Rewrite using `[lead, lead, RingHom.map_det, ← Matrix.det_transpose]`. Both sides reduce to the same expression.

Rewrite `d2` using `[c1, c2]`. Establish `l1 : a (Fin.last r) = 0` using `(mul_eq_zero.1 (by`. Rewrite using `[Gq]`. Take the linear combination `Z.det * d2 + T' * σ (lead Z r (Nat.le_succ r)) * d1)).resolve_left hG`. Establish `l2 : a' (Fin.last r) = 0` using `(mul_eq_zero.1 (by`.

Rewrite using `[Gq]`. Take the linear combination `σ Z.det * d1 + T * lead Z r (Nat.le_succ r) * d2)).resolve_left hG`. Establish `z : Z *ᵥ a' = 0`. Rewrite using `[← e1, right_eq_add]`. Use extensionality with `i`.

Apply the tactic sequence `by_cases hi : i = Fin.last r <;> simp [TF, Matrix.mulVec_diagonal, hi, l1]`. Establish `ha' : a' = 0`. Distinguish the cases in `hd : Z.det = 0`. Establish `hl : lead Z r (Nat.le_succ r) ≠ 0` using `fun h0 => hG (by simp [Gq, hd, h0])`. Use `Matrix.eq_zero_of_mulVec_eq_zero hl (v := fun i => a' i.castSucc) (by` as an intermediate fact.

Use extensionality with `i`. Use `congrFun z i.castSucc` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, l2, mul_zero, add_zero] at this`. Conclude with `this)`. Use extensionality with `i`.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact l2`. Consider the case `cast i => exact congrFun this i`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hd z`. Use `⟨?_, ha'⟩` and prove the remaining obligations.

Rewrite `e` using `[ha', Matrix.mulVec_zero, add_zero]`. Rewrite using `[← Matrix.one_mulVec a, ← hL, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]`.
-/
theorem indep_of_Gq_ne_zero (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {T T' : E}
    {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
    (h : (P, P') ∈ XZ σ J T T' Z) (hG : Gq σ T T' Z ≠ 0) (a a' : Fin (r + 1) → E)
    (e : P *ᵥ a + P' *ᵥ a' = 0) : a = 0 ∧ a' = 0 := by
  obtain ⟨⟨⟨L, hL⟩, h1⟩, ⟨-, h2⟩, h3⟩ := h
  dsimp only at hL h1 h2 h3
  have h4 : pairM σ J P P' = cT σ Z := by
    rw [← h3, pairM, pairM]
    conv_rhs => rw [cT, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    have : ((cT σ P).map σ)ᵀ = P := by
      ext i j
      simp [cT, hσ]
    rw [this, Matrix.mul_assoc]
    exact congrArg (fun M => cT σ P' * (M * P)) hJ.symm
  have e1 : TF r T *ᵥ a + Z *ᵥ a' = 0 := by
    rw [← h1, ← h3, pairM, pairM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec a',
      ← Matrix.mulVec_add, e, Matrix.mulVec_zero]
  have e2 : TF r T' *ᵥ a' + cT σ Z *ᵥ a = 0 := by
    rw [← h2, ← h4, pairM, pairM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec a,
      ← Matrix.mulVec_add, add_comm (P' *ᵥ a'), e, Matrix.mulVec_zero]
  have d1 := det_mul_last e1
  have d2 := det_mul_last e2
  have c1 : (cT σ Z).det = σ Z.det := by rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl
  have c2 : lead (cT σ Z) r (Nat.le_succ r) = σ (lead Z r (Nat.le_succ r)) := by
    rw [lead, lead, RingHom.map_det, ← Matrix.det_transpose]
    rfl
  rw [c1, c2] at d2
  have l1 : a (Fin.last r) = 0 := (mul_eq_zero.1 (by
    rw [Gq]
    linear_combination Z.det * d2 + T' * σ (lead Z r (Nat.le_succ r)) * d1)).resolve_left hG
  have l2 : a' (Fin.last r) = 0 := (mul_eq_zero.1 (by
    rw [Gq]
    linear_combination σ Z.det * d1 + T * lead Z r (Nat.le_succ r) * d2)).resolve_left hG
  have z : Z *ᵥ a' = 0 := by
    rw [← e1, right_eq_add]
    ext i
    by_cases hi : i = Fin.last r <;> simp [TF, Matrix.mulVec_diagonal, hi, l1]
  have ha' : a' = 0 := by
    by_cases hd : Z.det = 0
    · have hl : lead Z r (Nat.le_succ r) ≠ 0 := fun h0 => hG (by simp [Gq, hd, h0])
      have := Matrix.eq_zero_of_mulVec_eq_zero hl (v := fun i => a' i.castSucc) (by
        ext i
        have := congrFun z i.castSucc
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, l2, mul_zero, add_zero] at this
        exact this)
      ext i
      induction i using Fin.lastCases with
      | last => exact l2
      | cast i => exact congrFun this i
    · exact Matrix.eq_zero_of_mulVec_eq_zero hd z
  refine ⟨?_, ha'⟩
  rw [ha', Matrix.mulVec_zero, add_zero] at e
  rw [← Matrix.one_mulVec a, ← hL, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]

end Gram

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [cT], by simp [Matrix.det_fin_two]⟩, by rw [Inhab.gq_zero]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hg), _, Inhab.mem_genConf_zero σ hg⟩`.
-/
example (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    IsHermU σ (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) E) ∧
      Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] ≠ 0 ∧
      (GenConf (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)]).Nonempty :=
  ⟨⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [cT], by simp [Matrix.det_fin_two]⟩,
    by rw [Inhab.gq_zero]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hg), _, Inhab.mem_genConf_zero σ hg⟩

end GlobalTheory.SgGlob.Iota
