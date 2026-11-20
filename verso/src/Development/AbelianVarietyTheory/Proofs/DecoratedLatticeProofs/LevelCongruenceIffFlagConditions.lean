import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagBasis.Cong

section Gen

variable {A : Type} [CommRing A] {S : Subring A} {n : ℕ} {g : A}

/- English proof (translation)
Establish `: (C *ᵥ fun l => B l j) i = (C * B) i j` using `rfl`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, this, hCB, Matrix.one_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem inv_mulVec_col (B C : Matrix (Fin n) (Fin n) A) (hCB : C * B = 1) (u : A) (j i : Fin n) :
    (C *ᵥ (u • fun l => B l j)) i = if i = j then u else 0 := by
  have : (C *ᵥ fun l => B l j) i = (C * B) i j := rfl
  rw [Matrix.mulVec_smul, Pi.smul_apply, this, hCB, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/- English proof (translation)
Establish `hCX : C * X = m * C`. Combine the equalities or inequalities in the displayed calculation. Establish `hXM : ∀ y ∈ M, X *ᵥ y ∈ M`. Introduce `y hy`. Rewrite `hy`, the goal using `[hM]`.

Use `choose t ht ht' using hy`. Introduce `i`. Use `⟨∑ l, m i l * t l, sum_mem fun l _ => mul_mem (hm i l) (ht l), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, hCX, ← Matrix.mulVec_mulVec, Finset.mul_sum]`. Use `show ∑ l, m i l * (C *ᵥ y) l = _`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[ht' l]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : X *ᵥ (ε • fun l => B l j) = ∑ i, m i j • (ε • fun l => B l i)`. Use extensionality with `l`.

Establish `: (X *ᵥ fun l => B l j) l = (X * B) l j` using `rfl`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, this, hX, Matrix.mul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hd : X *ᵥ (ε • fun l => B l j) - X *ᵥ v ∈ M`. Rewrite using `[← Matrix.mulVec_sub]`. Conclude with `hXM _ hv`. Establish `hred : X *ᵥ v ∈ Submodule.span S T ⊔ M ↔ X *ᵥ (ε • fun l => B l j) ∈ Submodule.span S T ⊔ M`. Establish `hd' : X *ᵥ (ε • fun l => B l j) - X *ᵥ v ∈ Submodule.span S T ⊔ M` using `Submodule.mem_sup_right hd`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using add_mem hd' h`. Introduce `h`. Simplify using `using sub_mem h hd'`.

Rewrite using `[hred]`. Prove the components needed by the constructor for the conclusion. Introduce `h i hi`. Set `Q : Submodule S (Fin n → A)` to `{ carrier := {y | ∃ t ∈ S, (C *ᵥ y) i = g * t} add_mem' := by`. Introduce and unpack `a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩`.

Conclude with `⟨s + t, add_mem hs ht, by rw [Matrix.mulVec_add, Pi.add_apply, ha, hb]; ring⟩`. Use the proof step `zero_mem' := ⟨0, zero_mem _, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨s, hs, ha⟩`. Use `⟨c * s, mul_mem c.2 hs, ?_⟩` and prove the remaining obligations.

Use `show (C *ᵥ ((c : A) • a)) i = _`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, ha, smul_eq_mul]`. Use `ring }`. Establish `hMQ : M ≤ Q` using `fun y hy => (hM y).1 hy i`. Establish `hTQ : Submodule.span S T ≤ Q`.

Use `Submodule.span_le.2 fun s hs => ?_` and prove the remaining obligations. Take `⟨u, i', hi', hu⟩` from `h1 s hs`. Establish `h0 : (u • fun l => B l i') ∈ Q`. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_mulVec_col B C hCB, if_neg, mul_zero]`.

Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Simplify using `using sub_mem h0 (hMQ hu)`. Take `⟨t, ht, h'⟩` from `sup_le hTQ hMQ h`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations.

Rewrite using `[← h', Matrix.mulVec_mulVec, hCX, ← Matrix.mulVec_mulVec]`. Use `show _ = ∑ l, m i l * (C *ᵥ (ε • fun l => B l j)) l`. Simplify using `only [inv_mulVec_col B C hCB, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`.

Rewrite using `[hsum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < N`. Conclude with `Submodule.smul_mem _ (⟨m i j, hm i j⟩ : S) (h2 i hi)`. Take `⟨t, ht, h'⟩` from `h i (not_lt.1 hi)`.

Use `Submodule.mem_sup_right ((hM _).2 fun l => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, inv_mulVec_col B C hCB]`. Use `split_ifs`. Conclude with `⟨t, ht, by rw [← h', mul_comm]⟩`. Conclude with `⟨0, zero_mem _, by simp⟩`.
-/
theorem col_iff (B C m X : Matrix (Fin n) (Fin n) A) (hCB : C * B = 1) (hX : X * B = B * m) (hBC : B * C = 1)
    (hm : ∀ i j, m i j ∈ S) (M : Submodule S (Fin n → A))
    (hM : ∀ y, y ∈ M ↔ ∀ i, ∃ t ∈ S, (C *ᵥ y) i = g * t)
    (T : Set (Fin n → A)) (N : ℕ) (ε : A) (j : Fin n) (v : Fin n → A) (hv : (ε • fun l => B l j) - v ∈ M)
    (h1 : ∀ s ∈ T, ∃ (u : A) (i : Fin n), i.val < N ∧ (u • fun l => B l i) - s ∈ M)
    (h2 : ∀ i : Fin n, i.val < N → (ε • fun l => B l i) ∈ Submodule.span S T ⊔ M) :
    X *ᵥ v ∈ Submodule.span S T ⊔ M ↔ ∀ i : Fin n, N ≤ i.val → ∃ t ∈ S, ε * m i j = g * t := by
  have hCX : C * X = m * C := by
    calc C * X = C * X * (B * C) := by rw [hBC, mul_one]
      _ = C * (X * B) * C := by simp only [mul_assoc]
      _ = m * C := by rw [hX, ← mul_assoc, hCB, one_mul]
  have hXM : ∀ y ∈ M, X *ᵥ y ∈ M := by
    intro y hy
    rw [hM] at hy ⊢
    choose t ht ht' using hy
    intro i
    refine ⟨∑ l, m i l * t l, sum_mem fun l _ => mul_mem (hm i l) (ht l), ?_⟩
    rw [Matrix.mulVec_mulVec, hCX, ← Matrix.mulVec_mulVec, Finset.mul_sum]
    show ∑ l, m i l * (C *ᵥ y) l = _
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ht' l]; ring
  have hsum : X *ᵥ (ε • fun l => B l j) = ∑ i, m i j • (ε • fun l => B l i) := by
    ext l
    have : (X *ᵥ fun l => B l j) l = (X * B) l j := rfl
    rw [Matrix.mulVec_smul, Pi.smul_apply, this, hX, Matrix.mul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hd : X *ᵥ (ε • fun l => B l j) - X *ᵥ v ∈ M := by
    rw [← Matrix.mulVec_sub]; exact hXM _ hv
  have hred : X *ᵥ v ∈ Submodule.span S T ⊔ M ↔ X *ᵥ (ε • fun l => B l j) ∈ Submodule.span S T ⊔ M := by
    have hd' : X *ᵥ (ε • fun l => B l j) - X *ᵥ v ∈ Submodule.span S T ⊔ M := Submodule.mem_sup_right hd
    constructor
    · intro h; simpa using add_mem hd' h
    · intro h; simpa using sub_mem h hd'
  rw [hred]
  constructor
  · intro h i hi
    let Q : Submodule S (Fin n → A) :=
      { carrier := {y | ∃ t ∈ S, (C *ᵥ y) i = g * t}
        add_mem' := by
          rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
          exact ⟨s + t, add_mem hs ht, by rw [Matrix.mulVec_add, Pi.add_apply, ha, hb]; ring⟩
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        smul_mem' := by
          rintro c a ⟨s, hs, ha⟩
          refine ⟨c * s, mul_mem c.2 hs, ?_⟩
          show (C *ᵥ ((c : A) • a)) i = _
          rw [Matrix.mulVec_smul, Pi.smul_apply, ha, smul_eq_mul]; ring }
    have hMQ : M ≤ Q := fun y hy => (hM y).1 hy i
    have hTQ : Submodule.span S T ≤ Q := by
      refine Submodule.span_le.2 fun s hs => ?_
      obtain ⟨u, i', hi', hu⟩ := h1 s hs
      have h0 : (u • fun l => B l i') ∈ Q := by
        refine ⟨0, zero_mem _, ?_⟩
        rw [inv_mulVec_col B C hCB, if_neg, mul_zero]
        rintro rfl; omega
      simpa using sub_mem h0 (hMQ hu)
    obtain ⟨t, ht, h'⟩ := sup_le hTQ hMQ h
    refine ⟨t, ht, ?_⟩
    rw [← h', Matrix.mulVec_mulVec, hCX, ← Matrix.mulVec_mulVec]
    show _ = ∑ l, m i l * (C *ᵥ (ε • fun l => B l j)) l
    simp only [inv_mulVec_col B C hCB, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro h
    rw [hsum]
    refine sum_mem fun i _ => ?_
    by_cases hi : i.val < N
    · exact Submodule.smul_mem _ (⟨m i j, hm i j⟩ : S) (h2 i hi)
    · obtain ⟨t, ht, h'⟩ := h i (not_lt.1 hi)
      refine Submodule.mem_sup_right ((hM _).2 fun l => ?_)
      rw [smul_smul, inv_mulVec_col B C hCB]
      split_ifs
      · exact ⟨t, ht, by rw [← h', mul_comm]⟩
      · exact ⟨0, zero_mem _, by simp⟩

end Gen

/- English proof (translation)
Use `show Submodule.span _ _ = Submodule.span _ _`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨⟨x, hx⟩, rfl⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x.1, x.2, rfl⟩`.
-/
theorem hatL_eq (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩

/- English proof (translation)
Establish `hL : ∀ x : VA I, x ∈ I.Lf ↔ ∀ i, (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ x) i ∈ IntAf I.F I.E` using `fun x => by rw [← hatL_eq]; exact hβ x`. Prove the components needed by the constructor for the conclusion. Introduce `hy i`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨x, hx, rfl⟩` from `hy`. Conclude with `⟨_, (hL x).1 hx i, by rw [Matrix.mulVec_smul]; rfl⟩`. Consider the case `zero => exact ⟨0, zero_mem _, by rw [Matrix.mulVec_zero, mul_zero]; rfl⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨s, hs, ha⟩` from `ha`.

Take `⟨t, ht, hb⟩` from `hb`. Conclude with `⟨s + t, add_mem hs ht, by rw [Matrix.mulVec_add, Pi.add_apply, ha, hb, mul_add]⟩`. Consider the case `smul c a _ ha`. Take `⟨s, hs, ha⟩` from `ha`. Use `⟨c * s, mul_mem c.2 hs, ?_⟩` and prove the remaining obligations.

Use `show (_ *ᵥ ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • a)) i = _`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, ha, smul_eq_mul, mul_left_comm]`. Introduce `h choose t ht ht' using h`. Establish `e : y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • ((β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ t)`. Establish `: ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • t` using `funext ht'`.

Rewrite using `[← Matrix.mulVec_smul, ← this, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[e]`. Use `Submodule.subset_span ⟨_, (hL _).2 fun i => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Conclude with `ht i`.
-/
theorem mem_mL_iff (I : AutInst) (g : ℕ) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (hβ : IsFrame β I.L) (y : VA I) :
    y ∈ mL I g ↔ ∀ i, ∃ t ∈ IntAf I.F I.E,
      (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ y) i =
        (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t := by
  have hL : ∀ x : VA I, x ∈ I.Lf ↔ ∀ i,
      (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ x) i ∈
        IntAf I.F I.E := fun x => by rw [← hatL_eq]; exact hβ x
  constructor
  · intro hy i
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨_, (hL x).1 hx i, by rw [Matrix.mulVec_smul]; rfl⟩
    | zero => exact ⟨0, zero_mem _, by rw [Matrix.mulVec_zero, mul_zero]; rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨t, ht, hb⟩ := hb
      exact ⟨s + t, add_mem hs ht, by rw [Matrix.mulVec_add, Pi.add_apply, ha, hb, mul_add]⟩
    | smul c a _ ha =>
      obtain ⟨s, hs, ha⟩ := ha
      refine ⟨c * s, mul_mem c.2 hs, ?_⟩
      show (_ *ᵥ ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • a)) i = _
      rw [Matrix.mulVec_smul, Pi.smul_apply, ha, smul_eq_mul, mul_left_comm]
  · intro h
    choose t ht ht' using h
    have e : y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) •
        ((β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ t) := by
      have : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ y =
          (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • t := funext ht'
      rw [← Matrix.mulVec_smul, ← this, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [e]
    refine Submodule.subset_span ⟨_, (hL _).2 fun i => ?_, rfl⟩
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact ht i

/- English proof (translation)
Take `⟨y, hy⟩` from `hx`. Establish `: β⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β = intGL I.F I.E I.n y`. Rewrite using `[← hy]`. Use `show β⁻¹ * (β * intGL I.F I.E I.n y * β⁻¹) * β = _`. Use `group`.

Unfold `matIn`. Rewrite using `[this, Matrix.sub_apply, Matrix.one_apply]`. Use `sub_mem (y.1 i j).2 ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`.
-/
theorem matIn_int (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf)
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) (i j : Fin I.n) : (matIn I β x - 1) i j ∈ IntAf I.F I.E := by
  obtain ⟨y, hy⟩ := hx
  have : β⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β = intGL I.F I.E I.n y := by
    rw [← hy]
    show β⁻¹ * (β * intGL I.F I.E I.n y * β⁻¹) * β = _
    group
  unfold matIn
  rw [this, Matrix.sub_apply, Matrix.one_apply]
  refine sub_mem (y.1 i j).2 ?_
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Take `⟨-, -, -, -, ⟨-, hew0, hew, -⟩, ⟨hbw, hbwd⟩, -, -⟩` from `hR`. Take `⟨hfr, hcol⟩` from `hβ`. Establish `hX : (I.fmat x - 1) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * (matIn I β x - 1)`. Unfold `matIn`. Rewrite using `[sub_mul, mul_sub, one_mul, mul_one, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]`.

Establish `key` using `col_iff (S := IntAf I.F I.E) (g := (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) _ _ _ _ β.inv_mul hX β.mul_inv (matIn_int I β x hx) (mL I g) (mem_mL_iff I g β hfr)`. Establish `he : ∀ (a : Fin ρ) (j : Fin I.n), j.val = a.val → ((1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) - e0 a ∈ mL I g`. Introduce `a j hj`. Use `hcol j` as an intermediate fact. Rewrite `this` using `[hj, flagVec, dif_pos a.2]`.

Rewrite using `[one_smul]`. Conclude with `this`. Establish `hz : ∀ (j : Fin I.n), j.val = ρ + k → ((1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) - z0 ∈ mL I g`. Introduce `j hj`. Use `hcol j` as an intermediate fact.

Rewrite `this` using `[hj, flagVec, dif_neg (by omega), dif_neg (by omega), if_pos rfl]`. Rewrite using `[one_smul]`. Conclude with `this`. Establish `hb : ∀ (a : Fin k) (j : Fin I.n), j.val = ρ + a.val → (ew • fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) - bw a ∈ mL I g`. Introduce `a j hj`.

Use `hcol j` as an intermediate fact. Establish `ha : j.val - ρ < k` using `by omega`. Rewrite `this` using `[flagVec, dif_neg (by omega), dif_pos ha]`. Establish `e : (⟨j.val - ρ, ha⟩ : Fin k) = a` using `Fin.ext (by simp only; omega)`. Rewrite `this` using `[e]`.

Establish `h2` using `Submodule.smul_mem _ (⟨ew, hew⟩ : IntAf I.F I.E) this`. Establish `e2 : ew • bwd (Fin.rev a) = 0` using `by rw [hbwd, smul_smul, hew0, zero_smul]`. Rewrite `h2` using `[Subring.smul_def]`. Simplify using `only at h2`. Rewrite `h2` using `[smul_sub, smul_add, ← hbw, e2, add_zero]`. Then use the resulting hypothesis.

Establish `sup : ∀ (T : Set (VA I)) (a s : VA I), s ∈ T → a - s ∈ mL I g → a ∈ Submodule.span (IntAf I.F I.E) T ⊔ mL I g` using `fun T a s hs h => by`. Use `add_mem (Submodule.mem_sup_right (S := Submodule.span (IntAf I.F I.E) T) h) (Submodule.mem_sup_left (Submodule.subset_span hs))` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `k1 : ∀ (a : Fin ρ) (j : Fin I.n), j.val = a.val → (InMod I g (e0 '' {b | b.1 < a.1}) ((I.fmat x - 1) *ᵥ e0 a) ↔ ∀ i : Fin I.n, a.val ≤ i.val → ZMod' I g ((matIn I β x - 1) i j))`. Introduce `a j hj`.

Use `key (e0 '' {b | b.1 < a.1}) a.val 1 j (e0 a) (he a j hj) (by` as an intermediate fact. Introduce and unpack `_ ⟨b, hb', rfl⟩`. Conclude with `⟨1, ⟨b.val, by omega⟩, hb', he b _ rfl⟩)`. Use the proof step `(fun i hi => sup _ _ (e0 ⟨i.val, by omega⟩) ⟨_, hi, rfl⟩ (he _ i rfl))`. Simplify using `only [one_mul] at this`.

Conclude with `this`. Establish `k2 : ∀ (j : Fin I.n), j.val = ρ + k → (InMod I g (Set.range e0) ((I.fmat x - 1) *ᵥ z0) ↔ ∀ i : Fin I.n, ρ ≤ i.val → ZMod' I g ((matIn I β x - 1) i j))`. Introduce `j hj`. Use `key (Set.range e0) ρ 1 j z0 (hz j hj) (by` as an intermediate fact. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `⟨1, ⟨b.val, by omega⟩, b.2, he b _ rfl⟩)`. Use the proof step `(fun i hi => sup _ _ (e0 ⟨i.val, hi⟩) ⟨_, rfl⟩ (he _ i rfl))`. Simplify using `only [one_mul] at this`. Conclude with `this`. Establish `k3 : ∀ (a : Fin k) (j : Fin I.n), j.val = ρ + a.val → (InMod I g (Set.range e0 ∪ bw '' {b | b.1 < a.1}) ((I.fmat x - 1) *ᵥ bw a) ↔ ∀ i : Fin I.n, ρ + a.val ≤ i.val → ZMod' I g (ew * (matIn I β x - 1) i j))`.

Introduce `a j hj`. Use `key (Set.range e0 ∪ bw '' {b | b.1 < a.1}) (ρ + a.val) ew j (bw a) (hb a j hj) ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨b, rfl⟩ | ⟨b, hb', rfl⟩)`. Conclude with `⟨1, ⟨b.val, by omega⟩, by simp only; omega, he b _ rfl⟩`. Establish `hb'' : b.val < a.val` using `hb'`.

Conclude with `⟨ew, ⟨ρ + b.val, by omega⟩, by simp only; omega, hb b _ rfl⟩`. Introduce `i hi`. Distinguish the cases in `h : i.val < ρ`. Use `sup (Set.range e0 ∪ bw '' {b | b.1 < a.1}) _ (e0 ⟨i.val, h⟩) (Or.inl ⟨_, rfl⟩) (he _ i rfl)` as an intermediate fact. Rewrite `this` using `[one_smul]`.

Conclude with `Submodule.smul_mem _ (⟨ew, hew⟩ : IntAf I.F I.E) this`. Conclude with `sup _ _ (bw ⟨i.val - ρ, by omega⟩) (Or.inr ⟨_, by show i.val - ρ < a.val; omega, rfl⟩) (hb _ i (by simp only; omega))`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c1, c2, c3⟩`. Use `⟨fun i j hj hi => ?_, fun i j hj hi => ?_, fun i j hj hj' hi => ?_⟩` and prove the remaining obligations.

Conclude with `(k1 ⟨j.val, hj⟩ j rfl).1 (c1 _) i hi`. Conclude with `(k2 j hj).1 c2 i hi`. Conclude with `(k3 ⟨j.val - ρ, by omega⟩ j (by simp only; omega)).1 (c3 _) i (by simp only; omega)`. Introduce and unpack `⟨c1, c2, c3⟩`. Use `⟨fun a => ?_, ?_, fun a => ?_⟩` and prove the remaining obligations.

Conclude with `(k1 a ⟨a.val, by omega⟩ rfl).2 fun i hi => c1 i _ a.2 hi`. Conclude with `(k2 ⟨ρ + k, by omega⟩ rfl).2 fun i hi => c2 i _ rfl hi`. Conclude with `(k3 a ⟨ρ + a.val, by omega⟩ rfl).2 fun i hi => c3 i _ (by simp only; omega) (by simp only; omega) hi`.
-/
theorem k2cong_iff_flagCond (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (hR : IsRefFrame I g e0 f0 z0 bw bwd ew) (hn : I.n = 2 * ρ + k + 1)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (hβ : IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β)
    (x : I.Gf) (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) :
    K2cong I g e0 z0 bw x ↔ FlagCond (ZMod' I g) ρ k ew (matIn I β x) := by
  obtain ⟨-, -, -, -, ⟨-, hew0, hew, -⟩, ⟨hbw, hbwd⟩, -, -⟩ := hR
  obtain ⟨hfr, hcol⟩ := hβ
  have hX : (I.fmat x - 1) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) =
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * (matIn I β x - 1) := by
    unfold matIn
    rw [sub_mul, mul_sub, one_mul, mul_one, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have key := col_iff (S := IntAf I.F I.E) (g := (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) _ _ _ _ β.inv_mul hX β.mul_inv
    (matIn_int I β x hx) (mL I g) (mem_mL_iff I g β hfr)
  have he : ∀ (a : Fin ρ) (j : Fin I.n), j.val = a.val → ((1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) •
      fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) - e0 a ∈ mL I g := by
    intro a j hj
    have := hcol j
    rw [hj, flagVec, dif_pos a.2] at this
    rw [one_smul]; exact this
  have hz : ∀ (j : Fin I.n), j.val = ρ + k → ((1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) •
      fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) - z0 ∈ mL I g := by
    intro j hj
    have := hcol j
    rw [hj, flagVec, dif_neg (by omega), dif_neg (by omega), if_pos rfl] at this
    rw [one_smul]; exact this
  have hb : ∀ (a : Fin k) (j : Fin I.n), j.val = ρ + a.val → (ew •
      fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) - bw a ∈ mL I g := by
    intro a j hj
    have := hcol j
    have ha : j.val - ρ < k := by omega
    rw [flagVec, dif_neg (by omega), dif_pos ha] at this
    have e : (⟨j.val - ρ, ha⟩ : Fin k) = a := Fin.ext (by simp only; omega)
    rw [e] at this
    have h2 := Submodule.smul_mem _ (⟨ew, hew⟩ : IntAf I.F I.E) this
    have e2 : ew • bwd (Fin.rev a) = 0 := by rw [hbwd, smul_smul, hew0, zero_smul]
    rw [Subring.smul_def] at h2
    simp only at h2
    rwa [smul_sub, smul_add, ← hbw, e2, add_zero] at h2
  have sup : ∀ (T : Set (VA I)) (a s : VA I), s ∈ T → a - s ∈ mL I g →
      a ∈ Submodule.span (IntAf I.F I.E) T ⊔ mL I g := fun T a s hs h => by
    have := add_mem (Submodule.mem_sup_right (S := Submodule.span (IntAf I.F I.E) T) h)
      (Submodule.mem_sup_left (Submodule.subset_span hs))
    rwa [sub_add_cancel] at this
  have k1 : ∀ (a : Fin ρ) (j : Fin I.n), j.val = a.val →
      (InMod I g (e0 '' {b | b.1 < a.1}) ((I.fmat x - 1) *ᵥ e0 a) ↔
        ∀ i : Fin I.n, a.val ≤ i.val → ZMod' I g ((matIn I β x - 1) i j)) := by
    intro a j hj
    have := key (e0 '' {b | b.1 < a.1}) a.val 1 j (e0 a) (he a j hj)
      (by
        rintro _ ⟨b, hb', rfl⟩
        exact ⟨1, ⟨b.val, by omega⟩, hb', he b _ rfl⟩)
      (fun i hi => sup _ _ (e0 ⟨i.val, by omega⟩) ⟨_, hi, rfl⟩ (he _ i rfl))
    simp only [one_mul] at this
    exact this
  have k2 : ∀ (j : Fin I.n), j.val = ρ + k →
      (InMod I g (Set.range e0) ((I.fmat x - 1) *ᵥ z0) ↔
        ∀ i : Fin I.n, ρ ≤ i.val → ZMod' I g ((matIn I β x - 1) i j)) := by
    intro j hj
    have := key (Set.range e0) ρ 1 j z0 (hz j hj)
      (by
        rintro _ ⟨b, rfl⟩
        exact ⟨1, ⟨b.val, by omega⟩, b.2, he b _ rfl⟩)
      (fun i hi => sup _ _ (e0 ⟨i.val, hi⟩) ⟨_, rfl⟩ (he _ i rfl))
    simp only [one_mul] at this
    exact this
  have k3 : ∀ (a : Fin k) (j : Fin I.n), j.val = ρ + a.val →
      (InMod I g (Set.range e0 ∪ bw '' {b | b.1 < a.1}) ((I.fmat x - 1) *ᵥ bw a) ↔
        ∀ i : Fin I.n, ρ + a.val ≤ i.val → ZMod' I g (ew * (matIn I β x - 1) i j)) := by
    intro a j hj
    refine key (Set.range e0 ∪ bw '' {b | b.1 < a.1}) (ρ + a.val) ew j (bw a) (hb a j hj) ?_ ?_
    · rintro _ (⟨b, rfl⟩ | ⟨b, hb', rfl⟩)
      · exact ⟨1, ⟨b.val, by omega⟩, by simp only; omega, he b _ rfl⟩
      · have hb'' : b.val < a.val := hb'
        exact ⟨ew, ⟨ρ + b.val, by omega⟩, by simp only; omega, hb b _ rfl⟩
    · intro i hi
      by_cases h : i.val < ρ
      · have := sup (Set.range e0 ∪ bw '' {b | b.1 < a.1}) _ (e0 ⟨i.val, h⟩) (Or.inl ⟨_, rfl⟩) (he _ i rfl)
        rw [one_smul] at this
        exact Submodule.smul_mem _ (⟨ew, hew⟩ : IntAf I.F I.E) this
      · exact sup _ _ (bw ⟨i.val - ρ, by omega⟩) (Or.inr ⟨_, by show i.val - ρ < a.val; omega, rfl⟩)
          (hb _ i (by simp only; omega))
  constructor
  · rintro ⟨c1, c2, c3⟩
    refine ⟨fun i j hj hi => ?_, fun i j hj hi => ?_, fun i j hj hj' hi => ?_⟩
    · exact (k1 ⟨j.val, hj⟩ j rfl).1 (c1 _) i hi
    · exact (k2 j hj).1 c2 i hi
    · exact (k3 ⟨j.val - ρ, by omega⟩ j (by simp only; omega)).1 (c3 _) i (by simp only; omega)
  · rintro ⟨c1, c2, c3⟩
    refine ⟨fun a => ?_, ?_, fun a => ?_⟩
    · exact (k1 a ⟨a.val, by omega⟩ rfl).2 fun i hi => c1 i _ a.2 hi
    · exact (k2 ⟨ρ + k, by omega⟩ rfl).2 fun i hi => c2 i _ rfl hi
    · exact (k3 a ⟨ρ + a.val, by omega⟩ rfl).2 fun i hi => c3 i _ (by simp only; omega) (by simp only; omega) hi

end GlobalTheory.FlagBasis.Cong

end
