import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth

open Matrix

namespace Formalism.HermitianLattices.Ext.L3.PinE

variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]

def e₀ : Unit ⊕ κ → A := Pi.single (Sum.inl ()) 1

def HH (H' : Matrix κ κ A) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A := fromBlocks 1 0 0 H'

/- English proof (translation)
Simplify using `[HH, fromBlocks_conjTranspose, fromBlocks_multiply]`.
-/
theorem form_block (H' X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * HH H' * fromBlocks 1 0 0 X' =
      fromBlocks 1 0 0 (X'ᴴ * H' * X') := by
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply]

/- English proof (translation)
Unfold `e₀`. Rewrite using `[mulVec_single_one]`. Use extensionality with `i`. Apply the tactic sequence `rcases i with ⟨⟩ | i <;> simp`.
-/
theorem block_mulVec_e₀ (X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) *ᵥ e₀ = e₀ := by
  unfold e₀
  rw [mulVec_single_one]
  ext i
  rcases i with ⟨⟩ | i <;> simp

/- English proof (translation)
Establish `h11 : Y (Sum.inl ()) (Sum.inl ()) = 1`. Use `congrFun h0 (Sum.inl ())` as an intermediate fact. Simplify `this` using `[e₀, mulVec_single_one]`. Establish `h21 : ∀ i, Y (Sum.inr i) (Sum.inl ()) = 0`. Introduce `i`.

Use `congrFun h0 (Sum.inr i)` as an intermediate fact. Simplify `this` using `[e₀, mulVec_single_one]`. Establish `hA : Y.toBlocks₁₁ = 1`. Use extensionality with `⟨⟩ ⟨⟩`. Simplify `h11` using `[toBlocks₁₁]`.

Establish `hC : Y.toBlocks₂₁ = 0`. Use extensionality with `i ⟨⟩`. Simplify `h21 i` using `[toBlocks₂₁]`. Establish `hYb : Y = fromBlocks 1 Y.toBlocks₁₂ 0 Y.toBlocks₂₂` using `by conv_lhs => rw [← fromBlocks_toBlocks Y]`. Rewrite using `[hA, hC]`.

Rewrite `hY` using `[hYb]`. Establish `key` using `congrArg Matrix.toBlocks₁₂ hY`. Establish `key2` using `congrArg Matrix.toBlocks₂₂ hY`. Simplify using `[HH, fromBlocks_conjTranspose, fromBlocks_multiply] at key key2`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify `key2` using `[key]`. Rewrite `hYb` using `[key]`. Conclude with `hYb`.
-/
theorem eq_block_of_fix {H' : Matrix κ κ A} {Y : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A}
    (hY : Yᴴ * HH H' * Y = HH H') (h0 : Y *ᵥ e₀ = e₀) :
    Y.toBlocks₂₂ᴴ * H' * Y.toBlocks₂₂ = H' ∧ Y = fromBlocks 1 0 0 Y.toBlocks₂₂ := by
  have h11 : Y (Sum.inl ()) (Sum.inl ()) = 1 := by
    have := congrFun h0 (Sum.inl ())
    simpa [e₀, mulVec_single_one] using this
  have h21 : ∀ i, Y (Sum.inr i) (Sum.inl ()) = 0 := by
    intro i
    have := congrFun h0 (Sum.inr i)
    simpa [e₀, mulVec_single_one] using this
  have hA : Y.toBlocks₁₁ = 1 := by
    ext ⟨⟩ ⟨⟩
    simpa [toBlocks₁₁] using h11
  have hC : Y.toBlocks₂₁ = 0 := by
    ext i ⟨⟩
    simpa [toBlocks₂₁] using h21 i
  have hYb : Y = fromBlocks 1 Y.toBlocks₁₂ 0 Y.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks Y]
    rw [hA, hC]
  rw [hYb] at hY
  have key := congrArg Matrix.toBlocks₁₂ hY
  have key2 := congrArg Matrix.toBlocks₂₂ hY
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply] at key key2
  refine ⟨?_, ?_⟩
  · simpa [key] using key2
  · rw [key] at hYb
    exact hYb

/- English proof (translation)
Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hX]`. Simplify using `[e₀, mulVec_single_one, dotProduct, Fintype.sum_sum_type, h00]`.
-/
theorem form_col {H X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A} (hX : Xᴴ * H * X = H)
    (h00 : H (Sum.inl ()) (Sum.inl ()) = 1) : star (X *ᵥ e₀) ⬝ᵥ (H *ᵥ (X *ᵥ e₀)) = 1 := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hX]
  simp [e₀, mulVec_single_one, dotProduct, Fintype.sum_sum_type, h00]

/- English proof (translation)
Use `choose G G' hG using htr`. Establish `h00 : HH H' (Sum.inl ()) (Sum.inl ()) = (1 : A)` using `by simp [HH]`. Establish `hinv : ∀ x hx, G' x hx * G x hx = 1` using `fun x hx => by first`. Consider the case `exact mul_eq_one_comm.mp (hG x hx).2.1`. Consider the case `exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) (hG x hx).2.1`.

Consider the case `exact (Matrix.mul_eq_one_comm (M := G x hx) (N := G' x hx)).mp (hG x hx).2.1`. Establish `hG'form : ∀ x hx, (G' x hx)ᴴ * HH H' * G' x hx = HH H'`. Introduce `x hx`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[(hG x hx).1]`.

Use `_ = (G x hx * G' x hx)ᴴ * HH H' * (G x hx * G' x hx) := by`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = HH H' := by rw [(hG x hx).2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hGeq : ∀ x y (hx : star x ⬝ᵥ (HH H' *ᵥ x) = 1) (hy : star y ⬝ᵥ (HH H' *ᵥ y) = 1), x = y → G x hx = G y hy ∧ G' x hx = G' y hy`. Introduce and unpack `x _ hx hy rfl`.

Conclude with `⟨rfl, rfl⟩`. Establish `fixY : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'), (G' (X *ᵥ e₀) (form_col hX h00) * X)ᴴ * HH H' * (G' (X *ᵥ e₀) (form_col hX h00) * X) = HH H' ∧ (G' (X *ᵥ e₀) (form_col hX h00) * X) *ᵥ e₀ = e₀`. Introduce `X hX`. Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = HH H' := by rw [hG'form, hX]`. Establish `h1 : G' (X *ᵥ e₀) (form_col hX h00) *ᵥ (G (X *ᵥ e₀) (form_col hX h00) *ᵥ e₀) = e₀`. Rewrite using `[Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Rewrite `h1` using `[(hG _ _).2.2]`.

Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `h1`. Establish `recon : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'), X = G (X *ᵥ e₀) (form_col hX h00) * fromBlocks 1 0 0 (G' (X *ᵥ e₀) (form_col hX h00) * X).toBlocks₂₂`. Introduce `X hX`. Rewrite using `[← (eq_block_of_fix (fixY X hX).1 (fixY X hX).2).2, ← Matrix.mul_assoc, (hG _ _).2.1, Matrix.one_mul]`.

Set `f : {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} → {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} × {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'}` to `fun X => (⟨X.1 *ᵥ e₀, form_col X.2 h00⟩, ⟨_, (eq_block_of_fix (fixY X.1 X.2).1 (fixY X.1 X.2).2).1⟩)`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X1, hX1⟩ ⟨X2, hX2⟩ h`. Simplify using `only [f, Prod.mk.injEq, Subtype.mk.injEq] at h`.

Take `⟨h1, h2⟩` from `h`. Take `⟨hGG, hGG'⟩` from `hGeq _ _ (form_col hX1 h00) (form_col hX2 h00) h1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[recon X1 hX1, recon X2 hX2, hGG, h2]`.

Introduce and unpack `⟨⟨x, hx⟩, ⟨X', hX'⟩⟩`. Establish `hform : (G x hx * fromBlocks 1 0 0 X')ᴴ * HH H' * (G x hx * fromBlocks 1 0 0 X') = HH H'`. Combine the equalities or inequalities in the displayed calculation. Establish `hxe : (G x hx * fromBlocks 1 0 0 X') *ᵥ e₀ = x`. Rewrite using `[← Matrix.mulVec_mulVec, block_mulVec_e₀, (hG x hx).2.2]`.

Use `⟨⟨_, hform⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [f]`. Take `⟨_, hGG'⟩` from `hGeq _ _ (form_col hform h00) hx hxe`. Use `Prod.ext (Subtype.ext hxe) (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hGG', ← Matrix.mul_assoc, hinv, Matrix.one_mul, Matrix.toBlocks_fromBlocks₂₂]`. Rewrite using `[← Nat.card_prod]`. Conclude with `Nat.card_congr (Equiv.ofBijective f hf)`.
-/
theorem card_split [Finite A] (H' : Matrix κ κ A)
    (htr : ∀ x : Unit ⊕ κ → A, star x ⬝ᵥ (HH H' *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A, Gᴴ * HH H' * G = HH H' ∧ G * G' = 1 ∧ G *ᵥ e₀ = x) :
    Nat.card {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} =
      Nat.card {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} *
        Nat.card {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} := by
  classical
  choose G G' hG using htr
  have h00 : HH H' (Sum.inl ()) (Sum.inl ()) = (1 : A) := by simp [HH]
  have hinv : ∀ x hx, G' x hx * G x hx = 1 := fun x hx => by
    first
      | exact mul_eq_one_comm.mp (hG x hx).2.1
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) (hG x hx).2.1
      | exact (Matrix.mul_eq_one_comm (M := G x hx) (N := G' x hx)).mp (hG x hx).2.1
  have hG'form : ∀ x hx, (G' x hx)ᴴ * HH H' * G' x hx = HH H' := by
    intro x hx
    calc (G' x hx)ᴴ * HH H' * G' x hx = (G' x hx)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) * G' x hx := by
          rw [(hG x hx).1]
      _ = (G x hx * G' x hx)ᴴ * HH H' * (G x hx * G' x hx) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = HH H' := by rw [(hG x hx).2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGeq : ∀ x y (hx : star x ⬝ᵥ (HH H' *ᵥ x) = 1) (hy : star y ⬝ᵥ (HH H' *ᵥ y) = 1), x = y →
      G x hx = G y hy ∧ G' x hx = G' y hy := by
    rintro x _ hx hy rfl
    exact ⟨rfl, rfl⟩
  have fixY : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      (G' (X *ᵥ e₀) (form_col hX h00) * X)ᴴ * HH H' * (G' (X *ᵥ e₀) (form_col hX h00) * X) = HH H' ∧
      (G' (X *ᵥ e₀) (form_col hX h00) * X) *ᵥ e₀ = e₀ := by
    intro X hX
    constructor
    · calc _ = Xᴴ * ((G' (X *ᵥ e₀) (form_col hX h00))ᴴ * HH H' * G' (X *ᵥ e₀) (form_col hX h00)) * X := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = HH H' := by rw [hG'form, hX]
    · have h1 : G' (X *ᵥ e₀) (form_col hX h00) *ᵥ (G (X *ᵥ e₀) (form_col hX h00) *ᵥ e₀) = e₀ := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [(hG _ _).2.2] at h1
      rw [← Matrix.mulVec_mulVec]
      exact h1
  have recon : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      X = G (X *ᵥ e₀) (form_col hX h00) *
        fromBlocks 1 0 0 (G' (X *ᵥ e₀) (form_col hX h00) * X).toBlocks₂₂ := by
    intro X hX
    rw [← (eq_block_of_fix (fixY X hX).1 (fixY X hX).2).2, ← Matrix.mul_assoc, (hG _ _).2.1,
      Matrix.one_mul]
  let f : {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} →
      {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} × {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} :=
    fun X => (⟨X.1 *ᵥ e₀, form_col X.2 h00⟩,
      ⟨_, (eq_block_of_fix (fixY X.1 X.2).1 (fixY X.1 X.2).2).1⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨X1, hX1⟩ ⟨X2, hX2⟩ h
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hGG, hGG'⟩ := hGeq _ _ (form_col hX1 h00) (form_col hX2 h00) h1
      apply Subtype.ext
      dsimp only
      rw [recon X1 hX1, recon X2 hX2, hGG, h2]
    · rintro ⟨⟨x, hx⟩, ⟨X', hX'⟩⟩
      have hform : (G x hx * fromBlocks 1 0 0 X')ᴴ * HH H' * (G x hx * fromBlocks 1 0 0 X') = HH H' := by
        calc _ = (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) *
              fromBlocks 1 0 0 X' := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = HH H' := by rw [(hG x hx).1, form_block, hX']; rfl
      have hxe : (G x hx * fromBlocks 1 0 0 X') *ᵥ e₀ = x := by
        rw [← Matrix.mulVec_mulVec, block_mulVec_e₀, (hG x hx).2.2]
      refine ⟨⟨_, hform⟩, ?_⟩
      simp only [f]
      obtain ⟨_, hGG'⟩ := hGeq _ _ (form_col hform h00) hx hxe
      refine Prod.ext (Subtype.ext hxe) (Subtype.ext ?_)
      dsimp only
      rw [hGG', ← Matrix.mul_assoc, hinv, Matrix.one_mul, Matrix.toBlocks_fromBlocks₂₂]
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f hf)

end Formalism.HermitianLattices.Ext.L3.PinE
