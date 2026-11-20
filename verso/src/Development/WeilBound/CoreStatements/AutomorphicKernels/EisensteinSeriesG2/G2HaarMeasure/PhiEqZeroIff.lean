import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open Matrix

namespace GlobalTheory.EisBL.NilAlg

variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

def blk (X : Matrix n n B) : Matrix (n ⊕ n) (n ⊕ n) B := fromBlocks (1 + X) (-X) X (1 - X)

/- English proof (translation)
Simplify using `only [blk, fromBlocks_multiply]`. Rewrite using `[fromBlocks_inj]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring`.
-/
theorem blk_mul (X Y : Matrix n n B) : blk X * blk Y = blk (X + Y) := by
  simp only [blk, fromBlocks_multiply]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

omit [Fintype n] in
/- English proof (translation)
Simplify using `[blk, fromBlocks_one]`.
-/
theorem blk_zero : blk (0 : Matrix n n B) = 1 := by
  simp [blk, fromBlocks_one]

def phi (c : B →+* B) (J X : Matrix n n B) : Matrix n n B := Xᵀ * J + J * X.map c

/- English proof (translation)
Establish `e : ∀ M : Matrix n n B, M.map c = c.mapMatrix M` using `fun _ => rfl`. Simplify using `only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]`.
-/
theorem blk_map (c : B →+* B) (X : Matrix n n B) : (blk X).map c = blk (X.map c) := by
  have e : ∀ M : Matrix n n B, M.map c = c.mapMatrix M := fun _ => rfl
  simp only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]

/- English proof (translation)
Rewrite using `[blk_map]`. Simplify using `only [blk, phi, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_add, transpose_add, transpose_sub, transpose_neg, transpose_one]`. Rewrite using `[fromBlocks_inj]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring`.
-/
theorem blk_form (c : B →+* B) (J X : Matrix n n B) :
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c =
      GlobalTheory.WeilM.dbl J + fromBlocks (phi c J X) (-phi c J X) (-phi c J X) (phi c J X) := by
  rw [blk_map]
  simp only [blk, phi, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_add, transpose_add,
    transpose_sub, transpose_neg, transpose_one]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/- English proof (translation)
Rewrite using `[blk_form]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[GlobalTheory.WeilM.dbl, fromBlocks_add, fromBlocks_inj]`. Simplify using `using h.1`.

Introduce `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem blk_form_iff (c : B →+* B) (J X : Matrix n n B) :
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c = GlobalTheory.WeilM.dbl J ↔ phi c J X = 0 := by
  rw [blk_form]
  constructor
  · intro h
    rw [GlobalTheory.WeilM.dbl, fromBlocks_add, fromBlocks_inj] at h
    simpa using h.1
  · intro h
    rw [h]
    simp

def tau (c : B →+* B) (J K X : Matrix n n B) : Matrix n n B := -(J * X.map c * K)ᵀ

/- English proof (translation)
Unfold `phi tau`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : J * X.map c * K = -Xᵀ`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h1, transpose_neg, transpose_transpose, neg_neg]`. Introduce `h`. Establish `h1 : Xᵀ = -(J * X.map c * K)` using `by conv_lhs => rw [← h]`. Rewrite using `[transpose_neg, transpose_transpose]`. Rewrite using `[h1]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem phi_eq_zero_iff (c : B →+* B) {J K : Matrix n n B} (hJK : J * K = 1) (hKJ : K * J = 1)
    (X : Matrix n n B) : phi c J X = 0 ↔ tau c J K X = X := by
  unfold phi tau
  constructor
  · intro h
    have h1 : J * X.map c * K = -Xᵀ := by
      calc J * X.map c * K = (Xᵀ * J + J * X.map c) * K - Xᵀ * (J * K) := by noncomm_ring
        _ = -Xᵀ := by rw [h, hJK]; noncomm_ring
    rw [h1, transpose_neg, transpose_transpose, neg_neg]
  · intro h
    have h1 : Xᵀ = -(J * X.map c * K) := by
      conv_lhs => rw [← h]
      rw [transpose_neg, transpose_transpose]
    rw [h1]
    calc -(J * X.map c * K) * J + J * X.map c = -(J * X.map c * (K * J)) + J * X.map c := by noncomm_ring
      _ = 0 := by rw [hKJ]; noncomm_ring

/- English proof (translation)
Unfold `tau`. Rewrite using `[show (X + Y).map c = X.map c + Y.map c from map_add c.mapMatrix X Y, Matrix.mul_add, Matrix.add_mul, transpose_add, neg_add]`.
-/
theorem tau_add (c : B →+* B) (J K X Y : Matrix n n B) : tau c J K (X + Y) = tau c J K X + tau c J K Y := by
  unfold tau
  rw [show (X + Y).map c = X.map c + Y.map c from map_add c.mapMatrix X Y, Matrix.mul_add, Matrix.add_mul,
    transpose_add, neg_add]

omit [DecidableEq n] in
/- English proof (translation)
Unfold `tau`. Establish `: (h • X).map c = h • X.map c`. Use extensionality with `i j`. Simplify using `[Matrix.map_apply, Matrix.smul_apply, map_mul, hh]`. Rewrite using `[this, Matrix.mul_smul, Matrix.smul_mul, transpose_smul, smul_neg]`.
-/
theorem tau_smul (c : B →+* B) (J K : Matrix n n B) (h : B) (hh : c h = h) (X : Matrix n n B) :
    tau c J K (h • X) = h • tau c J K X := by
  unfold tau
  have : (h • X).map c = h • X.map c := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hh]
  rw [this, Matrix.mul_smul, Matrix.smul_mul, transpose_smul, smul_neg]

/- English proof (translation)
Establish `hcc : (X.map c).map c = X` using `by ext i j; simp [hc]`. Establish `h1 : (tau c J K X).map c = -(K * Xᵀ * J)`. Unfold `tau`. Rewrite using `[Matrix.map_neg _ (map_neg c), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc, transpose_mul, transpose_mul, hKc, hJc]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hε, one_smul, Matrix.mul_assoc]`.

Use `show -(J * (tau c J K X).map c * K)ᵀ = X`. Rewrite using `[h1]`. Rewrite using `[show J * -(K * Xᵀ * J) * K = -((J * K) * Xᵀ * (J * K)) by noncomm_ring, transpose_neg, neg_neg, hJK, Matrix.one_mul, Matrix.mul_one, transpose_transpose]`.
-/
theorem tau_tau (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (X : Matrix n n B) :
    tau c J K (tau c J K X) = X := by
  have hcc : (X.map c).map c = X := by ext i j; simp [hc]
  have h1 : (tau c J K X).map c = -(K * Xᵀ * J) := by
    unfold tau
    rw [Matrix.map_neg _ (map_neg c), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc, transpose_mul, transpose_mul,
      hKc, hJc]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hε, one_smul, Matrix.mul_assoc]
  show -(J * (tau c J K X).map c * K)ᵀ = X
  rw [h1]
  rw [show J * -(K * Xᵀ * J) * K = -((J * K) * Xᵀ * (J * K)) by noncomm_ring, transpose_neg, neg_neg, hJK,
    Matrix.one_mul, Matrix.mul_one, transpose_transpose]

def proj (c : B →+* B) (J K : Matrix n n B) (h : B) (X : Matrix n n B) : Matrix n n B := h • (X + tau c J K X)

/- English proof (translation)
Unfold `proj`. Rewrite using `[tau_add, ← smul_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem proj_add (c : B →+* B) (J K : Matrix n n B) (h : B) (X Y : Matrix n n B) :
    proj c J K h (X + Y) = proj c J K h X + proj c J K h Y := by
  unfold proj
  rw [tau_add, ← smul_add]
  congr 1
  abel

/- English proof (translation)
Rewrite using `[phi_eq_zero_iff c hJK hKJ]`. Unfold `proj`. Rewrite using `[tau_smul c J K h hh, tau_add, tau_tau c hc ε hε hJc hKc hJK, add_comm]`.
-/
theorem phi_proj (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (hKJ : K * J = 1) (h : B) (hh : c h = h)
    (X : Matrix n n B) : phi c J (proj c J K h X) = 0 := by
  rw [phi_eq_zero_iff c hJK hKJ]
  unfold proj
  rw [tau_smul c J K h hh, tau_add, tau_tau c hc ε hε hJc hKc hJK, add_comm]

/- English proof (translation)
Unfold `proj`. Rewrite using `[(phi_eq_zero_iff c hJK hKJ X).1 hX, ← two_smul B X, smul_smul, h2, one_smul]`.
-/
theorem proj_of_phi (c : B →+* B) {J K : Matrix n n B} (hJK : J * K = 1) (hKJ : K * J = 1) (h : B) (h2 : h * 2 = 1)
    (X : Matrix n n B) (hX : phi c J X = 0) : proj c J K h X = X := by
  unfold proj
  rw [(phi_eq_zero_iff c hJK hKJ X).1 hX, ← two_smul B X, smul_smul, h2, one_smul]

/- English proof (translation)
Establish `hm : (K.map c)ᵀ * (ε • J) = 1`. Rewrite using `[← hJc, ← transpose_mul, ← Matrix.map_mul, hJK, Matrix.map_one _ (map_zero c) (map_one c), transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε, one_smul, hJK, Matrix.mul_one]`. Use `_ = ((K.map c)ᵀ * (ε • J)) * (ε • K) := (Matrix.mul_assoc _ _ _).symm`.

Use `_ = ε • K := by rw [hm, Matrix.one_mul]`.
-/
theorem hKc_of (c : B →+* B) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1) (hJc : (J.map c)ᵀ = ε • J)
    (hJK : J * K = 1) (hKJ : K * J = 1) : (K.map c)ᵀ = ε • K := by
  have hm : (K.map c)ᵀ * (ε • J) = 1 := by
    rw [← hJc, ← transpose_mul, ← Matrix.map_mul, hJK, Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  calc (K.map c)ᵀ = (K.map c)ᵀ * ((ε • J) * (ε • K)) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε, one_smul, hJK, Matrix.mul_one]
    _ = ((K.map c)ᵀ * (ε • J)) * (ε • K) := (Matrix.mul_assoc _ _ _).symm
    _ = ε • K := by rw [hm, Matrix.one_mul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `hM : M - 1 = fromBlocks (M - 1).toBlocks₁₁ (M - 1).toBlocks₁₂ (M - 1).toBlocks₂₁ (M - 1).toBlocks₂₂` using `(fromBlocks_toBlocks (M - 1)).symm`. Use `set a := (M - 1).toBlocks₁₁`. Use `set b := (M - 1).toBlocks₁₂`.

Use `set c := (M - 1).toBlocks₂₁`. Use `set d := (M - 1).toBlocks₂₂`. Rewrite `h1` using `[hM, fromBlocks_mul_fromRows]`. Rewrite `h2` using `[hM, fromCols_mul_fromBlocks]`. Establish `e1` using `congrArg Matrix.toRows₁ h1`.

Establish `e2` using `congrArg Matrix.toRows₂ h1`. Establish `e3` using `congrArg Matrix.toCols₁ h2`. Establish `e4` using `congrArg Matrix.toCols₂ h2`. Establish `z1 : toRows₁ (0 : Matrix (n ⊕ n) n B) = 0` using `by ext; rfl`. Establish `z2 : toRows₂ (0 : Matrix (n ⊕ n) n B) = 0` using `by ext; rfl`.

Establish `z3 : toCols₁ (0 : Matrix n (n ⊕ n) B) = 0` using `by ext; rfl`. Establish `z4 : toCols₂ (0 : Matrix n (n ⊕ n) B) = 0` using `by ext; rfl`. Simplify using `only [toRows₁_fromRows, toRows₂_fromRows, toCols₁_fromCols, toCols₂_fromCols, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, z1, z2, z3, z4] at e1 e2 e3 e4`. Establish `hb : b = -a` using `eq_neg_of_add_eq_zero_right e1`. Establish `hc : c = a` using `(sub_eq_zero.1 (by simpa [sub_eq_add_neg] using e3)).symm`.

Establish `hd : d = -a` using `by rw [← hc]; exact eq_neg_of_add_eq_zero_right e2`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `: M = 1 + (M - 1)` using `by abel`. Rewrite using `[this, hM, hb, hc, hd, blk, ← fromBlocks_one, fromBlocks_add]`. Simplify using `[sub_eq_add_neg]`.

Introduce and unpack `⟨X, rfl⟩`. Establish `e : blk X - 1 = fromBlocks X (-X) X (-X)`. Rewrite using `[blk, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]`. Apply the tactic sequence `congr 1 <;> abel`. Rewrite using `[e, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks]`.

Apply the tactic sequence `constructor <;> ext i j <;> (try rcases i with i | i) <;> (try rcases j with j | j) <;>`. Apply the tactic sequence `simp [Matrix.fromRows, Matrix.fromCols, Sum.elim_inl, Sum.elim_inr] <;> rfl`.
-/
theorem unip_iff_blk (M : Matrix (n ⊕ n) (n ⊕ n) B) :
    ((M - 1) * Matrix.fromRows (1 : Matrix n n B) (1 : Matrix n n B) = 0 ∧
      Matrix.fromCols (1 : Matrix n n B) (-1 : Matrix n n B) * (M - 1) = 0) ↔
      ∃ X, M = blk X := by
  constructor
  · rintro ⟨h1, h2⟩
    have hM : M - 1 = fromBlocks (M - 1).toBlocks₁₁ (M - 1).toBlocks₁₂ (M - 1).toBlocks₂₁ (M - 1).toBlocks₂₂ :=
      (fromBlocks_toBlocks (M - 1)).symm
    set a := (M - 1).toBlocks₁₁
    set b := (M - 1).toBlocks₁₂
    set c := (M - 1).toBlocks₂₁
    set d := (M - 1).toBlocks₂₂
    rw [hM, fromBlocks_mul_fromRows] at h1
    rw [hM, fromCols_mul_fromBlocks] at h2
    have e1 := congrArg Matrix.toRows₁ h1
    have e2 := congrArg Matrix.toRows₂ h1
    have e3 := congrArg Matrix.toCols₁ h2
    have e4 := congrArg Matrix.toCols₂ h2
    have z1 : toRows₁ (0 : Matrix (n ⊕ n) n B) = 0 := by ext; rfl
    have z2 : toRows₂ (0 : Matrix (n ⊕ n) n B) = 0 := by ext; rfl
    have z3 : toCols₁ (0 : Matrix n (n ⊕ n) B) = 0 := by ext; rfl
    have z4 : toCols₂ (0 : Matrix n (n ⊕ n) B) = 0 := by ext; rfl
    simp only [toRows₁_fromRows, toRows₂_fromRows, toCols₁_fromCols, toCols₂_fromCols, Matrix.mul_one,
      Matrix.one_mul, Matrix.neg_mul, z1, z2, z3, z4] at e1 e2 e3 e4
    have hb : b = -a := eq_neg_of_add_eq_zero_right e1
    have hc : c = a := (sub_eq_zero.1 (by simpa [sub_eq_add_neg] using e3)).symm
    have hd : d = -a := by rw [← hc]; exact eq_neg_of_add_eq_zero_right e2
    refine ⟨a, ?_⟩
    have : M = 1 + (M - 1) := by abel
    rw [this, hM, hb, hc, hd, blk, ← fromBlocks_one, fromBlocks_add]
    simp [sub_eq_add_neg]
  · rintro ⟨X, rfl⟩
    have e : blk X - 1 = fromBlocks X (-X) X (-X) := by
      rw [blk, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
      congr 1 <;> abel
    rw [e, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks]
    constructor <;> ext i j <;> (try rcases i with i | i) <;> (try rcases j with j | j) <;>
      simp [Matrix.fromRows, Matrix.fromCols, Sum.elim_inl, Sum.elim_inr] <;> rfl

/- English proof (translation)
Establish `e : ∀ M : Matrix n n B, M.map f = f.mapMatrix M` using `fun _ => rfl`. Simplify using `only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]`.
-/
theorem blk_map' {B' : Type} [CommRing B'] (f : B →+* B') (X : Matrix n n B) : (blk X).map f = blk (X.map f) := by
  have e : ∀ M : Matrix n n B, M.map f = f.mapMatrix M := fun _ => rfl
  simp only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]

/- English proof (translation)
Establish `hs : ∀ (a : B) (M : Matrix n n B), (a • M).map f = f a • M.map f`. Introduce `a M`. Use extensionality with `i j`. Simplify using `[Matrix.map_apply, Matrix.smul_apply, map_mul]`. Establish `hcc : (X.map c).map f = (X.map f).map c'` using `by ext i j; simp [hf]`.

Unfold `proj tau`. Rewrite using `[hs, show (X + -(J * X.map c * K)ᵀ).map f = X.map f + (-(J * X.map c * K)ᵀ).map f from map_add f.mapMatrix _ _, Matrix.map_neg _ (map_neg f), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc]`.
-/
theorem proj_map {B' : Type} [CommRing B'] (f : B →+* B') (c : B →+* B) (c' : B' →+* B')
    (hf : ∀ x, f (c x) = c' (f x)) (J K : Matrix n n B) (h : B) (X : Matrix n n B) :
    (proj c J K h X).map f = proj c' (J.map f) (K.map f) (f h) (X.map f) := by
  have hs : ∀ (a : B) (M : Matrix n n B), (a • M).map f = f a • M.map f := by
    intro a M; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
  have hcc : (X.map c).map f = (X.map f).map c' := by ext i j; simp [hf]
  unfold proj tau
  rw [hs, show (X + -(J * X.map c * K)ᵀ).map f = X.map f + (-(J * X.map c * K)ᵀ).map f from
    map_add f.mapMatrix _ _, Matrix.map_neg _ (map_neg f), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc]

end GlobalTheory.EisBL.NilAlg
