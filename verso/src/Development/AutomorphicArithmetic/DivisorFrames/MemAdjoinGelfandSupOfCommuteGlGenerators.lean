import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose

open Matrix Formalism.REAL GlobalTheory.TorFin

namespace UpperTheory.AdjointWordCommutation
open GlobalTheory.SmoothForms

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A}

/- English proof (translation)
Establish `hBC : Subalgebra.toSubmodule B * Subalgebra.toSubmodule C ≤ Subalgebra.toSubmodule C * Subalgebra.toSubmodule B` using `Submodule.mul_le.2 fun b hb c hc => by`. Rewrite using `[← h c hc b hb]`. Conclude with `Submodule.mul_mem_mul hc hb`. Establish `hCC : Subalgebra.toSubmodule C * Subalgebra.toSubmodule C ≤ Subalgebra.toSubmodule C` using `Submodule.mul_le.2 fun a ha b hb => show a * b ∈ C from C.mul_mem ha hb`. Establish `hBB : Subalgebra.toSubmodule B * Subalgebra.toSubmodule B ≤ Subalgebra.toSubmodule B` using `Submodule.mul_le.2 fun a ha b hb => show a * b ∈ B from B.mul_mem ha hb`.

Establish `hmul : (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B) * (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B) ≤ Subalgebra.toSubmodule C * Subalgebra.toSubmodule B`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : (1 : A) ∈ Subalgebra.toSubmodule C * Subalgebra.toSubmodule B`. Simplify using `using Submodule.mul_mem_mul (show (1 : A) ∈ Subalgebra.toSubmodule C from one_mem C) (show (1 : A) ∈ Subalgebra.toSubmodule B from one_mem B)`. Set `S : Subalgebra ℂ A` to `Submodule.toSubalgebra (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B) h1 (fun x y hx hy => hmul (Submodule.mul_mem_mul hx hy))`.

Establish `hle : C ⊔ B ≤ S`. Use `sup_le (fun c hc => ?_) (fun b hb => ?_)` and prove the remaining obligations. Use `Submodule.mul_mem_mul (show c ∈ Subalgebra.toSubmodule C from hc) (show (1 : A) ∈ Subalgebra.toSubmodule B from one_mem B)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `this`.

Use `Submodule.mul_mem_mul (show (1 : A) ∈ Subalgebra.toSubmodule C from one_mem C) (show b ∈ Subalgebra.toSubmodule B from hb)` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `this`. Conclude with `hle hz`.
-/
private theorem mem_mul_of_sup (C B : Subalgebra ℂ A) (h : ∀ a ∈ C, ∀ b ∈ B, a * b = b * a) {z : A}
    (hz : z ∈ C ⊔ B) : z ∈ Subalgebra.toSubmodule C * Subalgebra.toSubmodule B := by
  have hBC : Subalgebra.toSubmodule B * Subalgebra.toSubmodule C ≤
      Subalgebra.toSubmodule C * Subalgebra.toSubmodule B :=
    Submodule.mul_le.2 fun b hb c hc => by
      rw [← h c hc b hb]
      exact Submodule.mul_mem_mul hc hb
  have hCC : Subalgebra.toSubmodule C * Subalgebra.toSubmodule C ≤ Subalgebra.toSubmodule C :=
    Submodule.mul_le.2 fun a ha b hb => show a * b ∈ C from C.mul_mem ha hb
  have hBB : Subalgebra.toSubmodule B * Subalgebra.toSubmodule B ≤ Subalgebra.toSubmodule B :=
    Submodule.mul_le.2 fun a ha b hb => show a * b ∈ B from B.mul_mem ha hb
  have hmul : (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B) *
      (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B) ≤
      Subalgebra.toSubmodule C * Subalgebra.toSubmodule B := by
    calc (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B) *
          (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B)
        = Subalgebra.toSubmodule C * (Subalgebra.toSubmodule B * Subalgebra.toSubmodule C) *
            Subalgebra.toSubmodule B := by simp only [mul_assoc]
      _ ≤ Subalgebra.toSubmodule C * (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B) *
            Subalgebra.toSubmodule B := mul_le_mul' (mul_le_mul' le_rfl hBC) le_rfl
      _ = (Subalgebra.toSubmodule C * Subalgebra.toSubmodule C) *
            (Subalgebra.toSubmodule B * Subalgebra.toSubmodule B) := by simp only [mul_assoc]
      _ ≤ Subalgebra.toSubmodule C * Subalgebra.toSubmodule B := mul_le_mul' hCC hBB
  have h1 : (1 : A) ∈ Subalgebra.toSubmodule C * Subalgebra.toSubmodule B := by
    simpa using Submodule.mul_mem_mul (show (1 : A) ∈ Subalgebra.toSubmodule C from one_mem C)
      (show (1 : A) ∈ Subalgebra.toSubmodule B from one_mem B)
  let S : Subalgebra ℂ A := Submodule.toSubalgebra
    (Subalgebra.toSubmodule C * Subalgebra.toSubmodule B) h1
    (fun x y hx hy => hmul (Submodule.mul_mem_mul hx hy))
  have hle : C ⊔ B ≤ S := by
    refine sup_le (fun c hc => ?_) (fun b hb => ?_)
    · have := Submodule.mul_mem_mul (show c ∈ Subalgebra.toSubmodule C from hc)
        (show (1 : A) ∈ Subalgebra.toSubmodule B from one_mem B)
      rw [mul_one] at this
      exact this
    · have := Submodule.mul_mem_mul (show (1 : A) ∈ Subalgebra.toSubmodule C from one_mem C)
        (show b ∈ Subalgebra.toSubmodule B from hb)
      rw [one_mul] at this
      exact this
  exact hle hz

/- English proof (translation)
The claim follows from `Submodule.mul_le.2 fun _ hm _ hp => Submodule.mul_mem_mul (h hm) hp`.
-/
private theorem mul_mono_left {M N P : Submodule ℂ A} (h : M ≤ N) : M * P ≤ N * P :=
  Submodule.mul_le.2 fun _ hm _ hp => Submodule.mul_mem_mul (h hm) hp

/- English proof (translation)
Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `m hm b hb`. Establish `hb' : b ∈ B` using `hb`. Establish `: X i j * (m * b) - m * b * X i j = (X i j * m - m * X i j) * b`. Simplify using `only [sub_mul, mul_assoc, ← hB b hb' i j]`.

Rewrite using `[this]`. Conclude with `Submodule.mul_mem_mul (filt_ad hX d i j hm) hb`. Introduce `x y hx hy`. Establish `: X i j * (x + y) - (x + y) * X i j = (X i j * x - x * X i j) + (X i j * y - y * X i j)`. Rewrite using `[mul_add, add_mul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `add_mem hx hy`.
-/
private theorem filtB_ad (hX : GlRel X) (B : Subalgebra ℂ A) (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j)
    (d : ℕ) (i j : Fin n) {y : A} (hy : y ∈ filt X d * Subalgebra.toSubmodule B) :
    X i j * y - y * X i j ∈ filt X d * Subalgebra.toSubmodule B := by
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro m hm b hb
    have hb' : b ∈ B := hb
    have : X i j * (m * b) - m * b * X i j = (X i j * m - m * X i j) * b := by
      simp only [sub_mul, mul_assoc, ← hB b hb' i j]
    rw [this]
    exact Submodule.mul_mem_mul (filt_ad hX d i j hm) hb
  · intro x y hx hy
    have : X i j * (x + y) - (x + y) * X i j = (X i j * x - x * X i j) + (X i j * y - y * X i j) := by
      rw [mul_add, add_mul]; abel
    rw [this]
    exact add_mem hx hy

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.blockDiag_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]`.
-/
private theorem blockDiag_left {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (P : κ → Matrix ι ι ℂ)
    (N : Matrix (ι × κ) (ι × κ) ℂ) (k : κ) : (blockDiagonal P * N).blockDiag k = P k * N.blockDiag k := by
  ext i j
  simp [Matrix.blockDiag_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.blockDiag_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]`.
-/
private theorem blockDiag_right {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (P : κ → Matrix ι ι ℂ)
    (N : Matrix (ι × κ) (ι × κ) ℂ) (k : κ) : (N * blockDiagonal P).blockDiag k = N.blockDiag k * P k := by
  ext i j
  simp [Matrix.blockDiag_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]

private def Phi (X : Fin n → Fin n → A) (d : ℕ) {r : ℕ} (b : Fin r → A) :
    Matrix ((Fin d → Fin n) × Fin r) ((Fin d → Fin n) × Fin r) ℂ →ₗ[ℂ] A where
  toFun N := ∑ k, wordMap X d (N.blockDiag k) * b k
  map_add' N N' := by simp [blockDiag_add, add_mul, Finset.sum_add_distrib]
  map_smul' c N := by simp [blockDiag_smul, Finset.smul_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem Phi_apply (d : ℕ) {r : ℕ} (b : Fin r → A) (N) :
    Phi X d b N = ∑ k, wordMap X d (N.blockDiag k) * b k := rfl

/- English proof (translation)
Rewrite using `[Phi_apply, Phi_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [blockDiag_sub, Pi.sub_apply, blockDiag_left, blockDiag_right]`. Rewrite using `[← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits _ _ X hX d i j]`. Simplify using `only [sub_mul, mul_assoc, ← hb k i j]`.
-/
private theorem Phi_ad (hX : GlRel X) (d : ℕ) {r : ℕ} (b : Fin r → A) (hb : ∀ k i j, X i j * b k = b k * X i j)
    (i j : Fin n) (N) :
    Phi X d b (blockDiagonal (fun _ => polar n d i j) * N - N * blockDiagonal (fun _ => polar n d i j)) =
      X i j * Phi X d b N - Phi X d b N * X i j := by
  rw [Phi_apply, Phi_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [blockDiag_sub, Pi.sub_apply, blockDiag_left, blockDiag_right]
  rw [← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits _ _ X hX d i j]
  simp only [sub_mul, mul_assoc, ← hb k i j]

/- English proof (translation)
Establish `hcomm : ∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M₀ * T = T * M₀`. Introduce `T hT`. Establish `hTa` using `GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT`. Establish `hT' : T ∈ Subalgebra.centralizer ℂ {M₀}`. Use `Algebra.adjoin_le ?_ hTa` and prove the remaining obligations.

Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`. Introduce and unpack `g rfl`. Conclude with `(h2 p.1 p.2).symm`. Conclude with `(Subalgebra.mem_centralizer_iff ℂ).1 hT' M₀ rfl`.

Establish `hspan` using `GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d M₀ hcomm`. Use `clear hcomm h2`. Proceed by induction on `hspan using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨π, rfl⟩` from `hx`.

Conclude with `GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter _ _ X hX d π`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c₁, hc₁, h₁⟩` from `hx`. Take `⟨c₂, hc₂, h₂⟩` from `hy`.

Use `⟨c₁ + c₂, add_mem hc₁ hc₂, ?_⟩` and prove the remaining obligations. Establish `: wordMap X d (x + y) - (c₁ + c₂) = (wordMap X d x - c₁) + (wordMap X d y - c₂)`. Rewrite using `[map_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `add_mem h₁ h₂`. Consider the case `smul a x _ hx`. Take `⟨c, hc, h⟩` from `hx`. Use `⟨a • c, Subalgebra.smul_mem _ hc a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ← smul_sub]`.

Conclude with `Submodule.smul_mem _ a h`.
-/
private theorem word_of_comm (hX : GlRel X) (d : ℕ) (M₀ : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ)
    (h2 : ∀ i j, polar n d i j * M₀ = M₀ * polar n d i j) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA X)), wordMap X d M₀ - c ∈ filt X d := by
  have hcomm : ∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ,
      (∀ π, T * permMat n d π = permMat n d π * T) → M₀ * T = T * M₀ := by
    intro T hT
    have hTa := GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT
    have hT' : T ∈ Subalgebra.centralizer ℂ {M₀} := by
      refine Algebra.adjoin_le ?_ hTa
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro g rfl
      exact (h2 p.1 p.2).symm
    exact (Subalgebra.mem_centralizer_iff ℂ).1 hT' M₀ rfl
  have hspan := GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d M₀ hcomm
  clear hcomm h2
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨π, rfl⟩ := hx
    exact GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter _ _ X hX d π
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, hc₁, h₁⟩ := hx
    obtain ⟨c₂, hc₂, h₂⟩ := hy
    refine ⟨c₁ + c₂, add_mem hc₁ hc₂, ?_⟩
    have : wordMap X d (x + y) - (c₁ + c₂) = (wordMap X d x - c₁) + (wordMap X d y - c₂) := by
      rw [map_add]; abel
    rw [this]
    exact add_mem h₁ h₂
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    refine ⟨a • c, Subalgebra.smul_mem _ hc a, ?_⟩
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a h

/- English proof (translation)
Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `m hm c hc`. Take `⟨M', rfl⟩` from `LinearMap.mem_range.1 hm`. Use `⟨1, fun _ => c, blockDiagonal fun _ => M', fun _ => hc, ?_⟩` and prove the remaining obligations. Simplify using `[Phi_apply, blockDiag_blockDiagonal]`.

Introduce and unpack `x y ⟨r, b, M, hb, rfl⟩ ⟨r', b', M', hb', rfl⟩`. Use `⟨r + r', Fin.append b b', blockDiagonal (Fin.append M.blockDiag M'.blockDiag), ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp [hb, hb']`. Simplify using `[Phi_apply, blockDiag_blockDiagonal, Fin.sum_univ_add]`.
-/
private theorem exists_Phi (B : Subalgebra ℂ A) (d : ℕ) {x : A}
    (hx : x ∈ LinearMap.range (wordMap X d) * Subalgebra.toSubmodule B) :
    ∃ (r : ℕ) (b : Fin r → A) (M : Matrix ((Fin d → Fin n) × Fin r) ((Fin d → Fin n) × Fin r) ℂ),
      (∀ k, b k ∈ B) ∧ Phi X d b M = x := by
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm c hc
    obtain ⟨M', rfl⟩ := LinearMap.mem_range.1 hm
    refine ⟨1, fun _ => c, blockDiagonal fun _ => M', fun _ => hc, ?_⟩
    simp [Phi_apply, blockDiag_blockDiagonal]
  · rintro x y ⟨r, b, M, hb, rfl⟩ ⟨r', b', M', hb', rfl⟩
    refine ⟨r + r', Fin.append b b', blockDiagonal (Fin.append M.blockDiag M'.blockDiag), ?_, ?_⟩
    · intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp [hb, hb']
    · simp [Phi_apply, blockDiag_blockDiagonal, Fin.sum_univ_add]

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `z hz _`. Establish `h0 : filt X 0 = ⊥` using `by simp [filt]`. Rewrite `hz` using `[h0, Submodule.bot_mul]`.

Rewrite using `[(Submodule.mem_bot ℂ).1 hz]`. Conclude with `zero_mem _`. Consider the case `succ d ih`. Introduce `z hz hcz`. Establish `hle : filt X (d + 1) * Subalgebra.toSubmodule B ≤ LinearMap.range (wordMap X d) * Subalgebra.toSubmodule B ⊔ filt X d * Subalgebra.toSubmodule B`.

Rewrite using `[← Submodule.sup_mul]`. Conclude with `mul_mono_left (filt_succ d)`. Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 (hle hz)`. Take `⟨r, b, M, hbB, rfl⟩` from `exists_Phi B d hx`. Establish `hb : ∀ k i j, X i j * b k = b k * X i j` using `fun k => hB _ (hbB k)`.

Set `S : Set (Matrix ((Fin d → Fin n) × Fin r) ((Fin d → Fin n) × Fin r) ℂ)` to `Set.range fun p : Fin n × Fin n => blockDiagonal fun _ : Fin r => polar n d p.1 p.2`. Set `N` to `(filt X d * Subalgebra.toSubmodule B).comap (Phi X d b)`. Establish `hS : ∀ x ∈ S, xᴴ ∈ S`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `⟨(p.2, p.1), by simp [blockDiagonal_conjTranspose, polar_conjTranspose]⟩`.

Establish `hN : ∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N`. Introduce and unpack `_ ⟨p, rfl⟩ y' hy'`. Use `show Phi X d b (_ * _ - _ * _) ∈ filt X d * Subalgebra.toSubmodule B`. Simplify using `only`. Rewrite using `[Phi_ad hX d b hb]`.

Conclude with `filtB_ad hX B hB d p.1 p.2 hy'`. Establish `hM : ∀ x ∈ S, x * M - M * x ∈ N`. Introduce and unpack `_ ⟨p, rfl⟩`. Use `show Phi X d b (_ * _ - _ * _) ∈ filt X d * Subalgebra.toSubmodule B`. Simplify using `only`.

Rewrite using `[Phi_ad hX d b hb]`. Establish `e` using `hcz p.1 p.2`. Establish `: X p.1 p.2 * Phi X d b M - Phi X d b M * X p.1 p.2 = -(X p.1 p.2 * y - y * X p.1 p.2)`. Rewrite `e` using `[mul_add, add_mul]`. Rewrite using `[neg_sub, sub_eq_sub_iff_add_eq_add, add_comm (y * X p.1 p.2)]`.

Conclude with `e`. Rewrite using `[this]`. Conclude with `neg_mem (filtB_ad hX B hB d p.1 p.2 hy)`. Take `⟨M₀, hMM₀, hM₀⟩` from `GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _ S N hS hN M hM`. Establish `h2 : ∀ k i j, polar n d i j * M₀.blockDiag k = M₀.blockDiag k * polar n d i j`.

Introduce `k i j`. Establish `e` using `congrArg (fun Q => Q.blockDiag k) (hM₀ _ ⟨(i, j), rfl⟩)`. Simplify `e` using `[blockDiag_left, blockDiag_right]`. Use `choose c hcG hcf using fun k => word_of_comm hX d (M₀.blockDiag k) (h2 k)`. Establish `huT : ∑ k, c k * b k ∈ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B` using `Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ ((le_sup_left : Algebra.adjoin ℂ (Set.range (gelfA X)) ≤ _ ⊔ B) (hcG k)) ((le_sup_right : B ≤ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B) (hbB k))`.

Establish `hw : Phi X d b M + y - ∑ k, c k * b k = Phi X d b (M - M₀) + y + ∑ k, (wordMap X d (M₀.blockDiag k) - c k) * b k`. Rewrite using `[map_sub, Phi_apply d b M₀]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Establish `hwmem : Phi X d b M + y - ∑ k, c k * b k ∈ filt X d * Subalgebra.toSubmodule B`.

Rewrite using `[hw]`. Conclude with `add_mem (add_mem hMM₀ hy) (Submodule.sum_mem _ fun k _ => Submodule.mul_mem_mul (hcf k) (hbB k))`. Establish `hucomm : ∀ i j, X i j * ∑ k, c k * b k = (∑ k, c k * b k) * X i j`. Introduce `i j`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, gelf_adjoin_comm hX (hcG k) i j, mul_assoc, hb k i j, ← mul_assoc]`. Establish `hwcomm : ∀ i j, X i j * (Phi X d b M + y - ∑ k, c k * b k) = (Phi X d b M + y - ∑ k, c k * b k) * X i j`. Introduce `i j`. Rewrite using `[mul_sub, sub_mul, hcz i j, hucomm i j]`.

Establish `hmem` using `ih _ hwmem hwcomm`. Establish `e : Phi X d b M + y = (Phi X d b M + y - ∑ k, c k * b k) + ∑ k, c k * b k` using `by abel`. Rewrite using `[e]`. Conclude with `add_mem hmem huT`.
-/
private theorem central_of_filtB (hX : GlRel X) (B : Subalgebra ℂ A)
    (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j) (d : ℕ) :
    ∀ z ∈ filt X d * Subalgebra.toSubmodule B, (∀ i j, X i j * z = z * X i j) →
      z ∈ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B := by
  induction d with
  | zero =>
    intro z hz _
    have h0 : filt X 0 = ⊥ := by simp [filt]
    rw [h0, Submodule.bot_mul] at hz
    rw [(Submodule.mem_bot ℂ).1 hz]
    exact zero_mem _
  | succ d ih =>
    intro z hz hcz
    have hle : filt X (d + 1) * Subalgebra.toSubmodule B ≤
        LinearMap.range (wordMap X d) * Subalgebra.toSubmodule B ⊔
          filt X d * Subalgebra.toSubmodule B := by
      rw [← Submodule.sup_mul]
      exact mul_mono_left (filt_succ d)
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (hle hz)
    obtain ⟨r, b, M, hbB, rfl⟩ := exists_Phi B d hx
    have hb : ∀ k i j, X i j * b k = b k * X i j := fun k => hB _ (hbB k)
    let S : Set (Matrix ((Fin d → Fin n) × Fin r) ((Fin d → Fin n) × Fin r) ℂ) :=
      Set.range fun p : Fin n × Fin n => blockDiagonal fun _ : Fin r => polar n d p.1 p.2
    let N := (filt X d * Subalgebra.toSubmodule B).comap (Phi X d b)
    have hS : ∀ x ∈ S, xᴴ ∈ S := by
      rintro _ ⟨p, rfl⟩
      exact ⟨(p.2, p.1), by simp [blockDiagonal_conjTranspose, polar_conjTranspose]⟩
    have hN : ∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N := by
      rintro _ ⟨p, rfl⟩ y' hy'
      show Phi X d b (_ * _ - _ * _) ∈ filt X d * Subalgebra.toSubmodule B
      dsimp only
      rw [Phi_ad hX d b hb]
      exact filtB_ad hX B hB d p.1 p.2 hy'
    have hM : ∀ x ∈ S, x * M - M * x ∈ N := by
      rintro _ ⟨p, rfl⟩
      show Phi X d b (_ * _ - _ * _) ∈ filt X d * Subalgebra.toSubmodule B
      dsimp only
      rw [Phi_ad hX d b hb]
      have e := hcz p.1 p.2
      have : X p.1 p.2 * Phi X d b M - Phi X d b M * X p.1 p.2 =
          -(X p.1 p.2 * y - y * X p.1 p.2) := by
        rw [mul_add, add_mul] at e
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, add_comm (y * X p.1 p.2)]
        exact e
      rw [this]
      exact neg_mem (filtB_ad hX B hB d p.1 p.2 hy)
    obtain ⟨M₀, hMM₀, hM₀⟩ := GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _ S N hS hN M hM
    have h2 : ∀ k i j, polar n d i j * M₀.blockDiag k = M₀.blockDiag k * polar n d i j := by
      intro k i j
      have e := congrArg (fun Q => Q.blockDiag k) (hM₀ _ ⟨(i, j), rfl⟩)
      simpa [blockDiag_left, blockDiag_right] using e
    choose c hcG hcf using fun k => word_of_comm hX d (M₀.blockDiag k) (h2 k)
    have huT : ∑ k, c k * b k ∈ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B :=
      Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _
        ((le_sup_left : Algebra.adjoin ℂ (Set.range (gelfA X)) ≤ _ ⊔ B) (hcG k))
        ((le_sup_right : B ≤ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B) (hbB k))
    have hw : Phi X d b M + y - ∑ k, c k * b k = Phi X d b (M - M₀) + y +
        ∑ k, (wordMap X d (M₀.blockDiag k) - c k) * b k := by
      rw [map_sub, Phi_apply d b M₀]
      simp only [sub_mul, Finset.sum_sub_distrib]
      abel
    have hwmem : Phi X d b M + y - ∑ k, c k * b k ∈ filt X d * Subalgebra.toSubmodule B := by
      rw [hw]
      exact add_mem (add_mem hMM₀ hy)
        (Submodule.sum_mem _ fun k _ => Submodule.mul_mem_mul (hcf k) (hbB k))
    have hucomm : ∀ i j, X i j * ∑ k, c k * b k = (∑ k, c k * b k) * X i j := by
      intro i j
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, gelf_adjoin_comm hX (hcG k) i j, mul_assoc, hb k i j, ← mul_assoc]
    have hwcomm : ∀ i j, X i j * (Phi X d b M + y - ∑ k, c k * b k) =
        (Phi X d b M + y - ∑ k, c k * b k) * X i j := by
      intro i j
      rw [mul_sub, sub_mul, hcz i j, hucomm i j]
    have hmem := ih _ hwmem hwcomm
    have e : Phi X d b M + y = (Phi X d b M + y - ∑ k, c k * b k) + ∑ k, c k * b k := by abel
    rw [e]
    exact add_mem hmem huT

/- English proof (translation)
Establish `hcomm : ∀ a ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2), ∀ b ∈ B, a * b = b * a`. Introduce `a ha b hb`. Establish `hcen : a ∈ Subalgebra.centralizer ℂ {b}`. Use `Algebra.adjoin_le ?_ ha` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`. Introduce and unpack `g rfl`. Conclude with `(hB g hb p.1 p.2).symm`. Conclude with `((Subalgebra.mem_centralizer_iff ℂ).1 hcen b rfl).symm`. Establish `hz'` using `mem_mul_of_sup _ B hcomm hz`.

Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d, z ∈ filt X d * Subalgebra.toSubmodule B := by`. Use `Submodule.mul_induction_on hz' ?_ ?_` and prove the remaining obligations. Introduce `m hm b hb`. Take `⟨d, hd⟩` from `exists_filt (show m ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) from hm)`. Conclude with `⟨d, Submodule.mul_mem_mul hd hb⟩`.

Introduce and unpack `x y ⟨d₁, h₁⟩ ⟨d₂, h₂⟩`. Conclude with `⟨max d₁ d₂, add_mem (mul_mono_left (filt_mono (le_max_left _ _)) h₁) (mul_mono_left (filt_mono (le_max_right _ _)) h₂)⟩`. Conclude with `central_of_filtB hX B hB d z hd hc`.
-/
private theorem main (hX : GlRel X) (B : Subalgebra ℂ A)
    (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j) (z : A)
    (hz : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) ⊔ B)
    (hc : ∀ i j, X i j * z = z * X i j) : z ∈ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B := by
  have hcomm : ∀ a ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2),
      ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have hcen : a ∈ Subalgebra.centralizer ℂ {b} := by
      refine Algebra.adjoin_le ?_ ha
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro g rfl
      exact (hB g hb p.1 p.2).symm
    exact ((Subalgebra.mem_centralizer_iff ℂ).1 hcen b rfl).symm
  have hz' := mem_mul_of_sup _ B hcomm hz
  obtain ⟨d, hd⟩ : ∃ d, z ∈ filt X d * Subalgebra.toSubmodule B := by
    refine Submodule.mul_induction_on hz' ?_ ?_
    · intro m hm b hb
      obtain ⟨d, hd⟩ := exists_filt (show m ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) from hm)
      exact ⟨d, Submodule.mul_mem_mul hd hb⟩
    · rintro x y ⟨d₁, h₁⟩ ⟨d₂, h₂⟩
      exact ⟨max d₁ d₂, add_mem (mul_mono_left (filt_mono (le_max_left _ _)) h₁)
        (mul_mono_left (filt_mono (le_max_right _ _)) h₂)⟩
  exact central_of_filtB hX B hB d z hd hc

end UpperTheory.AdjointWordCommutation

/- English proof (translation)
Introduce `A _ _ n X hX B hB z hz hc`. Conclude with `UpperTheory.AdjointWordCommutation.main hX B hB z hz hc`.
-/
theorem UpperTheory.mem_adjoin_gelfand_sup_of_commute_glGenerators :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), GlRel X → ∀ B : Subalgebra ℂ A, (∀ b ∈ B, ∀ i j, X i j * b = b * X i j) → ∀ z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) ⊔ B, (∀ i j, X i j * z = z * X i j) → z ∈ Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA X)) ⊔ B := by
  intro A _ _ n X hX B hB z hz hc
  exact UpperTheory.AdjointWordCommutation.main hX B hB z hz hc
