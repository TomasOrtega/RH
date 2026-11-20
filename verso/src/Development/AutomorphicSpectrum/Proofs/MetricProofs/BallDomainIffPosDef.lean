import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.MemBall

/- English proof (translation)
Establish `h0 : 0 ≤ star x ⬝ᵥ x` using `dotProduct_star_self_nonneg x`. Establish `hz` using `Complex.nonneg_iff.1 h0`. Establish `heq : star x ⬝ᵥ x = (((star x ⬝ᵥ x).re : ℝ) : ℂ)`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Simplify using `using hz.2.symm`. Use `⟨(star x ⬝ᵥ x).re, hz.1, heq, fun hx => ?_⟩` and prove the remaining obligations. Establish `hp : 0 < star x ⬝ᵥ x` using `dotProduct_star_self_pos_iff.2 hx`. Conclude with `(Complex.pos_iff.1 hp).1`.
-/
theorem exists_sqLen {m : Type} [Fintype m] (x : m → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ star x ⬝ᵥ x = (r : ℂ) ∧ (x ≠ 0 → 0 < r) := by
  have h0 : 0 ≤ star x ⬝ᵥ x := dotProduct_star_self_nonneg x
  have hz := Complex.nonneg_iff.1 h0
  have heq : star x ⬝ᵥ x = (((star x ⬝ᵥ x).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz.2.symm
  refine ⟨(star x ⬝ᵥ x).re, hz.1, heq, fun hx => ?_⟩
  have hp : 0 < star x ⬝ᵥ x := dotProduct_star_self_pos_iff.2 hx
  exact (Complex.pos_iff.1 hp).1

/- English proof (translation)
Rewrite using `[sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]`.
-/
theorem qf_one_sub {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) (w : n → ℂ) :
    star w ⬝ᵥ ((1 - Aᴴ * A) *ᵥ w) = star w ⬝ᵥ w - star (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := by
  rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]

/- English proof (translation)
Use `posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩` and prove the remaining obligations. Simplify using `[IsHermitian, conjTranspose_sub, conjTranspose_mul]`. Establish `hq` using `qf_one_sub Aᴴ v`. Rewrite `hq` using `[conjTranspose_conjTranspose]`. Rewrite using `[hq]`.

Take `⟨c, hc0, hc, hcp⟩` from `exists_sqLen v`. Take `⟨a, ha0, ha, hap⟩` from `exists_sqLen (Aᴴ *ᵥ v)`. Rewrite using `[hc, ha, ← Complex.ofReal_sub]`. Establish `hcpos` using `hcp hv`. It suffices to establish `hac : a < c from by exact_mod_cast sub_pos.2 hac`.

Distinguish the cases in `hw : Aᴴ *ᵥ v = 0`. Establish `: a = 0`. Establish `: (a : ℂ) = 0` using `by rw [← ha, hw]; simp`. Conclude with `this` after adjusting the coercions. Rewrite using `[this]`.

Conclude with `hcpos`. Establish `hapos` using `hap hw`. Use `set w := Aᴴ *ᵥ v with hwdef`. Take `⟨b, hb0, hb, -⟩` from `exists_sqLen (A *ᵥ w)`. Establish `hba : b < a`.

Establish `h1` using `(posDef_iff_dotProduct_mulVec.1 h).2 hw`. Rewrite `h1` using `[qf_one_sub, ha, hb, ← Complex.ofReal_sub]`. Establish `: (0 : ℝ) < a - b` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpv : star (A *ᵥ w) ⬝ᵥ v = (a : ℂ)`.

Rewrite using `[star_mulVec, ← dotProduct_mulVec, ← hwdef, ha]`. Establish `hvp : star v ⬝ᵥ (A *ᵥ w) = (a : ℂ)`. Rewrite using `[dotProduct_mulVec, ← star_star (star v ᵥ* A)]`. Rewrite using `[star_vecMul, star_star, ← hwdef, ha]`. Establish `hu` using `dotProduct_star_self_nonneg ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v)`.

Establish `hexp : star ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v) ⬝ᵥ ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v) = ((c * (c * b - a ^ 2) : ℝ) : ℂ)`. Simplify using `only [star_sub, star_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, hb, hc, hpv, hvp]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hu` using `[hexp]`. Establish `hu' : 0 ≤ c * (c * b - a ^ 2)` using `by exact_mod_cast hu`. Establish `h2 : 0 ≤ c * b - a ^ 2` using `nonneg_of_mul_nonneg_right hu' hcpos`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem posDef_adjoint {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ)
    (h : (1 - Aᴴ * A).PosDef) : (1 - A * Aᴴ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩
  · simp [IsHermitian, conjTranspose_sub, conjTranspose_mul]
  have hq := qf_one_sub Aᴴ v
  rw [conjTranspose_conjTranspose] at hq
  rw [hq]
  obtain ⟨c, hc0, hc, hcp⟩ := exists_sqLen v
  obtain ⟨a, ha0, ha, hap⟩ := exists_sqLen (Aᴴ *ᵥ v)
  rw [hc, ha, ← Complex.ofReal_sub]
  have hcpos := hcp hv
  suffices hac : a < c from by exact_mod_cast sub_pos.2 hac
  by_cases hw : Aᴴ *ᵥ v = 0
  · have : a = 0 := by
      have : (a : ℂ) = 0 := by rw [← ha, hw]; simp
      exact_mod_cast this
    rw [this]; exact hcpos
  have hapos := hap hw
  set w := Aᴴ *ᵥ v with hwdef
  obtain ⟨b, hb0, hb, -⟩ := exists_sqLen (A *ᵥ w)
  have hba : b < a := by
    have h1 := (posDef_iff_dotProduct_mulVec.1 h).2 hw
    rw [qf_one_sub, ha, hb, ← Complex.ofReal_sub] at h1
    have : (0 : ℝ) < a - b := by exact_mod_cast h1
    linarith
  have hpv : star (A *ᵥ w) ⬝ᵥ v = (a : ℂ) := by
    rw [star_mulVec, ← dotProduct_mulVec, ← hwdef, ha]
  have hvp : star v ⬝ᵥ (A *ᵥ w) = (a : ℂ) := by
    rw [dotProduct_mulVec, ← star_star (star v ᵥ* A)]
    rw [star_vecMul, star_star, ← hwdef, ha]
  have hu := dotProduct_star_self_nonneg ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v)
  have hexp : star ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v) ⬝ᵥ ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v) =
      ((c * (c * b - a ^ 2) : ℝ) : ℂ) := by
    simp only [star_sub, star_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, hb, hc, hpv, hvp]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    push_cast
    ring
  rw [hexp] at hu
  have hu' : 0 ≤ c * (c * b - a ^ 2) := by exact_mod_cast hu
  have h2 : 0 ≤ c * b - a ^ 2 := nonneg_of_mul_nonneg_right hu' hcpos
  nlinarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨posDef_adjoint A, fun h => by simpa using posDef_adjoint Aᴴ (by simpa using h)⟩`.
-/
theorem posDef_adjoint_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    (1 - Aᴴ * A).PosDef ↔ (1 - A * Aᴴ).PosDef :=
  ⟨posDef_adjoint A, fun h => by simpa using posDef_adjoint Aᴴ (by simpa using h)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k`. Establish `hinj : Function.Injective (fun i : m => (i, k))` using `fun a b hab => (Prod.ext_iff.1 hab).1`. Use `h.submatrix hinj` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `a b`. Simplify using `[blockDiagonal_apply]`. Introduce `h`. Use `posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[IsHermitian, blockDiagonal_conjTranspose]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `(h k).1`. Establish `hmv : ∀ i k, (blockDiagonal M *ᵥ x) (i, k) = (M k *ᵥ fun i => x (i, k)) i`. Introduce `i k`.

Simplify using `only [mulVec, dotProduct, Fintype.sum_prod_type_right, blockDiagonal_apply]`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Ne.symm hc]`.

Simplify using the standard rewrite rules. Establish `hsum : star x ⬝ᵥ (blockDiagonal M *ᵥ x) = ∑ k, star (fun i => x (i, k)) ⬝ᵥ (M k *ᵥ fun i => x (i, k))`. Simplify using `only [dotProduct, Fintype.sum_prod_type_right, hmv]`. Both sides reduce to the same expression. Rewrite using `[hsum]`.

Take `⟨⟨i, k⟩, hp⟩` from `Function.ne_iff.1 hx`. Use `Finset.sum_pos' (fun k _ => (h k).posSemidef.dotProduct_mulVec_nonneg _) ⟨k, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `(posDef_iff_dotProduct_mulVec.1 (h k)).2 (Function.ne_iff.2 ⟨i, ?_⟩)` and prove the remaining obligations. Simplify using `using hp`.
-/
theorem posDef_blockDiagonal_iff {m o : Type} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (M : o → Matrix m m ℂ) : (blockDiagonal M).PosDef ↔ ∀ k, (M k).PosDef := by
  constructor
  · intro h k
    have hinj : Function.Injective (fun i : m => (i, k)) := fun a b hab => (Prod.ext_iff.1 hab).1
    have := h.submatrix hinj
    convert this using 1
    ext a b
    simp [blockDiagonal_apply]
  · intro h
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, blockDiagonal_conjTranspose]
      congr 1
      funext k
      exact (h k).1
    have hmv : ∀ i k, (blockDiagonal M *ᵥ x) (i, k) = (M k *ᵥ fun i => x (i, k)) i := by
      intro i k
      simp only [mulVec, dotProduct, Fintype.sum_prod_type_right, blockDiagonal_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    have hsum : star x ⬝ᵥ (blockDiagonal M *ᵥ x) =
        ∑ k, star (fun i => x (i, k)) ⬝ᵥ (M k *ᵥ fun i => x (i, k)) := by
      simp only [dotProduct, Fintype.sum_prod_type_right, hmv]
      rfl
    rw [hsum]
    obtain ⟨⟨i, k⟩, hp⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun k _ => (h k).posSemidef.dotProduct_mulVec_nonneg _) ⟨k, Finset.mem_univ _, ?_⟩
    refine (posDef_iff_dotProduct_mulVec.1 (h k)).2 (Function.ne_iff.2 ⟨i, ?_⟩)
    simpa using hp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Prove the components needed by the constructor for the conclusion. Establish `h1 : (fromBlocks A 0 0 D).submatrix (Sum.inl : m → m ⊕ n) Sum.inl = A`. Use extensionality with `a c`.

Simplify using the standard rewrite rules. Conclude with `h1 ▸ h.submatrix Sum.inl_injective`. Establish `h1 : (fromBlocks A 0 0 D).submatrix (Sum.inr : n → m ⊕ n) Sum.inr = D`. Use extensionality with `a c`. Simplify using the standard rewrite rules.

Conclude with `h1 ▸ h.submatrix Sum.inr_injective`. Introduce and unpack `⟨hA, hD⟩`. Use `posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[IsHermitian, fromBlocks_conjTranspose, hA.1, hD.1]`. Simplify using the standard rewrite rules.

Establish `hsum : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) = star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr))`. Rewrite using `[fromBlocks_mulVec]`. Simplify using `[dotProduct, Fintype.sum_sum_type]`. Rewrite using `[hsum]`. Establish `h1` using `hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)`.

Establish `h2` using `hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)`. Take `⟨p, hp⟩` from `Function.ne_iff.1 hx`. Break down `p with i | i` into its components or cases. Use `add_pos_of_pos_of_nonneg ((posDef_iff_dotProduct_mulVec.1 hA).2 (Function.ne_iff.2 ⟨i, ?_⟩)) h2` and prove the remaining obligations. Simplify using `using hp`.

Use `add_pos_of_nonneg_of_pos h1 ((posDef_iff_dotProduct_mulVec.1 hD).2 (Function.ne_iff.2 ⟨i, ?_⟩))` and prove the remaining obligations. Simplify using `using hp`.
-/
theorem posDef_fromBlocks_diag_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) : (fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  constructor
  · intro h
    constructor
    · have h1 : (fromBlocks A 0 0 D).submatrix (Sum.inl : m → m ⊕ n) Sum.inl = A := by
        ext a c; simp
      exact h1 ▸ h.submatrix Sum.inl_injective
    · have h1 : (fromBlocks A 0 0 D).submatrix (Sum.inr : n → m ⊕ n) Sum.inr = D := by
        ext a c; simp
      exact h1 ▸ h.submatrix Sum.inr_injective
  · rintro ⟨hA, hD⟩
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, fromBlocks_conjTranspose, hA.1, hD.1]
      simp
    have hsum : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
      rw [fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type]
    rw [hsum]
    have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
    rcases p with i | i
    · refine add_pos_of_pos_of_nonneg ((posDef_iff_dotProduct_mulVec.1 hA).2 (Function.ne_iff.2 ⟨i, ?_⟩)) h2
      simpa using hp
    · refine add_pos_of_nonneg_of_pos h1 ((posDef_iff_dotProduct_mulVec.1 hD).2 (Function.ne_iff.2 ⟨i, ?_⟩))
      simpa using hp

/- English proof (translation)
Rewrite using `[posDef_adjoint_iff Z, ← PosDef.transpose_iff (M := 1 - Z * Zᴴ)]`. Establish `: (1 - Z * Zᴴ)ᵀ = 1 - Zᵀᴴ * Zᵀ`. Rewrite using `[transpose_sub, transpose_one, transpose_mul]`. Use `congr 2`. Rewrite using `[this]`.
-/
theorem posDef_transpose_block {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (Z : Matrix m n ℂ) :
    (1 - Zᵀᴴ * Zᵀ).PosDef ↔ (1 - Zᴴ * Z).PosDef := by
  rw [posDef_adjoint_iff Z, ← PosDef.transpose_iff (M := 1 - Z * Zᴴ)]
  have : (1 - Z * Zᴴ)ᵀ = 1 - Zᵀᴴ * Zᵀ := by
    rw [transpose_sub, transpose_one, transpose_mul]
    congr 2
  rw [this]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.MemBall

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

open MemBall in

/- English proof (translation)
Establish `hblk : (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t = blockDiagonal fun τ => fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0 (1 - (ballMat q t τ)ᵀᴴ * (ballMat q t τ)ᵀ)`. Rewrite using `[bigZ, blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.sub_apply, Pi.one_apply]`.

Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply]`. Simplify using `only [conjTranspose_zero, mul_zero, zero_mul, add_zero, zero_add, ← fromBlocks_one]`. Apply the tactic sequence `ext (a | a) (c | c) <;> simp [Matrix.one_apply]`. Establish `hsub : (1 : Matrix (Fin g) (Fin g) ℂ) - (bigZe e q t)ᴴ * bigZe e q t = ((1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm`. Rewrite using `[bigZe, conjTranspose_submatrix, submatrix_mul_equiv]`.

Use extensionality with `a c`. Simplify using `[Matrix.one_apply]`. Establish `hequiv : ((1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm).PosDef ↔ (1 - (bigZ q t)ᴴ * bigZ q t).PosDef` using `⟨fun h => by simpa using h.submatrix e.injective, fun h => h.submatrix e.symm.injective⟩`. Rewrite using `[hsub, hequiv, hblk, posDef_blockDiagonal_iff]`. Simplify using `only [posDef_fromBlocks_diag_iff, posDef_transpose_block, and_self]`.

Both sides reduce to the same expression.
-/
theorem mem_ballDom_iff_posDef_bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    t ∈ ballDom q ↔ (1 - (bigZe e q t)ᴴ * bigZe e q t).PosDef := by
  have hblk : (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t =
      blockDiagonal fun τ => fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0
        (1 - (ballMat q t τ)ᵀᴴ * (ballMat q t τ)ᵀ) := by
    rw [bigZ, blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]
    congr 1
    funext τ
    simp only [Pi.sub_apply, Pi.one_apply]
    rw [fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [conjTranspose_zero, mul_zero, zero_mul, add_zero, zero_add, ← fromBlocks_one]
    ext (a | a) (c | c) <;> simp [Matrix.one_apply]
  have hsub : (1 : Matrix (Fin g) (Fin g) ℂ) - (bigZe e q t)ᴴ * bigZe e q t =
      ((1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm := by
    rw [bigZe, conjTranspose_submatrix, submatrix_mul_equiv]
    ext a c
    simp [Matrix.one_apply]
  have hequiv : ((1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm).PosDef ↔
      (1 - (bigZ q t)ᴴ * bigZ q t).PosDef :=
    ⟨fun h => by simpa using h.submatrix e.injective, fun h => h.submatrix e.symm.injective⟩
  rw [hsub, hequiv, hblk, posDef_blockDiagonal_iff]
  simp only [posDef_fromBlocks_diag_iff, posDef_transpose_block, and_self]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
