import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompA

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DecH

variable {n : ℕ}

/- English proof (translation)
Establish `hrel : Cᴴ * A = Aᴴ * C`. Establish `h'` using `h`. Unfold `PositivityTheory.Rg.Sw.InG PositivityTheory.Rg.Sw.JJ at h'`. Rewrite `h'` using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Establish `h1` using `(fromBlocks_inj.1 h').1`.

Simplify using `at h1`. Conclude with `neg_add_eq_zero.1 h1`. Establish `hM : (A - Complex.I • C)ᴴ * (A - Complex.I • C) = Aᴴ * A + Cᴴ * C`. Simplify using `only [conjTranspose_sub, conjTranspose_smul, Complex.star_def, Complex.conj_I, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, hrel]`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp [Complex.I_sq]`.

Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `exists_mulVec_eq_zero_iff.2 hdet`. Establish `hv2 : (Aᴴ * A + Cᴴ * C) *ᵥ v = 0`. Rewrite using `[← hM, ← mulVec_mulVec, hv, mulVec_zero]`. Use `set V : Fin n ⊕ Fin n → ℂ := Sum.elim v 0 with hV`.

Use `set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromBlocks A 0 C 0 with hPdef`. Establish `hP : (Pᴴ * P) *ᵥ V = 0`. Rewrite using `[hPdef, fromBlocks_conjTranspose, fromBlocks_multiply]`. Simplify using `[hV, fromBlocks_mulVec, hv2]`. Establish `hP2` using `(conjTranspose_mul_self_mulVec_eq_zero _ _).1 hP`.

Establish `hg : fromBlocks A B C D *ᵥ V = 0`. Use `hP2` as an intermediate fact. Simplify using `[hV, hPdef, fromBlocks_mulVec] at this ⊢`. Conclude with `this`. Establish `hV0 : V ≠ 0`.

Introduce `h0`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun h0 (Sum.inl i)` as an intermediate fact. Simplify `this` using `[hV]`.

Conclude with `hu.ne_zero (exists_mulVec_eq_zero_iff.1 ⟨V, hV0, hg⟩)`.
-/
theorem det_sub_I_smul_ne_zero {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D))
    (hu : IsUnit (fromBlocks A B C D).det) : (A - Complex.I • C).det ≠ 0 := by
  classical
  have hrel : Cᴴ * A = Aᴴ * C := by
    have h' := h
    unfold PositivityTheory.Rg.Sw.InG PositivityTheory.Rg.Sw.JJ at h'
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h'
    have h1 := (fromBlocks_inj.1 h').1
    simp at h1
    exact neg_add_eq_zero.1 h1
  have hM : (A - Complex.I • C)ᴴ * (A - Complex.I • C) = Aᴴ * A + Cᴴ * C := by
    simp only [conjTranspose_sub, conjTranspose_smul, Complex.star_def, Complex.conj_I,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, hrel]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  have hv2 : (Aᴴ * A + Cᴴ * C) *ᵥ v = 0 := by
    rw [← hM, ← mulVec_mulVec, hv, mulVec_zero]
  set V : Fin n ⊕ Fin n → ℂ := Sum.elim v 0 with hV
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromBlocks A 0 C 0 with hPdef
  have hP : (Pᴴ * P) *ᵥ V = 0 := by
    rw [hPdef, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp [hV, fromBlocks_mulVec, hv2]
  have hP2 := (conjTranspose_mul_self_mulVec_eq_zero _ _).1 hP
  have hg : fromBlocks A B C D *ᵥ V = 0 := by
    have := hP2
    simp [hV, hPdef, fromBlocks_mulVec] at this ⊢
    exact this
  have hV0 : V ≠ 0 := by
    intro h0
    apply hv0
    funext i
    have := congrFun h0 (Sum.inl i)
    simpa [hV] using this
  exact hu.ne_zero (exists_mulVec_eq_zero_iff.1 ⟨V, hV0, hg⟩)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Use `set p : Polynomial ℂ := ((Polynomial.X : Polynomial ℂ) • (-C).map Polynomial.C + A.map Polynomial.C).det with hp`. Establish `heval : ∀ z : ℂ, p.eval z = (A - z • C).det`. Introduce `z`.

Rewrite using `[hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish `hp0 : p = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Apply `Set.Infinite.mono _ (Set.infinite_range_of_injective Complex.ofReal_injective)` to reduce the goal to its premises. Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[Set.mem_setOf_eq, Polynomial.IsRoot, heval]`.

Conclude with `hne t`. Apply `h` to reduce the goal to its premises. Use `heval Complex.I` as an intermediate fact. Rewrite `this` using `[hp0, Polynomial.eval_zero]`. Conclude with `this.symm`.
-/
theorem exists_real_det_ne_zero {A C : Matrix (Fin n) (Fin n) ℂ} (h : (A - Complex.I • C).det ≠ 0) :
    ∃ t : ℝ, (A - (t : ℂ) • C).det ≠ 0 := by
  classical
  by_contra hne
  push_neg at hne
  set p : Polynomial ℂ :=
    ((Polynomial.X : Polynomial ℂ) • (-C).map Polynomial.C + A.map Polynomial.C).det with hp
  have heval : ∀ z : ℂ, p.eval z = (A - z • C).det := by
    intro z
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨t, rfl⟩
    rw [Set.mem_setOf_eq, Polynomial.IsRoot, heval]
    exact hne t
  apply h
  have := heval Complex.I
  rw [hp0, Polynomial.eval_zero] at this
  exact this.symm

end PositivityTheory.Rg.Sw.Glob.DecH
