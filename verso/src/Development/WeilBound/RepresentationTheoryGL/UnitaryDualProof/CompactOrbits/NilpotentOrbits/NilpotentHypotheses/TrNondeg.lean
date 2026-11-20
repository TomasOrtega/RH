import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def qL {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) :
    Matrix (Fin n) (Fin n) k →ₗ[k] (Fin (Module.finrank k Z) → k) :=
  LinearMap.pi fun i => (Matrix.traceLinearMap (Fin n) k k) ∘ₗ
    LinearMap.mulLeft k (((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qL_apply {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) :
    qL k Z x = qZ Z x := rfl

/- English proof (translation)
Use `haveI hred : IsReduced Z := hZ.2`. Use `letI : CommRing Z := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }`. Use `haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z`. Take `⟨m, y, hy⟩` from `IsArtinian.exists_pow_succ_smul_dvd c (1 : Z)`. Simplify using `only [smul_eq_mul, mul_one] at hy`.

Establish `hpow : ∀ j : ℕ, c ^ m * (c * y) ^ j = c ^ m`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcm : c ^ m ≠ 0` using `fun h0 => hc (IsReduced.eq_zero c ⟨m, h0⟩)`. Establish `he : c ^ m * y ^ (m + 1) * c = (c * y) ^ (m + 1)` using `by ring`. Use `⟨c ^ m * y ^ (m + 1), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsIdempotentElem, he]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `h0`. Apply `hcm` to reduce the goal to its premises. Rewrite `h0` using `[he]`. Rewrite using `[← hpow (m + 1), h0, mul_zero]`.
-/
theorem exists_idem {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (c : Z) (hc : c ≠ 0) :
    ∃ b : Z, IsIdempotentElem (b * c) ∧ b * c ≠ 0 := by
  haveI hred : IsReduced Z := hZ.2
  letI : CommRing Z := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  obtain ⟨m, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd c (1 : Z)
  simp only [smul_eq_mul, mul_one] at hy
  have hpow : ∀ j : ℕ, c ^ m * (c * y) ^ j = c ^ m := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc c ^ m * (c * y) ^ (j + 1) = c ^ (m + 1) * y * (c * y) ^ j := by ring
        _ = c ^ m := by rw [hy, ih]
  have hcm : c ^ m ≠ 0 := fun h0 => hc (IsReduced.eq_zero c ⟨m, h0⟩)
  have he : c ^ m * y ^ (m + 1) * c = (c * y) ^ (m + 1) := by ring
  refine ⟨c ^ m * y ^ (m + 1), ?_, ?_⟩
  · rw [IsIdempotentElem, he]
    calc (c * y) ^ (m + 1) * (c * y) ^ (m + 1) = c * y ^ (m + 1) * (c ^ m * (c * y) ^ (m + 1)) := by ring
      _ = (c * y) ^ (m + 1) := by rw [hpow]; ring
  · intro h0
    apply hcm
    rw [he] at h0
    rw [← hpow (m + 1), h0, mul_zero]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Take `⟨b, hb, hb0⟩` from `exists_idem k Z hZ c hc`. Take `⟨M, hMdef⟩ : ∃ M : Matrix (Fin n) (Fin n) k, M = ((b * c : Z) : Matrix (Fin n) (Fin n) k)` from `⟨_, rfl⟩`. Establish `hM : IsIdempotentElem M`. Rewrite using `[hMdef, IsIdempotentElem, ← Subalgebra.coe_mul, hb]`.

Establish `htr : M.trace = 0`. Rewrite using `[hMdef, Subalgebra.coe_mul]`. Conclude with `h b`. Establish `hf : IsIdempotentElem (Matrix.toLin' M)` using `by show Matrix.toLin' M ∘ₗ Matrix.toLin' M = Matrix.toLin' M`. Rewrite using `[← Matrix.toLin'_mul, hM]`.

Establish `htf : LinearMap.trace k (Fin n → k) (Matrix.toLin' M) = 0`. Rewrite using `[LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Conclude with `htr`. Establish `h0` using `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hf htf`. Apply `hb0` to reduce the goal to its premises.

Establish `hM0 : M = 0` using `Matrix.toLin'.injective (by rw [h0, map_zero])`. Conclude with `Subtype.ext (by rw [← hMdef, hM0]; rfl)`.
-/
theorem tr_nondeg [CharZero k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (c : Z)
    (h : ∀ b : Z, trace ((b : Matrix (Fin n) (Fin n) k) * (c : Matrix (Fin n) (Fin n) k)) = 0) : c = 0 := by
  by_contra hc
  obtain ⟨b, hb, hb0⟩ := exists_idem k Z hZ c hc
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin n) (Fin n) k, M = ((b * c : Z) : Matrix (Fin n) (Fin n) k) := ⟨_, rfl⟩
  have hM : IsIdempotentElem M := by
    rw [hMdef, IsIdempotentElem, ← Subalgebra.coe_mul, hb]
  have htr : M.trace = 0 := by
    rw [hMdef, Subalgebra.coe_mul]; exact h b
  have hf : IsIdempotentElem (Matrix.toLin' M) := by
    show Matrix.toLin' M ∘ₗ Matrix.toLin' M = Matrix.toLin' M
    rw [← Matrix.toLin'_mul, hM]
  have htf : LinearMap.trace k (Fin n → k) (Matrix.toLin' M) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    exact htr
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hf htf
  apply hb0
  have hM0 : M = 0 := Matrix.toLin'.injective (by rw [h0, map_zero])
  exact Subtype.ext (by rw [← hMdef, hM0]; rfl)

/- English proof (translation)
Set `φ : Z →ₗ[k] (Fin (Module.finrank k Z) → k)` to `qL k Z ∘ₗ Z.val.toLinearMap`. Establish `hφ : ∀ z : Z, φ z = qZ Z z` using `fun z => qL_apply k Z z`. Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`.

Rewrite `hz` using `[hφ]`. Apply `tr_nondeg k Z hZ z` to reduce the goal to its premises. Introduce `b`. Set `ψ : Z →ₗ[k] k` to `Matrix.traceLinearMap (Fin n) k k ∘ₗ LinearMap.mulRight k (z : Matrix (Fin n) (Fin n) k) ∘ₗ Z.val.toLinearMap`. Establish `hψ : ψ = 0`.

Use `(Module.finBasis k Z).ext fun i => ?_` and prove the remaining obligations. Conclude with `congrFun hz i`. Conclude with `LinearMap.congr_fun hψ b`. Establish `hdim : Module.finrank k Z = Module.finrank k (Fin (Module.finrank k Z) → k)` using `by simp`. Establish `hsurj : Function.Surjective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj`.

Set `e` to `LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩`. Establish `he : ∀ y, φ (e.symm y) = y` using `fun y => e.apply_symm_apply y`. Establish `key : ∀ x, qZ Z ((e.symm (qL k Z x) : Z) : Matrix (Fin n) (Fin n) k) = qZ Z x`. Introduce `x`. Rewrite using `[← hφ, he, qL_apply]`.

Use `⟨Z.val.toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ qL k Z, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x show piZ Z x = ((e.symm (qL k Z x) : Z) : Matrix (Fin n) (Fin n) k)`. Establish `h : ∃ c ∈ Z, qZ Z c = qZ Z x` using `⟨_, (e.symm (qL k Z x)).2, key x⟩`. Unfold `piZ`. Rewrite using `[dif_pos h]`.

Establish `hc` using `h.choose_spec`. Establish `hq : (⟨h.choose, hc.1⟩ : Z) = e.symm (qL k Z x)` using `hinj (by rw [hφ, hφ]; exact hc.2.trans (key x).symm)`. Conclude with `congrArg Subtype.val hq`. Introduce `x`. Conclude with `(e.symm (qL k Z x)).2`.

Introduce `x`. Conclude with `key x`. Introduce `c hc`. Establish `hs : e.symm (qL k Z c) = ⟨c, hc⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Use `show ((e.symm (qL k Z c) : Z) : Matrix (Fin n) (Fin n) k) = c`. Rewrite using `[hs]`.
-/
theorem piZ_lin' [CharZero k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    ∃ L : Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k,
      (∀ x, piZ Z x = L x) ∧ (∀ x, L x ∈ Z) ∧ (∀ x, qZ Z (L x) = qZ Z x) ∧ ∀ c ∈ Z, L c = c := by
  let φ : Z →ₗ[k] (Fin (Module.finrank k Z) → k) := qL k Z ∘ₗ Z.val.toLinearMap
  have hφ : ∀ z : Z, φ z = qZ Z z := fun z => qL_apply k Z z
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [hφ] at hz
    apply tr_nondeg k Z hZ z
    intro b
    let ψ : Z →ₗ[k] k := Matrix.traceLinearMap (Fin n) k k ∘ₗ
      LinearMap.mulRight k (z : Matrix (Fin n) (Fin n) k) ∘ₗ Z.val.toLinearMap
    have hψ : ψ = 0 := by
      refine (Module.finBasis k Z).ext fun i => ?_
      exact congrFun hz i
    exact LinearMap.congr_fun hψ b
  have hdim : Module.finrank k Z = Module.finrank k (Fin (Module.finrank k Z) → k) := by simp
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ y, φ (e.symm y) = y := fun y => e.apply_symm_apply y
  have key : ∀ x, qZ Z ((e.symm (qL k Z x) : Z) : Matrix (Fin n) (Fin n) k) = qZ Z x := by
    intro x
    rw [← hφ, he, qL_apply]
  refine ⟨Z.val.toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ qL k Z, ?_, ?_, ?_, ?_⟩
  · intro x
    show piZ Z x = ((e.symm (qL k Z x) : Z) : Matrix (Fin n) (Fin n) k)
    have h : ∃ c ∈ Z, qZ Z c = qZ Z x := ⟨_, (e.symm (qL k Z x)).2, key x⟩
    unfold piZ
    rw [dif_pos h]
    have hc := h.choose_spec
    have hq : (⟨h.choose, hc.1⟩ : Z) = e.symm (qL k Z x) :=
      hinj (by rw [hφ, hφ]; exact hc.2.trans (key x).symm)
    exact congrArg Subtype.val hq
  · intro x
    exact (e.symm (qL k Z x)).2
  · intro x
    exact key x
  · intro c hc
    have hs : e.symm (qL k Z c) = ⟨c, hc⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    show ((e.symm (qL k Z c) : Z) : Matrix (Fin n) (Fin n) k) = c
    rw [hs]

end PositivityTheory.RgUd.T.Nil.Asm
