import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RefForm

/- English proof (translation)
Simplify using `[cT, Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {k : ℕ} (X Y : Matrix (Fin k) (Fin k) A) :
    cT σ (X * Y) = cT σ Y * cT σ X := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_cT_conj {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) : cT (starRingEnd ℂ) (cT (starRingEnd ℂ) X) = X := by
  ext i j; simp [cT]

/- English proof (translation)
Simplify using `only [cT, Matrix.det_transpose]`. Conclude with `((starRingEnd ℂ).map_det X).symm`.
-/
theorem det_cT_conj {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) : (cT (starRingEnd ℂ) X).det = starRingEnd ℂ X.det := by
  simp only [cT, Matrix.det_transpose]
  exact ((starRingEnd ℂ).map_det X).symm

/- English proof (translation)
Establish `: cT (starRingEnd ℂ) (Matrix.diagonal μ) = Matrix.diagonal (fun r => starRingEnd ℂ (μ r))`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[cT]`.

Simplify using `[cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]`. Rewrite using `[this, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `r`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ r]`.

Simplify using the standard rewrite rules.
-/
theorem cT_diag_mul_diag {k : ℕ} (μ : Fin k → ℂ) (hμ : ∀ r, ‖μ r‖ = 1) :
    cT (starRingEnd ℂ) (Matrix.diagonal μ) * Matrix.diagonal μ = 1 := by
  have : cT (starRingEnd ℂ) (Matrix.diagonal μ) = Matrix.diagonal (fun r => starRingEnd ℂ (μ r)) := by
    ext i j; by_cases h : i = j
    · subst h; simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [this, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext r
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ r]; simp

/- English proof (translation)
Use `set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom`. Establish `hστ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = starRingEnd ℂ (τ x)` using `fun τ x => IsCMField.complexEmbedding_complexConj E τ x`. Establish `hmapcT : ∀ (τ : E →+* ℂ) (X : Matrix (Fin n) (Fin n) E), (cT σ X).map τ = cT (starRingEnd ℂ) (X.map τ)`. Introduce `τ X`. Use extensionality with `i j`.

Simplify using `[cT, hστ]`. Take `⟨τ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) E => X.map τ₀)` using `Matrix.map_injective τ₀.injective`. Take `⟨W, μ, hW, hμ, hWγ, hH⟩` from `h τ₀`. Use `⟨?_, ?_, ?_, fun τ => ?_⟩` and prove the remaining obligations.

Apply `hinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(cT σ H).map τ₀ = H.map τ₀`. Rewrite using `[hmapcT, hH, cT_mul, cT_cT_conj]`. Introduce `h0`. Establish `: τ₀ H.det = 0` using `by rw [h0, map_zero]`.

Rewrite `this` using `[RingHom.map_det, RingHom.mapMatrix_apply, hH, Matrix.det_mul, det_cT_conj]`. Break down `mul_eq_zero.mp this with h1 | h1` into its components or cases. Conclude with `hW (by simpa using h1)`. Conclude with `hW h1`. Apply `hinj` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(cT σ γ * H * γ).map τ₀ = H.map τ₀`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hmapcT, hH]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = cT (starRingEnd ℂ) W * (cT (starRingEnd ℂ) (Matrix.diagonal μ) * Matrix.diagonal μ) * W := by`. Rewrite using `[hWγ, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT (starRingEnd ℂ) W * W := by rw [cT_diag_mul_diag μ hμ, Matrix.mul_one]`. Take `⟨W, μ, hW, -, -, hH⟩` from `h τ`.

Conclude with `⟨W, hW, hH⟩`.
-/
theorem assemble (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (γ H : Matrix (Fin n) (Fin n) E)
    (h : ∀ τ : E →+* ℂ, ∃ (W : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), W.det ≠ 0 ∧ (∀ r, ‖μ r‖ = 1) ∧
      W * γ.map τ = Matrix.diagonal μ * W ∧ H.map τ = cT (starRingEnd ℂ) W * W) :
    IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ * H * γ = H ∧
      (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) := by
  set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hστ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = starRingEnd ℂ (τ x) := fun τ x =>
    IsCMField.complexEmbedding_complexConj E τ x
  have hmapcT : ∀ (τ : E →+* ℂ) (X : Matrix (Fin n) (Fin n) E),
      (cT σ X).map τ = cT (starRingEnd ℂ) (X.map τ) := by
    intro τ X; ext i j; simp [cT, hστ]
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) E => X.map τ₀) :=
    Matrix.map_injective τ₀.injective
  obtain ⟨W, μ, hW, hμ, hWγ, hH⟩ := h τ₀
  refine ⟨?_, ?_, ?_, fun τ => ?_⟩
  · apply hinj
    change (cT σ H).map τ₀ = H.map τ₀
    rw [hmapcT, hH, cT_mul, cT_cT_conj]
  · intro h0
    have : τ₀ H.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hH, Matrix.det_mul, det_cT_conj] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hW (by simpa using h1)
    · exact hW h1
  · apply hinj
    change (cT σ γ * H * γ).map τ₀ = H.map τ₀
    rw [Matrix.map_mul, Matrix.map_mul, hmapcT, hH]
    calc cT (starRingEnd ℂ) (γ.map τ₀) * (cT (starRingEnd ℂ) W * W) * γ.map τ₀
        = cT (starRingEnd ℂ) (W * γ.map τ₀) * (W * γ.map τ₀) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (starRingEnd ℂ) W * (cT (starRingEnd ℂ) (Matrix.diagonal μ) * Matrix.diagonal μ) * W := by
          rw [hWγ, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (starRingEnd ℂ) W * W := by rw [cT_diag_mul_diag μ hμ, Matrix.mul_one]
  · obtain ⟨W, μ, hW, -, -, hH⟩ := h τ
    exact ⟨W, hW, hH⟩

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

/- English proof (translation)
Take `⟨hm, hn, hs, hr⟩` from `hP`. Use `set s := (P.map τ).roots`. Establish `hnd : s.Nodup` using `nodup_roots (hs.map)`. Establish `hcard : s.card = n`. Rewrite using `[← hn, ← Polynomial.natDegree_map τ]`.

Conclude with `splits_iff_card_roots.mp (IsAlgClosed.splits _)`. Establish `hc : s.toFinset.card = n` using `by rw [Multiset.toFinset_card_of_nodup hnd, hcard]`. Set `e : Fin n ≃ s.toFinset` to `(finCongr hc.symm).trans s.toFinset.equivFin.symm`. Use `⟨fun r => ((e r) : ℂ), Subtype.val_injective.comp e.injective, fun r => hr τ _ ?_, fun r => ?_⟩` and prove the remaining obligations. Conclude with `Multiset.mem_toFinset.mp (e r).2`.

Establish `hmem : ((e r) : ℂ) ∈ s` using `Multiset.mem_toFinset.mp (e r).2`. Rewrite using `[← Polynomial.eval_map]`. Conclude with `(mem_roots (hm.map τ).ne_zero).mp hmem`.
-/
theorem exists_roots_enum (E : Type) [Field E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (τ : E →+* ℂ) :
    ∃ μ : Fin n → ℂ, Function.Injective μ ∧ (∀ r, ‖μ r‖ = 1) ∧ ∀ r, P.eval₂ τ (μ r) = 0 := by
  obtain ⟨hm, hn, hs, hr⟩ := hP
  set s := (P.map τ).roots
  have hnd : s.Nodup := nodup_roots (hs.map)
  have hcard : s.card = n := by
    rw [← hn, ← Polynomial.natDegree_map τ]
    exact splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hc : s.toFinset.card = n := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e : Fin n ≃ s.toFinset := (finCongr hc.symm).trans s.toFinset.equivFin.symm
  refine ⟨fun r => ((e r) : ℂ), Subtype.val_injective.comp e.injective, fun r => hr τ _ ?_, fun r => ?_⟩
  · exact Multiset.mem_toFinset.mp (e r).2
  · have hmem : ((e r) : ℂ) ∈ s := Multiset.mem_toFinset.mp (e r).2
    rw [← Polynomial.eval_map]
    exact (mem_roots (hm.map τ).ne_zero).mp hmem

noncomputable def powBasis {E : Type} [Field E] (P : E[X]) (hm : P.Monic) :
    Module.Basis (Fin P.natDegree) E (AdjoinRoot P) :=
  (AdjoinRoot.powerBasis hm.ne_zero).basis.reindex (finCongr (AdjoinRoot.powerBasis_dim hm.ne_zero))

/- English proof (translation)
Simplify using `[powBasis, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]`.
-/
theorem powBasis_apply {E : Type} [Field E] (P : E[X]) (hm : P.Monic) (i : Fin P.natDegree) :
    powBasis P hm i = AdjoinRoot.root P ^ (i : ℕ) := by
  simp [powBasis, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]

noncomputable def compMat {E : Type} [Field E] (P : E[X]) (hm : P.Monic) :
    Matrix (Fin P.natDegree) (Fin P.natDegree) E :=
  Algebra.leftMulMatrix (powBasis P hm) (AdjoinRoot.root P)

/- English proof (translation)
Use extensionality with `r j`. Set `φ : AdjoinRoot P →+* ℂ` to `AdjoinRoot.lift τ (μ r) (hμ r)`. Establish `hφ : ∀ a : AdjoinRoot P, φ a = ∑ i, τ ((powBasis P hm).repr a i) * μ r ^ (i : ℕ)`. Introduce `a`. Use `conv_lhs => rw [← (powBasis P hm).sum_repr a]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, powBasis_apply, map_pow]`. Simplify using `[φ, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]`. Establish `key` using `hφ (AdjoinRoot.root P * powBasis P hm j)`.

Rewrite `key` using `[map_mul, powBasis_apply, map_pow]`. Simplify using `only [φ, AdjoinRoot.lift_root] at key`. Rewrite using `[Matrix.diagonal_mul]`. Simplify using `only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.map_apply, compMat, Algebra.leftMulMatrix_eq_repr_mul, powBasis_apply]`. Rewrite using `[key]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vandermonde_mul_compMat (E : Type) [Field E] (P : E[X]) (hm : P.Monic) (τ : E →+* ℂ)
    (μ : Fin P.natDegree → ℂ) (hμ : ∀ r, P.eval₂ τ (μ r) = 0) :
    Matrix.vandermonde μ * (compMat P hm).map τ = Matrix.diagonal μ * Matrix.vandermonde μ := by
  ext r j
  let φ : AdjoinRoot P →+* ℂ := AdjoinRoot.lift τ (μ r) (hμ r)
  have hφ : ∀ a : AdjoinRoot P, φ a = ∑ i, τ ((powBasis P hm).repr a i) * μ r ^ (i : ℕ) := by
    intro a
    conv_lhs => rw [← (powBasis P hm).sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, powBasis_apply, map_pow]
    simp [φ, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  have key := hφ (AdjoinRoot.root P * powBasis P hm j)
  rw [map_mul, powBasis_apply, map_pow] at key
  simp only [φ, AdjoinRoot.lift_root] at key
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.map_apply,
    compMat, Algebra.leftMulMatrix_eq_repr_mul, powBasis_apply]
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Use `haveI : Module.Finite E (AdjoinRoot P) := Module.Finite.of_basis (powBasis P hm)`. Establish `h1 : (compMat P hm).charpoly = (Algebra.lmul E (AdjoinRoot P) (AdjoinRoot.root P)).charpoly` using `LinearMap.charpoly_toMatrix _ _`. Establish `h2 : (Algebra.leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero).basis (AdjoinRoot.root P)).charpoly = (Algebra.lmul E (AdjoinRoot P) (AdjoinRoot.root P)).charpoly` using `LinearMap.charpoly_toMatrix _ _`. Rewrite using `[h1, ← h2]`. Use `(charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)` as an intermediate fact.

Simplify `this` using `[AdjoinRoot.powerBasis_gen]`.
-/
theorem charpoly_compMat {E : Type} [Field E] (P : E[X]) (hm : P.Monic) : (compMat P hm).charpoly = P := by
  haveI : Module.Finite E (AdjoinRoot P) := Module.Finite.of_basis (powBasis P hm)
  have h1 : (compMat P hm).charpoly = (Algebra.lmul E (AdjoinRoot P) (AdjoinRoot.root P)).charpoly :=
    LinearMap.charpoly_toMatrix _ _
  have h2 : (Algebra.leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero).basis (AdjoinRoot.root P)).charpoly =
      (Algebra.lmul E (AdjoinRoot P) (AdjoinRoot.root P)).charpoly :=
    LinearMap.charpoly_toMatrix _ _
  rw [h1, ← h2]
  have := (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)
  simpa [AdjoinRoot.powerBasis_gen] using this

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

/- English proof (translation)
Establish `hinv : Matrix.diagonal (fun r => (μ r)⁻¹) * Matrix.diagonal μ = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `r`. Conclude with `inv_mul_cancel₀ (hμ0 r)`.

Establish `hWT' : W * T' = Matrix.diagonal (fun r => (μ r)⁻¹) * W`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv, Matrix.one_mul]`. Use `_ = Matrix.diagonal (fun r => (μ r)⁻¹) * (W * T) * T' := by`. Rewrite using `[hWT, Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal μ) W]`.

Use `_ = Matrix.diagonal (fun r => (μ r)⁻¹) * W := by`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hTT', Matrix.mul_one]`. Establish `h1 : SemiconjBy W T' (Matrix.diagonal fun r => (μ r)⁻¹)` using `hWT'`. Establish `h2 : SemiconjBy W T (Matrix.diagonal μ)` using `hWT`. Establish `hs` using `(h1.pow_right i).mul_right (h2.pow_right j)`.

Rewrite `hs` using `[Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]`. Establish `hu : IsUnit W.det` using `isUnit_iff_ne_zero.mpr hW`. Establish `hM : T' ^ i * T ^ j = W⁻¹ * (Matrix.diagonal (fun r => ((fun r => (μ r)⁻¹) ^ i) r * (μ ^ j) r) * W)`. Rewrite using `[← hs.eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Rewrite using `[hM, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.trace_diagonal]`.

Simplify using the standard rewrite rules.
-/
theorem trace_semiconj {k : ℕ} (W T T' : Matrix (Fin k) (Fin k) ℂ) (μ : Fin k → ℂ) (hμ0 : ∀ r, μ r ≠ 0)
    (hW : W.det ≠ 0) (hWT : W * T = Matrix.diagonal μ * W) (hTT' : T * T' = 1) (i j : ℕ) :
    (T' ^ i * T ^ j).trace = ∑ r, (μ r)⁻¹ ^ i * μ r ^ j := by
  have hinv : Matrix.diagonal (fun r => (μ r)⁻¹) * Matrix.diagonal μ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext r; exact inv_mul_cancel₀ (hμ0 r)
  have hWT' : W * T' = Matrix.diagonal (fun r => (μ r)⁻¹) * W := by
    calc W * T' = Matrix.diagonal (fun r => (μ r)⁻¹) * Matrix.diagonal μ * W * T' := by
          rw [hinv, Matrix.one_mul]
      _ = Matrix.diagonal (fun r => (μ r)⁻¹) * (W * T) * T' := by
          rw [hWT, Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal μ) W]
      _ = Matrix.diagonal (fun r => (μ r)⁻¹) * W := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hTT', Matrix.mul_one]
  have h1 : SemiconjBy W T' (Matrix.diagonal fun r => (μ r)⁻¹) := hWT'
  have h2 : SemiconjBy W T (Matrix.diagonal μ) := hWT
  have hs := (h1.pow_right i).mul_right (h2.pow_right j)
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal] at hs
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr hW
  have hM : T' ^ i * T ^ j = W⁻¹ * (Matrix.diagonal (fun r => ((fun r => (μ r)⁻¹) ^ i) r * (μ ^ j) r) * W) := by
    rw [← hs.eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [hM, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    Matrix.trace_diagonal]
  simp

/- English proof (translation)
Establish `hP'` using `hP`. Take `⟨hm, hn, -, hr⟩` from `hP`. Substitute `hn` using the available equality. Establish `h0 : P.coeff 0 ≠ 0`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Introduce `h`. Establish `hroot : (0 : ℂ) ∈ (P.map τ).roots`. Rewrite using `[mem_roots (hm.map τ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h, map_zero]`. Use `hr τ 0 hroot` as an intermediate fact. Simplify using `at this`.

Establish `hd : IsUnit (compMat P hm).det`. Rewrite using `[Matrix.det_eq_sign_charpoly_coeff, charpoly_compMat]`. Conclude with `isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)`. Use `set N : GL (Fin P.natDegree) E := ((Matrix.isUnit_iff_isUnit_det _).mpr hd).unit with hNdef`. Establish `hNval : N.val = compMat P hm` using `IsUnit.unit_spec _`.

Use `⟨N, Matrix.of fun i j => ((N⁻¹).val ^ (i : ℕ) * N.val ^ (j : ℕ)).trace, by rw [hNval, charpoly_compMat], fun τ => ?_⟩` and prove the remaining obligations. Take `⟨μ, hμi, hμ1, hμr⟩` from `exists_roots_enum E _ P hP' τ`. Establish `hμ0 : ∀ r, μ r ≠ 0` using `fun r h => by simpa [h] using hμ1 r`. Establish `hW : (Matrix.vandermonde μ).det ≠ 0` using `Matrix.det_vandermonde_ne_zero_iff.mpr hμi`. Establish `hWT : Matrix.vandermonde μ * N.val.map τ = Matrix.diagonal μ * Matrix.vandermonde μ`.

Rewrite using `[hNval]`. Conclude with `vandermonde_mul_compMat E P hm τ μ hμr`. Establish `hTT' : N.val.map τ * (N⁻¹).val.map τ = 1`. Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero τ) (map_one τ)]`. Use `⟨Matrix.vandermonde μ, μ, hW, hμ1, hWT, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.of_apply, AddMonoidHom.map_trace τ]`. Establish `hmap : (((N⁻¹).val ^ (i : ℕ) * N.val ^ (j : ℕ)).map τ) = ((N⁻¹).val.map τ) ^ (i : ℕ) * (N.val.map τ) ^ (j : ℕ)`. Simplify using `only [← RingHom.mapMatrix_apply, map_mul, map_pow]`. Rewrite using `[hmap, trace_semiconj _ _ _ μ hμ0 hW hWT hTT']`.

Simplify using `only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vandermonde_apply]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, Complex.inv_eq_conj (hμ1 r)]`.
-/
theorem exists_model (E : Type) [Field E] [NumberField E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) :
    ∃ (N : GL (Fin n) E) (H : Matrix (Fin n) (Fin n) E), N.val.charpoly = P ∧
      ∀ τ : E →+* ℂ, ∃ (W : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), W.det ≠ 0 ∧ (∀ r, ‖μ r‖ = 1) ∧
        W * N.val.map τ = Matrix.diagonal μ * W ∧ H.map τ = cT (starRingEnd ℂ) W * W := by
  have hP' := hP
  obtain ⟨hm, hn, -, hr⟩ := hP
  subst hn
  have h0 : P.coeff 0 ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro h
    have hroot : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots (hm.map τ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h, map_zero]
    have := hr τ 0 hroot
    simp at this
  have hd : IsUnit (compMat P hm).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_compMat]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)
  set N : GL (Fin P.natDegree) E := ((Matrix.isUnit_iff_isUnit_det _).mpr hd).unit with hNdef
  have hNval : N.val = compMat P hm := IsUnit.unit_spec _
  refine ⟨N, Matrix.of fun i j => ((N⁻¹).val ^ (i : ℕ) * N.val ^ (j : ℕ)).trace, by rw [hNval, charpoly_compMat],
    fun τ => ?_⟩
  obtain ⟨μ, hμi, hμ1, hμr⟩ := exists_roots_enum E _ P hP' τ
  have hμ0 : ∀ r, μ r ≠ 0 := fun r h => by simpa [h] using hμ1 r
  have hW : (Matrix.vandermonde μ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hμi
  have hWT : Matrix.vandermonde μ * N.val.map τ = Matrix.diagonal μ * Matrix.vandermonde μ := by
    rw [hNval]; exact vandermonde_mul_compMat E P hm τ μ hμr
  have hTT' : N.val.map τ * (N⁻¹).val.map τ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero τ) (map_one τ)]
  refine ⟨Matrix.vandermonde μ, μ, hW, hμ1, hWT, ?_⟩
  ext i j
  rw [Matrix.map_apply, Matrix.of_apply, AddMonoidHom.map_trace τ]
  have hmap : (((N⁻¹).val ^ (i : ℕ) * N.val ^ (j : ℕ)).map τ) =
      ((N⁻¹).val.map τ) ^ (i : ℕ) * (N.val.map τ) ^ (j : ℕ) := by
    simp only [← RingHom.mapMatrix_apply, map_mul, map_pow]
  rw [hmap, trace_semiconj _ _ _ μ hμ0 hW hWT hTT']
  simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_pow, Complex.inv_eq_conj (hμ1 r)]

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, IsCMField.complexEmbedding_complexConj E τ]`.
-/
theorem map_cT_complexConj (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ)
    (X : Matrix (Fin n) (Fin n) E) :
    (cT (IsCMField.complexConj E).toRingEquiv.toRingHom X).map τ = cT (starRingEnd ℂ) (X.map τ) := by
  ext i j; simp [cT, IsCMField.complexEmbedding_complexConj E τ]

/- English proof (translation)
Introduce `E _ _ _ n γ₀ hP`. Take `⟨N, H, hNc, hmod⟩` from `exists_model E n _ hP`. Take `⟨h, hh⟩` from `GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable E n N γ₀ hNc (hNc ▸ hP.2.2.1)`. Use `⟨cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * H * h.val, assemble E n γ₀.val _ fun τ => ?_⟩` and prove the remaining obligations. Take `⟨W, μ, hW, hμ1, hWN, hH⟩` from `hmod τ`.

Establish `hinv1 : h.val.map τ * (h⁻¹).val.map τ = 1`. Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero τ) (map_one τ)]`. Establish `hdh : (h.val.map τ).det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det hinv1` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`. Use `⟨W * h.val.map τ, μ, by rw [Matrix.det_mul]; exact mul_ne_zero hW hdh, hμ1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hh, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.diagonal μ * (W * h.val.map τ) := by`. Rewrite using `[hinv1, Matrix.mul_one, hWN, Matrix.mul_assoc]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_cT_complexConj, hH, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem exists_refForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E),
    γ₀.val.charpoly ∈ Ell E n → ∃ H₀ : Matrix (Fin n) (Fin n) E,
      IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ ∧ H₀.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ ∧
      (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) := by
  intro E _ _ _ n γ₀ hP
  obtain ⟨N, H, hNc, hmod⟩ := exists_model E n _ hP
  obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable E n N γ₀ hNc (hNc ▸ hP.2.2.1)
  refine ⟨cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * H * h.val,
    assemble E n γ₀.val _ fun τ => ?_⟩
  obtain ⟨W, μ, hW, hμ1, hWN, hH⟩ := hmod τ
  have hinv1 : h.val.map τ * (h⁻¹).val.map τ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hdh : (h.val.map τ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hinv1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨W * h.val.map τ, μ, by rw [Matrix.det_mul]; exact mul_ne_zero hW hdh, hμ1, ?_, ?_⟩
  · rw [hh, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    calc W * h.val.map τ * ((h⁻¹).val.map τ * N.val.map τ * h.val.map τ)
        = W * (h.val.map τ * (h⁻¹).val.map τ) * N.val.map τ * h.val.map τ := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal μ * (W * h.val.map τ) := by
          rw [hinv1, Matrix.mul_one, hWN, Matrix.mul_assoc]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT_complexConj, hH, cT_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.RefForm
