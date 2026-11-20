import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartanDecompositionGeneralLinearStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDetStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MatrixAdditiveHaarNormalizedStatement
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.QLScale

open scoped ENNReal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

def rightMul (n : ℕ) {m : ℕ} (g : GL (Fin m) F) :
    Matrix (Fin n) (Fin m) F ≃ₜ+ Matrix (Fin n) (Fin m) F where
  toFun x := x * (g : Matrix (Fin m) (Fin m) F)
  invFun x := x * ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
  left_inv x := by beta_reduce; rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv x := by beta_reduce; rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  map_add' x y := Matrix.add_mul x y _
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

def leftMul {n : ℕ} (m : ℕ) (g : GL (Fin n) F) :
    Matrix (Fin n) (Fin m) F ≃ₜ+ Matrix (Fin n) (Fin m) F where
  toFun x := (g : Matrix (Fin n) (Fin n) F) * x
  invFun x := ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * x
  left_inv x := by beta_reduce; rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv x := by beta_reduce; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ x y
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

def dg {m : ℕ} : (Fin m → Fˣ) →* GL (Fin m) F where
  toFun u :=
    { val := Matrix.diagonal fun i => (u i : F)
      inv := Matrix.diagonal fun i => (((u i)⁻¹ : Fˣ) : F)
      val_inv := by simp [Matrix.diagonal_mul_diagonal]
      inv_val := by simp [Matrix.diagonal_mul_diagonal] }
  map_one' := by ext; simp [Matrix.one_apply, Matrix.diagonal_apply]
  map_mul' u v := by
    apply Units.ext
    simp [Matrix.diagonal_mul_diagonal]

def colLat (O : Subring F) (ϖ : F) (n : ℕ) {m : ℕ} (j : Fin m) : Set (Matrix (Fin n) (Fin m) F) :=
  {x | ∀ i b, x i b * (if b = j then ϖ else 1) ∈ O}

/- English proof (translation)
Establish `hx' : ∀ i j, x i j ∈ O` using `hx`. Establish `hg' : ∀ i j, g i j ∈ O` using `hg`. Use `show ∀ i j, (x * g) i j ∈ O`. Introduce `i j`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `Subring.sum_mem O fun k _ => O.mul_mem (hx' i k) (hg' k j)`.
-/
theorem intMat_mul {n m : ℕ} {x : Matrix (Fin n) (Fin m) F} {g : Matrix (Fin m) (Fin m) F}
    (hx : x ∈ intMat O n m) (hg : IsInt O g) : x * g ∈ intMat O n m := by
  have hx' : ∀ i j, x i j ∈ O := hx
  have hg' : ∀ i j, g i j ∈ O := hg
  show ∀ i j, (x * g) i j ∈ O
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem O fun k _ => O.mul_mem (hx' i k) (hg' k j)

/- English proof (translation)
Establish `hx' : ∀ i j, x i j ∈ O` using `hx`. Establish `hg' : ∀ i j, g i j ∈ O` using `hg`. Use `show ∀ i j, (g * x) i j ∈ O`. Introduce `i j`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `Subring.sum_mem O fun k _ => O.mul_mem (hg' i k) (hx' k j)`.
-/
theorem mul_intMat {n m : ℕ} {x : Matrix (Fin n) (Fin m) F} {g : Matrix (Fin n) (Fin n) F}
    (hg : IsInt O g) (hx : x ∈ intMat O n m) : g * x ∈ intMat O n m := by
  have hx' : ∀ i j, x i j ∈ O := hx
  have hg' : ∀ i j, g i j ∈ O := hg
  show ∀ i j, (g * x) i j ∈ O
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem O fun k _ => O.mul_mem (hg' i k) (hx' k j)

/- English proof (translation)
Establish `h` using `(hLF.lt_one ϖ).2 ⟨1, O.one_mem, (mul_one ϖ).symm⟩`. Rewrite using `[hLF.O_eq]`. Conclude with `(Valuation.mem_integer_iff _ _).2 h.le`.
-/
theorem pi_mem (hLF : LF O ϖ nrm q) : ϖ ∈ O := by
  have h := (hLF.lt_one ϖ).2 ⟨1, O.one_mem, (mul_one ϖ).symm⟩
  rw [hLF.O_eq]
  exact (Valuation.mem_integer_iff _ _).2 h.le

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Conclude with `hLF.lt_one a`.
-/
theorem res_zero (hLF : LF 𝒪[F] ϖ nrm q) (a : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] a = 0 ↔ ∃ o ∈ 𝒪[F], (a : F) = ϖ * o := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact hLF.lt_one a

/- English proof (translation)
Introduce `h`. Apply `hLF.ne` to reduce the goal to its premises. Establish `h2 : nrm ϖ = 0` using `by rw [hLF.nrm_pi, h, Nat.cast_zero, _root_.inv_zero]`. Conclude with `(AbsoluteValue.eq_zero (abv := nrm)).1 h2`.
-/
theorem q_ne_zero (hLF : LF O ϖ nrm q) : q ≠ 0 := by
  intro h
  apply hLF.ne
  have h2 : nrm ϖ = 0 := by rw [hLF.nrm_pi, h, Nat.cast_zero, _root_.inv_zero]
  exact (AbsoluteValue.eq_zero (abv := nrm)).1 h2

section Measure

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Take `⟨hB, hopen, hcomp, -, hHaar, huniq⟩` from `GlobalTheory.T.matrix_additive_haar_normalized hLF n m`. Use `haveI := hB`. Use `haveI := hinv`. Use `haveI := hHaar dx hinv h1`. Establish `hφc : Continuous φ` using `φ.continuous`.

Establish `hφm : Measurable φ` using `hφc.measurable`. Establish `h0 : (0 : Matrix (Fin n) (Fin m) F) ∈ φ ⁻¹' intMat O n m` using `by show φ 0 ∈ intMat O n m`. Rewrite using `[map_zero]`. Use `show ∀ i j, (0 : Matrix (Fin n) (Fin m) F) i j ∈ O`. Introduce `i j`.

Conclude with `O.zero_mem`. Establish `hc0 : dx (φ ⁻¹' intMat O n m) ≠ 0` using `(hopen.preimage hφc).measure_ne_zero dx ⟨0, h0⟩`. Establish `hK : IsCompact (φ ⁻¹' intMat O n m)`. Establish `hset : φ ⁻¹' intMat O n m = φ.symm '' intMat O n m`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨φ x, hx, φ.symm_apply_apply x⟩`. Introduce and unpack `⟨y, hy, rfl⟩ show φ (φ.symm y) ∈ intMat O n m`. Rewrite using `[φ.apply_symm_apply]`.

Conclude with `hy`. Rewrite using `[hset]`. Conclude with `hcomp.image φ.symm.continuous`. Establish `hctop : dx (φ ⁻¹' intMat O n m) ≠ ⊤` using `hK.measure_lt_top.ne`. Use `haveI hinvm : (Measure.map φ dx).IsAddLeftInvariant := by`.

Use `⟨fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_map (measurable_const_add g) hφm]`. Establish `hfun : ((g + ·) ∘ φ) = φ ∘ (φ.symm g + ·)`. Use function extensionality and compare the values at `x`. Simplify using `[map_add]`.

Rewrite using `[hfun, ← Measure.map_map hφm (measurable_const_add _), map_add_left_eq_self]`. Establish `hν : ((dx (φ ⁻¹' intMat O n m))⁻¹ • Measure.map φ dx) (intMat O n m) = 1`. Rewrite using `[Measure.smul_apply, Measure.map_apply hφm hopen.measurableSet, smul_eq_mul, ENNReal.inv_mul_cancel hc0 hctop]`. Establish `heq` using `huniq dx hinv h1 ((dx (φ ⁻¹' intMat O n m))⁻¹ • Measure.map φ dx) inferInstance hν`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[smul_smul, ENNReal.mul_inv_cancel hc0 hctop, one_smul]`. Use `_ = dx (φ ⁻¹' intMat O n m) • dx := by rw [← heq]`.
-/
theorem map_eq_smul (hLF : LF O ϖ nrm q) {n m : ℕ} {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1)
    (φ : Matrix (Fin n) (Fin m) F ≃ₜ+ Matrix (Fin n) (Fin m) F) :
    Measure.map φ dx = dx (φ ⁻¹' intMat O n m) • dx := by
  obtain ⟨hB, hopen, hcomp, -, hHaar, huniq⟩ := GlobalTheory.T.matrix_additive_haar_normalized hLF n m
  haveI := hB
  haveI := hinv
  haveI := hHaar dx hinv h1
  have hφc : Continuous φ := φ.continuous
  have hφm : Measurable φ := hφc.measurable
  have h0 : (0 : Matrix (Fin n) (Fin m) F) ∈ φ ⁻¹' intMat O n m := by
    show φ 0 ∈ intMat O n m
    rw [map_zero]
    show ∀ i j, (0 : Matrix (Fin n) (Fin m) F) i j ∈ O
    intro i j
    exact O.zero_mem
  have hc0 : dx (φ ⁻¹' intMat O n m) ≠ 0 := (hopen.preimage hφc).measure_ne_zero dx ⟨0, h0⟩
  have hK : IsCompact (φ ⁻¹' intMat O n m) := by
    have hset : φ ⁻¹' intMat O n m = φ.symm '' intMat O n m := by
      ext x
      constructor
      · intro hx
        exact ⟨φ x, hx, φ.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        show φ (φ.symm y) ∈ intMat O n m
        rw [φ.apply_symm_apply]
        exact hy
    rw [hset]
    exact hcomp.image φ.symm.continuous
  have hctop : dx (φ ⁻¹' intMat O n m) ≠ ⊤ := hK.measure_lt_top.ne
  haveI hinvm : (Measure.map φ dx).IsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_add g) hφm]
    have hfun : ((g + ·) ∘ φ) = φ ∘ (φ.symm g + ·) := by
      funext x
      simp [map_add]
    rw [hfun, ← Measure.map_map hφm (measurable_const_add _), map_add_left_eq_self]
  have hν : ((dx (φ ⁻¹' intMat O n m))⁻¹ • Measure.map φ dx) (intMat O n m) = 1 := by
    rw [Measure.smul_apply, Measure.map_apply hφm hopen.measurableSet, smul_eq_mul,
      ENNReal.inv_mul_cancel hc0 hctop]
  have heq := huniq dx hinv h1 ((dx (φ ⁻¹' intMat O n m))⁻¹ • Measure.map φ dx) inferInstance hν
  calc Measure.map φ dx
      = dx (φ ⁻¹' intMat O n m) • ((dx (φ ⁻¹' intMat O n m))⁻¹ • Measure.map φ dx) := by
        rw [smul_smul, ENNReal.mul_inv_cancel hc0 hctop, one_smul]
    _ = dx (φ ⁻¹' intMat O n m) • dx := by rw [← heq]

/- English proof (translation)
Take `⟨o, ho, heq⟩` from `(res_zero hLF (⟨y * ϖ, hy⟩ - s)).1 (by rw [map_sub, hs, sub_self])`. Establish `hne` using `hLF.ne`. Establish `heq' : y * ϖ - (s : F) = ϖ * o` using `by simpa using heq`. Establish `hval : -(ϖ⁻¹ * (s : F)) + y = o`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_sub, mul_comm y ϖ, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ϖ⁻¹ * (ϖ * o) := by rw [heq']`. Use `_ = o := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]`. Rewrite using `[hval]`.

Conclude with `ho`.
-/
private theorem neg_inv_mul_add_mem_of_residue_eq (hLF : LF 𝒪[F] ϖ nrm q) (y : F) (hy : y * ϖ ∈ 𝒪[F]) (s : 𝒪[F])
    (hs : IsLocalRing.residue 𝒪[F] s = IsLocalRing.residue 𝒪[F] ⟨y * ϖ, hy⟩) :
    -(ϖ⁻¹ * (s : F)) + y ∈ 𝒪[F] := by
  obtain ⟨o, ho, heq⟩ := (res_zero hLF (⟨y * ϖ, hy⟩ - s)).1 (by rw [map_sub, hs, sub_self])
  have hne := hLF.ne
  have heq' : y * ϖ - (s : F) = ϖ * o := by simpa using heq
  have hval : -(ϖ⁻¹ * (s : F)) + y = o := by
    calc -(ϖ⁻¹ * (s : F)) + y = ϖ⁻¹ * (y * ϖ - s) := by
          rw [mul_sub, mul_comm y ϖ, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]; ring
      _ = ϖ⁻¹ * (ϖ * o) := by rw [heq']
      _ = o := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hval]
  exact ho

/- English proof (translation)
Establish `hw : ϖ⁻¹ * ((s : F) - t) ∈ 𝒪[F]`. Establish `h` using `sub_mem ht hs`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : IsLocalRing.residue 𝒪[F] (s - t) = 0` using `(res_zero hLF (s - t)).2 ⟨_, hw, by push_cast; rw [← mul_assoc, mul_inv_cancel₀ hLF.ne, one_mul]⟩`.

Rewrite `h0` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
private theorem residue_eq_of_neg_inv_mul_add_mem (hLF : LF 𝒪[F] ϖ nrm q) (y : F) (s t : 𝒪[F])
    (hs : -(ϖ⁻¹ * (s : F)) + y ∈ 𝒪[F]) (ht : -(ϖ⁻¹ * (t : F)) + y ∈ 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] s = IsLocalRing.residue 𝒪[F] t := by
  have hw : ϖ⁻¹ * ((s : F) - t) ∈ 𝒪[F] := by
    have h := sub_mem ht hs
    convert h using 1
    ring
  have h0 : IsLocalRing.residue 𝒪[F] (s - t) = 0 :=
    (res_zero hLF (s - t)).2 ⟨_, hw, by push_cast; rw [← mul_assoc, mul_inv_cancel₀ hLF.ne, one_mul]⟩
  rwa [map_sub, sub_eq_zero] at h0

/- English proof (translation)
Establish `hne` using `hLF.ne`. Establish `h` using `add_mem (mul_mem hs (pi_mem hLF)) s.2`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `field_simp <;> ring`.
-/
private theorem mul_mem_of_neg_inv_mul_add_mem (hLF : LF 𝒪[F] ϖ nrm q) (y : F) (s : 𝒪[F])
    (hs : -(ϖ⁻¹ * (s : F)) + y ∈ 𝒪[F]) : y * ϖ ∈ 𝒪[F] := by
  have hne := hLF.ne
  have h := add_mem (mul_mem hs (pi_mem hLF)) s.2
  convert h using 1
  field_simp <;> ring

/- English proof (translation)
Take `⟨hB, hopen, -, -, -, -⟩` from `GlobalTheory.T.matrix_additive_haar_normalized hLF n m`. Use `haveI := hB`. Use `haveI := hinv`. Take `rfl : O = 𝒪[F]` from `hLF.O_eq`. Use `haveI : Finite 𝓀[F] := Nat.finite_of_card_ne_zero (by rw [← hLF.card]; exact q_ne_zero hLF)`.

Use `haveI : Fintype 𝓀[F] := Fintype.ofFinite _`. Take `⟨s, hs⟩ : ∃ s : 𝓀[F] → 𝒪[F], ∀ r, IsLocalRing.residue 𝒪[F] (s r) = r` from `⟨_, Function.surjInv_eq IsLocalRing.residue_surjective⟩`. Set `E : (Fin n → 𝓀[F]) → Matrix (Fin n) (Fin m) F` to `fun r i b => if b = j then ϖ⁻¹ * (s (r i) : F) else 0`. Set `T : (Fin n → 𝓀[F]) → Set (Matrix (Fin n) (Fin m) F)` to `fun r => (fun x => -E r + x) ⁻¹' intMat 𝒪[F] n m`. Establish `hmemT : ∀ r x, x ∈ T r ↔ ∀ i b, -(if b = j then ϖ⁻¹ * (s (r i) : F) else 0) + x i b ∈ 𝒪[F]` using `fun _ _ => Iff.rfl`.

Establish `hT : ∀ r, dx (T r) = 1` using `fun r => by show dx ((fun x => -E r + x) ⁻¹' intMat 𝒪[F] n m) = 1`. Rewrite using `[measure_preimage_add, h1]`. Establish `hTm : ∀ r, MeasurableSet (T r)` using `fun r => (hopen.preimage (continuous_const.add continuous_id)).measurableSet`. Establish `hcol : colLat 𝒪[F] ϖ n j = ⋃ r, T r`. Use extensionality with `x`.

Rewrite using `[Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : ∀ i b, x i b * (if b = j then ϖ else 1) ∈ 𝒪[F]` using `hx`. Establish `hxj : ∀ i, x i j * ϖ ∈ 𝒪[F]` using `fun i => by simpa using hx' i j`.

Use `⟨fun i => IsLocalRing.residue 𝒪[F] ⟨x i j * ϖ, hxj i⟩, (hmemT _ x).2 fun i b => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : b = j`. Rewrite using `[hb, if_pos rfl]`. Conclude with `neg_inv_mul_add_mem_of_residue_eq hLF (x i j) (hxj i) _ (hs _)`. Rewrite using `[if_neg hb, neg_zero, zero_add]`.

Simplify `hx' i b` using `[hb]`. Introduce and unpack `⟨r, hr⟩`. Establish `hr'` using `(hmemT r x).1 hr`. Use `show ∀ i b, x i b * (if b = j then ϖ else 1) ∈ 𝒪[F]`. Introduce `i b`.

Distinguish the cases in `hb : b = j`. Rewrite using `[hb, if_pos rfl]`. Establish `h3` using `hr' i j`. Rewrite `h3` using `[if_pos rfl]`. Conclude with `mul_mem_of_neg_inv_mul_add_mem hLF (x i j) (s (r i)) h3`.

Establish `h3` using `hr' i b`. Rewrite `h3` using `[if_neg hb, neg_zero, zero_add]`. Rewrite using `[if_neg hb, mul_one]`. Conclude with `h3`. Establish `hdisj : Pairwise (Function.onFun Disjoint T)`.

Introduce `r r' hrr'`. Use `Set.disjoint_left.2 fun x h h' => hrr' (funext fun i => ?_)` and prove the remaining obligations. Establish `h1'` using `(hmemT r x).1 h i j`. Establish `h2'` using `(hmemT r' x).1 h' i j`. Rewrite `h1'`, `h2'` using `[if_pos rfl]`.

Rewrite using `[← hs (r i), ← hs (r' i)]`. Conclude with `residue_eq_of_neg_inv_mul_add_mem hLF (x i j) _ _ h1' h2'`. Rewrite using `[hcol, measure_iUnion hdisj hTm]`. Simplify using `only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, ← Nat.card_eq_fintype_card, ← hLF.card]`. Rewrite using `[Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, ← hLF.card, Nat.cast_pow]`.
-/
theorem vol_colLat (hLF : LF O ϖ nrm q) {n m : ℕ} {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1) (j : Fin m) :
    dx (colLat O ϖ n j) = (q : ℝ≥0∞) ^ n := by
  obtain ⟨hB, hopen, -, -, -, -⟩ := GlobalTheory.T.matrix_additive_haar_normalized hLF n m
  haveI := hB
  haveI := hinv
  obtain rfl : O = 𝒪[F] := hLF.O_eq
  haveI : Finite 𝓀[F] := Nat.finite_of_card_ne_zero (by rw [← hLF.card]; exact q_ne_zero hLF)
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  classical
  obtain ⟨s, hs⟩ : ∃ s : 𝓀[F] → 𝒪[F], ∀ r, IsLocalRing.residue 𝒪[F] (s r) = r :=
    ⟨_, Function.surjInv_eq IsLocalRing.residue_surjective⟩
  let E : (Fin n → 𝓀[F]) → Matrix (Fin n) (Fin m) F :=
    fun r i b => if b = j then ϖ⁻¹ * (s (r i) : F) else 0
  let T : (Fin n → 𝓀[F]) → Set (Matrix (Fin n) (Fin m) F) :=
    fun r => (fun x => -E r + x) ⁻¹' intMat 𝒪[F] n m
  have hmemT : ∀ r x, x ∈ T r ↔
      ∀ i b, -(if b = j then ϖ⁻¹ * (s (r i) : F) else 0) + x i b ∈ 𝒪[F] := fun _ _ => Iff.rfl
  have hT : ∀ r, dx (T r) = 1 := fun r => by
    show dx ((fun x => -E r + x) ⁻¹' intMat 𝒪[F] n m) = 1
    rw [measure_preimage_add, h1]
  have hTm : ∀ r, MeasurableSet (T r) := fun r =>
    (hopen.preimage (continuous_const.add continuous_id)).measurableSet
  have hcol : colLat 𝒪[F] ϖ n j = ⋃ r, T r := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · intro hx
      have hx' : ∀ i b, x i b * (if b = j then ϖ else 1) ∈ 𝒪[F] := hx
      have hxj : ∀ i, x i j * ϖ ∈ 𝒪[F] := fun i => by simpa using hx' i j
      refine ⟨fun i => IsLocalRing.residue 𝒪[F] ⟨x i j * ϖ, hxj i⟩, (hmemT _ x).2 fun i b => ?_⟩
      by_cases hb : b = j
      · rw [hb, if_pos rfl]
        exact neg_inv_mul_add_mem_of_residue_eq hLF (x i j) (hxj i) _ (hs _)
      · rw [if_neg hb, neg_zero, zero_add]
        simpa [hb] using hx' i b
    · rintro ⟨r, hr⟩
      have hr' := (hmemT r x).1 hr
      show ∀ i b, x i b * (if b = j then ϖ else 1) ∈ 𝒪[F]
      intro i b
      by_cases hb : b = j
      · rw [hb, if_pos rfl]
        have h3 := hr' i j
        rw [if_pos rfl] at h3
        exact mul_mem_of_neg_inv_mul_add_mem hLF (x i j) (s (r i)) h3
      · have h3 := hr' i b
        rw [if_neg hb, neg_zero, zero_add] at h3
        rw [if_neg hb, mul_one]
        exact h3
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro r r' hrr'
    refine Set.disjoint_left.2 fun x h h' => hrr' (funext fun i => ?_)
    have h1' := (hmemT r x).1 h i j
    have h2' := (hmemT r' x).1 h' i j
    rw [if_pos rfl] at h1' h2'
    rw [← hs (r i), ← hs (r' i)]
    exact residue_eq_of_neg_inv_mul_add_mem hLF (x i j) _ _ h1' h2'
  rw [hcol, measure_iUnion hdisj hTm]
  simp only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_pow, ← Nat.card_eq_fintype_card, ← hLF.card]
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, ← hLF.card, Nat.cast_pow]

def scale (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g : GL (Fin m) F) : ℝ≥0∞ :=
  ENNReal.ofReal ((nrm (g : Matrix (Fin m) (Fin m) F).det)⁻¹ ^ n)

/- English proof (translation)
Conclude with `AbsoluteValue.pos (abv := nrm) (Matrix.isUnits_det_units g).ne_zero`.
-/
theorem det_pos (nrm : AbsoluteValue F ℝ) {m : ℕ} (g : GL (Fin m) F) :
    0 < nrm (g : Matrix (Fin m) (Fin m) F).det := by
  exact AbsoluteValue.pos (abv := nrm) (Matrix.isUnits_det_units g).ne_zero

/- English proof (translation)
Simplify using `only [scale, Units.val_mul, Matrix.det_mul, map_mul, mul_inv, mul_pow]`. Conclude with `ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 (AbsoluteValue.nonneg nrm _)) _)`.
-/
theorem scale_mul (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g h : GL (Fin m) F) :
    scale nrm n (g * h) = scale nrm n g * scale nrm n h := by
  simp only [scale, Units.val_mul, Matrix.det_mul, map_mul, mul_inv, mul_pow]
  exact ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 (AbsoluteValue.nonneg nrm _)) _)

/- English proof (translation)
Rewrite using `[scale, Ne, ENNReal.ofReal_eq_zero, not_le]`. Conclude with `pow_pos (inv_pos.2 (det_pos nrm g)) n`.
-/
theorem scale_ne_zero (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g : GL (Fin m) F) :
    scale nrm n g ≠ 0 := by
  rw [scale, Ne, ENNReal.ofReal_eq_zero, not_le]
  exact pow_pos (inv_pos.2 (det_pos nrm g)) n

/- English proof (translation)
The claim follows from `ENNReal.ofReal_ne_top`.
-/
theorem scale_ne_top (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g : GL (Fin m) F) :
    scale nrm n g ≠ ⊤ := ENNReal.ofReal_ne_top

/- English proof (translation)
Establish `hd` using `det_pos nrm g`. Establish `h1 : nrm ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det * nrm (g : Matrix (Fin m) (Fin m) F).det = 1`. Rewrite using `[← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, AbsoluteValue.map_one]`. Unfold `scale`. Rewrite using `[eq_inv_of_mul_eq_one_left h1, ← ENNReal.ofReal_inv_of_pos (pow_pos (inv_pos.2 hd) n)]`.

Use `congr 1`. Conclude with `inv_pow _ _`.
-/
theorem scale_inv (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g : GL (Fin m) F) :
    scale nrm n g⁻¹ = (scale nrm n g)⁻¹ := by
  have hd := det_pos nrm g
  have h1 : nrm ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det *
      nrm (g : Matrix (Fin m) (Fin m) F).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one,
      AbsoluteValue.map_one]
  unfold scale
  rw [eq_inv_of_mul_eq_one_left h1, ← ENNReal.ofReal_inv_of_pos (pow_pos (inv_pos.2 hd) n)]
  congr 1
  exact inv_pow _ _

/- English proof (translation)
Conclude with `(continuous_id.matrix_mul continuous_const).measurable`.
-/
theorem measurable_rightMul {m : ℕ} (n : ℕ) [BorelSpace (Matrix (Fin n) (Fin m) F)]
    (g : GL (Fin m) F) : Measurable (rightMul n g : Matrix (Fin n) (Fin m) F → _) := by
  exact (continuous_id.matrix_mul continuous_const).measurable

def stab (nrm : AbsoluteValue F ℝ) {n m : ℕ} [BorelSpace (Matrix (Fin n) (Fin m) F)]
    (dx : Measure (Matrix (Fin n) (Fin m) F)) : Subgroup (GL (Fin m) F) where
  carrier := {g | Measure.map (rightMul n g) dx = scale nrm n g • dx}
  one_mem' := by
    have : (⇑(rightMul n (1 : GL (Fin m) F)) : _ → _) = id := by
      funext x; simp [rightMul]
    show Measure.map _ dx = _
    rw [this, Measure.map_id]
    simp [scale]
  mul_mem' := by
    intro g h hg hh
    have : (⇑(rightMul n (g * h)) : _ → _) = rightMul n h ∘ rightMul n g := by
      funext x; simp [rightMul, Matrix.mul_assoc]
    show Measure.map _ dx = _
    rw [this, ← Measure.map_map (measurable_rightMul n h) (measurable_rightMul n g), show Measure.map _ dx = _ from hg,
      Measure.map_smul, show Measure.map _ dx = _ from hh, smul_smul, scale_mul, mul_comm]
  inv_mem' := by
    intro g hg
    have hid : (⇑(rightMul n g⁻¹) ∘ ⇑(rightMul n g) : _ → _) = id := by
      funext x; simp [rightMul, Matrix.mul_assoc]
    have h2 : Measure.map (rightMul n g⁻¹) (Measure.map (rightMul n g) dx) = dx := by
      rw [Measure.map_map (measurable_rightMul n g⁻¹) (measurable_rightMul n g), hid, Measure.map_id]
    rw [show Measure.map _ dx = _ from hg, Measure.map_smul] at h2
    show Measure.map _ dx = _
    rw [scale_inv]
    conv_rhs => rw [← h2]
    rw [smul_smul, ENNReal.inv_mul_cancel (scale_ne_zero nrm n g) (scale_ne_top nrm n g), one_smul]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_stab {n m : ℕ} [BorelSpace (Matrix (Fin n) (Fin m) F)]
    {dx : Measure (Matrix (Fin n) (Fin m) F)} {g : GL (Fin m) F} :
    g ∈ stab nrm dx ↔ Measure.map (rightMul n g) dx = scale nrm n g • dx := Iff.rfl

/- English proof (translation)
Establish `hk' : IsInt O (k : Matrix (Fin m) (Fin m) F) ∧ IsInt O ((k⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)` using `hk`. Establish `hdet : nrm (k : Matrix (Fin m) (Fin m) F).det = 1` using `((GlobalTheory.T.mem_integralGL_iff_integral_unit_det hLF m k).1 hk).2`. Rewrite using `[mem_stab, map_eq_smul hLF hinv h1 (rightMul n k)]`. Establish `hpre : (rightMul n k : Matrix (Fin n) (Fin m) F → _) ⁻¹' intMat O n m = intMat O n m`. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `x * (k : Matrix (Fin m) (Fin m) F) ∈ intMat O n m ↔ x ∈ intMat O n m`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h2` using `intMat_mul hx hk'.2`. Rewrite `h2` using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Then use the resulting hypothesis.

Introduce `hx`. Conclude with `intMat_mul hx hk'.1`. Rewrite using `[hpre, h1, scale, hdet, inv_one, one_pow, ENNReal.ofReal_one]`.
-/
theorem glint_mem_stab (hLF : LF O ϖ nrm q) {n m : ℕ} [BorelSpace (Matrix (Fin n) (Fin m) F)]
    {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1) {k : GL (Fin m) F}
    (hk : k ∈ GLint O m) : k ∈ stab nrm dx := by
  have hk' : IsInt O (k : Matrix (Fin m) (Fin m) F) ∧
      IsInt O ((k⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := hk
  have hdet : nrm (k : Matrix (Fin m) (Fin m) F).det = 1 := ((GlobalTheory.T.mem_integralGL_iff_integral_unit_det hLF m k).1 hk).2
  rw [mem_stab, map_eq_smul hLF hinv h1 (rightMul n k)]
  have hpre : (rightMul n k : Matrix (Fin n) (Fin m) F → _) ⁻¹' intMat O n m = intMat O n m := by
    ext x
    change x * (k : Matrix (Fin m) (Fin m) F) ∈ intMat O n m ↔ x ∈ intMat O n m
    constructor
    · intro hx
      have h2 := intMat_mul hx hk'.2
      rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h2
    · intro hx
      exact intMat_mul hx hk'.1
  rw [hpre, h1, scale, hdet, inv_one, one_pow, ENNReal.ofReal_one]

/- English proof (translation)
Establish `hval : ((dg (Pi.mulSingle j (Units.mk0 ϖ hLF.ne)) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun b => if b = j then ϖ else 1`. Express the relevant statement in the definitionally equal form `Matrix.diagonal (fun i => (((Pi.mulSingle j (Units.mk0 ϖ hLF.ne) : Fin m → Fˣ) i : Fˣ) : F)) = _`. Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = j`.

Rewrite using `[hb]`. Simplify using the standard rewrite rules. Simplify using `[hb]`. Rewrite using `[mem_stab, map_eq_smul hLF hinv h1]`. Establish `hpre : (rightMul n (dg (Pi.mulSingle j (Units.mk0 ϖ hLF.ne))) : Matrix (Fin n) (Fin m) F → _) ⁻¹' intMat O n m = colLat O ϖ n j`.

Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x * ((dg (Pi.mulSingle j (Units.mk0 ϖ hLF.ne)) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) ∈ intMat O n m ↔ _`. Rewrite using `[hval]`. Use `show (∀ i b, (x * Matrix.diagonal fun b => if b = j then ϖ else 1) i b ∈ O) ↔ ∀ i b, x i b * (if b = j then ϖ else 1) ∈ O`. Simplify using `only [Matrix.mul_diagonal]`.

Rewrite using `[hpre, vol_colLat hLF hinv h1 j, scale, hval, Matrix.det_diagonal, Finset.prod_ite_eq', if_pos (Finset.mem_univ j), hLF.nrm_pi, inv_inv, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]`.
-/
theorem single_mem_stab (hLF : LF O ϖ nrm q) {n m : ℕ} [BorelSpace (Matrix (Fin n) (Fin m) F)]
    {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1) (j : Fin m) :
    dg (Pi.mulSingle j (Units.mk0 ϖ hLF.ne)) ∈ stab nrm dx := by
  have hval : ((dg (Pi.mulSingle j (Units.mk0 ϖ hLF.ne)) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.diagonal fun b => if b = j then ϖ else 1 := by
    change Matrix.diagonal (fun i => (((Pi.mulSingle j (Units.mk0 ϖ hLF.ne) : Fin m → Fˣ) i : Fˣ) : F)) = _
    congr 1
    funext b
    by_cases hb : b = j
    · rw [hb]
      simp
    · simp [hb]
  rw [mem_stab, map_eq_smul hLF hinv h1]
  have hpre : (rightMul n (dg (Pi.mulSingle j (Units.mk0 ϖ hLF.ne))) : Matrix (Fin n) (Fin m) F → _) ⁻¹'
      intMat O n m = colLat O ϖ n j := by
    ext x
    change x * ((dg (Pi.mulSingle j (Units.mk0 ϖ hLF.ne)) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) ∈
      intMat O n m ↔ _
    rw [hval]
    show (∀ i b, (x * Matrix.diagonal fun b => if b = j then ϖ else 1) i b ∈ O) ↔ ∀ i b, x i b * (if b = j then ϖ else 1) ∈ O
    simp only [Matrix.mul_diagonal]
  rw [hpre, vol_colLat hLF hinv h1 j, scale, hval, Matrix.det_diagonal, Finset.prod_ite_eq',
    if_pos (Finset.mem_univ j), hLF.nrm_pi, inv_inv, ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

/- English proof (translation)
Use `show (fun i => (Units.mk0 ϖ hLF.ne) ^ e i) ∈ (stab nrm dx).comap dg`. Rewrite using `[← Finset.univ_prod_mulSingle (fun i => (Units.mk0 ϖ hLF.ne) ^ e i)]`. Use `Subgroup.prod_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `h2 : (Pi.mulSingle j ((Units.mk0 ϖ hLF.ne : Fˣ) ^ e j) : Fin m → Fˣ) = (Pi.mulSingle j (Units.mk0 ϖ hLF.ne : Fˣ) : Fin m → Fˣ) ^ e j` using `map_zpow (MonoidHom.mulSingle (fun _ : Fin m => Fˣ) j) (Units.mk0 ϖ hLF.ne) (e j)`. Rewrite using `[h2]`.

Conclude with `Subgroup.zpow_mem _ (Subgroup.mem_comap.2 (single_mem_stab hLF hinv h1 j)) _`.
-/
theorem diag_mem_stab (hLF : LF O ϖ nrm q) {n m : ℕ} [BorelSpace (Matrix (Fin n) (Fin m) F)]
    {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1) (e : Fin m → ℤ) :
    dg (fun i => (Units.mk0 ϖ hLF.ne) ^ e i) ∈ stab nrm dx := by
  show (fun i => (Units.mk0 ϖ hLF.ne) ^ e i) ∈ (stab nrm dx).comap dg
  rw [← Finset.univ_prod_mulSingle (fun i => (Units.mk0 ϖ hLF.ne) ^ e i)]
  refine Subgroup.prod_mem _ fun j _ => ?_
  have h2 : (Pi.mulSingle j ((Units.mk0 ϖ hLF.ne : Fˣ) ^ e j) : Fin m → Fˣ) =
      (Pi.mulSingle j (Units.mk0 ϖ hLF.ne : Fˣ) : Fin m → Fˣ) ^ e j :=
    map_zpow (MonoidHom.mulSingle (fun _ : Fin m => Fˣ) j) (Units.mk0 ϖ hLF.ne) (e j)
  rw [h2]
  exact Subgroup.zpow_mem _ (Subgroup.mem_comap.2 (single_mem_stab hLF hinv h1 j)) _

/- English proof (translation)
Use `haveI : BorelSpace (Matrix (Fin n) (Fin m) F) := (GlobalTheory.T.matrix_additive_haar_normalized hLF n m).1`. Use `⟨fun g => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨k₁, hk₁, k₂, hk₂, e, d, hd, rfl⟩` from `GlobalTheory.T.cartan_decomposition_generalLinear hLF m g`. Establish `hdd : d = dg (fun i => (Units.mk0 ϖ hLF.ne) ^ e i)`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[hd]`. Express the relevant statement in the definitionally equal form `_ = Matrix.diagonal fun i => ((((Units.mk0 ϖ hLF.ne) ^ e i : Fˣ)) : F)`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Establish `hmem : k₁ * d * k₂ ∈ stab nrm dx`. Use `Subgroup.mul_mem _ (Subgroup.mul_mem _ (glint_mem_stab hLF hinv h1 hk₁) ?_) (glint_mem_stab hLF hinv h1 hk₂)` and prove the remaining obligations. Rewrite using `[hdd]`. Conclude with `diag_mem_stab hLF hinv h1 e`. Conclude with `mem_stab.1 hmem`.

Establish `hk' : IsInt O (k : Matrix (Fin n) (Fin n) F) ∧ IsInt O ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)` using `hk`. Establish `h` using `map_eq_smul hLF hinv h1 (leftMul m k)`. Establish `hpre : (leftMul m k : Matrix (Fin n) (Fin m) F → _) ⁻¹' intMat O n m = intMat O n m`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `(k : Matrix (Fin n) (Fin n) F) * x ∈ intMat O n m ↔ x ∈ intMat O n m`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h2` using `mul_intMat hk'.2 hx`. Rewrite `h2` using `[← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Then use the resulting hypothesis. Introduce `hx`.

Conclude with `mul_intMat hk'.1 hx`. Rewrite `h` using `[hpre, h1, one_smul]`. Conclude with `h`.
-/
theorem map_mul_eq (hLF : LF O ϖ nrm q) (n m : ℕ) (dx : Measure (Matrix (Fin n) (Fin m) F))
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1) :
    (∀ g : GL (Fin m) F, Measure.map (fun x : Matrix (Fin n) (Fin m) F =>
        x * (g : Matrix (Fin m) (Fin m) F)) dx =
      ENNReal.ofReal ((nrm (g : Matrix (Fin m) (Fin m) F).det)⁻¹ ^ n) • dx) ∧
    (∀ k ∈ GLint O n, Measure.map (fun x : Matrix (Fin n) (Fin m) F =>
        (k : Matrix (Fin n) (Fin n) F) * x) dx = dx) := by
  haveI : BorelSpace (Matrix (Fin n) (Fin m) F) := (GlobalTheory.T.matrix_additive_haar_normalized hLF n m).1
  refine ⟨fun g => ?_, fun k hk => ?_⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, e, d, hd, rfl⟩ := GlobalTheory.T.cartan_decomposition_generalLinear hLF m g
    have hdd : d = dg (fun i => (Units.mk0 ϖ hLF.ne) ^ e i) := by
      apply Units.ext
      rw [hd]
      change _ = Matrix.diagonal fun i => ((((Units.mk0 ϖ hLF.ne) ^ e i : Fˣ)) : F)
      congr 1
      funext i
      simp
    have hmem : k₁ * d * k₂ ∈ stab nrm dx := by
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (glint_mem_stab hLF hinv h1 hk₁) ?_)
        (glint_mem_stab hLF hinv h1 hk₂)
      rw [hdd]
      exact diag_mem_stab hLF hinv h1 e
    exact mem_stab.1 hmem
  · have hk' : IsInt O (k : Matrix (Fin n) (Fin n) F) ∧
        IsInt O ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := hk
    have h := map_eq_smul hLF hinv h1 (leftMul m k)
    have hpre : (leftMul m k : Matrix (Fin n) (Fin m) F → _) ⁻¹' intMat O n m = intMat O n m := by
      ext x
      change (k : Matrix (Fin n) (Fin n) F) * x ∈ intMat O n m ↔ x ∈ intMat O n m
      constructor
      · intro hx
        have h2 := mul_intMat hk'.2 hx
        rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at h2
      · intro hx
        exact mul_intMat hk'.1 hx
    rw [hpre, h1, one_smul] at h
    exact h

end Measure

/- English proof (translation)
Introduce `hLF n m dx hinv h1` and use `map_mul_eq hLF n m dx hinv h1`.
-/
theorem haar_mat_scale : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, ∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → (∀ g : GL (Fin m) F, Measure.map (fun x : Matrix (Fin n) (Fin m) F => x * (g : Matrix (Fin m) (Fin m) F)) dx = ENNReal.ofReal ((nrm (g : Matrix (Fin m) (Fin m) F).det)⁻¹ ^ n) • dx) ∧ (∀ k ∈ GLint O n, Measure.map (fun x : Matrix (Fin n) (Fin m) F => (k : Matrix (Fin n) (Fin n) F) * x) dx = dx) :=
  fun hLF n m dx hinv h1 => map_mul_eq hLF n m dx hinv h1

end GlobalTheory.CompanionTheory.QLScale
