import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CellDec.Unimod

variable {R : Type} [CommRing R] {n : ℕ}

def Fil (k : ℕ) (X : Matrix (Fin n) (Fin n) R) : Prop := ∀ i j : Fin n, (j : ℕ) < i + k → X i j = 0

/- English proof (translation)
Introduce `i j h` and use `by rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]`.
-/
theorem fil_add {k : ℕ} {X Y : Matrix (Fin n) (Fin n) R} (hX : Fil k X) (hY : Fil k Y) : Fil k (X + Y) :=
  fun i j h => by rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

/- English proof (translation)
Introduce `i j h` and use `by rw [Matrix.sub_apply, hX i j h, hY i j h, sub_zero]`.
-/
theorem fil_sub {k : ℕ} {X Y : Matrix (Fin n) (Fin n) R} (hX : Fil k X) (hY : Fil k Y) : Fil k (X - Y) :=
  fun i j h => by rw [Matrix.sub_apply, hX i j h, hY i j h, sub_zero]

/- English proof (translation)
Introduce `i j h` and use `by rw [Matrix.smul_apply, hX i j h, smul_zero]`.
-/
theorem fil_nsmul {k : ℕ} {X : Matrix (Fin n) (Fin n) R} (hX : Fil k X) (m : ℕ) : Fil k (m • X) :=
  fun i j h => by rw [Matrix.smul_apply, hX i j h, smul_zero]

/- English proof (translation)
Introduce `i j h` and use `hX i j (by omega)`.
-/
theorem fil_mono {a b : ℕ} {X : Matrix (Fin n) (Fin n) R} (hX : Fil b X) (hab : a ≤ b) : Fil a X :=
  fun i j h => hX i j (by omega)

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (l : ℕ) < i + a`. Rewrite using `[hX i l h, zero_mul]`.

Rewrite using `[hY l j (by omega), mul_zero]`.
-/
theorem fil_mul {a b : ℕ} {X Y : Matrix (Fin n) (Fin n) R} (hX : Fil a X) (hY : Fil b Y) :
    Fil (a + b) (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : (l : ℕ) < i + a
  · rw [hX i l h, zero_mul]
  · rw [hY l j (by omega), mul_zero]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro i j _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Establish `e : (1 + X) ^ (m + 1) - 1 - (m + 1) • X = ((1 + X) ^ m - 1 - m • X) + ((1 + X) ^ m - 1 - m • X) * X + m • (X * X)`.

Rewrite using `[pow_succ, add_smul, one_smul, mul_add, mul_one, sub_mul, sub_mul, one_mul, smul_mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `fil_add (fil_add ih (fil_mono (fil_mul ih hX) (by omega))) (fil_nsmul (fil_mono (fil_mul hX hX) (by omega)) m)` and prove the remaining obligations.
-/
theorem fil_pow {k : ℕ} (hk : 1 ≤ k) {X : Matrix (Fin n) (Fin n) R} (hX : Fil k X) (m : ℕ) :
    Fil (k + 1) ((1 + X) ^ m - 1 - m • X) := by
  induction m with
  | zero => intro i j _; simp
  | succ m ih =>
    have e : (1 + X) ^ (m + 1) - 1 - (m + 1) • X =
        ((1 + X) ^ m - 1 - m • X) + ((1 + X) ^ m - 1 - m • X) * X + m • (X * X) := by
      rw [pow_succ, add_smul, one_smul, mul_add, mul_one, sub_mul, sub_mul, one_mul, smul_mul_assoc]; abel
    rw [e]
    refine fil_add (fil_add ih (fil_mono (fil_mul ih hX) (by omega))) (fil_nsmul (fil_mono (fil_mul hX hX) (by omega)) m)

end GlobalTheory.CellDec.Unimod

namespace GlobalTheory.CellDec.Unimod

variable {R : Type} [CommRing R] {n : ℕ}

def wt (c : Rˣ) (i : Fin n) : Rˣ := c⁻¹ ^ (i : ℕ)

/- English proof (translation)
Simplify using `only [wt, h, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel, inv_mul_cancel, one_mul, inv_pow, inv_inv]`.
-/
theorem wt_mul_inv (c : Rˣ) {i j : Fin n} {k : ℕ} (h : (j : ℕ) = i + k) :
    (wt c i * (wt c j)⁻¹ : Rˣ) = c ^ k := by
  simp only [wt, h, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel, inv_mul_cancel, one_mul, inv_pow, inv_inv]

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]`. Distinguish the cases in `h' : (j : ℕ) < i + k`. Rewrite using `[hX i j h']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hj : (j : ℕ) = i + k` using `by omega`. Use `congrArg (fun x : Rˣ => (x : R)) (wt_mul_inv c hj)` as an intermediate fact. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val] at this`. Rewrite using `[mul_right_comm, this, sub_self]`.
-/
theorem fil_conj (c : Rˣ) {k : ℕ} {X : Matrix (Fin n) (Fin n) R} (hX : Fil k X) :
    Fil (k + 1) (diagonal (fun i => (wt c i : R)) * X * diagonal (fun i => (((wt c i)⁻¹ : Rˣ) : R))
      - ((c : R) ^ k) • X) := by
  intro i j h
  rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases h' : (j : ℕ) < i + k
  · rw [hX i j h']; ring
  · have hj : (j : ℕ) = i + k := by omega
    have := congrArg (fun x : Rˣ => (x : R)) (wt_mul_inv c hj)
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this
    rw [mul_right_comm, this, sub_self]

/- English proof (translation)
Set `M : (GlobalTheory.SmGL.unipB R (Fin n)) → Matrix (Fin n) (Fin n) R` to `fun u => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)`. Establish `hne : ∀ u : (GlobalTheory.SmGL.unipB R (Fin n)), Δ u ≠ 0` using `fun u h => by`. Use `map_mul Δ u u⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, map_one, h, zero_mul]`. Conclude with `one_ne_zero this`.

Establish `key : ∀ d k : ℕ, n ≤ k + d → 1 ≤ k → ∀ u : (GlobalTheory.SmGL.unipB R (Fin n)), Fil k (M u - 1) → Δ u = 1`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `k hk _ u hu`.

Establish `: u = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `hu i j (by omega)` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, sub_eq_zero]`. Conclude with `this`. Rewrite using `[this, map_one]`. Consider the case `succ d ih`. Introduce `k hk hk1 u hu`.

Establish `P` using `ih (k + 1) (by omega) (by omega)`. Use `set X := M u - 1 with hXdef`. Use `set t := GlobalTheory.SmGL.diagT R (Fin n) (wt c)`. Use `set a : (GlobalTheory.SmGL.unipB R (Fin n)) := u ^ (2 ^ k)`. Use `set b : (GlobalTheory.SmGL.unipB R (Fin n)) := ⟨t * u * t⁻¹, GlobalTheory.CellDec.diagT_conj_mem (wt c) u.2⟩`.

Establish `hMa : M a = (1 + X) ^ (2 ^ k)`. Rewrite using `[hXdef, add_sub_cancel]`. Simplify using `only [M, a, Subgroup.coe_pow, Units.val_pow_eq_pow_val]`. Establish `hMb : M b - 1 = diagonal (fun i => (wt c i : R)) * X * diagonal (fun i => (((wt c i)⁻¹ : Rˣ) : R))`. Establish `e1 : M b = diagonal (fun i => (wt c i : R)) * M u * diagonal (fun i => (((wt c i)⁻¹ : Rˣ) : R))`.

Simplify using `only [M, b, t, Units.val_mul, ← map_inv, GlobalTheory.SmGL.val_diagT, Pi.inv_apply]`. Establish `e2 : diagonal (fun i : Fin n => (wt c i : R)) * diagonal (fun i : Fin n => (((wt c i)⁻¹ : Rˣ) : R)) = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[e1, hXdef, mul_sub, sub_mul, mul_one, e2]`. Establish `hba : Fil (k + 1) (M b - M a)`. Establish `e : M b - M a = (M b - 1 - ((c : R) ^ k) • X) - (M a - 1 - (2 ^ k : ℕ) • X)`. Establish `: ((c : R) ^ k) • X = (2 ^ k : ℕ) • X`.

Rewrite using `[hc, ← Nat.cast_smul_eq_nsmul R]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[this]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, hMb, hMa]`. Conclude with `fil_sub (fil_conj c hu) (fil_pow hk1 hu _)`. Establish `hinv : Fil 0 (M a⁻¹)` using `fun i j h => ((GlobalTheory.SmGL.mem_unipB R).1 (a⁻¹).2).1 i j (by simpa using h)`. Establish `hab : Fil (k + 1) (M (a⁻¹ * b) - 1)`. Establish `e : M (a⁻¹ * b) - 1 = M a⁻¹ * (M b - M a)`.

Establish `h1 : M a⁻¹ * M a = 1`. Simplify using `only [M, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`. Both sides reduce to the same expression. Simplify using `only [M, Subgroup.coe_mul, Units.val_mul] at h1 ⊢`. Rewrite using `[mul_sub, h1]`.

Rewrite using `[e]`. Simplify using `using fil_mul hinv hba`. Establish `h1 : Δ b = Δ a`. Establish `: b = a * (a⁻¹ * b)` using `by group`. Rewrite using `[this, map_mul, P _ hab, mul_one]`.

Establish `hb : Δ b = Δ u` using `hΔ u`. Rewrite `h1` using `[hb, map_pow]`. Establish `h2 : Δ u ^ (2 ^ k - 1) = 1`. Establish `h3 : Δ u ^ (2 ^ k - 1) * Δ u = 1 * Δ u`. Rewrite using `[← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul, ← h1]`.

Conclude with `mul_right_cancel₀ (hne u) h3`. Establish `h4 : 2 ^ k - 1 ≠ 0`. Establish `: 2 ≤ 2 ^ k`. Combine the equalities or inequalities in the displayed calculation. Use linear arithmetic over natural numbers and integers.

Conclude with `(pow_eq_one_iff_of_nonneg zero_le h4).1 h2`. Use `key n 1 (by omega) le_rfl u fun i j h => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB R).1 u.2`. Rewrite using `[Matrix.sub_apply]`. Use `show ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j = 0`.

Break down `lt_or_eq_of_le (Nat.lt_succ_iff.1 h) with h' | h'` into its components or cases. Rewrite using `[h1 i j h', Matrix.one_apply_ne (fun e => by rw [e] at h'; exact lt_irrefl _ h'), sub_zero]`. Establish `: j = i` using `Fin.ext h'`. Substitute `this` using the available equality. Rewrite using `[h2, Matrix.one_apply_eq, sub_self]`.
-/
theorem hom_trivial (c : Rˣ) (hc : (c : R) = 2) (Δ : GlobalTheory.SmGL.unipB R (Fin n) →* ℝ≥0)
    (hΔ : ∀ u : GlobalTheory.SmGL.unipB R (Fin n),
      Δ ⟨GlobalTheory.SmGL.diagT R (Fin n) (wt c) * u * (GlobalTheory.SmGL.diagT R (Fin n) (wt c))⁻¹,
        GlobalTheory.CellDec.diagT_conj_mem (wt c) u.2⟩ = Δ u)
    (u : GlobalTheory.SmGL.unipB R (Fin n)) : Δ u = 1 := by
  let M : (GlobalTheory.SmGL.unipB R (Fin n)) → Matrix (Fin n) (Fin n) R := fun u => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  have hne : ∀ u : (GlobalTheory.SmGL.unipB R (Fin n)), Δ u ≠ 0 := fun u h => by
    have := map_mul Δ u u⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at this
    exact one_ne_zero this
  have key : ∀ d k : ℕ, n ≤ k + d → 1 ≤ k → ∀ u : (GlobalTheory.SmGL.unipB R (Fin n)), Fil k (M u - 1) → Δ u = 1 := by
    intro d
    induction d with
    | zero =>
      intro k hk _ u hu
      have : u = 1 := by
        apply Subtype.ext; apply Units.ext; ext i j
        have := hu i j (by omega)
        rw [Matrix.sub_apply, sub_eq_zero] at this
        exact this
      rw [this, map_one]
    | succ d ih =>
      intro k hk hk1 u hu
      have P := ih (k + 1) (by omega) (by omega)
      set X := M u - 1 with hXdef
      set t := GlobalTheory.SmGL.diagT R (Fin n) (wt c)
      set a : (GlobalTheory.SmGL.unipB R (Fin n)) := u ^ (2 ^ k)
      set b : (GlobalTheory.SmGL.unipB R (Fin n)) := ⟨t * u * t⁻¹, GlobalTheory.CellDec.diagT_conj_mem (wt c) u.2⟩
      have hMa : M a = (1 + X) ^ (2 ^ k) := by
        rw [hXdef, add_sub_cancel]
        simp only [M, a, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      have hMb : M b - 1 = diagonal (fun i => (wt c i : R)) * X * diagonal (fun i => (((wt c i)⁻¹ : Rˣ) : R)) := by
        have e1 : M b = diagonal (fun i => (wt c i : R)) * M u * diagonal (fun i => (((wt c i)⁻¹ : Rˣ) : R)) := by
          simp only [M, b, t, Units.val_mul, ← map_inv, GlobalTheory.SmGL.val_diagT, Pi.inv_apply]
        have e2 : diagonal (fun i : Fin n => (wt c i : R)) * diagonal (fun i : Fin n => (((wt c i)⁻¹ : Rˣ) : R)) = 1 := by
          rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1; funext i; simp
        rw [e1, hXdef, mul_sub, sub_mul, mul_one, e2]
      have hba : Fil (k + 1) (M b - M a) := by
        have e : M b - M a = (M b - 1 - ((c : R) ^ k) • X) - (M a - 1 - (2 ^ k : ℕ) • X) := by
          have : ((c : R) ^ k) • X = (2 ^ k : ℕ) • X := by
            rw [hc, ← Nat.cast_smul_eq_nsmul R]; push_cast; rfl
          rw [this]; abel
        rw [e, hMb, hMa]
        exact fil_sub (fil_conj c hu) (fil_pow hk1 hu _)
      have hinv : Fil 0 (M a⁻¹) := fun i j h =>
        ((GlobalTheory.SmGL.mem_unipB R).1 (a⁻¹).2).1 i j (by simpa using h)
      have hab : Fil (k + 1) (M (a⁻¹ * b) - 1) := by
        have e : M (a⁻¹ * b) - 1 = M a⁻¹ * (M b - M a) := by
          have h1 : M a⁻¹ * M a = 1 := by
            simp only [M, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
          simp only [M, Subgroup.coe_mul, Units.val_mul] at h1 ⊢
          rw [mul_sub, h1]
        rw [e]; simpa using fil_mul hinv hba
      have h1 : Δ b = Δ a := by
        have : b = a * (a⁻¹ * b) := by group
        rw [this, map_mul, P _ hab, mul_one]
      have hb : Δ b = Δ u := hΔ u
      rw [hb, map_pow] at h1

      have h2 : Δ u ^ (2 ^ k - 1) = 1 := by
        have h3 : Δ u ^ (2 ^ k - 1) * Δ u = 1 * Δ u := by
          rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul, ← h1]
        exact mul_right_cancel₀ (hne u) h3
      have h4 : 2 ^ k - 1 ≠ 0 := by
        have : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
        omega
      exact (pow_eq_one_iff_of_nonneg zero_le h4).1 h2
  refine key n 1 (by omega) le_rfl u fun i j h => ?_
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 u.2
  rw [Matrix.sub_apply]
  show ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j = 0
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 h) with h' | h'
  · rw [h1 i j h', Matrix.one_apply_ne (fun e => by rw [e] at h'; exact lt_irrefl _ h'), sub_zero]
  · have : j = i := Fin.ext h'
    subst this
    rw [h2, Matrix.one_apply_eq, sub_self]

end GlobalTheory.CellDec.Unimod

namespace GlobalTheory.CellDec.Unimod

/- English proof (translation)
Establish `R : ∀ (ρ : Measure G) [ρ.IsHaarMeasure] (h : G), ρ.map (· * h) = (Measure.modularCharacterFun h) • ρ`. Introduce `ρ _ h`. Rewrite using `[Measure.modularCharacterFun_eq_haarScalarFactor ρ h]`. Conclude with `Measure.isMulLeftInvariant_eq_smul _ ρ`. Set `μ : Measure G` to `Measure.haar`.

Set `ν : Measure G` to `μ.map φ`. Use `haveI : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ φ`. Establish `h1 : ν.map (· * φ g) = Measure.modularCharacterFun g • ν`. Establish `e : (· * φ g) ∘ φ = φ ∘ (· * g)` using `funext fun x => (map_mul φ x g).symm`. Simplify using `only [ν]`.

Establish `hφ : Measurable (φ : G → G)` using `(map_continuous φ).measurable`. Rewrite using `[Measure.map_map (measurable_mul_const _) hφ, e, ← Measure.map_map hφ (measurable_mul_const g), R μ g, Measure.map_smul]`. Establish `h2` using `R ν (φ g)`. Rewrite `h2` using `[h1]`. Take `⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G)` from `inferInstance`.

Establish `h3` using `congrArg (fun m : Measure G => m K) h2`. Simplify using `only [Measure.coe_nnreal_smul_apply] at h3`. Establish `hne : ν K ≠ 0` using `(Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'`. Establish `hnt : ν K ≠ ⊤` using `K.isCompact.measure_lt_top.ne`. Establish `h4` using `(ENNReal.mul_left_inj hne hnt).1 h3`.

Conclude with `(ENNReal.coe_injective h4).symm`.
-/
theorem modularCharacter_map_equiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (φ : G ≃ₜ* G) (g : G) : Measure.modularCharacter (φ g) = Measure.modularCharacter g := by
  have R : ∀ (ρ : Measure G) [ρ.IsHaarMeasure] (h : G),
      ρ.map (· * h) = (Measure.modularCharacterFun h) • ρ := by
    intro ρ _ h
    rw [Measure.modularCharacterFun_eq_haarScalarFactor ρ h]
    exact Measure.isMulLeftInvariant_eq_smul _ ρ
  let μ : Measure G := Measure.haar
  let ν : Measure G := μ.map φ
  haveI : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ φ
  have h1 : ν.map (· * φ g) = Measure.modularCharacterFun g • ν := by
    have e : (· * φ g) ∘ φ = φ ∘ (· * g) := funext fun x => (map_mul φ x g).symm
    simp only [ν]
    have hφ : Measurable (φ : G → G) := (map_continuous φ).measurable
    rw [Measure.map_map (measurable_mul_const _) hφ, e,
      ← Measure.map_map hφ (measurable_mul_const g), R μ g, Measure.map_smul]
  have h2 := R ν (φ g)
  rw [h1] at h2
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have h3 := congrArg (fun m : Measure G => m K) h2
  simp only [Measure.coe_nnreal_smul_apply] at h3
  have hne : ν K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hnt : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h4 := (ENNReal.mul_left_inj hne hnt).1 h3
  exact (ENNReal.coe_injective h4).symm

def conjEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (t : G)
    (h1 : ∀ u ∈ H, t * u * t⁻¹ ∈ H) (h2 : ∀ u ∈ H, t⁻¹ * u * t ∈ H) : H ≃ₜ* H where
  toFun u := ⟨t * u * t⁻¹, h1 u u.2⟩
  invFun u := ⟨t⁻¹ * u * t, h2 u u.2⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end GlobalTheory.CellDec.Unimod

namespace GlobalTheory.CellDec

open GlobalTheory.CellDec.Unimod in

/- English proof (translation)
Introduce `E _ _ n _ _ ν _`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E`. Use `haveI : LocallyCompactSpace (GA E n) := by haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Ad E)) haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding …`.

Conclude with `Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Use `haveI : SecondCountableTopology (GA E n) := by haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E)) haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.i …`. Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`. Establish `hcl : IsClosed ((NA E n : Subgroup (GA E n)) : Set (GA E n))`. Establish `hc : ∀ i j : Fin n, Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) i j` using `fun i j => (continuous_id.matrix_elem i j).comp Units.continuous_val`.

Establish `e : ((NA E n : Subgroup (GA E n)) : Set (GA E n)) = (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i j = 0}) ∩ ⋂ i : Fin n, {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i i = 1}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, NA, GlobalTheory.SmGL.mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]`. Rewrite using `[e]`. Conclude with `(isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const).inter (isClosed_iInter fun i => isClosed_eq (hc i i) continuous_const)`.

Use `haveI : LocallyCompactSpace (NA E n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (NA E n) := TopologicalSpace.Subtype.secondCountableTopology _`. Set `c : (Ad E)ˣ` to `Units.map (algebraMap E (Ad E)).toMonoidHom (Units.mk0 2 two_ne_zero)`. Establish `hc : (c : Ad E) = 2` using `by show algebraMap E (Ad E) 2 = 2`. Conclude with `map_ofNat _ 2`.

Set `t : GA E n` to `GlobalTheory.SmGL.diagT (Ad E) (Fin n) (wt c)`. Establish `h1 : ∀ u ∈ NA E n, t * u * t⁻¹ ∈ NA E n` using `fun u hu => diagT_conj_mem (wt c) hu`. Establish `h2 : ∀ u ∈ NA E n, t⁻¹ * u * t ∈ NA E n` using `fun u hu => by`. Use `diagT_conj_mem (wt c)⁻¹ hu` as an intermediate fact. Rewrite `this` using `[map_inv, inv_inv]`. Then use the resulting hypothesis.

Establish `hΔ : ∀ g : NA E n, Measure.modularCharacter g = 1` using `hom_trivial c hc Measure.modularCharacter fun u => modularCharacter_map_equiv (conjEquiv (NA E n) t h1 h2) u`. Use `haveI : ν.IsMulRightInvariant := ⟨fun g => by`. Use `Measure.isMulLeftInvariant_eq_smul (ν.map (· * g)) ν` as an intermediate fact. Rewrite `this` using `[← Measure.modularCharacterFun_eq_haarScalarFactor ν g]`. Rewrite using `[this, show Measure.modularCharacterFun g = 1 from hΔ g, one_smul]⟩`.

Prove the components needed by the constructor for the conclusion. Set `s : ENNReal` to `Measure.haarScalarFactor ν.inv ν`. Establish `hs : ν.inv = s • ν` using `Measure.isMulLeftInvariant_eq_smul ν.inv ν`. Establish `e1 : Measure.map Inv.inv (Measure.map Inv.inv ν) = s ^ 2 • ν`. Rewrite using `[← Measure.inv_def ν, hs, Measure.map_smul, ← Measure.inv_def ν, hs, smul_smul, pow_two]`.

Establish `e2 : ν = s ^ 2 • ν`. Rewrite `e1` using `[Measure.map_map continuous_inv.measurable continuous_inv.measurable]`. Simplify `e1` using `only [inv_involutive, Function.Involutive.comp_self, Measure.map_id]`. Take `⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (NA E n))` from `inferInstance`. Establish `e3 : s ^ 2 * ν K = 1 ^ 2 * ν K` using `by conv_rhs => rw [e2]`.

Simplify using the standard rewrite rules. Establish `e4 : s ^ 2 = 1 ^ 2` using `(ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne' K.isCompact.measure_lt_top.ne).1 e3`. Establish `e5 : s = 1` using `(ENNReal.pow_right_strictMono two_ne_zero).injective e4`. Rewrite using `[hs, e5, one_smul]`.
-/
theorem NA_isInvInvariant : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)]
    [BorelSpace (GA E n)] (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ν.IsInvInvariant := by
  intro E _ _ n _ _ ν _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : LocallyCompactSpace (GA E n) := by
    haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E)) :=
      inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Ad E))
    haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
    exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GA E n) := by
    haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
    haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  have hcl : IsClosed ((NA E n : Subgroup (GA E n)) : Set (GA E n)) := by
    have hc : ∀ i j : Fin n, Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) i j :=
      fun i j => (continuous_id.matrix_elem i j).comp Units.continuous_val
    have e : ((NA E n : Subgroup (GA E n)) : Set (GA E n)) =
        (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i j = 0}) ∩
          ⋂ i : Fin n, {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i i = 1} := by
      ext g
      simp only [SetLike.mem_coe, NA, GlobalTheory.SmGL.mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [e]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (hc i j) continuous_const).inter
      (isClosed_iInter fun i => isClosed_eq (hc i i) continuous_const)
  haveI : LocallyCompactSpace (NA E n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (NA E n) := TopologicalSpace.Subtype.secondCountableTopology _

  let c : (Ad E)ˣ := Units.map (algebraMap E (Ad E)).toMonoidHom (Units.mk0 2 two_ne_zero)
  have hc : (c : Ad E) = 2 := by
    show algebraMap E (Ad E) 2 = 2
    exact map_ofNat _ 2
  let t : GA E n := GlobalTheory.SmGL.diagT (Ad E) (Fin n) (wt c)
  have h1 : ∀ u ∈ NA E n, t * u * t⁻¹ ∈ NA E n := fun u hu => diagT_conj_mem (wt c) hu
  have h2 : ∀ u ∈ NA E n, t⁻¹ * u * t ∈ NA E n := fun u hu => by
    have := diagT_conj_mem (wt c)⁻¹ hu
    rwa [map_inv, inv_inv] at this
  have hΔ : ∀ g : NA E n, Measure.modularCharacter g = 1 :=
    hom_trivial c hc Measure.modularCharacter fun u =>
      modularCharacter_map_equiv (conjEquiv (NA E n) t h1 h2) u
  haveI : ν.IsMulRightInvariant := ⟨fun g => by
    have := Measure.isMulLeftInvariant_eq_smul (ν.map (· * g)) ν
    rw [← Measure.modularCharacterFun_eq_haarScalarFactor ν g] at this
    rw [this, show Measure.modularCharacterFun g = 1 from hΔ g, one_smul]⟩
  constructor
  let s : ENNReal := Measure.haarScalarFactor ν.inv ν
  have hs : ν.inv = s • ν := Measure.isMulLeftInvariant_eq_smul ν.inv ν
  have e1 : Measure.map Inv.inv (Measure.map Inv.inv ν) = s ^ 2 • ν := by
    rw [← Measure.inv_def ν, hs, Measure.map_smul, ← Measure.inv_def ν, hs, smul_smul, pow_two]
  have e2 : ν = s ^ 2 • ν := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at e1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using e1
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (NA E n)) := inferInstance
  have e3 : s ^ 2 * ν K = 1 ^ 2 * ν K := by
    conv_rhs => rw [e2]
    simp
  have e4 : s ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 e3
  have e5 : s = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective e4
  rw [hs, e5, one_smul]

end GlobalTheory.CellDec
