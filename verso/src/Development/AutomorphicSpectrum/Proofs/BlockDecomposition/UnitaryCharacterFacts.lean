import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.TorusChar

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ hij]`.

Conclude with `h i j hij`.
-/
theorem exists_diag {n : ℕ} {g : GL (Fin n) L} (h : IsDiagM g) :
    (g : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (g : Matrix (Fin n) (Fin n) L) i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [Matrix.diagonal_apply_ne _ hij]; exact h i j hij

/- English proof (translation)
Introduce `h0`. Establish `h1 : ((g * g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1` using `by simp`. Rewrite `h1` using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero]`. Conclude with `zero_ne_one h1`. Introduce `j _`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[h0, zero_mul]`. Rewrite using `[h i j hij, zero_mul]`.
-/
theorem diag_ne_zero {n : ℕ} {g : GL (Fin n) L} (h : IsDiagM g) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  intro h0
  have h1 : ((g * g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
  · exact zero_ne_one h1
  · intro j _
    by_cases hij : i = j
    · subst hij; rw [h0, zero_mul]
    · rw [h i j hij, zero_mul]

/- English proof (translation)
Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[exists_diag h, Matrix.diagonal_mul_diagonal]`. Simplify using `only [Matrix.diagonal_apply_eq]`. Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`.

Use extensionality with `i`. Conclude with `mul_inv_cancel₀ (diag_ne_zero h i)`.
-/
theorem inv_val {n : ℕ} {g : GL (Fin n) L} (h : IsDiagM g) :
    ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((g : Matrix (Fin n) (Fin n) L) i i)⁻¹) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [exists_diag h, Matrix.diagonal_mul_diagonal]
  simp only [Matrix.diagonal_apply_eq]
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  exact mul_inv_cancel₀ (diag_ne_zero h i)

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[inv_val h, Matrix.diagonal_apply_ne _ hij]`.
-/
theorem isDiag_inv {n : ℕ} {g : GL (Fin n) L} (h : IsDiagM g) : IsDiagM g⁻¹ := by
  intro i j hij
  rw [inv_val h, Matrix.diagonal_apply_ne _ hij]

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[Units.val_mul, exists_diag h, exists_diag h', Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ hij]`.
-/
theorem isDiag_mul {n : ℕ} {g k : GL (Fin n) L} (h : IsDiagM g) (h' : IsDiagM k) : IsDiagM (g * k) := by
  intro i j hij
  rw [Units.val_mul, exists_diag h, exists_diag h', Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_ne _ hij]

/- English proof (translation)
Establish `key : ∀ i j : Fin n, ((s * u * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (s : Matrix (Fin n) (Fin n) L) i i * (u : Matrix (Fin n) (Fin n) L) i j * ((s : Matrix (Fin n) (Fin n) L) j j)⁻¹`. Introduce `i j`. Rewrite using `[Units.val_mul, Units.val_mul, inv_val hs, Matrix.mul_diagonal]`. Use `congr 1`. Use `conv_lhs => rw [exists_diag hs]`.

Rewrite using `[Matrix.diagonal_mul]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[key, hu.1 i j hij]`. Simplify using the standard rewrite rules. Rewrite using `[key, hu.2 i, mul_one]`.

Conclude with `mul_inv_cancel₀ (diag_ne_zero hs i)`.
-/
theorem isUni_conj {n : ℕ} {s u : GL (Fin n) L} (hs : IsDiagM s) (hu : IsUniM u) : IsUniM (s * u * s⁻¹) := by
  have key : ∀ i j : Fin n, ((s * u * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      (s : Matrix (Fin n) (Fin n) L) i i * (u : Matrix (Fin n) (Fin n) L) i j *
        ((s : Matrix (Fin n) (Fin n) L) j j)⁻¹ := by
    intro i j
    rw [Units.val_mul, Units.val_mul, inv_val hs, Matrix.mul_diagonal]
    congr 1
    conv_lhs => rw [exists_diag hs]
    rw [Matrix.diagonal_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, hu.1 i j hij]; simp
  · rw [key, hu.2 i, mul_one]; exact mul_inv_cancel₀ (diag_ne_zero hs i)

variable {σ : L →+* L} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hle : jacU ρ ≤ (jacU ρ).comap (ρ s)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, v, rfl⟩`. Use `Submodule.subset_span ⟨s * u * s⁻¹, ?_, ρ s v, ?_⟩` and prove the remaining obligations. Use `isUni_conj hs hu` as an intermediate fact.

Simplify using `using this`. Establish `e : ρ (s * u * s⁻¹) (ρ s v) = ρ s (ρ u v)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]`. Rewrite using `[map_sub, e]`. Conclude with `hle hx`.
-/
theorem map_jac (ρ : Representation ℂ (GU σ n) V) {s : GU σ n} (hs : IsDiagM (s : GL (Fin n) L))
    {x : V} (hx : x ∈ jacU ρ) : ρ s x ∈ jacU ρ := by
  have hle : jacU ρ ≤ (jacU ρ).comap (ρ s) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, v, rfl⟩
    refine Submodule.subset_span ⟨s * u * s⁻¹, ?_, ρ s v, ?_⟩
    · have := isUni_conj hs hu
      simpa using this
    · have e : ρ (s * u * s⁻¹) (ρ s v) = ρ s (ρ u v) := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]
      rw [map_sub, e]
  exact hle hx

/- English proof (translation)
Establish `h1` using `he (s * t) (by simpa using isDiag_mul hs ht)`. Establish `h2` using `map_jac ρ hs (he t ht)`. Establish `h3` using `(jacU ρ).smul_mem (ξ t) (he s hs)`. Establish `h4` using `(jacU ρ).sub_mem ((jacU ρ).sub_mem h1 h2) h3`. Establish `h5 : (ρ (s * t) y - ξ (s * t) • y) - ρ s (ρ t y - ξ t • y) - ξ t • (ρ s y - ξ s • y) = (ξ s * ξ t - ξ (s * t)) • y`.

Simplify using `only [map_sub, map_smul, map_mul, Module.End.mul_apply, smul_sub, sub_smul, mul_smul]`. Rewrite using `[smul_comm (ξ t) (ξ s) y]`. Normalize the expressions using the abelian group laws. Rewrite `h4` using `[h5]`. Assume the negation of the conclusion as `hne`.

Conclude with `hy (((jacU ρ).smul_mem_iff (sub_ne_zero.2 (Ne.symm hne))).1 h4)`.
-/
theorem xi_mul {ρ : Representation ℂ (GU σ n) V} {ξ : GU σ n → ℂ} {y : V} (hy : y ∉ jacU ρ)
    (he : ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y - ξ t • y ∈ jacU ρ)
    {s t : GU σ n} (hs : IsDiagM (s : GL (Fin n) L)) (ht : IsDiagM (t : GL (Fin n) L)) :
    ξ (s * t) = ξ s * ξ t := by
  have h1 := he (s * t) (by simpa using isDiag_mul hs ht)
  have h2 := map_jac ρ hs (he t ht)
  have h3 := (jacU ρ).smul_mem (ξ t) (he s hs)
  have h4 := (jacU ρ).sub_mem ((jacU ρ).sub_mem h1 h2) h3
  have h5 : (ρ (s * t) y - ξ (s * t) • y) - ρ s (ρ t y - ξ t • y) - ξ t • (ρ s y - ξ s • y) =
      (ξ s * ξ t - ξ (s * t)) • y := by
    simp only [map_sub, map_smul, map_mul, Module.End.mul_apply, smul_sub, sub_smul, mul_smul]
    rw [smul_comm (ξ t) (ξ s) y]
    abel
  rw [h5] at h4
  by_contra hne
  exact hy (((jacU ρ).smul_mem_iff (sub_ne_zero.2 (Ne.symm hne))).1 h4)

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Formalism.UG.cT]`. Simplify using `[Formalism.UG.cT, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]`.
-/
theorem cT_diag (σ : L →+* L) (d : Fin n → L) :
    Formalism.UG.cT σ (Matrix.diagonal d) = Matrix.diagonal (fun i => σ (d i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Formalism.UG.cT]
  · simp [Formalism.UG.cT, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]

/- English proof (translation)
Establish `h : Formalism.UG.cT σ ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n * ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n` using `t.2`. Establish `h'` using `congrFun (congrFun h i) j`. Rewrite `h'` using `[exists_diag ht, cT_diag, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Simplify `h'` using `[antiJ, hij]`.
-/
theorem diag_rel {t : GU σ n} (ht : IsDiagM (t : GL (Fin n) L)) {i j : Fin n}
    (hij : i.val + j.val + 1 = n) :
    σ (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j = 1 := by
  have h : Formalism.UG.cT σ ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n := t.2
  have h' := congrFun (congrFun h i) j
  rw [exists_diag ht, cT_diag, Matrix.mul_diagonal, Matrix.diagonal_mul] at h'
  simpa [antiJ, hij] using h'

def mkDiag (σ : L →+* L) (n : ℕ) (d : Fin n → L) (hd : ∀ i, d i ≠ 0)
    (hJ : ∀ i j : Fin n, i.val + j.val + 1 = n → σ (d i) * d j = 1) : GU σ n :=
  ⟨⟨Matrix.diagonal d, Matrix.diagonal (fun i => (d i)⁻¹),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hd i),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hd i)⟩,
    by
      change Formalism.UG.cT σ (Matrix.diagonal d) * antiJ L n * Matrix.diagonal d = antiJ L n
      rw [cT_diag]
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hij : i.val + j.val + 1 = n
      · simpa [antiJ, hij] using hJ i j hij
      · simp [antiJ, hij]⟩

def ext0 {m : ℕ} (a : Fin m → ℤ) (i : ℕ) : ℤ := if h : i < m then a ⟨i, h⟩ else 0

def eps (n : ℕ) (a : Fin (n / 2) → ℤ) (i : Fin n) : ℤ := ext0 a i.val - ext0 a (n - 1 - i.val)

/- English proof (translation)
Apply the tactic sequence `unfold ext0; split_ifs <;> simp`.
-/
theorem matrixExtendByZero_add {m : ℕ} (a b : Fin m → ℤ) (i : ℕ) : ext0 (a + b) i = ext0 a i + ext0 b i := by
  unfold ext0; split_ifs <;> simp

/- English proof (translation)
Unfold `eps`. Rewrite using `[matrixExtendByZero_add, matrixExtendByZero_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eps_add (a b : Fin (n / 2) → ℤ) (i : Fin n) : eps n (a + b) i = eps n a i + eps n b i := by
  unfold eps; rw [matrixExtendByZero_add, matrixExtendByZero_add]; ring

/- English proof (translation)
Simplify using `[eps, ext0]`.
-/
theorem eps_zero (i : Fin n) : eps n 0 i = 0 := by
  simp [eps, ext0]

/- English proof (translation)
Establish `h1 : n - 1 - i.val = j.val` using `by omega`. Establish `h2 : n - 1 - j.val = i.val` using `by omega`. Unfold `eps`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eps_anti (a : Fin (n / 2) → ℤ) {i j : Fin n} (hij : i.val + j.val + 1 = n) :
    eps n a j = - eps n a i := by
  have h1 : n - 1 - i.val = j.val := by omega
  have h2 : n - 1 - j.val = i.val := by omega
  unfold eps; rw [h1, h2]; ring

def tU {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) (n : ℕ) (a : Fin (n / 2) → ℤ) : GU σ n :=
  mkDiag σ n (fun i => ϖ ^ eps n a i) (fun i => zpow_ne_zero _ h0) (by
    intro i j hij
    simp only [map_zpow₀, hσ]
    rw [eps_anti a hij, zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero _ h0))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tU_val {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) (a : Fin (n / 2) → ℤ) :
    (((tU h0 hσ n a : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ϖ ^ eps n a i) := rfl

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[tU_val, Matrix.diagonal_apply_ne _ hij]`.
-/
theorem isDiag_tU {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) (a : Fin (n / 2) → ℤ) :
    IsDiagM ((tU h0 hσ n a : GU σ n) : GL (Fin n) L) := by
  intro i j hij
  rw [tU_val, Matrix.diagonal_apply_ne _ hij]

/- English proof (translation)
Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, Units.val_mul, tU_val, tU_val, tU_val, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use extensionality with `i`. Rewrite using `[eps_add, zpow_add₀ h0]`.
-/
theorem tU_add {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) (a b : Fin (n / 2) → ℤ) :
    (tU h0 hσ n (a + b) : GU σ n) = tU h0 hσ n a * tU h0 hσ n b := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, tU_val, tU_val, tU_val, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  rw [eps_add, zpow_add₀ h0]

/- English proof (translation)
Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Rewrite using `[tU_val]`. Simplify using `[eps_zero]`.
-/
theorem tU_zero {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) : (tU h0 hσ n 0 : GU σ n) = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [tU_val]
  simp [eps_zero]

/- English proof (translation)
Establish `hmem : ∀ x : L, Valued.v x = 1 → x ∈ intL L` using `fun x h => (Valuation.mem_integer_iff _ _).2 h.le`. Establish `hinv : ∀ i, Valued.v ((((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) = 1`. Introduce `i`. Rewrite using `[map_inv₀, hv, inv_one]`. Unfold `KU`.

Rewrite using `[Subgroup.mem_subgroupOf]`. Use `⟨k.2, ⟨Matrix.diagonal (fun i => ⟨_, hmem _ (hv i)⟩), Matrix.diagonal (fun i => ⟨_, hmem _ (hinv i)⟩), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`.

Conclude with `mul_inv_cancel₀ (diag_ne_zero hk i)`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`. Conclude with `inv_mul_cancel₀ (diag_ne_zero hk i)`.

Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(Matrix.diagonal _).map _ = _`. Use `conv_rhs => rw [exists_diag hk]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.diagonal_apply_ne _ hij]`.
-/
theorem mem_KU {k : GU σ n} (hk : IsDiagM (k : GL (Fin n) L))
    (hv : ∀ i, Valued.v (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1) : k ∈ KU σ n := by
  have hmem : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x h => (Valuation.mem_integer_iff _ _).2 h.le
  have hinv : ∀ i, Valued.v ((((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) = 1 := by
    intro i; rw [map_inv₀, hv, inv_one]
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  refine ⟨k.2, ⟨Matrix.diagonal (fun i => ⟨_, hmem _ (hv i)⟩), Matrix.diagonal (fun i => ⟨_, hmem _ (hinv i)⟩), ?_, ?_⟩, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i
    exact mul_inv_cancel₀ (diag_ne_zero hk i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i
    exact inv_mul_cancel₀ (diag_ne_zero hk i)
  · apply Units.ext
    change (Matrix.diagonal _).map _ = _
    conv_rhs => rw [exists_diag hk]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij]

/- English proof (translation)
Establish `h : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Unfold `ordL`. Rewrite using `[dif_neg h, hϖ]`. Use `conv_lhs => rw [← WithZero.coe_unzero h]`. Rewrite using `[← WithZero.coe_zpow]`.

Use `congr 1`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem v_eq_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {x : L} (hx : x ≠ 0) : Valued.v x = (Valued.v ϖ) ^ (ordL x) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dif_neg h, hϖ]
  conv_lhs => rw [← WithZero.coe_unzero h]
  rw [← WithZero.coe_zpow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

/- English proof (translation)
Establish `hne : x ≠ 0` using `by rintro rfl; simp at h`. Take `⟨w, rfl⟩` from `WithZero.ne_zero_iff_exists.1 hne`. Establish `h1 : w * w = 1` using `by exact_mod_cast h`. Establish `h2` using `congrArg Multiplicative.toAdd h1`. Establish `h3 : w = 1`.

Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using `only [toAdd_mul, toAdd_one] at h2 ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h3]`. Both sides reduce to the same expression.
-/
theorem sq_one {x : WithZero (Multiplicative ℤ)} (h : x * x = 1) : x = 1 := by
  have hne : x ≠ 0 := by rintro rfl; simp at h
  obtain ⟨w, rfl⟩ := WithZero.ne_zero_iff_exists.1 hne
  have h1 : w * w = 1 := by exact_mod_cast h
  have h2 := congrArg Multiplicative.toAdd h1
  have h3 : w = 1 := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one] at h2 ⊢
    omega
  rw [h3]; rfl

def ordVec (t : GU σ n) : Fin (n / 2) → ℤ := fun i =>
  ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    ⟨i.val, lt_of_lt_of_le i.2 (Nat.div_le_self n 2)⟩ ⟨i.val, lt_of_lt_of_le i.2 (Nat.div_le_self n 2)⟩)

/- English proof (translation)
Establish `hi` using `i.2`. Set `j : Fin n` to `⟨n - 1 - i.val, by omega⟩`. Establish `hj : j.val = n - 1 - i.val` using `rfl`. Establish `hij : i.val + j.val + 1 = n` using `by omega`. Establish `hv : Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) * Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) = 1`.

Rewrite using `[← hσv (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i), ← map_mul, diag_rel ht hij, map_one]`. Unfold `eps`. Distinguish the cases in `h1 : i.val < n / 2`. Establish `e1 : ext0 (ordVec t) i.val = ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)`. Unfold `ext0`.

Rewrite using `[dif_pos h1]`. Both sides reduce to the same expression. Establish `e2 : ext0 (ordVec t) (n - 1 - i.val) = 0`. Unfold `ext0; rw [dif_neg (by omega)]`. Rewrite using `[e1, e2, sub_zero]`.

Conclude with `v_eq_zpow hϖ (diag_ne_zero ht i)`. Establish `e1 : ext0 (ordVec t) i.val = 0`. Unfold `ext0`. Rewrite using `[dif_neg h1]`. Distinguish the cases in `h2 : j.val < n / 2`.

Establish `e2 : ext0 (ordVec t) (n - 1 - i.val) = ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j)`. Unfold `ext0; rw [dif_pos (by omega)]; rfl`. Rewrite using `[e1, e2, zero_sub, zpow_neg, ← v_eq_zpow hϖ (diag_ne_zero ht j)]`. Conclude with `eq_inv_of_mul_eq_one_left hv`. Establish `hji : j = i` using `Fin.ext (by omega)`.

Establish `e2 : ext0 (ordVec t) (n - 1 - i.val) = 0`. Unfold `ext0; rw [dif_neg (by omega)]`. Rewrite using `[e1, e2, sub_zero, zpow_zero]`. Rewrite `hv` using `[hji]`. Conclude with `sq_one hv`.
-/
theorem v_entry {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {t : GU σ n} (ht : IsDiagM (t : GL (Fin n) L)) (i : Fin n) :
    Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = (Valued.v ϖ) ^ eps n (ordVec t) i := by
  have hi := i.2
  let j : Fin n := ⟨n - 1 - i.val, by omega⟩
  have hj : j.val = n - 1 - i.val := rfl
  have hij : i.val + j.val + 1 = n := by omega
  have hv : Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) = 1 := by
    rw [← hσv (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i), ← map_mul, diag_rel ht hij, map_one]
  unfold eps
  by_cases h1 : i.val < n / 2
  · have e1 : ext0 (ordVec t) i.val = ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) := by
      unfold ext0; rw [dif_pos h1]; rfl
    have e2 : ext0 (ordVec t) (n - 1 - i.val) = 0 := by
      unfold ext0; rw [dif_neg (by omega)]
    rw [e1, e2, sub_zero]
    exact v_eq_zpow hϖ (diag_ne_zero ht i)
  · have e1 : ext0 (ordVec t) i.val = 0 := by
      unfold ext0; rw [dif_neg h1]
    by_cases h2 : j.val < n / 2
    · have e2 : ext0 (ordVec t) (n - 1 - i.val) =
          ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) := by
        unfold ext0; rw [dif_pos (by omega)]; rfl
      rw [e1, e2, zero_sub, zpow_neg, ← v_eq_zpow hϖ (diag_ne_zero ht j)]
      exact eq_inv_of_mul_eq_one_left hv
    · have hji : j = i := Fin.ext (by omega)
      have e2 : ext0 (ordVec t) (n - 1 - i.val) = 0 := by
        unfold ext0; rw [dif_neg (by omega)]
      rw [e1, e2, sub_zero, zpow_zero]
      rw [hji] at hv
      exact sq_one hv

/- English proof (translation)
Establish `hT` using `isDiag_tU (σ := σ) h0 hσ (ordVec t)`. Establish `hk : IsDiagM (((tU h0 hσ n (ordVec t))⁻¹ * t : GU σ n) : GL (Fin n) L)`. Simplify using `using isDiag_mul (isDiag_inv hT) ht`. Use `⟨(tU h0 hσ n (ordVec t))⁻¹ * t, mem_KU hk ?_, hk, by simp⟩` and prove the remaining obligations. Introduce `i`.

Establish `he : ((((tU h0 hσ n (ordVec t))⁻¹ * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = (ϖ ^ eps n (ordVec t) i)⁻¹ * ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, inv_val hT, tU_val, Matrix.diagonal_mul]`. Simplify using the standard rewrite rules. Apply the tactic sequence `rw [he, map_mul, map_inv₀, map_zpow₀, v_entry hϖ hσv ht i]`. Conclude with `inv_mul_cancel₀ (zpow_ne_zero _ (by`.

Rewrite using `[hϖ]`. Conclude with `WithZero.coe_ne_zero))`.
-/
theorem exists_decomp {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {t : GU σ n} (ht : IsDiagM (t : GL (Fin n) L)) :
    ∃ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) ∧ t = tU h0 hσ n (ordVec t) * k := by
  have hT := isDiag_tU (σ := σ) h0 hσ (ordVec t)
  have hk : IsDiagM (((tU h0 hσ n (ordVec t))⁻¹ * t : GU σ n) : GL (Fin n) L) := by
    simpa using isDiag_mul (isDiag_inv hT) ht
  refine ⟨(tU h0 hσ n (ordVec t))⁻¹ * t, mem_KU hk ?_, hk, by simp⟩
  intro i
  have he : ((((tU h0 hσ n (ordVec t))⁻¹ * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      (ϖ ^ eps n (ordVec t) i)⁻¹ * ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, inv_val hT, tU_val, Matrix.diagonal_mul]
    simp
  rw [he, map_mul, map_inv₀, map_zpow₀, v_entry hϖ hσv ht i]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by
    rw [hϖ]; exact WithZero.coe_ne_zero))

/- English proof (translation)
Set `f : (Fin m → ℤ) →+ Additive ℂˣ` to `AddMonoidHom.mk' (fun a => Additive.ofMul (Φ a)) (fun a b => by rw [h]; rfl)`. Establish `ha : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin m → ℤ)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `h2 : f a = ∑ i, a i • f (Pi.single i 1)` using `by conv_lhs => rw [ha]`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => map_zsmul f _ _`. Establish `h3` using `congrArg Additive.toMul h2`. Simplify `h3` using `[f, toMul_sum]`.
-/
theorem hom_prod {m : ℕ} (Φ : (Fin m → ℤ) → ℂˣ) (h : ∀ a b, Φ (a + b) = Φ a * Φ b) (a : Fin m → ℤ) :
    Φ a = ∏ i, Φ (Pi.single i 1) ^ a i := by
  let f : (Fin m → ℤ) →+ Additive ℂˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (Φ a))
    (fun a b => by rw [h]; rfl)
  have ha : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin m → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : f a = ∑ i, a i • f (Pi.single i 1) := by
    conv_lhs => rw [ha]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul f _ _
  have h3 := congrArg Additive.toMul h2
  simpa [f, toMul_sum] using h3

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n V _ _ ρ hU ξ y hy he hk`. Take `⟨-, hσv, hσϖ, hϖ, -, hq, -⟩` from `hU`. Establish `h0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ` using `[h, map_zero]`.

Conclude with `WithZero.coe_ne_zero hϖ.symm`. Establish `hT : ∀ a, IsDiagM ((tU h0 hσϖ n a : GU σ n) : GL (Fin n) L)` using `isDiag_tU h0 hσϖ`. Establish `hone : ξ 1 = 1` using `hk 1 (one_mem _) (by`. Introduce `i j hij`. Simplify using `[Matrix.one_apply_ne hij])`.

Establish `hmul : ∀ a b, ξ (tU h0 hσϖ n (a + b)) = ξ (tU h0 hσϖ n a) * ξ (tU h0 hσϖ n b)`. Introduce `a b`. Rewrite using `[tU_add]`. Conclude with `xi_mul hy he (hT a) (hT b)`. Set `Φ : (Fin (n / 2) → ℤ) → ℂˣ` to `fun a => ⟨ξ (tU h0 hσϖ n a), ξ (tU h0 hσϖ n (-a)), by rw [← hmul, add_neg_cancel, tU_zero, hone], by rw [← hmul, neg_add_cancel, tU_zero, hone]⟩`.

Establish `hΦ : ∀ a b, Φ (a + b) = Φ a * Φ b` using `fun a b => Units.ext (hmul a b)`. Establish `hq0 : (q : ℂ) ≠ 0`. Establish `: q ≠ 0` using `by omega`. Conclude with `this` after adjusting the coercions. Use `⟨fun i => Φ (Pi.single i 1) * Units.mk0 (q : ℂ) hq0 ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)), fun t ht => ?_⟩` and prove the remaining obligations.

Take `⟨k, hkK, hkd, hdec⟩` from `exists_decomp h0 hσϖ hϖ hσv ht`. Establish `h1 : ξ t = ((Φ (ordVec t) : ℂˣ) : ℂ)` using `by conv_lhs => rw [hdec]`. Rewrite using `[xi_mul hy he (hT _) hkd, hk k hkK hkd, mul_one]`. Rewrite using `[h1, hom_prod Φ hΦ, Units.coe_prod]`. Unfold `chiDeltaU`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi : i.val < n` using `lt_of_lt_of_le i.2 (Nat.div_le_self n 2)`. Rewrite using `[dif_pos hi]`. Express the relevant statement in the definitionally equal form `_ = _ ^ (ordVec t i) * _ ^ (-(ordVec t i) * _)`. Simplify using `only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_mk0]`.

Rewrite using `[mul_zpow, mul_assoc, ← zpow_mul, ← zpow_add₀ hq0]`. Establish `: ((n : ℤ) - 1 - 2 * (i.val : ℤ)) * ordVec t i + -(ordVec t i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)) = 0` using `by ring`. Rewrite using `[this, zpow_zero, mul_one]`.
-/
theorem charU : PositivityTheory.SphericalProduct.CharU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ hU ξ y hy he hk
  obtain ⟨-, hσv, hσϖ, hϖ, -, hq, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.coe_ne_zero hϖ.symm
  have hT : ∀ a, IsDiagM ((tU h0 hσϖ n a : GU σ n) : GL (Fin n) L) := isDiag_tU h0 hσϖ
  have hone : ξ 1 = 1 := hk 1 (one_mem _) (by
    intro i j hij
    simp [Matrix.one_apply_ne hij])
  have hmul : ∀ a b, ξ (tU h0 hσϖ n (a + b)) = ξ (tU h0 hσϖ n a) * ξ (tU h0 hσϖ n b) := by
    intro a b
    rw [tU_add]
    exact xi_mul hy he (hT a) (hT b)
  let Φ : (Fin (n / 2) → ℤ) → ℂˣ := fun a => ⟨ξ (tU h0 hσϖ n a), ξ (tU h0 hσϖ n (-a)),
    by rw [← hmul, add_neg_cancel, tU_zero, hone], by rw [← hmul, neg_add_cancel, tU_zero, hone]⟩
  have hΦ : ∀ a b, Φ (a + b) = Φ a * Φ b := fun a b => Units.ext (hmul a b)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  refine ⟨fun i => Φ (Pi.single i 1) * Units.mk0 (q : ℂ) hq0 ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)), fun t ht => ?_⟩
  obtain ⟨k, hkK, hkd, hdec⟩ := exists_decomp h0 hσϖ hϖ hσv ht
  have h1 : ξ t = ((Φ (ordVec t) : ℂˣ) : ℂ) := by
    conv_lhs => rw [hdec]
    rw [xi_mul hy he (hT _) hkd, hk k hkK hkd, mul_one]
  rw [h1, hom_prod Φ hΦ, Units.coe_prod]
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : i.val < n := lt_of_lt_of_le i.2 (Nat.div_le_self n 2)
  rw [dif_pos hi]
  change _ = _ ^ (ordVec t i) * _ ^ (-(ordVec t i) * _)
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_mk0]
  rw [mul_zpow, mul_assoc, ← zpow_mul, ← zpow_add₀ hq0]
  have : ((n : ℤ) - 1 - 2 * (i.val : ℤ)) * ordVec t i + -(ordVec t i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)) = 0 := by ring
  rw [this, zpow_zero, mul_one]

end GlobalTheory.CompanionTheory.TorusChar

end
