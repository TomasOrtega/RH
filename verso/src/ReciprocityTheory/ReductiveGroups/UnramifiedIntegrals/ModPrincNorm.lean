import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQuadInt

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Establish `hs : Real.sqrt d ≠ 0` using `(Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'`. Establish `hre` using `congrArg Complex.re h`. Establish `him` using `congrArg Complex.im h`. Simplify using `[sqD] at hre him`. Conclude with `⟨hre, him.resolve_right (by`.

Introduce `h0`. Apply `hs` to reduce the goal to its premises. Simplify using `using h0)⟩`.
-/
theorem sqD_indep {d : ℕ} (hd : 0 < d) (u v : ℚ) (h : (u : ℂ) + v * sqD d = 0) : u = 0 ∧ v = 0 := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sqD] at hre him
  exact ⟨hre, him.resolve_right (by
    intro h0
    apply hs
    simpa using h0)⟩

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t h`. Apply `sqD_indep hd` to reduce the goal to its premises. Use `congrArg (fun z : KQ d => (z : ℂ)) h` as an intermediate fact. Simplify `this` using `[sqK, Algebra.smul_def]`.
-/
theorem sqK_li {d : ℕ} (hd : 0 < d) : LinearIndependent ℚ ![(1 : KQ d), sqK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  apply sqD_indep hd
  have := congrArg (fun z : KQ d => (z : ℂ)) h
  simpa [sqK, Algebra.smul_def] using this

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[sqK, Algebra.smul_def, h]`.
-/
theorem sqK_decomp {d : ℕ} (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    z = p • (1 : KQ d) + q • sqK d := by
  apply Subtype.ext
  simp [sqK, Algebra.smul_def, h]

/- English proof (translation)
Introduce `z _`. Take `⟨u, v, h⟩` from `(KQ_mem_iff d z).1 z.2`. Rewrite using `[sqK_decomp z u v h]`. Use `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))` and prove the remaining obligations.
-/
theorem sqK_span {d : ℕ} : ⊤ ≤ Submodule.span ℚ (Set.range ![(1 : KQ d), sqK d]) := by
  intro z _
  obtain ⟨u, v, h⟩ := (KQ_mem_iff d z).1 z.2
  rw [sqK_decomp z u v h]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

def bKQ {d : ℕ} (hd : 0 < d) : Module.Basis (Fin 2) ℚ (KQ d) := Module.Basis.mk (sqK_li hd) sqK_span

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `sqD_sq d` as an intermediate fact. Simplify using `[sqK, ← this, sq]`.
-/
theorem sqK_mul_self (d : ℕ) : sqK d * sqK d = -(d : KQ d) := by
  apply Subtype.ext
  have := sqD_sq d
  simp [sqK, ← this, sq]

/- English proof (translation)
Establish `h0 : bKQ hd 0 = 1` using `by simp [bKQ]`. Establish `h1 : bKQ hd 1 = sqK d` using `by simp [bKQ]`. Establish `hz` using `sqK_decomp z p q h`. Establish `e0 : z * bKQ hd 0 = p • bKQ hd 0 + q • bKQ hd 1`. Rewrite using `[h0, h1, mul_one]`.

Conclude with `hz`. Establish `e1 : z * bKQ hd 1 = (-(d : ℚ) * q) • bKQ hd 0 + p • bKQ hd 1`. Rewrite using `[h0, h1, hz, add_mul, smul_mul_assoc, smul_mul_assoc, sqK_mul_self, one_mul]`. Simplify using `only [Algebra.smul_def, mul_one]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Algebra.norm_eq_matrix_det (bKQ hd), Matrix.det_fin_two]`. Simplify using `only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add, map_smul, Module.Basis.repr_self]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_KQ {d : ℕ} (hd : 0 < d) (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    Algebra.norm ℚ z = p ^ 2 + d * q ^ 2 := by
  have h0 : bKQ hd 0 = 1 := by simp [bKQ]
  have h1 : bKQ hd 1 = sqK d := by simp [bKQ]
  have hz := sqK_decomp z p q h
  have e0 : z * bKQ hd 0 = p • bKQ hd 0 + q • bKQ hd 1 := by
    rw [h0, h1, mul_one]; exact hz
  have e1 : z * bKQ hd 1 = (-(d : ℚ) * q) • bKQ hd 0 + p • bKQ hd 1 := by
    rw [h0, h1, hz, add_mul, smul_mul_assoc, smul_mul_assoc, sqK_mul_self, one_mul]
    simp only [Algebra.smul_def, mul_one]
    push_cast
    ring
  rw [Algebra.norm_eq_matrix_det (bKQ hd), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add, map_smul, Module.Basis.repr_self]
  simp
  ring

/- English proof (translation)
Establish `hd0 : 0 < d` using `by omega`. Establish `hn` using `norm_KQ hd0 (x : KQ d) (a + b / 2) (b / 2) (by`. Rewrite using `[h]`. Simplify using `only [omegaK, sqD]`. Use `push_cast`.

Use the proof step `ring)`. Rewrite `hn` using `[← Algebra.coe_norm_int]`. Establish `hn' : 4 * Algebra.norm ℤ x = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d)`. Establish `: (4 : ℚ) * (Algebra.norm ℤ x : ℚ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d)`. Rewrite using `[hn]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Establish `hpos : 0 ≤ Algebra.norm ℤ x`. Establish `: 0 ≤ 4 * Algebra.norm ℤ x`. Rewrite using `[hn']`.

Establish `: 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + (d : ℤ)) = (2 * a + b) ^ 2 + d * b ^ 2` using `by ring`. Rewrite using `[this]`. Check the signs of the components of the expression. Use linear arithmetic over natural numbers and integers. Rewrite using `[Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg hpos, hn']`.
-/
theorem absNorm_span {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) (a b : ℤ)
    (h : (((x : KQ d) : ℂ)) = a + b * omegaK d) :
    4 * (Ideal.absNorm (Ideal.span {x}) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  have hd0 : 0 < d := by omega
  have hn := norm_KQ hd0 (x : KQ d) (a + b / 2) (b / 2) (by
    rw [h]; simp only [omegaK, sqD]; push_cast; ring)
  rw [← Algebra.coe_norm_int] at hn
  have hn' : 4 * Algebra.norm ℤ x = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
    have : (4 : ℚ) * (Algebra.norm ℤ x : ℚ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
      rw [hn]; ring
    exact_mod_cast this
  have hpos : 0 ≤ Algebra.norm ℤ x := by
    have : 0 ≤ 4 * Algebra.norm ℤ x := by
      rw [hn']
      have : 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + (d : ℤ)) = (2 * a + b) ^ 2 + d * b ^ 2 := by ring
      rw [this]; positivity
    omega
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg hpos, hn']

/- English proof (translation)
Rewrite `hv` using `[ClassGroup.mk0_eq_one_iff]`. Take `⟨x, hx⟩` from `hv.principal`. Take `⟨a, b, hab⟩` from `quadInt hsf hd x`. Use `⟨a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[← absNorm_span hsf hd x a b hab, Ideal.absNorm_apply, Submodule.cardQuot_apply, hx]`.
-/
theorem princ_form {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    ∃ a b : ℤ, 4 * (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  rw [ClassGroup.mk0_eq_one_iff] at hv
  obtain ⟨x, hx⟩ := hv.principal
  obtain ⟨a, b, hab⟩ := quadInt hsf hd x
  refine ⟨a, b, ?_⟩
  rw [← absNorm_span hsf hd x a b hab, Ideal.absNorm_apply, Submodule.cardQuot_apply, hx]

end ReciprocityTheory.ChartRestriction.L1
