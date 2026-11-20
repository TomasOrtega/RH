import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds

open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

namespace BoundedBasis

section Algebra

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Introduce `M _ _ φ hφ`. Use `⟨fun _ => 0, fun m => ⟨fun _ => 0, 0, ?_⟩⟩` and prove the remaining obligations. Establish `: m = 0` using `hφ (Subsingleton.elim _ _)`.

Simplify using `[this]`. Consider the case `succ r ih`. Introduce `M _ _ φ hφ`. Set `π : M →ₗ[R] R` to `(LinearMap.proj 0).comp φ`. Establish `hI : ∃ y : M, ∀ m : M, ∃ (c : R) (m' : M), π m = c * π y + a * π m'`.

Distinguish the cases in `h0 : ∀ m, π m = 0`. Conclude with `⟨0, fun m => ⟨0, 0, by simp [h0 m]⟩⟩`. Use `push Not at h0`. Take `⟨z, hz⟩` from `h0`. Take `⟨y, hy⟩` from `IsDedekindDomain.exists_eq_span_pair (I := LinearMap.range π) (x := a * π z) ⟨a • z, by simp⟩ (mul_ne_zero ha hz)`.

Choose the witnesses or unpack the hypotheses as in `⟨y', rfl⟩ : y ∈ (LinearMap.range π : Ideal R) := by`. Rewrite using `[hy]; exact Ideal.subset_span (by simp)`. Use `⟨y', fun m => ?_⟩` and prove the remaining obligations. Establish `hm : π m ∈ (LinearMap.range π : Ideal R)` using `⟨m, rfl⟩`. Rewrite `hm` using `[hy, Ideal.mem_span_pair]`.

Take `⟨s, t, hst⟩` from `hm`. Conclude with `⟨t, s • z, by rw [← hst, map_smul, smul_eq_mul]; ring⟩`. Take `⟨y, hy⟩` from `hI`. Set `φ' : LinearMap.ker π →ₗ[R] (Fin r → R)` to `LinearMap.pi fun i => (LinearMap.proj i.succ).comp (φ.comp (LinearMap.ker π).subtype)`. Establish `hφ' : Function.Injective φ'`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `m hm`. Use `Subtype.ext (hφ ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Rewrite using `[Submodule.coe_zero, map_zero]`. Conclude with `m.2`. Simplify `congrFun hm i` using `[φ']`. Take `⟨x, hx⟩` from `ih (LinearMap.ker π) φ' hφ'`. Use `⟨Fin.cons y fun i => (x i : M), fun m => ?_⟩` and prove the remaining obligations.

Take `⟨c, m₁, h⟩` from `hy m`. Take `⟨d, m₂, h₂⟩` from `hx ⟨m - c • y - a • m₁, by`. Rewrite using `[LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, h]`. Use the proof step `simp⟩`. Use `⟨Fin.cons c d, m₁ + (m₂ : M), ?_⟩` and prove the remaining obligations.

Establish `h₃` using `congrArg Subtype.val h₂`. Simplify using `only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at h₃`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, smul_add]`. Rewrite `h₃` using `[sub_sub, sub_eq_iff_eq_add]`.

Rewrite using `[h₃]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_generators_mod_smul {R : Type*} [CommRing R] [IsDedekindDomain R] {a : R}
    (ha : a ≠ 0) (r : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M]
      (φ : M →ₗ[R] (Fin r → R)), Function.Injective φ →
      ∃ x : Fin r → M, ∀ m : M, ∃ (c : Fin r → R) (m' : M), m = ∑ i, c i • x i + a • m' := by
  induction r with
  | zero =>
    intro M _ _ φ hφ
    refine ⟨fun _ => 0, fun m => ⟨fun _ => 0, 0, ?_⟩⟩
    have : m = 0 := hφ (Subsingleton.elim _ _)
    simp [this]
  | succ r ih =>
    intro M _ _ φ hφ
    let π : M →ₗ[R] R := (LinearMap.proj 0).comp φ
    have hI : ∃ y : M, ∀ m : M, ∃ (c : R) (m' : M), π m = c * π y + a * π m' := by
      by_cases h0 : ∀ m, π m = 0
      · exact ⟨0, fun m => ⟨0, 0, by simp [h0 m]⟩⟩
      · push Not at h0
        obtain ⟨z, hz⟩ := h0
        obtain ⟨y, hy⟩ := IsDedekindDomain.exists_eq_span_pair (I := LinearMap.range π)
          (x := a * π z) ⟨a • z, by simp⟩ (mul_ne_zero ha hz)
        obtain ⟨y', rfl⟩ : y ∈ (LinearMap.range π : Ideal R) := by
          rw [hy]; exact Ideal.subset_span (by simp)
        refine ⟨y', fun m => ?_⟩
        have hm : π m ∈ (LinearMap.range π : Ideal R) := ⟨m, rfl⟩
        rw [hy, Ideal.mem_span_pair] at hm
        obtain ⟨s, t, hst⟩ := hm
        exact ⟨t, s • z, by rw [← hst, map_smul, smul_eq_mul]; ring⟩
    obtain ⟨y, hy⟩ := hI
    let φ' : LinearMap.ker π →ₗ[R] (Fin r → R) :=
      LinearMap.pi fun i => (LinearMap.proj i.succ).comp (φ.comp (LinearMap.ker π).subtype)
    have hφ' : Function.Injective φ' := by
      rw [injective_iff_map_eq_zero]
      intro m hm
      refine Subtype.ext (hφ ?_)
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Submodule.coe_zero, map_zero]
        exact m.2
      · simpa [φ'] using congrFun hm i
    obtain ⟨x, hx⟩ := ih (LinearMap.ker π) φ' hφ'
    refine ⟨Fin.cons y fun i => (x i : M), fun m => ?_⟩
    obtain ⟨c, m₁, h⟩ := hy m
    obtain ⟨d, m₂, h₂⟩ := hx ⟨m - c • y - a • m₁, by
      rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, h]; simp⟩
    refine ⟨Fin.cons c d, m₁ + (m₂ : M), ?_⟩
    have h₃ := congrArg Subtype.val h₂
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at h₃
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_add]
    rw [sub_sub, sub_eq_iff_eq_add] at h₃
    rw [h₃]
    abel

/- English proof (translation)
Use `Fintype.ofFinite (Set.range f)` as an intermediate fact. Use `⟨Finset.univ.image fun b : Set.range f => b.2.choose, ?_, fun s => ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.card_univ, ← Nat.card_eq_fintype_card]`. Conclude with `Nat.card_le_card_of_injective _ Subtype.val_injective`.

Conclude with `⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨f s, s, rfl⟩), (⟨s, rfl⟩ : f s ∈ Set.range f).choose_spec⟩`.
-/
theorem exists_finset_representatives {α β : Type*} [Finite β] (S : Set α) (f : S → β) :
    ∃ V : Finset S, V.card ≤ Nat.card β ∧ ∀ s : S, ∃ t ∈ V, f t = f s := by
  classical
  have := Fintype.ofFinite (Set.range f)
  refine ⟨Finset.univ.image fun b : Set.range f => b.2.choose, ?_, fun s => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  · exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨f s, s, rfl⟩),
      (⟨s, rfl⟩ : f s ∈ Set.range f).choose_spec⟩

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hinj : Function.Injective N.vecMulLinear`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Conclude with `Matrix.eq_zero_of_vecMul_eq_zero hN hx`. Set `P : Submodule ℤ (Fin r → 𝓞 E)` to `(LinearMap.range N.vecMulLinear).restrictScalars ℤ`.

Set `e : (Fin r → 𝓞 E) ≃+ P` to `(LinearEquiv.ofInjective _ hinj).toAddEquiv`. Establish `key` using `Submodule.natAbs_det_equiv P e`. Establish `hcomp : P.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin r → 𝓞 E) →+ P) = (Matrix.toLin' Nᵀ).restrictScalars ℤ` using `LinearMap.ext fun x => by`. Express the relevant statement in the definitionally equal form `x ᵥ* N = Nᵀ *ᵥ x`. Rewrite using `[Matrix.mulVec_transpose]`.

Rewrite `key` using `[hcomp, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose]`. Rewrite using `[key]`. Both sides reduce to the same expression.
-/
theorem card_quotient_range_vecMulLinear {r : ℕ} (N : Matrix (Fin r) (Fin r) (𝓞 E))
    (hN : N.det ≠ 0) :
    Nat.card ((Fin r → 𝓞 E) ⧸ LinearMap.range N.vecMulLinear) =
      (Algebra.norm ℤ N.det).natAbs := by
  have hinj : Function.Injective N.vecMulLinear := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_vecMul_eq_zero hN hx
  let P : Submodule ℤ (Fin r → 𝓞 E) := (LinearMap.range N.vecMulLinear).restrictScalars ℤ
  let e : (Fin r → 𝓞 E) ≃+ P := (LinearEquiv.ofInjective _ hinj).toAddEquiv
  have key := Submodule.natAbs_det_equiv P e
  have hcomp : P.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin r → 𝓞 E) →+ P) =
      (Matrix.toLin' Nᵀ).restrictScalars ℤ :=
    LinearMap.ext fun x => by
      change x ᵥ* N = Nᵀ *ᵥ x
      rw [Matrix.mulVec_transpose]
  rw [hcomp, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose] at key
  rw [key]
  rfl

/- English proof (translation)
Establish `h3` using `congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (x : E))`. Establish `h4 : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (x : E)‖ ≤ a ^ finrank ℚ E`. Rewrite using `[← AlgHom.card ℚ E ℂ, ← Finset.card_univ, ← Finset.prod_const]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun σ _ => h σ.toRingHom`. Rewrite `h3` using `[norm_prod, ← Algebra.coe_norm_int]`.

Use `le_trans (le_of_eq ?_) (h3 ▸ h4)` and prove the remaining obligations. Simplify using `[Nat.cast_natAbs]`.
-/
theorem natAbs_norm_le_pow {x : 𝓞 E} {a : ℝ} (h : ∀ σ : E →+* ℂ, ‖σ (x : E)‖ ≤ a) :
    ((Algebra.norm ℤ x).natAbs : ℝ) ≤ a ^ finrank ℚ E := by
  have h3 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (x : E))
  have h4 : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (x : E)‖ ≤ a ^ finrank ℚ E := by
    rw [← AlgHom.card ℚ E ℂ, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun σ _ => h σ.toRingHom
  rw [norm_prod, ← Algebra.coe_norm_int] at h3
  refine le_trans (le_of_eq ?_) (h3 ▸ h4)
  simp [Nat.cast_natAbs]

/- English proof (translation)
Establish `h1` using `Matrix.det_le (A := M) (abv := NormedField.toAbsoluteValue ℂ) (x := b) h`. Rewrite `h1` using `[Fintype.card_fin, nsmul_eq_mul]`. Use `le_trans h1 ?_` and prove the remaining obligations. Rewrite using `[mul_pow]`. Use `gcongr`.

Conclude with `Nat.factorial_le_pow r` after adjusting the coercions.
-/
theorem norm_det_le_pow {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i k, ‖M i k‖ ≤ b) : ‖M.det‖ ≤ (r * b) ^ r := by
  have h1 := Matrix.det_le (A := M) (abv := NormedField.toAbsoluteValue ℂ) (x := b) h
  rw [Fintype.card_fin, nsmul_eq_mul] at h1
  refine le_trans h1 ?_
  rw [mul_pow]
  gcongr
  exact_mod_cast Nat.factorial_le_pow r

/- English proof (translation)
Establish `h` using `IsTotallyComplex.finrank E`. Unfold `fdeg`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_eq_two_mul_fdeg [IsCMField E] : finrank ℚ E = 2 * fdeg E := by
  have h := IsTotallyComplex.finrank E
  unfold fdeg
  omega

end Algebra

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Simplify using `[herm, add_mul, Finset.sum_add_distrib]`.
-/
theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[herm, Finset.mul_sum, mul_assoc]`.
-/
theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp [herm, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [herm, vecMul, dotProduct, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ fun b => cc (y b) := by
  simp only [herm, vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

noncomputable def gramOf (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i k => herm G (v i) (v k)

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [gramOf, herm, Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul, transpose_apply, map_apply]`. Conclude with `Finset.sum_comm`.
-/
theorem gramOf_eq (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    gramOf G v = Matrix.of v * G * ((Matrix.of v).map (IsCMField.complexConj E).toRingHom)ᵀ := by
  ext i k
  simp only [gramOf, herm, Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul, transpose_apply,
    map_apply]
  exact Finset.sum_comm

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
The claim follows from `((Matrix.isUnit_iff_isUnit_det _).1 ((Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of v)).1 hv)).ne_zero`.
-/
theorem det_of_ne_zero {v : Fin r → Fin r → E} (hv : LinearIndependent E v) :
    (Matrix.of v).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1
    ((Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of v)).1 hv)).ne_zero

/- English proof (translation)
Rewrite using `[gramOf_eq, det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Use `mul_ne_zero (mul_ne_zero (det_of_ne_zero hv) hG) ?_` and prove the remaining obligations. Conclude with `(map_ne_zero _).2 (det_of_ne_zero hv)`.
-/
theorem det_gramOf_ne_zero {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    {v : Fin r → Fin r → E} (hv : LinearIndependent E v) : (gramOf G v).det ≠ 0 := by
  rw [gramOf_eq, det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  refine mul_ne_zero (mul_ne_zero (det_of_ne_zero hv) hG) ?_
  exact (map_ne_zero _).2 (det_of_ne_zero hv)

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use extensionality with `k`. Simplify using `[vecMul, dotProduct, Finset.sum_apply]`.
-/
theorem vecMul_of (c : Fin r → E) (v : Fin r → Fin r → E) :
    c ᵥ* Matrix.of v = ∑ i, c i • v i := by
  ext k
  simp [vecMul, dotProduct, Finset.sum_apply]

/- English proof (translation)
Rewrite using `[gramOf_eq, ← vecMul_vecMul, ← vecMul_vecMul, herm_eq_dotProduct]`. Both sides reduce to the same expression.
-/
theorem herm_vecMul_left (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (c : Fin r → E)
    (k : Fin r) : herm G (c ᵥ* Matrix.of v) (v k) = (c ᵥ* gramOf G v) k := by
  rw [gramOf_eq, ← vecMul_vecMul, ← vecMul_vecMul, herm_eq_dotProduct]
  rfl

/- English proof (translation)
Rewrite using `[herm_eq_dotProduct, herm_eq_dotProduct, gramOf_eq, ← vecMul_vecMul, ← vecMul_vecMul, ← dotProduct_mulVec _ _ᵀ, mulVec_transpose]`. Use `congr 1`. Use extensionality with `b`. Simplify using `[cc, vecMul, dotProduct]`.
-/
theorem herm_vecMul (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (c d : Fin r → E) :
    herm G (c ᵥ* Matrix.of v) (d ᵥ* Matrix.of v) = herm (gramOf G v) c d := by
  rw [herm_eq_dotProduct, herm_eq_dotProduct, gramOf_eq, ← vecMul_vecMul, ← vecMul_vecMul,
    ← dotProduct_mulVec _ _ᵀ, mulVec_transpose]
  congr 1
  ext b
  simp [cc, vecMul, dotProduct]

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨x ᵥ* (Matrix.of v)⁻¹, by rw [vecMul_vecMul, nonsing_inv_mul _ (det_of_ne_zero hv).isUnit, vecMul_one]⟩`.
-/
theorem exists_vecMul_eq {v : Fin r → Fin r → E} (hv : LinearIndependent E v) (x : Fin r → E) :
    ∃ c, x = c ᵥ* Matrix.of v :=
  ⟨x ᵥ* (Matrix.of v)⁻¹, by
    rw [vecMul_vecMul, nonsing_inv_mul _ (det_of_ne_zero hv).isUnit, vecMul_one]⟩

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Establish `hw' : IsUnit (Matrix.of w)ᵀ.det`. Rewrite using `[det_transpose]`. Conclude with `(det_of_ne_zero hw).isUnit`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero ((Matrix.of v)ᵀ * ((Matrix.of w)ᵀ)⁻¹) ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul, det_transpose]`.

Conclude with `mul_ne_zero (det_of_ne_zero hv) (isUnit_nonsing_inv_det _ hw').ne_zero`. Express the relevant statement in the definitionally equal form `((Matrix.of v)ᵀ * ((Matrix.of w)ᵀ)⁻¹) *ᵥ _ = _`. Rewrite using `[← mulVec_transpose, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hw', Matrix.mul_one, mulVec_transpose]`.
-/
theorem exists_gl_mulVec {v w : Fin r → Fin r → E} (hv : LinearIndependent E v)
    (hw : LinearIndependent E w) : ∃ γ : GL (Fin r) E, ∀ c : Fin r → E,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (c ᵥ* Matrix.of w) = c ᵥ* Matrix.of v := by
  have hw' : IsUnit (Matrix.of w)ᵀ.det := by
    rw [det_transpose]; exact (det_of_ne_zero hw).isUnit
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero ((Matrix.of v)ᵀ * ((Matrix.of w)ᵀ)⁻¹) ?_,
    fun c => ?_⟩
  · rw [det_mul, det_transpose]
    exact mul_ne_zero (det_of_ne_zero hv) (isUnit_nonsing_inv_det _ hw').ne_zero
  · change ((Matrix.of v)ᵀ * ((Matrix.of w)ᵀ)⁻¹) *ᵥ _ = _
    rw [← mulVec_transpose, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hw',
      Matrix.mul_one, mulVec_transpose]

end Herm

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)

noncomputable def pairing (v : Fin r → Fin r → E) (hv : ∀ i, v i ∈ X.L') :
    X.Λ →ₗ[𝓞 E] (Fin r → 𝓞 E) where
  toFun x k := ⟨herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k),
    X.L'_int _ (X.NA_sub _ x.2) _ (hv k)⟩
  map_add' x y := by
    funext k
    refine RingOfIntegers.ext ?_
    change herm X.Gm ((X.NA : E) • ((x : Fin r → E) + y)) (v k) =
      herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k) +
        herm X.Gm ((X.NA : E) • (y : Fin r → E)) (v k)
    rw [smul_add, herm_add_left]
  map_smul' c x := by
    funext k
    refine RingOfIntegers.ext ?_
    change herm X.Gm ((X.NA : E) • ((c : E) • (x : Fin r → E))) (v k) =
      (c : E) * herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k)
    rw [smul_comm, herm_smul_left]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k) = _`. Rewrite using `[hc, ← smul_vecMul, herm_vecMul_left]`.
-/
theorem coe_pairing (v : Fin r → Fin r → E) (hv : ∀ i, v i ∈ X.L') (x : X.Λ) (c : Fin r → E)
    (hc : (x : Fin r → E) = c ᵥ* Matrix.of v) (k : Fin r) :
    ((pairing X v hv x k : 𝓞 E) : E) = (((X.NA : E) • c) ᵥ* gramOf X.Gm v) k := by
  change herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k) = _
  rw [hc, ← smul_vecMul, herm_vecMul_left]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨c, hc⟩` from `exists_vecMul_eq hi x`. Establish `h : ((X.NA : E) • c) ᵥ* gramOf X.Gm v = 0`. Use function extensionality and compare the values at `k`.

Rewrite using `[← coe_pairing X v hv x c hc k, hx]`. Simplify using the standard rewrite rules. Establish `h1` using `Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero X.Gm_det hi) h`. Establish `h2 : c = 0` using `(smul_eq_zero.1 h1).resolve_left (by exact_mod_cast X.NA_pos.ne')`. Use `Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[hc, h2, zero_vecMul]`. Both sides reduce to the same expression.
-/
theorem pairing_injective {v : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L')
    (hi : LinearIndependent E v) : Function.Injective (pairing X v hv) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := exists_vecMul_eq hi x
  have h : ((X.NA : E) • c) ᵥ* gramOf X.Gm v = 0 := by
    funext k
    rw [← coe_pairing X v hv x c hc k, hx]
    simp
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero X.Gm_det hi) h
  have h2 : c = 0 := (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast X.NA_pos.ne')
  refine Subtype.ext ?_
  rw [hc, h2, zero_vecMul]
  rfl

/- English proof (translation)
Use `X.NC_sub _ ?_` and prove the remaining obligations. Rewrite using `[vecMul_of]`. Conclude with `Submodule.sum_mem _ fun i _ => X.L'.smul_mem (o i) (hv i)`.
-/
theorem smul_vecMul_mem {v : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L') (o : Fin r → 𝓞 E) :
    (X.NC : E) • ((fun i => (o i : E)) ᵥ* Matrix.of v) ∈ X.Λ := by
  refine X.NC_sub _ ?_
  rw [vecMul_of]
  exact Submodule.sum_mem _ fun i _ => X.L'.smul_mem (o i) (hv i)

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_gl_mulVec hvi hwi`. Establish `key : ∀ x ∈ X.Λ, ∀ c d : Fin r → E, x = c ᵥ* Matrix.of v → x = d ᵥ* Matrix.of w → ∃ o : Fin r → 𝓞 E, d = c + (X.g : E) • (X.NC : E) • fun i => (o i : E)`. Introduce `x hx c d hc hd`. Take `⟨o, ho⟩` from `h ⟨x, hx⟩`. Use `⟨o, ?_⟩` and prove the remaining obligations.

Establish `h1 : ((X.NA : E) • (d - (c + (X.g : E) • (X.NC : E) • fun i => (o i : E)))) ᵥ* gramOf X.Gm v = 0`. Use function extensionality and compare the values at `k`. Establish `h2` using `congrArg (algebraMap (𝓞 E) E) (congrFun ho k)`. Establish `h3` using `coe_pairing X v hv ⟨x, hx⟩ c hc k`. Establish `h4` using `coe_pairing X w hw ⟨x, hx⟩ d hd k`.

Rewrite `h4` using `[hwA, ← hvA]`. Rewrite `h2` using `[Pi.sub_apply, map_sub]`. Express the relevant statement in the definitionally equal form `_ = ((pairing X w hw ⟨x, hx⟩ k : 𝓞 E) : E) - (pairing X v hv ⟨x, hx⟩ k : 𝓞 E) at h2`. Rewrite `h2` using `[h3, h4]`. Rewrite using `[smul_sub, smul_add, sub_vecMul, add_vecMul, Pi.sub_apply, Pi.add_apply, ← sub_sub, ← h2, hvA]`.

Simplify using `only [vecMulLinear_apply, vecMul, dotProduct, map_sum, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, Pi.smul_apply, map_apply, Pi.zero_apply, ← Finset.sum_sub_distrib]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero X.Gm_det hvi) h1`.

Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h5).resolve_left (by exact_mod_cast X.NA_pos.ne'))`. Establish `hg : ∀ y ∈ X.Λ, (X.g : E) • y ∈ X.Λ` using `fun y hy => by`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hy _`. Establish `hcong : ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (X.g : E) • y`.

Introduce `x hx`. Take `⟨c, hc⟩` from `exists_vecMul_eq hvi x`. Take `⟨d, hd⟩` from `exists_vecMul_eq hwi x`. Take `⟨o, ho⟩` from `key x hx c d hc hd`. Use `⟨_, smul_vecMul_mem X hv o, ?_⟩` and prove the remaining obligations.

Establish `: (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = d ᵥ* Matrix.of v` using `by rw [hd, hγ]`. Rewrite using `[this, ho, add_vecMul, ← hc, smul_vecMul, smul_vecMul, add_sub_cancel_left]`. Use `⟨γ, X.cong γ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ hcong, fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `exists_vecMul_eq hwi x`. Take `⟨d, rfl⟩` from `exists_vecMul_eq hwi y`.

Rewrite using `[hγ, hγ, herm_vecMul, herm_vecMul, hvA, hwA]`. Take `⟨y, hy, h⟩` from `hcong x hx`. Rewrite using `[sub_eq_iff_eq_add.1 h]`. Conclude with `add_mem (hg y hy) hx`. Take `⟨c, rfl⟩` from `exists_vecMul_eq hwi x`.

Take `⟨d, hd⟩` from `exists_vecMul_eq hwi ((γ : Matrix (Fin r) (Fin r) E) *ᵥ (c ᵥ* Matrix.of w))`. Take `⟨o, ho⟩` from `key _ hx c d (hγ c) hd`. Rewrite `hx` using `[hd, ho, add_vecMul, smul_vecMul, smul_vecMul]`. Conclude with `(Submodule.add_mem_iff_left _ (hg _ (smul_vecMul_mem X hw o))).1 hx`. Use `hγ (Pi.single i 1)` as an intermediate fact.

Rewrite `this` using `[single_one_vecMul, single_one_vecMul]`. Conclude with `this.symm`.
-/
theorem exists_mem_of_pairing {v w : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L')
    (hw : ∀ i, w i ∈ X.L') (hvi : LinearIndependent E v) (hwi : LinearIndependent E w)
    (A : Matrix (Fin r) (Fin r) (𝓞 E)) (hvA : gramOf X.Gm v = A.map (algebraMap (𝓞 E) E))
    (hwA : gramOf X.Gm w = A.map (algebraMap (𝓞 E) E))
    (h : ∀ x : X.Λ, pairing X w hw x - pairing X v hv x ∈
      LinearMap.range (((X.NA * X.NC * X.g : ℕ) : 𝓞 E) • A).vecMulLinear) :
    ∃ γ ∈ X.Γ, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i := by
  obtain ⟨γ, hγ⟩ := exists_gl_mulVec hvi hwi
  have key : ∀ x ∈ X.Λ, ∀ c d : Fin r → E, x = c ᵥ* Matrix.of v → x = d ᵥ* Matrix.of w →
      ∃ o : Fin r → 𝓞 E, d = c + (X.g : E) • (X.NC : E) • fun i => (o i : E) := by
    intro x hx c d hc hd
    obtain ⟨o, ho⟩ := h ⟨x, hx⟩
    refine ⟨o, ?_⟩
    have h1 : ((X.NA : E) • (d - (c + (X.g : E) • (X.NC : E) • fun i => (o i : E)))) ᵥ*
        gramOf X.Gm v = 0 := by
      funext k
      have h2 := congrArg (algebraMap (𝓞 E) E) (congrFun ho k)
      have h3 := coe_pairing X v hv ⟨x, hx⟩ c hc k
      have h4 := coe_pairing X w hw ⟨x, hx⟩ d hd k
      rw [hwA, ← hvA] at h4
      rw [Pi.sub_apply, map_sub] at h2
      change _ = ((pairing X w hw ⟨x, hx⟩ k : 𝓞 E) : E) - (pairing X v hv ⟨x, hx⟩ k : 𝓞 E) at h2
      rw [h3, h4] at h2
      rw [smul_sub, smul_add, sub_vecMul, add_vecMul, Pi.sub_apply, Pi.add_apply, ← sub_sub, ← h2,
        hvA]
      simp only [vecMulLinear_apply, vecMul, dotProduct, map_sum, Matrix.smul_apply, smul_eq_mul,
        map_mul, map_natCast, Pi.smul_apply, map_apply, Pi.zero_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      push_cast
      ring
    have h5 := Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero X.Gm_det hvi) h1
    exact sub_eq_zero.1 ((smul_eq_zero.1 h5).resolve_left (by exact_mod_cast X.NA_pos.ne'))
  have hg : ∀ y ∈ X.Λ, (X.g : E) • y ∈ X.Λ := fun y hy => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
  have hcong : ∀ x ∈ X.Λ, ∃ y ∈ X.Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (X.g : E) • y := by
    intro x hx
    obtain ⟨c, hc⟩ := exists_vecMul_eq hvi x
    obtain ⟨d, hd⟩ := exists_vecMul_eq hwi x
    obtain ⟨o, ho⟩ := key x hx c d hc hd
    refine ⟨_, smul_vecMul_mem X hv o, ?_⟩
    have : (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = d ᵥ* Matrix.of v := by rw [hd, hγ]
    rw [this, ho, add_vecMul, ← hc, smul_vecMul, smul_vecMul, add_sub_cancel_left]
  refine ⟨γ, X.cong γ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ hcong, fun i => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_vecMul_eq hwi x
    obtain ⟨d, rfl⟩ := exists_vecMul_eq hwi y
    rw [hγ, hγ, herm_vecMul, herm_vecMul, hvA, hwA]
  · obtain ⟨y, hy, h⟩ := hcong x hx
    rw [sub_eq_iff_eq_add.1 h]
    exact add_mem (hg y hy) hx
  · obtain ⟨c, rfl⟩ := exists_vecMul_eq hwi x
    obtain ⟨d, hd⟩ := exists_vecMul_eq hwi ((γ : Matrix (Fin r) (Fin r) E) *ᵥ (c ᵥ* Matrix.of w))
    obtain ⟨o, ho⟩ := key _ hx c d (hγ c) hd
    rw [hd, ho, add_vecMul, smul_vecMul, smul_vecMul] at hx
    exact (Submodule.add_mem_iff_left _ (hg _ (smul_vecMul_mem X hw o))).1 hx
  · have := hγ (Pi.single i 1)
    rw [single_one_vecMul, single_one_vecMul] at this
    exact this.symm

end Lattice

end BoundedBasis

open BoundedBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsBoundedBasis (X : DataX E r) (B : ℝ) (v : Fin r → Fin r → E) : Prop :=
  (∀ i, v i ∈ X.L') ∧ LinearIndependent E v ∧
    ∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B

/- English proof (translation)
Set `S : Set (Fin r → Fin r → E)` to `{v | IsBoundedBasis X B v ∧ gramOf X.Gm v = A.map (algebraMap (𝓞 E) E)}`. Break down `S.eq_empty_or_nonempty with hS | ⟨u, hu, huA⟩` into its components or cases. Use `⟨∅, by simp, fun v hv hA => ?_, by simp; positivity⟩` and prove the remaining obligations. Conclude with `absurd (show v ∈ S from ⟨hv, hA⟩) (by simp [hS])`. Use `set n : ℕ := X.NA * X.NC * X.g with hn`.

Establish `hn0 : n ≠ 0` using `(Nat.mul_pos (Nat.mul_pos X.NA_pos X.NC_pos) X.g_pos).ne'`. Use `set N : Matrix (Fin r) (Fin r) (𝓞 E) := (n : 𝓞 E) • A with hN`. Establish `hA : A.det ≠ 0`. Introduce `h0`. Apply `det_gramOf_ne_zero X.Gm_det hu.2.1` to reduce the goal to its premises.

Rewrite using `[huA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`. Establish `hN0 : N.det ≠ 0`. Rewrite using `[hN, det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn0)) hA`. Establish `hcard` using `card_quotient_range_vecMulLinear N hN0`.

Establish `hbound : ((Algebra.norm ℤ N.det).natAbs : ℝ) ≤ ((r * (n * B)) ^ r) ^ finrank ℚ E`. Use `natAbs_norm_le_pow fun σ => ?_` and prove the remaining obligations. Establish `h1 : σ ((N.det : 𝓞 E) : E) = (N.map (σ.comp (algebraMap (𝓞 E) E))).det` using `RingHom.map_det (σ.comp (algebraMap (𝓞 E) E)) N`. Rewrite using `[h1]`. Use `norm_det_le_pow _ (by positivity) fun i k => ?_` and prove the remaining obligations.

Establish `h2 : algebraMap (𝓞 E) E (A i k) = herm X.Gm (u i) (u k)` using `(congrFun (congrFun huA i) k).symm`. Simplify using `only [hN, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, RingHom.comp_apply, h2, norm_mul, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left (hu.2.2 σ i k) (by positivity)`. Establish `: Finite ((Fin r → 𝓞 E) ⧸ LinearMap.range N.vecMulLinear)`. Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations.

Rewrite using `[hcard, Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]`. Conclude with `hN0`. Take `⟨x, hx⟩` from `exists_generators_mod_smul hN0 r X.Λ _ (pairing_injective X hu.1 hu.2.1)`. Take `⟨V, hV, hV'⟩` from `exists_finset_representatives S fun v j => (LinearMap.range N.vecMulLinear).mkQ (pairing X v.1 v.2.1.1 (x j))`. Use `⟨V.image Subtype.val, ?_, fun v hv hvA => ?_, ?_⟩` and prove the remaining obligations.

Introduce `v hv`. Take `⟨w, -, rfl⟩` from `Finset.mem_image.1 hv`. Conclude with `w.2.1`. Take `⟨w, hwV, hw⟩` from `hV' ⟨v, hv, hvA⟩`. Take `⟨γ, hγ, h⟩` from `exists_mem_of_pairing X hv.1 w.2.1.1 hv.2.1 w.2.1.2.1 A hvA w.2.2 fun m => by`.

Take `⟨c, m', rfl⟩` from `hx m`. Rewrite using `[map_add, map_add, add_sub_add_comm, map_sum, map_sum, ← Finset.sum_sub_distrib, map_smul, map_smul, ← smul_sub]`. Use `add_mem (Submodule.sum_mem _ fun j _ => ?_) ⟨(pairing X w.1 w.2.1.1 m' - pairing X v hv.1 m') ᵥ* N.adjugate, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ ((Submodule.Quotient.eq _).1 (congrFun hw j))`.

Rewrite using `[vecMulLinear_apply, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]`. Conclude with `⟨γ, hγ, w.1, Finset.mem_image_of_mem _ hwV, h⟩`. Rewrite `hV` using `[Nat.card_fun, hcard, Nat.card_eq_fintype_card, Fintype.card_fin]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.card_image_le.trans hV` after adjusting the coercions.

Use `_ ≤ (((r * (n * B)) ^ r) ^ finrank ℚ E) ^ r := by gcongr`. Use `_ = _ := by`. Rewrite using `[← pow_mul, ← pow_mul, finrank_eq_two_mul_fdeg, hn]`. Use `push_cast`. Apply the tactic sequence `congr 1 <;> ring`.
-/
theorem exists_finset_boundedBasis_of_gram (X : DataX E r) {B : ℝ} (hB : 0 ≤ B)
    (A : Matrix (Fin r) (Fin r) (𝓞 E)) :
    ∃ V : Finset (Fin r → Fin r → E), (∀ v ∈ V, IsBoundedBasis X B v) ∧
      (∀ v, IsBoundedBasis X B v → gramOf X.Gm v = A.map (algebraMap (𝓞 E) E) →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i) ∧
      (V.card : ℝ) ≤ ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by
  classical
  let S : Set (Fin r → Fin r → E) :=
    {v | IsBoundedBasis X B v ∧ gramOf X.Gm v = A.map (algebraMap (𝓞 E) E)}
  rcases S.eq_empty_or_nonempty with hS | ⟨u, hu, huA⟩
  · refine ⟨∅, by simp, fun v hv hA => ?_, by simp; positivity⟩
    exact absurd (show v ∈ S from ⟨hv, hA⟩) (by simp [hS])
  set n : ℕ := X.NA * X.NC * X.g with hn
  have hn0 : n ≠ 0 := (Nat.mul_pos (Nat.mul_pos X.NA_pos X.NC_pos) X.g_pos).ne'
  set N : Matrix (Fin r) (Fin r) (𝓞 E) := (n : 𝓞 E) • A with hN
  have hA : A.det ≠ 0 := by
    intro h0
    apply det_gramOf_ne_zero X.Gm_det hu.2.1
    rw [huA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hN0 : N.det ≠ 0 := by
    rw [hN, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn0)) hA
  have hcard := card_quotient_range_vecMulLinear N hN0
  have hbound : ((Algebra.norm ℤ N.det).natAbs : ℝ) ≤ ((r * (n * B)) ^ r) ^ finrank ℚ E := by
    refine natAbs_norm_le_pow fun σ => ?_
    have h1 : σ ((N.det : 𝓞 E) : E) = (N.map (σ.comp (algebraMap (𝓞 E) E))).det :=
      RingHom.map_det (σ.comp (algebraMap (𝓞 E) E)) N
    rw [h1]
    refine norm_det_le_pow _ (by positivity) fun i k => ?_
    have h2 : algebraMap (𝓞 E) E (A i k) = herm X.Gm (u i) (u k) :=
      (congrFun (congrFun huA i) k).symm
    simp only [hN, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast,
      RingHom.comp_apply, h2, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hu.2.2 σ i k) (by positivity)
  have : Finite ((Fin r → 𝓞 E) ⧸ LinearMap.range N.vecMulLinear) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard, Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
    exact hN0
  obtain ⟨x, hx⟩ := exists_generators_mod_smul hN0 r X.Λ _ (pairing_injective X hu.1 hu.2.1)
  obtain ⟨V, hV, hV'⟩ := exists_finset_representatives S fun v j =>
    (LinearMap.range N.vecMulLinear).mkQ (pairing X v.1 v.2.1.1 (x j))
  refine ⟨V.image Subtype.val, ?_, fun v hv hvA => ?_, ?_⟩
  · intro v hv
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv
    exact w.2.1
  · obtain ⟨w, hwV, hw⟩ := hV' ⟨v, hv, hvA⟩
    obtain ⟨γ, hγ, h⟩ := exists_mem_of_pairing X hv.1 w.2.1.1 hv.2.1 w.2.1.2.1 A hvA w.2.2
      fun m => by
        obtain ⟨c, m', rfl⟩ := hx m
        rw [map_add, map_add, add_sub_add_comm, map_sum, map_sum, ← Finset.sum_sub_distrib,
          map_smul, map_smul, ← smul_sub]
        refine add_mem (Submodule.sum_mem _ fun j _ => ?_) ⟨(pairing X w.1 w.2.1.1 m' -
          pairing X v hv.1 m') ᵥ* N.adjugate, ?_⟩
        · rw [map_smul, map_smul, ← smul_sub]
          exact Submodule.smul_mem _ _ ((Submodule.Quotient.eq _).1 (congrFun hw j))
        · rw [vecMulLinear_apply, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    exact ⟨γ, hγ, w.1, Finset.mem_image_of_mem _ hwV, h⟩
  · rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card, Fintype.card_fin] at hV
    calc ((V.image Subtype.val).card : ℝ) ≤ ((Algebra.norm ℤ N.det).natAbs : ℝ) ^ r := by
          exact_mod_cast Finset.card_image_le.trans hV
      _ ≤ (((r * (n * B)) ^ r) ^ finrank ℚ E) ^ r := by gcongr
      _ = _ := by
          rw [← pow_mul, ← pow_mul, finrank_eq_two_mul_fdeg, hn]
          push_cast
          congr 1 <;> ring

/- English proof (translation)
Take `⟨hfin, hc⟩` from `PackingSeparation.count (E := E) B hB`. Rewrite `hc` using `[Set.ncard_eq_toFinset_card _ hfin]`. Use `choose V hV₁ hV₂ hV₃ using exists_finset_boundedBasis_of_gram X hB`. Set `T : Finset (Fin r → Fin r → 𝓞 E)` to `Fintype.piFinset fun _ => Fintype.piFinset fun _ => hfin.toFinset`. Establish `hT : (T.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2)`.

Rewrite using `[Fintype.card_piFinset_const, Fintype.card_piFinset_const]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Use `⟨T.biUnion fun A => V (Matrix.of A), fun v hv => ?_, fun v hv => ?_, ?_⟩` and prove the remaining obligations. Take `⟨A, -, h⟩` from `Finset.mem_biUnion.1 hv`.

Conclude with `hV₁ _ v h`. Set `A : Fin r → Fin r → 𝓞 E` to `fun i k => ⟨herm X.Gm (v i) (v k), X.L'_int _ (hv.1 i) _ (hv.1 k)⟩`. Take `⟨γ, hγ, w, hw, h⟩` from `hV₂ (Matrix.of A) v hv rfl`. Use `⟨γ, hγ, w, Finset.mem_biUnion.2 ⟨A, ?_, hw⟩, h⟩` and prove the remaining obligations. Simplify using `only [T, Fintype.mem_piFinset, Set.Finite.mem_toFinset]`.

Conclude with `fun i k τ => hv.2.2 τ i k`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) * ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by gcongr`. Use `_ = _ := by`.

Simplify using `only [mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_finset_boundedBasis (X : DataX E r) {B : ℝ} (hB : 0 ≤ B) :
    ∃ V : Finset (Fin r → Fin r → E), (∀ v ∈ V, IsBoundedBasis X B v) ∧
      (∀ v, IsBoundedBasis X B v →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i) ∧
      (V.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
        ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2) := by
  classical
  obtain ⟨hfin, hc⟩ := PackingSeparation.count (E := E) B hB
  rw [Set.ncard_eq_toFinset_card _ hfin] at hc
  choose V hV₁ hV₂ hV₃ using exists_finset_boundedBasis_of_gram X hB
  let T : Finset (Fin r → Fin r → 𝓞 E) :=
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => hfin.toFinset
  have hT : (T.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) := by
    rw [Fintype.card_piFinset_const, Fintype.card_piFinset_const]
    push_cast
    calc ((hfin.toFinset.card : ℝ) ^ r) ^ r ≤ (((1 + 2 * B) ^ (2 * fdeg E)) ^ r) ^ r := by gcongr
      _ = _ := by rw [← pow_mul, ← pow_mul, sq]
  refine ⟨T.biUnion fun A => V (Matrix.of A), fun v hv => ?_, fun v hv => ?_, ?_⟩
  · obtain ⟨A, -, h⟩ := Finset.mem_biUnion.1 hv
    exact hV₁ _ v h
  · let A : Fin r → Fin r → 𝓞 E := fun i k =>
      ⟨herm X.Gm (v i) (v k), X.L'_int _ (hv.1 i) _ (hv.1 k)⟩
    obtain ⟨γ, hγ, w, hw, h⟩ := hV₂ (Matrix.of A) v hv rfl
    refine ⟨γ, hγ, w, Finset.mem_biUnion.2 ⟨A, ?_, hw⟩, h⟩
    simp only [T, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i k τ => hv.2.2 τ i k
  · calc ((T.biUnion fun A => V (Matrix.of A)).card : ℝ)
        ≤ ∑ A ∈ T, ((V (Matrix.of A)).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ T, ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) :=
          Finset.sum_le_sum fun A _ => hV₃ _
      _ = T.card * ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
          ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by gcongr
      _ = _ := by
          simp only [mul_pow]
          ring

/- English proof (translation)
Establish `hB0 : 0 ≤ B` using `zero_le_one.trans hB`. Take `⟨V, h₁, h₂, h₃⟩` from `exists_finset_boundedBasis X hB0`. Use `⟨V, h₁, fun v a b c => h₂ v ⟨a, b, c⟩, h₃, h₃.trans ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_pow, ← mul_pow]`. Use `pow_le_pow_left₀ (by positivity) ?_ _` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_finset_types_of_bounded_bases (X : DataX E r) {B : ℝ} (hB : 1 ≤ B) :
    ∃ V : Finset (Fin r → Fin r → E),
      (∀ v ∈ V, (∀ i, v i ∈ X.L') ∧ LinearIndependent E v ∧
        ∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B) ∧
      (∀ v : Fin r → Fin r → E, (∀ i, v i ∈ X.L') → LinearIndependent E v →
        (∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B) →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (w i)) ∧
      (V.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
        ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2) ∧
      (V.card : ℝ) ≤ (3 * (X.NA : ℝ) * X.NC * X.g * r * B ^ 2) ^ (2 * fdeg E * r ^ 2) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨V, h₁, h₂, h₃⟩ := exists_finset_boundedBasis X hB0
  refine ⟨V, h₁, fun v a b c => h₂ v ⟨a, b, c⟩, h₃, h₃.trans ?_⟩
  rw [← mul_pow, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  calc (1 + 2 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g
      ≤ (3 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g := by gcongr; linarith
    _ = _ := by ring

end GlobalTheory
