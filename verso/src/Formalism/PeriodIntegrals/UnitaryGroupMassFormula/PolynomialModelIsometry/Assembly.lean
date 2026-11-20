import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.IsPolyMon

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

/- English proof (translation)
Establish `h1` using `hg.1`. Rewrite `h1` using `[Matrix.mem_unitaryGroup_iff]`. Introduce `h0`. Use `congrArg Matrix.det h1` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`.

Conclude with `zero_ne_one this`.
-/
lemma det_ne_zero_of_mem_K {N : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) :
    g.det ≠ 0 := by
  have h1 := hg.1
  rw [Matrix.mem_unitaryGroup_iff] at h1
  intro h0
  have := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/- English proof (translation)
Introduce `h`. Use `congrArg (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)) h` as an intermediate fact. Rewrite `this` using `[detPoly, RingHom.map_det, map_zero]`. Establish `hm : (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)).mapMatrix (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) = 1`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Rewrite `this` using `[hm, det_one]`. Conclude with `one_ne_zero this`.
-/
lemma detPoly_ne_zero (N : ℕ) : detPoly N ≠ 0 := by
  intro h
  have := congrArg (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)) h
  rw [detPoly, RingHom.map_det, map_zero] at this
  have hm : (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)).mapMatrix
      (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    ext i j; simp
  rw [hm, det_one] at this
  exact one_ne_zero this

/- English proof (translation)
Establish `h1 : (rowAct ℂ (n` using `N) A).mapMatrix (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) = (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix A * Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ) := by`. Use extensionality with `i j`. Simplify using `[rowAct, Matrix.mul_apply]`. Rewrite using `[detPoly, AlgHom.map_det, h1, Matrix.det_mul, ← RingHom.map_det]`.
-/
lemma rowAct_detPoly {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    rowAct ℂ (n := N) A (detPoly N) = C A.det * detPoly N := by
  have h1 : (rowAct ℂ (n := N) A).mapMatrix
      (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) =
      (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix A *
        Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ) := by
    ext i j
    simp [rowAct, Matrix.mul_apply]
  rw [detPoly, AlgHom.map_det, h1, Matrix.det_mul, ← RingHom.map_det]

/- English proof (translation)
Introduce `N Λ H _ _ σ S hU hK`. Take `⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩` from `hK`. Establish `hK' : IsKTypeOf (allPos N) σ Λ S` using `⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩`. Use `haveI := hfin`. Take `⟨K, P, hP, hPσ⟩` from `hA N H σ S hU hfin hstab`.

Use `choose μ hμ using hI N Λ H σ v0 hU hv0ne hv0w`. Set `w0 : S` to `⟨v0, hv0S⟩`. Establish `hw0ne : w0 ≠ 0`. Introduce `h`. Apply `hv0ne` to reduce the goal to its premises.

Use `congrArg Subtype.val h` as an intermediate fact. Simplify `this` using `[w0]`. Establish `hT'` using `hT N Λ H σ S K P hU hstab hPσ w0 hv0w`. Establish `hL'` using `hL N Λ H σ S K P hU hK' hP hPσ w0 hv0w`. Establish `hT'' : ∀ (θ : Fin N → ℝ) (x : S), ⟪w0, P (torus θ) x⟫_ℂ = Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪w0, x⟫_ℂ`.

Introduce `θ x`. Rewrite using `[hT' θ x]`. Simplify using `only [hμ]`. Take `⟨ν, F, hν, hFmem, hF0, hFint⟩` from `hM N S P w0 μ K hP hw0ne hT'' hL'`. Establish `hanti : Antitone ν`.

Introduce `l j hlj`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Break down `eq_or_lt_of_le hlj with h | h` into its components or cases. Substitute `h` using the available equality.

Conclude with `lt_irrefl _ hlt`. Establish `hbot` using `dualWeylNonDom ℂ N N ν ⟨l, j, h, hlt⟩`. Use `hFmem w0` as an intermediate fact. Rewrite `this` using `[hbot, Submodule.mem_bot]`. Conclude with `hF0 this`.

Establish `hμanti : Antitone μ`. Introduce `a b hab`. Establish `h1` using `hν a`. Establish `h2` using `hν b`. Establish `h3 : (ν b : ℤ) ≤ ν a` using `by exact_mod_cast hanti hab`.

Use linear arithmetic over natural numbers and integers. Set `lam : DomWeight N` to `⟨μ, hμanti⟩`. Use `⟨lam, fun a => hμ a, ?_⟩` and prove the remaining obligations. Set `c : ℕ` to `if h : 0 < N then ν ⟨N - 1, by omega⟩ else 0`. Establish `hnat : ∀ a, lam.natW a + c = ν a`.

Introduce `a`. Establish `hN : 0 < N` using `a.pos`. Establish `h1` using `hν a`. Establish `h2` using `hν ⟨N - 1, by omega⟩`. Establish `h3 : ν ⟨N - 1, by omega⟩ ≤ ν a` using `hanti (by rw [Fin.le_def]; simp; omega)`.

Establish `h3' : (ν ⟨N - 1, by omega⟩ : ℤ) ≤ ν a` using `by exact_mod_cast h3`. Simplify using `only [DomWeight.natW, DomWeight.detShift, c, dif_pos hN, lam]`. Use linear arithmetic over natural numbers and integers. Establish `hlast : ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0`. Introduce `h`.

Simplify using `[DomWeight.natW, DomWeight.detShift, h, lam]`. Establish `hsplit` using `hD N lam.natW c hlast`. Establish `hνeq : (fun a => lam.natW a + c) = ν` using `funext hnat`. Establish `hFmem' : ∀ x, F x ∈ dualWeyl ℂ N N (fun a => lam.natW a + c)`. Introduce `x`.

Rewrite using `[hνeq]`. Conclude with `hFmem x`. Set `mulD : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ` to `LinearMap.mulLeft ℂ (detPoly N ^ c)`. Establish `hmulD_inj : Function.Injective mulD`. Introduce `f g hfg`.

Simplify using `only [mulD, LinearMap.mulLeft_apply] at hfg`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ (detPoly_ne_zero N)) hfg`. Set `U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)` to `nablaSq ℂ N lam ⊓ (LinearMap.range F).comap mulD`. Establish `hUst : ∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U`. Introduce `g f hf`.

Take `⟨hf1, hf2⟩` from `Submodule.mem_inf.mp hf`. Take `⟨x, hx⟩` from `LinearMap.mem_range.mp (Submodule.mem_comap.mp hf2)`. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Unfold `sqAct`. Conclude with `Submodule.smul_mem _ _ (dualWeylRowStable ℂ N N _ _ f hf1)`.

Use `set dg := (g : Matrix (Fin N) (Fin N) ℂ).det with hdgdef`. Establish `hdg : dg ≠ 0`. Use `(Matrix.GeneralLinearGroup.det g).ne_zero` as an intermediate fact. Rewrite `this` using `[Matrix.GeneralLinearGroup.val_det_apply]`. Then use the resulting hypothesis. Use `Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨(detPow ℂ N g lam.detShift * (dg ^ c)⁻¹) • P (g : Matrix (Fin N) (Fin N) ℂ) x, ?_⟩)` and prove the remaining obligations.

Rewrite using `[map_smul, hFint, hx]`. Simplify using `only [mulD, LinearMap.mulLeft_apply, sqAct]`. Rewrite using `[map_mul, map_pow, rowAct_detPoly, Matrix.det_transpose]`. Establish `key : C ((dg ^ c)⁻¹) * C dg ^ c = (1 : MvPolynomial (Fin N × Fin N) ℂ)`. Rewrite using `[← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdg), C_1]`.

Simplify using `only [smul_eq_C_mul, C_mul]`. Take the linear combination `(C (detPow ℂ N g lam.detShift) * detPoly N ^ c * rowAct ℂ (n := N) (g : Matrix (Fin N) (Fin N) ℂ)ᵀ f) * key`. Take `⟨f0, hf0mem, hf0eq⟩` from `hsplit (F w0) (hFmem' w0)`. Establish `hf0U : f0 ∈ U` using `Submodule.mem_inf.mpr ⟨hf0mem, Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨w0, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf0eq⟩)⟩`. Establish `hf0ne : f0 ≠ 0`.

Introduce `h`. Apply `hF0` to reduce the goal to its premises. Rewrite using `[hf0eq, h, mul_zero]`. Establish `hUeq : U = nablaSq ℂ N lam`. Break down `(hH N lam).2.1 U inf_le_left hUst with h | h` into its components or cases.

It suffices to derive a contradiction. Rewrite `hf0U` using `[h, Submodule.mem_bot]`. Conclude with `hf0ne hf0U`. Conclude with `h`. Establish `hFinj : Function.Injective F`.

Rewrite using `[← LinearMap.ker_eq_bot]`. Set `S' : Submodule ℂ H` to `(LinearMap.ker F).map S.subtype`. Establish `hS'le : S' ≤ S`. Introduce and unpack `_ ⟨y, _, rfl⟩`. Conclude with `y.2`.

Establish `hS'st : IsKStableOn (allPos N) σ S'`. Introduce and unpack `g hg _ ⟨y, hy, rfl⟩`. Establish `hd : g.det ^ K ≠ 0` using `pow_ne_zero _ (det_ne_zero_of_mem_K hg)`. Use `⟨(g.det ^ K)⁻¹ • P g y, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[SetLike.mem_coe, LinearMap.mem_ker]`.

Rewrite using `[map_smul, hFint, hy, map_zero, smul_zero]`. Simplify using `only [Submodule.subtype_apply, Submodule.coe_smul, hPσ g hg y, smul_smul, inv_mul_cancel₀ hd, one_smul]`. Break down `hirr S' hS'le hS'st with h | h` into its components or cases. Rewrite using `[eq_bot_iff]`. Introduce `y hy`.

Establish `hyS : (y : H) ∈ S'` using `⟨y, hy, rfl⟩`. Rewrite `hyS` using `[h, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `Subtype.ext hyS`. It suffices to derive a contradiction.

Establish `hv : v0 ∈ S'` using `by rw [h]; exact hv0S`. Take `⟨y, hy, hyv⟩` from `hv`. Establish `hyw : y = w0` using `Subtype.ext hyv`. Rewrite `hy` using `[hyw]`. Conclude with `hF0 hy`.

Set `φ : U →ₗ[ℂ] LinearMap.range F` to `LinearMap.codRestrict (LinearMap.range F) (mulD ∘ₗ U.subtype) (fun u => Submodule.mem_comap.mp (Submodule.mem_inf.mp u.2).2)`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Introduce `u v huv`. Use `congrArg Subtype.val huv` as an intermediate fact.

Simplify using `only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this`. Conclude with `Subtype.ext (hmulD_inj this)`. Introduce and unpack `⟨z, x, rfl⟩`. Take `⟨f', hf'mem, hf'eq⟩` from `hsplit (F x) (hFmem' x)`. Use `⟨⟨f', Submodule.mem_inf.mpr ⟨hf'mem, Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨x, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf'eq⟩)⟩⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, mulD, LinearMap.mulLeft_apply]`. Conclude with `hf'eq.symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem modelIso_of_steps (hA : PolyExt) (hI : LamInt) (hT : TorusEig) (hL : LowerInv)
    (hM : ModelMap) (hD : DetSplit) (hH : PI.HwIrred) : PI.ModelIso := by
  intro N Λ H _ _ σ S hU hK
  obtain ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩ := hK
  have hK' : IsKTypeOf (allPos N) σ Λ S := ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩
  haveI := hfin
  obtain ⟨K, P, hP, hPσ⟩ := hA N H σ S hU hfin hstab
  choose μ hμ using hI N Λ H σ v0 hU hv0ne hv0w
  let w0 : S := ⟨v0, hv0S⟩
  have hw0ne : w0 ≠ 0 := by
    intro h; apply hv0ne
    have := congrArg Subtype.val h
    simpa [w0] using this
  have hT' := hT N Λ H σ S K P hU hstab hPσ w0 hv0w
  have hL' := hL N Λ H σ S K P hU hK' hP hPσ w0 hv0w
  have hT'' : ∀ (θ : Fin N → ℝ) (x : S), ⟪w0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪w0, x⟫_ℂ := by
    intro θ x; rw [hT' θ x]; simp only [hμ]
  obtain ⟨ν, F, hν, hFmem, hF0, hFint⟩ := hM N S P w0 μ K hP hw0ne hT'' hL'
  have hanti : Antitone ν := by
    intro l j hlj
    by_contra hlt
    push_neg at hlt
    rcases eq_or_lt_of_le hlj with h | h
    · subst h; exact lt_irrefl _ hlt
    · have hbot := dualWeylNonDom ℂ N N ν ⟨l, j, h, hlt⟩
      have := hFmem w0
      rw [hbot, Submodule.mem_bot] at this
      exact hF0 this
  have hμanti : Antitone μ := by
    intro a b hab
    have h1 := hν a
    have h2 := hν b
    have h3 : (ν b : ℤ) ≤ ν a := by exact_mod_cast hanti hab
    omega
  let lam : DomWeight N := ⟨μ, hμanti⟩
  refine ⟨lam, fun a => hμ a, ?_⟩
  let c : ℕ := if h : 0 < N then ν ⟨N - 1, by omega⟩ else 0
  have hnat : ∀ a, lam.natW a + c = ν a := by
    intro a
    have hN : 0 < N := a.pos
    have h1 := hν a
    have h2 := hν ⟨N - 1, by omega⟩
    have h3 : ν ⟨N - 1, by omega⟩ ≤ ν a := hanti (by rw [Fin.le_def]; simp; omega)
    have h3' : (ν ⟨N - 1, by omega⟩ : ℤ) ≤ ν a := by exact_mod_cast h3
    simp only [DomWeight.natW, DomWeight.detShift, c, dif_pos hN, lam]
    omega
  have hlast : ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 := by
    intro h; simp [DomWeight.natW, DomWeight.detShift, h, lam]
  have hsplit := hD N lam.natW c hlast
  have hνeq : (fun a => lam.natW a + c) = ν := funext hnat
  have hFmem' : ∀ x, F x ∈ dualWeyl ℂ N N (fun a => lam.natW a + c) := by
    intro x; rw [hνeq]; exact hFmem x
  let mulD : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ :=
    LinearMap.mulLeft ℂ (detPoly N ^ c)
  have hmulD_inj : Function.Injective mulD := by
    intro f g hfg
    simp only [mulD, LinearMap.mulLeft_apply] at hfg
    exact mul_left_cancel₀ (pow_ne_zero _ (detPoly_ne_zero N)) hfg
  let U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
    nablaSq ℂ N lam ⊓ (LinearMap.range F).comap mulD
  have hUst : ∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U := by
    intro g f hf
    obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.mp hf
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hf2)
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · unfold sqAct
      exact Submodule.smul_mem _ _ (dualWeylRowStable ℂ N N _ _ f hf1)
    · set dg := (g : Matrix (Fin N) (Fin N) ℂ).det with hdgdef
      have hdg : dg ≠ 0 := by
        have := (Matrix.GeneralLinearGroup.det g).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
      refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr
        ⟨(detPow ℂ N g lam.detShift * (dg ^ c)⁻¹) • P (g : Matrix (Fin N) (Fin N) ℂ) x, ?_⟩)
      rw [map_smul, hFint, hx]
      simp only [mulD, LinearMap.mulLeft_apply, sqAct]
      rw [map_mul, map_pow, rowAct_detPoly, Matrix.det_transpose]
      have key : C ((dg ^ c)⁻¹) * C dg ^ c = (1 : MvPolynomial (Fin N × Fin N) ℂ) := by
        rw [← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdg), C_1]
      simp only [smul_eq_C_mul, C_mul]
      linear_combination (C (detPow ℂ N g lam.detShift) * detPoly N ^ c *
        rowAct ℂ (n := N) (g : Matrix (Fin N) (Fin N) ℂ)ᵀ f) * key
  obtain ⟨f0, hf0mem, hf0eq⟩ := hsplit (F w0) (hFmem' w0)
  have hf0U : f0 ∈ U := Submodule.mem_inf.mpr ⟨hf0mem, Submodule.mem_comap.mpr
    (LinearMap.mem_range.mpr ⟨w0, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf0eq⟩)⟩
  have hf0ne : f0 ≠ 0 := by
    intro h; apply hF0; rw [hf0eq, h, mul_zero]
  have hUeq : U = nablaSq ℂ N lam := by
    rcases (hH N lam).2.1 U inf_le_left hUst with h | h
    · exfalso; rw [h, Submodule.mem_bot] at hf0U; exact hf0ne hf0U
    · exact h
  have hFinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ H := (LinearMap.ker F).map S.subtype
    have hS'le : S' ≤ S := by
      rintro _ ⟨y, _, rfl⟩; exact y.2
    have hS'st : IsKStableOn (allPos N) σ S' := by
      rintro g hg _ ⟨y, hy, rfl⟩
      have hd : g.det ^ K ≠ 0 := pow_ne_zero _ (det_ne_zero_of_mem_K hg)
      refine ⟨(g.det ^ K)⁻¹ • P g y, ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker] at hy ⊢
        rw [map_smul, hFint, hy, map_zero, smul_zero]
      · simp only [Submodule.subtype_apply, Submodule.coe_smul, hPσ g hg y, smul_smul,
          inv_mul_cancel₀ hd, one_smul]
    rcases hirr S' hS'le hS'st with h | h
    · rw [eq_bot_iff]
      intro y hy
      have hyS : (y : H) ∈ S' := ⟨y, hy, rfl⟩
      rw [h, Submodule.mem_bot] at hyS
      rw [Submodule.mem_bot]
      exact Subtype.ext hyS
    · exfalso
      have hv : v0 ∈ S' := by rw [h]; exact hv0S
      obtain ⟨y, hy, hyv⟩ := hv
      have hyw : y = w0 := Subtype.ext hyv
      rw [hyw] at hy
      exact hF0 hy
  let φ : U →ₗ[ℂ] LinearMap.range F :=
    LinearMap.codRestrict (LinearMap.range F) (mulD ∘ₗ U.subtype)
      (fun u => Submodule.mem_comap.mp (Submodule.mem_inf.mp u.2).2)
  have hφ : Function.Bijective φ := by
    constructor
    · intro u v huv
      have := congrArg Subtype.val huv
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
      exact Subtype.ext (hmulD_inj this)
    · rintro ⟨z, x, rfl⟩
      obtain ⟨f', hf'mem, hf'eq⟩ := hsplit (F x) (hFmem' x)
      refine ⟨⟨f', Submodule.mem_inf.mpr ⟨hf'mem, Submodule.mem_comap.mpr
        (LinearMap.mem_range.mpr ⟨x, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf'eq⟩)⟩⟩, ?_⟩
      apply Subtype.ext
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, mulD,
        LinearMap.mulLeft_apply]
      exact hf'eq.symm
  calc Module.finrank ℂ S = Module.finrank ℂ (LinearMap.range F) :=
        (LinearMap.finrank_range_of_inj hFinj).symm
    _ = Module.finrank ℂ U := (LinearEquiv.ofBijective φ hφ).finrank_eq.symm
    _ = Module.finrank ℂ (nablaSq ℂ N lam) := (LinearEquiv.ofEq _ _ hUeq).finrank_eq

end PI.WMI
