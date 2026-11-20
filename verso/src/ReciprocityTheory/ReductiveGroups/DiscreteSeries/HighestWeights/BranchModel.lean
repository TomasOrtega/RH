import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ModelIso
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDense

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HW

section SlopeTestRemainingChoices
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix PI.WMI
open scoped InnerProductSpace

/- English proof (translation)
Establish `hA : PolyExt` using `polyExt_of polynomial_coefficients unitaryGroupDense_holds`. Establish `hI : LamInt` using `lambda_integrality`. Establish `hT : TorusEig` using `torus_eigenvalue_formula`. Establish `hL : LowerInv` using `lower_triangular_invariance`. Establish `hM : ModelMap` using `model_map_equivariance`.

Establish `hD : DetSplit` using `determinant_splitting_formula`. Establish `hH : PI.HwIrred` using `highest_weight_irreducible`. Take `⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩` from `id hK`. Establish `hK' : IsKTypeOf (allPos N) σ Λ S` using `⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩`. Use `haveI := hfin`.

Take `⟨K, P, hP, hPσ⟩` from `hA N H σ S hU hfin hstab`. Use `choose μ hμ using hI N Λ H σ v0 hU hv0ne hv0w`. Set `w0 : S` to `⟨v0, hv0S⟩`. Establish `hw0ne : w0 ≠ 0`. Introduce `h`.

Apply `hv0ne` to reduce the goal to its premises. Use `congrArg Subtype.val h` as an intermediate fact. Simplify `this` using `[w0]`. Establish `hT'` using `hT N Λ H σ S K P hU hstab hPσ w0 hv0w`. Establish `hL'` using `hL N Λ H σ S K P hU hK' hP hPσ w0 hv0w`.

Establish `hT'' : ∀ (θ : Fin N → ℝ) (x : S), ⟪w0, P (torus θ) x⟫_ℂ = Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪w0, x⟫_ℂ`. Introduce `θ x`. Rewrite using `[hT' θ x]`. Simplify using `only [hμ]`. Take `⟨ν, F, hν, hFmem, hF0, hFint⟩` from `hM N S P w0 μ K hP hw0ne hT'' hL'`.

Establish `hanti : Antitone ν`. Introduce `l j hlj`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Break down `eq_or_lt_of_le hlj with h | h` into its components or cases.

Substitute `h` using the available equality. Conclude with `lt_irrefl _ hlt`. Establish `hbot` using `dualWeylNonDom ℂ N N ν ⟨l, j, h, hlt⟩`. Use `hFmem w0` as an intermediate fact. Rewrite `this` using `[hbot, Submodule.mem_bot]`.

Conclude with `hF0 this`. Establish `hμanti : Antitone μ`. Introduce `a b hab`. Establish `h1` using `hν a`. Establish `h2` using `hν b`.

Establish `h3 : (ν b : ℤ) ≤ ν a` using `by exact_mod_cast hanti hab`. Use linear arithmetic over natural numbers and integers. Set `lam : DomWeight N` to `⟨μ, hμanti⟩`. Use `⟨lam, fun a => hμ a, ?_⟩` and prove the remaining obligations. Set `c : ℕ` to `if h : 0 < N then ν ⟨N - 1, by omega⟩ else 0`.

Establish `hnat : ∀ a, lam.natW a + c = ν a`. Introduce `a`. Establish `hN : 0 < N` using `a.pos`. Establish `h1` using `hν a`. Establish `h2` using `hν ⟨N - 1, by omega⟩`.

Establish `h3 : ν ⟨N - 1, by omega⟩ ≤ ν a` using `hanti (by rw [Fin.le_def]; simp; omega)`. Establish `h3' : (ν ⟨N - 1, by omega⟩ : ℤ) ≤ ν a` using `by exact_mod_cast h3`. Simplify using `only [DomWeight.natW, DomWeight.detShift, c, dif_pos hN, lam]`. Use linear arithmetic over natural numbers and integers. Establish `hlast : ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0`.

Introduce `h`. Simplify using `[DomWeight.natW, DomWeight.detShift, h, lam]`. Establish `hsplit` using `hD N lam.natW c hlast`. Establish `hνeq : (fun a => lam.natW a + c) = ν` using `funext hnat`. Establish `hFmem' : ∀ x, F x ∈ dualWeyl ℂ N N (fun a => lam.natW a + c)`.

Introduce `x`. Rewrite using `[hνeq]`. Conclude with `hFmem x`. Set `mulD : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ` to `LinearMap.mulLeft ℂ (detPoly N ^ c)`. Establish `hmulD_inj : Function.Injective mulD`.

Introduce `f g hfg`. Simplify using `only [mulD, LinearMap.mulLeft_apply] at hfg`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ (detPoly_ne_zero N)) hfg`. Set `U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)` to `nablaSq ℂ N lam ⊓ (LinearMap.range F).comap mulD`. Establish `hUst : ∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U`.

Introduce `g f hf`. Take `⟨hf1, hf2⟩` from `Submodule.mem_inf.mp hf`. Take `⟨x, hx⟩` from `LinearMap.mem_range.mp (Submodule.mem_comap.mp hf2)`. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Unfold `sqAct`.

Conclude with `Submodule.smul_mem _ _ (dualWeylRowStable ℂ N N _ _ f hf1)`. Use `set dg := (g : Matrix (Fin N) (Fin N) ℂ).det with hdgdef`. Establish `hdg : dg ≠ 0`. Use `(Matrix.GeneralLinearGroup.det g).ne_zero` as an intermediate fact. Rewrite `this` using `[Matrix.GeneralLinearGroup.val_det_apply]`. Then use the resulting hypothesis.

Use `Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨(detPow ℂ N g lam.detShift * (dg ^ c)⁻¹) • P (g : Matrix (Fin N) (Fin N) ℂ) x, ?_⟩)` and prove the remaining obligations. Rewrite using `[map_smul, hFint, hx]`. Simplify using `only [mulD, LinearMap.mulLeft_apply, sqAct]`. Rewrite using `[map_mul, map_pow, rowAct_detPoly, Matrix.det_transpose]`. Establish `key : C ((dg ^ c)⁻¹) * C dg ^ c = (1 : MvPolynomial (Fin N × Fin N) ℂ)`.

Rewrite using `[← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdg), C_1]`. Simplify using `only [smul_eq_C_mul, C_mul]`. Take the linear combination `(C (detPow ℂ N g lam.detShift) * detPoly N ^ c * rowAct ℂ (n := N) (g : Matrix (Fin N) (Fin N) ℂ)ᵀ f) * key`. Take `⟨f0, hf0mem, hf0eq⟩` from `hsplit (F w0) (hFmem' w0)`. Establish `hf0U : f0 ∈ U` using `Submodule.mem_inf.mpr ⟨hf0mem, Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨w0, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf0eq⟩)⟩`.

Establish `hf0ne : f0 ≠ 0`. Introduce `h`. Apply `hF0` to reduce the goal to its premises. Rewrite using `[hf0eq, h, mul_zero]`. Establish `hUeq : U = nablaSq ℂ N lam`.

Break down `(hH N lam).2.1 U inf_le_left hUst with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `hf0U` using `[h, Submodule.mem_bot]`. Conclude with `hf0ne hf0U`. Conclude with `h`.

Establish `hFinj : Function.Injective F`. Rewrite using `[← LinearMap.ker_eq_bot]`. Set `S' : Submodule ℂ H` to `(LinearMap.ker F).map S.subtype`. Establish `hS'le : S' ≤ S`. Introduce and unpack `_ ⟨y, _, rfl⟩`.

Conclude with `y.2`. Establish `hS'st : IsKStableOn (allPos N) σ S'`. Introduce and unpack `g hg _ ⟨y, hy, rfl⟩`. Establish `hd : g.det ^ K ≠ 0` using `pow_ne_zero _ (det_ne_zero_of_mem_K hg)`. Use `⟨(g.det ^ K)⁻¹ • P g y, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `hy`, the goal using `[SetLike.mem_coe, LinearMap.mem_ker]`. Rewrite using `[map_smul, hFint, hy, map_zero, smul_zero]`. Simplify using `only [Submodule.subtype_apply, Submodule.coe_smul, hPσ g hg y, smul_smul, inv_mul_cancel₀ hd, one_smul]`. Break down `hirr S' hS'le hS'st with h | h` into its components or cases. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Establish `hyS : (y : H) ∈ S'` using `⟨y, hy, rfl⟩`. Rewrite `hyS` using `[h, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `Subtype.ext hyS`.

It suffices to derive a contradiction. Establish `hv : v0 ∈ S'` using `by rw [h]; exact hv0S`. Take `⟨y, hy, hyv⟩` from `hv`. Establish `hyw : y = w0` using `Subtype.ext hyv`. Rewrite `hy` using `[hyw]`.

Conclude with `hF0 hy`. Set `φ : U →ₗ[ℂ] LinearMap.range F` to `LinearMap.codRestrict (LinearMap.range F) (mulD ∘ₗ U.subtype) (fun u => Submodule.mem_comap.mp (Submodule.mem_inf.mp u.2).2)`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Introduce `u v huv`.

Use `congrArg Subtype.val huv` as an intermediate fact. Simplify using `only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this`. Conclude with `Subtype.ext (hmulD_inj this)`. Introduce and unpack `⟨z, x, rfl⟩`. Take `⟨f', hf'mem, hf'eq⟩` from `hsplit (F x) (hFmem' x)`.

Use `⟨⟨f', Submodule.mem_inf.mpr ⟨hf'mem, Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨x, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf'eq⟩)⟩⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, mulD, LinearMap.mulLeft_apply]`. Conclude with `hf'eq.symm`. Set `eF : S ≃ₗ[ℂ] LinearMap.range F` to `LinearEquiv.ofInjective F hFinj`.

Set `eφ : U ≃ₗ[ℂ] LinearMap.range F` to `LinearEquiv.ofBijective φ hφ`. Set `e : S ≃ₗ[ℂ] nablaSq ℂ N lam` to `eF.trans (eφ.symm.trans (LinearEquiv.ofEq _ _ hUeq))`. Establish `he : ∀ x : S, detPoly N ^ c * ((e x : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) = F x`. Introduce `x`. Establish `h2 : ((eφ (eφ.symm (eF x)) : LinearMap.range F) : MvPolynomial (Fin N × Fin N) ℂ) = F x`.

Rewrite using `[eφ.apply_symm_apply]`. Both sides reduce to the same expression. Conclude with `h2`. Use `⟨e, ?_⟩` and prove the remaining obligations. Introduce `g hg x`.

Establish `hdg : (g : Matrix (Fin N) (Fin N) ℂ).det ≠ 0` using `det_ne_zero_of_mem_K hg`. Apply `hmulD_inj` to reduce the goal to its premises. Simplify using `only [mulD, LinearMap.mulLeft_apply]`. Rewrite using `[he]`. Establish `hy : P (g : Matrix (Fin N) (Fin N) ℂ) x = ((g : Matrix (Fin N) (Fin N) ℂ).det ^ K) • (⟨σ g x, hK.2.1 _ hg _ x.2⟩ : S)` using `Subtype.ext (by rw [hPσ _ hg x]; rfl)`.

Establish `hFy` using `hFint (g : Matrix (Fin N) (Fin N) ℂ) x`. Rewrite `hFy` using `[hy, map_smul, ← he x, map_mul, map_pow, rowAct_detPoly, Matrix.det_transpose]`. Use `set d := (g : Matrix (Fin N) (Fin N) ℂ).det with hd`. Establish `hdK : d ^ K ≠ 0` using `pow_ne_zero _ hdg`. Establish `hexp : detPow ℂ N g lam.detShift * d ^ K = d ^ c`.

Establish `hu : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) = d`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Distinguish the cases in `hN : 0 < N`. Establish `hds : lam.detShift = (c : ℤ) - K`. Establish `h1` using `hν ⟨N - 1, by omega⟩`.

Simplify using `only [DomWeight.detShift, c, dif_pos hN, lam]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[detPow, hds, _root_.zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu, mul_assoc, inv_mul_cancel₀ hdK, mul_one]`. Establish `hN0 : N = 0` using `by omega`. Substitute `hN0` using the available equality.

Establish `h1 : d = 1` using `by rw [hd]; exact Matrix.det_isEmpty`. Establish `hc : c = 0` using `by simp [c]`. Establish `hs : lam.detShift = 0` using `by simp [DomWeight.detShift]`. Rewrite using `[hc, hs, h1, detPow]`. Simplify using the standard rewrite rules.

Establish `hFy' : F ⟨σ g x, hK.2.1 _ hg _ x.2⟩ = C ((d ^ K)⁻¹) * (d ^ K • F ⟨σ g x, hK.2.1 _ hg _ x.2⟩)`. Rewrite using `[smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hdK, C_1, one_mul]`. Rewrite using `[hFy', hFy, sqAct, smul_eq_C_mul]`. Establish `hexp' : detPow ℂ N g lam.detShift = d ^ c * (d ^ K)⁻¹`. Rewrite using `[← hexp, mul_assoc, mul_inv_cancel₀ hdK, mul_one]`.

Rewrite using `[hexp', C_mul, C_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem highest_weight_model_equiv (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (hU : IsURepOn (Kset (allPos N)) σ) (hK : IsKTypeOf (allPos N) σ Λ S) :
    ∃ lam : DomWeight N, (∀ a, Λ a = ((lam.w a : ℤ) : ℝ)) ∧
      ∃ e : S ≃ₗ[ℂ] nablaSq ℂ N lam,
        ∀ (g : GL (Fin N) ℂ) (hg : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N)) (x : S),
          ((e ⟨σ g x, hK.2.1 _ hg _ x.2⟩ : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) =
            sqAct ℂ N lam g (e x) := by
  have hA : PolyExt := polyExt_of polynomial_coefficients unitaryGroupDense_holds
  have hI : LamInt := lambda_integrality
  have hT : TorusEig := torus_eigenvalue_formula
  have hL : LowerInv := lower_triangular_invariance
  have hM : ModelMap := model_map_equivariance
  have hD : DetSplit := determinant_splitting_formula
  have hH : PI.HwIrred := highest_weight_irreducible
  obtain ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩ := id hK
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
  let eF : S ≃ₗ[ℂ] LinearMap.range F := LinearEquiv.ofInjective F hFinj
  let eφ : U ≃ₗ[ℂ] LinearMap.range F := LinearEquiv.ofBijective φ hφ
  let e : S ≃ₗ[ℂ] nablaSq ℂ N lam := eF.trans (eφ.symm.trans (LinearEquiv.ofEq _ _ hUeq))
  have he : ∀ x : S, detPoly N ^ c * ((e x : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) = F x := by
    intro x
    have h2 : ((eφ (eφ.symm (eF x)) : LinearMap.range F) : MvPolynomial (Fin N × Fin N) ℂ) = F x := by
      rw [eφ.apply_symm_apply]; rfl
    exact h2
  refine ⟨e, ?_⟩
  intro g hg x
  have hdg : (g : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := det_ne_zero_of_mem_K hg
  apply hmulD_inj
  simp only [mulD, LinearMap.mulLeft_apply]
  rw [he]
  have hy : P (g : Matrix (Fin N) (Fin N) ℂ) x =
      ((g : Matrix (Fin N) (Fin N) ℂ).det ^ K) • (⟨σ g x, hK.2.1 _ hg _ x.2⟩ : S) :=
    Subtype.ext (by rw [hPσ _ hg x]; rfl)
  have hFy := hFint (g : Matrix (Fin N) (Fin N) ℂ) x
  rw [hy, map_smul, ← he x, map_mul, map_pow, rowAct_detPoly, Matrix.det_transpose] at hFy
  set d := (g : Matrix (Fin N) (Fin N) ℂ).det with hd
  have hdK : d ^ K ≠ 0 := pow_ne_zero _ hdg
  have hexp : detPow ℂ N g lam.detShift * d ^ K = d ^ c := by
    have hu : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) = d := by
      rw [Matrix.GeneralLinearGroup.val_det_apply]
    by_cases hN : 0 < N
    · have hds : lam.detShift = (c : ℤ) - K := by
        have h1 := hν ⟨N - 1, by omega⟩
        simp only [DomWeight.detShift, c, dif_pos hN, lam]
        omega
      rw [detPow, hds, _root_.zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu, mul_assoc, inv_mul_cancel₀ hdK, mul_one]
    · have hN0 : N = 0 := by omega
      subst hN0
      have h1 : d = 1 := by rw [hd]; exact Matrix.det_isEmpty
      have hc : c = 0 := by simp [c]
      have hs : lam.detShift = 0 := by simp [DomWeight.detShift]
      rw [hc, hs, h1, detPow]; simp
  have hFy' : F ⟨σ g x, hK.2.1 _ hg _ x.2⟩ = C ((d ^ K)⁻¹) * (d ^ K • F ⟨σ g x, hK.2.1 _ hg _ x.2⟩) := by
    rw [smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hdK, C_1, one_mul]
  rw [hFy', hFy, sqAct, smul_eq_C_mul]
  have hexp' : detPow ℂ N g lam.detShift = d ^ c * (d ^ K)⁻¹ := by
    rw [← hexp, mul_assoc, mul_inv_cancel₀ hdK, mul_one]
  rw [hexp', C_mul, C_pow]
  ring
end SlopeTestRemainingChoices

open Formalism.BasicNotions PI.UpqRep

/- English proof (translation)
The claim follows from `highest_weight_model_equiv N Λ H σ S hU hK`.
-/
theorem model_equiv (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (hU : IsURepOn (Kset (allPos N)) σ) (hK : IsKTypeOf (allPos N) σ Λ S) :
    ∃ lam : DomWeight N, (∀ a, Λ a = ((lam.w a : ℤ) : ℝ)) ∧
      ∃ e : S ≃ₗ[ℂ] nablaSq ℂ N lam,
        ∀ (g : GL (Fin N) ℂ) (hg : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N)) (x : S),
          ((e ⟨σ g x, hK.2.1 _ hg _ x.2⟩ : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) =
            sqAct ℂ N lam g (e x) :=
  highest_weight_model_equiv N Λ H σ S hU hK

end ReciprocityTheory.ChartRestriction.DS.HW
