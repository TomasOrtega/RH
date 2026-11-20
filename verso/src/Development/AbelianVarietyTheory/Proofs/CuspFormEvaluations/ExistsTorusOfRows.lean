import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitian

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ScalarTorus

open GlobalTheory.PeriodTorus

/- English proof (translation)
Set `fz : EuclideanSpace ℂ J ≃ₗ[ℤ] EuclideanSpace ℂ J` to `f.toAddEquiv.toIntLinearEquiv`. Establish `hr : Set.range (b.map f) = fz '' Set.range b`. Rewrite using `[Module.Basis.coe_map, Set.range_comp]`. Use `congr 1`. Use `show x ∈ Submodule.span ℤ (Set.range (b.map f)) ↔ f.symm x ∈ Submodule.span ℤ (Set.range b)`.

Rewrite using `[hr, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv]`. Both sides reduce to the same expression.
-/
private theorem mem_lat_basis_map_iff {J K : Type} [Fintype J] (b : Module.Basis K ℝ (EuclideanSpace ℂ J))
    (f : EuclideanSpace ℂ J ≃ₗ[ℝ] EuclideanSpace ℂ J) (x : EuclideanSpace ℂ J) :
    x ∈ I2.lat (b.map f) ↔ f.symm x ∈ I2.lat b := by
  let fz : EuclideanSpace ℂ J ≃ₗ[ℤ] EuclideanSpace ℂ J := f.toAddEquiv.toIntLinearEquiv
  have hr : Set.range (b.map f) = fz '' Set.range b := by
    rw [Module.Basis.coe_map, Set.range_comp]
    congr 1
  show x ∈ Submodule.span ℤ (Set.range (b.map f)) ↔ f.symm x ∈ Submodule.span ℤ (Set.range b)
  rw [hr, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv]
  rfl

open TorusAtAssembly in

/- English proof (translation)
Introduce `E _ _ _ H D g ty Pm t row ht hty hP hE hrow hinj`. Establish `hform : ∀ z w : Fin g → ℂ, hermForm (Matrix.diagonal fun _ => (t : ℂ)) z w = ∑ j, z j * ((t : ℂ) * (starRingEnd ℂ) (w j))`. Introduce `z w`. Simplify using `only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]`. Establish `hH : (Matrix.diagonal fun _ : Fin g => (t : ℂ)).IsHermitian` using `Matrix.isHermitian_diagonal_of_self_adjoint _ (by show star _ = _`.

Use function extensionality and compare the values at `i`. Use the proof step `simp)`. Establish `hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Matrix.diagonal fun _ : Fin g => (t : ℂ)) z z).re`. Introduce `z hz`. Rewrite using `[hform]`.

Establish `hterm : ∀ j, z j * ((t : ℂ) * (starRingEnd ℂ) (z j)) = ((t * Complex.normSq (z j) : ℝ) : ℂ)`. Introduce `j`. Rewrite using `[Complex.ofReal_mul, ← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hterm, ← Complex.ofReal_sum, Complex.ofReal_re]`.

Take `⟨j, hj⟩` from `Function.ne_iff.1 hz`. Conclude with `Finset.sum_pos' (fun i _ => mul_nonneg ht.le (Complex.normSq_nonneg _)) ⟨j, Finset.mem_univ _, mul_pos ht (Complex.normSq_pos.2 hj)⟩`. Take `⟨T₀, ψ₀, hr, hdim, hHf, hL, hact, heps⟩` from `exists_torusOf E H D g ty Pm _ hty hP hH hpos hE`. Establish `hrow' : ∀ j, row j < T₀.dim (ty j)`. Introduce `j`.

Rewrite using `[hdim]`. Conclude with `hrow j`. Set `f : Fin g → I2.Idx T₀.dim` to `fun j => ⟨ty j, ⟨row j, hrow' j⟩⟩`. Establish `hfinj : Function.Injective f`. Establish `hc : Function.Injective ((fun i : I2.Idx T₀.dim => (i.1, (i.2 : ℕ))) ∘ f)`.

Introduce `j j' h`. Simplify using `only [Function.comp, f, Prod.mk.injEq] at h`. Conclude with `hinj j j' h.1 h.2`. Conclude with `Function.Injective.of_comp hc`. Establish `hcard : Fintype.card (Fin g) = Fintype.card (I2.Idx T₀.dim)`.

Establish `h1 : Fintype.card (Fin g) = ∑ τ, Fintype.card {i // ty i = τ}`. Rewrite using `[← Fintype.card_sigma]`. Conclude with `Fintype.card_congr (Equiv.sigmaFiberEquiv ty).symm`. Rewrite using `[h1, Fintype.card_sigma]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.card_fin, hdim τ, ← Nat.card_eq_fintype_card, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult]`. Use `split_ifs with h`. Conclude with `(hty τ).1 h`. Conclude with `(hty τ).2 h`. Set `e : Fin g ≃ I2.Idx T₀.dim` to `Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩)`.

Establish `he_ty : ∀ i, ty (e.symm i) = i.1`. Introduce `i`. Conclude with `congrArg Sigma.fst (e.apply_symm_apply i)`. Establish `hs2 : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = t`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]`.

Establish `hs0 : (Real.sqrt t : ℂ) ≠ 0`. Conclude with `(Real.sqrt_pos.2 ht).ne'` after adjusting the coercions. Set `ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T₀.dim` to `{ toFun := fun z => WithLp.toLp 2 (fun i => (Real.sqrt t : ℂ) * z (e.symm i)) invFun := fun v j => v (e j) / (Real.sqrt t : ℂ) map_add' := by`. Introduce `z w`. Use extensionality with `i`.

Simplify using `[mul_add]`. Use the proof step `map_smul' := by`. Introduce `c z`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.smul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Use `left_inv := by`. Introduce `z`. Use function extensionality and compare the values at `j`. Simplify using `only [Equiv.symm_apply_apply]`.

Clear the denominators using the available nonvanishing facts. Use `right_inv := by`. Introduce `v`. Use extensionality with `i`. Simplify using `only [Equiv.apply_symm_apply]`.

Clear denominators, using `}` for the nonvanishing conditions. Establish `hψ : ∀ z i, ψ z i = (Real.sqrt t : ℂ) * z (e.symm i)` using `fun z i => rfl`. Establish `hψHf : ∀ z w, I2.Hf (ψ z) (ψ w) = hermForm (Matrix.diagonal fun _ => (t : ℂ)) z w`. Introduce `z w`. Rewrite using `[hform]`.

Unfold `I2.Hf`. Simplify using `only [hψ]`. Use `(e.symm.sum_comp (fun j => (Real.sqrt t : ℂ) * z j * (starRingEnd ℂ) ((Real.sqrt t : ℂ) * w j))).trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_ofReal]`. Take the linear combination `(z j * (starRingEnd ℂ) (w j)) * hs2`.

Establish `hψact : ∀ (α : 𝓞 E) z, ψ (fun k => ty k (α : E) * z k) = I2.act α (ψ z)`. Introduce `α z`. Use extensionality with `i`. Simplify using `only [hψ, I2.act, PiLp.toLp_apply]`. Rewrite using `[he_ty]`.

Expand and normalize the polynomial expressions, which then agree. Set `U : I2.Vsp T₀.dim ≃ₗ[ℂ] I2.Vsp T₀.dim` to `ψ₀.symm.trans ψ`. Establish `hUHf : ∀ x y, I2.Hf (U x) (U y) = I2.Hf x y`. Introduce `x y`. Establish `h1` using `hHf (ψ₀.symm x) (ψ₀.symm y)`.

Simplify using `only [LinearEquiv.apply_symm_apply] at h1`. Rewrite using `[h1, ← hψHf]`. Both sides reduce to the same expression. Establish `hUact : ∀ (α : 𝓞 E) x, U (I2.act α x) = I2.act α (U x)`. Introduce `α x`.

Take `⟨z, rfl⟩` from `ψ₀.surjective x`. Rewrite using `[← hact α z]`. Simplify using `only [U, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]`. Conclude with `hψact α z`. Establish `hUsymm_act : ∀ (α : 𝓞 E) x, U.symm (I2.act α x) = I2.act α (U.symm x)`.

Introduce `α x`. Apply `U.injective` to reduce the goal to its premises. Rewrite using `[hUact, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Establish `hUsymmHf : ∀ x y, I2.Hf (U.symm x) (U.symm y) = I2.Hf x y`. Introduce `x y`.

Rewrite using `[← hUHf, U.apply_symm_apply, U.apply_symm_apply]`. Establish `hmem : ∀ x, x ∈ I2.lat (T₀.b.map (U.restrictScalars ℝ)) ↔ U.symm x ∈ I2.lat T₀.b` using `fun x => mem_lat_basis_map_iff _ _ x`. Set `T' : I2.PT E` to `{ dim := T₀.dim r := T₀.r dim_conj := T₀.dim_conj b := T₀.b.map (U.restrictScalars ℝ) stable := by`. Introduce `α x hx`. Rewrite `hx`, the goal using `[hmem]`.

Rewrite using `[hUsymm_act]`. Conclude with `T₀.stable α _ hx`. Use `integral := by`. Introduce `x y hx hy`. Rewrite `hx`, `hy` using `[hmem]`.

Rewrite using `[← hUsymmHf]`. Conclude with `T₀.integral _ _ hx hy`. Use `perfect := by`. Introduce `φ`. Set `m : I2.lat T₀.b →+ I2.lat (T₀.b.map (U.restrictScalars ℝ))` to `AddMonoidHom.mk' (fun y => ⟨U y, (hmem _).2 (by rw [U.symm_apply_apply]; exact y.2)⟩) (by`.

Introduce `a b`. Apply `Subtype.ext` to reduce the goal to its premises. Use the proof step `simp)`. Take `⟨x₀, hx₀, hφ⟩` from `T₀.perfect (φ.comp m)`. Use `⟨U x₀, (hmem _).2 (by rw [U.symm_apply_apply]; exact hx₀), fun y => ?_⟩` and prove the remaining obligations.

Establish `hy : U.symm (y : I2.Vsp T₀.dim) ∈ I2.lat T₀.b` using `(hmem _).1 y.2`. Establish `h1` using `hφ ⟨_, hy⟩`. Establish `h2 : m ⟨_, hy⟩ = y` using `Subtype.ext (U.apply_symm_apply _)`. Rewrite `h1` using `[AddMonoidHom.comp_apply, h2]`. Rewrite using `[h1, ← hUHf, U.apply_symm_apply]`.

Use `eps := fun v => T₀.eps (U.symm v)`. Use `eps_pm := by`. Introduce `x hx`. Rewrite `hx` using `[hmem]`. Conclude with `T₀.eps_pm _ hx`.

Use `eps_add := by`. Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[hmem]`. Rewrite using `[map_add, T₀.eps_add _ hx _ hy, hUsymmHf]`. Use `eps_iso := by`.

Introduce `x hx h`. Rewrite `hx` using `[hmem]`. Conclude with `T₀.eps_iso _ hx fun α => by rw [← hUsymm_act, hUsymmHf]; exact h α }`. Establish `hTL : ∀ v, v ∈ T'.L ↔ U.symm v ∈ I2.lat T₀.b` using `hmem`. Establish `hTeps : ∀ v, T'.eps v = T₀.eps (U.symm v)` using `fun v => rfl`.

Use `⟨T', ψ, ⟨hr, hdim, hψHf, ?_, hψact, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `v`. Rewrite using `[hTL, hL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← U.apply_symm_apply v, ← ha]`. Simplify using `[U]`. Introduce and unpack `⟨a, ha⟩`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ha]`. Simplify using `[U]`. Introduce `a`. Rewrite using `[hTeps, ← heps a]`. Use `congr 1`.

Simplify using `[U]`. Introduce `j`. Use `⟨hrow' j, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[hψ]`.

Simplify using `only [PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, Pi.single_apply]`. Establish `hiff : e.symm i = j ↔ i = ⟨ty j, ⟨row j, hrow' j⟩⟩`. Rewrite using `[Equiv.symm_apply_eq]`. Both sides reduce to the same expression. Break down `em (i = ⟨ty j, ⟨row j, hrow' j⟩⟩) with h | h` into its components or cases.

Rewrite using `[if_pos (hiff.2 h), if_pos h]`. Rewrite using `[if_neg (mt hiff.1 h), if_neg h]`.
-/
theorem exists_torusOf_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (t : ℝ) (row : Fin g → ℕ), 0 < t → IsTypeFn H D.p D.q ty → IsPeriod D ty Pm → (∀ a b, (hermForm (Matrix.diagonal fun _ => (t : ℂ)) (Pm a) (Pm b)).im = D.EF a b) → (∀ j, row j < D.mult (ty j)) → (∀ j j', ty j = ty j' → row j = row j' → j = j') → ∃ (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsTorusOf D ty Pm (Matrix.diagonal fun _ => (t : ℂ)) T ψ ∧ ∀ j, ∃ h : row j < T.dim (ty j), ψ (Pi.single j 1) = open Classical in (Real.sqrt t : ℂ) • EuclideanSpace.single (⟨ty j, ⟨row j, h⟩⟩ : I2.Idx T.dim) (1 : ℂ) := by
  classical
  intro E _ _ _ H D g ty Pm t row ht hty hP hE hrow hinj
  have hform : ∀ z w : Fin g → ℂ, hermForm (Matrix.diagonal fun _ => (t : ℂ)) z w =
      ∑ j, z j * ((t : ℂ) * (starRingEnd ℂ) (w j)) := by
    intro z w
    simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
  have hH : (Matrix.diagonal fun _ : Fin g => (t : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      show star _ = _
      funext i
      simp)
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Matrix.diagonal fun _ : Fin g => (t : ℂ)) z z).re := by
    intro z hz
    rw [hform]
    have hterm : ∀ j, z j * ((t : ℂ) * (starRingEnd ℂ) (z j)) = ((t * Complex.normSq (z j) : ℝ) : ℂ) := by
      intro j
      rw [Complex.ofReal_mul, ← Complex.mul_conj]
      ring
    simp only [hterm, ← Complex.ofReal_sum, Complex.ofReal_re]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
    exact Finset.sum_pos' (fun i _ => mul_nonneg ht.le (Complex.normSq_nonneg _))
      ⟨j, Finset.mem_univ _, mul_pos ht (Complex.normSq_pos.2 hj)⟩
  obtain ⟨T₀, ψ₀, hr, hdim, hHf, hL, hact, heps⟩ := exists_torusOf E H D g ty Pm _ hty hP hH hpos hE
  have hrow' : ∀ j, row j < T₀.dim (ty j) := by
    intro j
    rw [hdim]
    exact hrow j
  let f : Fin g → I2.Idx T₀.dim := fun j => ⟨ty j, ⟨row j, hrow' j⟩⟩
  have hfinj : Function.Injective f := by
    have hc : Function.Injective ((fun i : I2.Idx T₀.dim => (i.1, (i.2 : ℕ))) ∘ f) := by
      intro j j' h
      simp only [Function.comp, f, Prod.mk.injEq] at h
      exact hinj j j' h.1 h.2
    exact Function.Injective.of_comp hc
  have hcard : Fintype.card (Fin g) = Fintype.card (I2.Idx T₀.dim) := by
    have h1 : Fintype.card (Fin g) = ∑ τ, Fintype.card {i // ty i = τ} := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv ty).symm
    rw [h1, Fintype.card_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.card_fin, hdim τ, ← Nat.card_eq_fintype_card, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult]
    split_ifs with h
    · exact (hty τ).1 h
    · exact (hty τ).2 h
  let e : Fin g ≃ I2.Idx T₀.dim :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩)
  have he_ty : ∀ i, ty (e.symm i) = i.1 := by
    intro i
    exact congrArg Sigma.fst (e.apply_symm_apply i)
  have hs2 : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = t := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  have hs0 : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ht).ne'
  let ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T₀.dim :=
    { toFun := fun z => WithLp.toLp 2 (fun i => (Real.sqrt t : ℂ) * z (e.symm i))
      invFun := fun v j => v (e j) / (Real.sqrt t : ℂ)
      map_add' := by
        intro z w
        ext i
        simp [mul_add]
      map_smul' := by
        intro c z
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.smul_apply]
        ring
      left_inv := by
        intro z
        funext j
        simp only [Equiv.symm_apply_apply]
        field_simp
      right_inv := by
        intro v
        ext i
        simp only [Equiv.apply_symm_apply]
        field_simp }
  have hψ : ∀ z i, ψ z i = (Real.sqrt t : ℂ) * z (e.symm i) := fun z i => rfl
  have hψHf : ∀ z w, I2.Hf (ψ z) (ψ w) = hermForm (Matrix.diagonal fun _ => (t : ℂ)) z w := by
    intro z w
    rw [hform]
    unfold I2.Hf
    simp only [hψ]
    refine (e.symm.sum_comp (fun j => (Real.sqrt t : ℂ) * z j * (starRingEnd ℂ) ((Real.sqrt t : ℂ) * w j))).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
    linear_combination (z j * (starRingEnd ℂ) (w j)) * hs2
  have hψact : ∀ (α : 𝓞 E) z, ψ (fun k => ty k (α : E) * z k) = I2.act α (ψ z) := by
    intro α z
    ext i
    simp only [hψ, I2.act, PiLp.toLp_apply]
    rw [he_ty]
    ring
  let U : I2.Vsp T₀.dim ≃ₗ[ℂ] I2.Vsp T₀.dim := ψ₀.symm.trans ψ
  have hUHf : ∀ x y, I2.Hf (U x) (U y) = I2.Hf x y := by
    intro x y
    have h1 := hHf (ψ₀.symm x) (ψ₀.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h1
    rw [h1, ← hψHf]
    rfl
  have hUact : ∀ (α : 𝓞 E) x, U (I2.act α x) = I2.act α (U x) := by
    intro α x
    obtain ⟨z, rfl⟩ := ψ₀.surjective x
    rw [← hact α z]
    simp only [U, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact hψact α z
  have hUsymm_act : ∀ (α : 𝓞 E) x, U.symm (I2.act α x) = I2.act α (U.symm x) := by
    intro α x
    apply U.injective
    rw [hUact, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hUsymmHf : ∀ x y, I2.Hf (U.symm x) (U.symm y) = I2.Hf x y := by
    intro x y
    rw [← hUHf, U.apply_symm_apply, U.apply_symm_apply]
  have hmem : ∀ x, x ∈ I2.lat (T₀.b.map (U.restrictScalars ℝ)) ↔ U.symm x ∈ I2.lat T₀.b :=
    fun x => mem_lat_basis_map_iff _ _ x
  let T' : I2.PT E :=
    { dim := T₀.dim
      r := T₀.r
      dim_conj := T₀.dim_conj
      b := T₀.b.map (U.restrictScalars ℝ)
      stable := by
        intro α x hx
        rw [hmem] at hx ⊢
        rw [hUsymm_act]
        exact T₀.stable α _ hx
      integral := by
        intro x y hx hy
        rw [hmem] at hx hy
        rw [← hUsymmHf]
        exact T₀.integral _ _ hx hy
      perfect := by
        intro φ
        let m : I2.lat T₀.b →+ I2.lat (T₀.b.map (U.restrictScalars ℝ)) :=
          AddMonoidHom.mk' (fun y => ⟨U y, (hmem _).2 (by rw [U.symm_apply_apply]; exact y.2)⟩)
            (by
              intro a b
              apply Subtype.ext
              simp)
        obtain ⟨x₀, hx₀, hφ⟩ := T₀.perfect (φ.comp m)
        refine ⟨U x₀, (hmem _).2 (by rw [U.symm_apply_apply]; exact hx₀), fun y => ?_⟩
        have hy : U.symm (y : I2.Vsp T₀.dim) ∈ I2.lat T₀.b := (hmem _).1 y.2
        have h1 := hφ ⟨_, hy⟩
        have h2 : m ⟨_, hy⟩ = y := Subtype.ext (U.apply_symm_apply _)
        rw [AddMonoidHom.comp_apply, h2] at h1
        rw [h1, ← hUHf, U.apply_symm_apply]
      eps := fun v => T₀.eps (U.symm v)
      eps_pm := by
        intro x hx
        rw [hmem] at hx
        exact T₀.eps_pm _ hx
      eps_add := by
        intro x hx y hy
        rw [hmem] at hx hy
        rw [map_add, T₀.eps_add _ hx _ hy, hUsymmHf]
      eps_iso := by
        intro x hx h
        rw [hmem] at hx
        exact T₀.eps_iso _ hx fun α => by rw [← hUsymm_act, hUsymmHf]; exact h α }
  have hTL : ∀ v, v ∈ T'.L ↔ U.symm v ∈ I2.lat T₀.b := hmem
  have hTeps : ∀ v, T'.eps v = T₀.eps (U.symm v) := fun v => rfl
  refine ⟨T', ψ, ⟨hr, hdim, hψHf, ?_, hψact, ?_⟩, ?_⟩
  · intro v
    rw [hTL, hL]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← U.apply_symm_apply v, ← ha]
      simp [U]
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← ha]
      simp [U]
  · intro a
    rw [hTeps, ← heps a]
    congr 1
    simp [U]
  · intro j
    refine ⟨hrow' j, ?_⟩
    ext i
    rw [hψ]
    simp only [PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, Pi.single_apply]
    have hiff : e.symm i = j ↔ i = ⟨ty j, ⟨row j, hrow' j⟩⟩ := by
      rw [Equiv.symm_apply_eq]
      rfl
    rcases em (i = ⟨ty j, ⟨row j, hrow' j⟩⟩) with h | h
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (mt hiff.1 h), if_neg h]

end GlobalTheory.ScalarTorus
