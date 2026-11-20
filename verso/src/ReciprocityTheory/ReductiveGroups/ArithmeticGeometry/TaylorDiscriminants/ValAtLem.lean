import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.ValAt

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X : Scheme.{0}}

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem valAt'_of (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valAt x U h f := dif_pos h

/- English proof (translation)
The claim follows from `dif_neg h`.
-/
theorem valAt'_of_not (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ¬ ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valAt' x U f = 0 :=
  dif_neg h

/- English proof (translation)
Distinguish the cases in `h : ⊤ ≤ x ⁻¹ᵁ U`. Simplify using `[valAt'_of _ _ h, valAt]`. Simplify using `[valAt'_of_not _ _ h]`.
-/
theorem valAt'_mul (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f * g) = valAt' x U f * valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp [valAt'_of _ _ h, valAt]
  · simp [valAt'_of_not _ _ h]

/- English proof (translation)
Distinguish the cases in `h : ⊤ ≤ x ⁻¹ᵁ U`. Simplify using `[valAt'_of _ _ h, valAt]`. Simplify using `[valAt'_of_not _ _ h]`.
-/
theorem valAt'_add (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f + g) = valAt' x U f + valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp [valAt'_of _ _ h, valAt]
  · simp [valAt'_of_not _ _ h]

/- English proof (translation)
Distinguish the cases in `h : ⊤ ≤ x ⁻¹ᵁ U`. Simplify using `[valAt'_of _ _ h, valAt]`. Simplify using `[valAt'_of_not _ _ h]`.
-/
theorem valAt'_sub (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f - g) = valAt' x U f - valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp [valAt'_of _ _ h, valAt]
  · simp [valAt'_of_not _ _ h]

/- English proof (translation)
Simplify using `[valAt'_of _ _ h, valAt]`.
-/
theorem valAt'_one (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U 1 = 1 := by
  simp [valAt'_of _ _ h, valAt]

def valHom (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ where
  toFun := valAt' x U
  map_one' := valAt'_one x U h
  map_mul' := valAt'_mul x U
  map_zero' := by simp [valAt'_of _ _ h, valAt]
  map_add' := valAt'_add x U

/- English proof (translation)
Establish `hU : ⊤ ≤ x ⁻¹ᵁ U` using `fun p hp => hVU (h hp)`. Rewrite using `[valAt'_of _ _ h, valAt'_of _ _ hU]`. Simplify using `only [valAt]`. Use `congr 1`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`.
-/
theorem valAt'_res (x : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' x V (X.presheaf.map (homOfLE hVU).op f) = valAt' x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => hVU (h hp)
  rw [valAt'_of _ _ h, valAt'_of _ _ hU]
  simp only [valAt]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/- English proof (translation)
Rewrite using `[valAt'_of _ _ h]`. Establish `key : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f`. Rewrite using `[Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, top_inf_eq]`. Establish `e2 : (x.appLE U ⊤ h).hom f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (valAt x U h f)`. Simplify using `[valAt]`.

Express the relevant statement in the definitionally equal form `_ ↔ p ∈ x ⁻¹ᵁ X.basicOpen f`. Rewrite using `[← key, e2, basicOpen_eq_of_affine]`. Use `Iff.trans ?_ (PrimeSpectrum.mem_basicOpen (R := ℂ) (valAt x U h f) p).symm` and prove the remaining obligations. Establish `hp` using `(p : PrimeSpectrum ℂ).isPrime`. Establish `hb : (p : PrimeSpectrum ℂ).asIdeal = ⊥` using `Ideal.eq_bot_of_prime _`.

Rewrite using `[hb, Submodule.mem_bot]`.
-/
theorem valAt'_ne_zero_iff (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (p : Sp ℂ) :
    valAt' x U f ≠ 0 ↔ x p ∈ X.basicOpen f := by
  rw [valAt'_of _ _ h]
  have key : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, top_inf_eq]
  have e2 : (x.appLE U ⊤ h).hom f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (valAt x U h f) := by
    simp [valAt]
  change _ ↔ p ∈ x ⁻¹ᵁ X.basicOpen f
  rw [← key, e2, basicOpen_eq_of_affine]
  refine Iff.trans ?_ (PrimeSpectrum.mem_basicOpen (R := ℂ) (valAt x U h f) p).symm
  have hp := (p : PrimeSpectrum ℂ).isPrime
  have hb : (p : PrimeSpectrum ℂ).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [hb, Submodule.mem_bot]

section Hol

open NumberField

variable {g : ℕ}

/- English proof (translation)
The claim follows from `ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ e z ⁻¹ᵁ U} (fun z => valAt' (e z) U f) (hol U f).1 (hol U f).2 z₀ h0`.
-/
theorem analyticAt_val (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (hol : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (e z) U f) {z | ⊤ ≤ e z ⁻¹ᵁ U})
    (U : X.Opens) (f : Γ(X, U)) (z₀ : Fin g → ℂ) (h0 : ⊤ ≤ e z₀ ⁻¹ᵁ U) :
    AnalyticAt ℂ (fun z => valAt' (e z) U f) z₀ :=
  ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ e z ⁻¹ᵁ U} (fun z => valAt' (e z) U f) (hol U f).1 (hol U f).2 z₀ h0

/- English proof (translation)
Establish `h1` using `h U f`. Establish `hc : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z))` using `continuous_const.prodMk continuous_id`. Establish `hd : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z))` using `(differentiable_const _).prodMk differentiable_id`. Prove the components needed by the constructor for the conclusion. Establish `ho` using `h1.1.preimage hc`.

Use `ho using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Conclude with `⟨fun hz => ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hz⟩, fun hz => hz.2⟩`. Introduce `z hz`. Establish `hw` using `h1.2 ((0 : Fin 0 → ℂ), z) ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hz⟩`.

Conclude with `hw.comp z (hd z).differentiableWithinAt (fun w hw' => ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hw'⟩)`.
-/
theorem hol_of_isHolTo (F : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)))
      (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => F bz.2)) (U : X.Opens) (f : Γ(X, U)) :
    IsOpen {z | ⊤ ≤ F z ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (F z) U f) {z | ⊤ ≤ F z ⁻¹ᵁ U} := by
  have h1 := h U f
  have hc : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := continuous_const.prodMk continuous_id
  have hd : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  constructor
  · have ho := h1.1.preimage hc
    convert ho using 1
    ext z
    exact ⟨fun hz => ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hz⟩, fun hz => hz.2⟩
  · intro z hz
    have hw := h1.2 ((0 : Fin 0 → ℂ), z) ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hz⟩
    exact hw.comp z (hd z).differentiableWithinAt (fun w hw' => ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hw'⟩)

/- English proof (translation)
The claim follows from `hol_of_isHolTo (fun z => (W.ex i P z).left) (W.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 U f`.
-/
theorem famHol {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (W : FamilyUnif Xo σ ty) (i : Fin W.n)
    (P : (W.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (W.Di i) ty P) (U : Xo.univ.t.G.left.Opens)
    (f : Γ(Xo.univ.t.G.left, U)) :
    IsOpen {z | ⊤ ≤ (W.ex i P z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (W.ex i P z).left U f) {z | ⊤ ≤ (W.ex i P z).left ⁻¹ᵁ U} :=
  hol_of_isHolTo (fun z => (W.ex i P z).left)
    (W.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 U f

end Hol

section Periodic

variable {g : ℕ}

/- English proof (translation)
Apply `hf.apply_eq_apply_of_bounded` to reduce the goal to its premises. Use `(hK.image hf.continuous).isBounded.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨w, hw, hl⟩` from `hcov z`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations.

Use `hper w (z - w) hl` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Conclude with `this.symm`.
-/
theorem periodic_const (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (L : AddSubgroup (Fin g → ℂ))
    (K : Set (Fin g → ℂ)) (hK : IsCompact K) (hcov : ∀ z, ∃ w ∈ K, z - w ∈ L)
    (hper : ∀ z, ∀ l ∈ L, f (z + l) = f z) (z w : Fin g → ℂ) : f z = f w := by
  apply hf.apply_eq_apply_of_bounded
  refine (hK.image hf.continuous).isBounded.subset ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨w, hw, hl⟩ := hcov z
  refine ⟨w, hw, ?_⟩
  have := hper w (z - w) hl
  rw [add_sub_cancel] at this
  exact this.symm

/- English proof (translation)
Take `⟨b, hbs, hbspan, hbli⟩` from `exists_linearIndependent ℝ (Set.range P)`. Establish `hsp : ⊤ ≤ Submodule.span ℝ (Set.range ((↑) : b → Fin g → ℂ))`. Rewrite using `[Subtype.range_coe, hbspan, hspan]`. Set `B : Module.Basis b ℝ (Fin g → ℂ)` to `Module.Basis.mk hbli hsp`. Establish `: Fintype b` using `FiniteDimensional.fintypeBasisIndex B`.

Set `K` to `(fun t : b → ℝ => ∑ i, t i • B i) '' Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)`. Establish `hK : IsCompact K` using `(isCompact_univ_pi fun _ => isCompact_Icc).image (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const)`. Establish `hB : ∀ i, ∃ a, P a = B i` using `fun i => by`. Rewrite using `[Module.Basis.mk_apply]`. Conclude with `hbs i.2`.

Use `periodic_const f hf P.range K hK (fun z => ?_) (fun z l hl => ?_) z w` and prove the remaining obligations. Use `⟨∑ i, Int.fract (B.repr z i) • B i, ⟨fun i => Int.fract (B.repr z i), fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hz : z - ∑ i, Int.fract (B.repr z i) • B i = ∑ i, ((⌊B.repr z i⌋ : ℤ) : ℝ) • B i` using `by set c := B.repr z with hc nth_rewrite 1 [← B.sum_repr z]`. Rewrite using `[← hc]`. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_smul, Int.self_sub_fract]`. Rewrite using `[hz]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hB i`.

Rewrite using `[← ha, Int.cast_smul_eq_zsmul ℝ, ← map_zsmul]`. Conclude with `⟨_, rfl⟩`. Take `⟨a, rfl⟩` from `hl`. Conclude with `hper z a`.
-/
theorem periodic_const_range {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z a, f (z + P a) = f z) (z w : Fin g → ℂ) : f z = f w := by
  classical
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℝ (Set.range P)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ((↑) : b → Fin g → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let B : Module.Basis b ℝ (Fin g → ℂ) := Module.Basis.mk hbli hsp
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  let K := (fun t : b → ℝ => ∑ i, t i • B i) '' Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const)
  have hB : ∀ i, ∃ a, P a = B i := fun i => by
    rw [Module.Basis.mk_apply]; exact hbs i.2
  refine periodic_const f hf P.range K hK (fun z => ?_) (fun z l hl => ?_) z w
  · refine ⟨∑ i, Int.fract (B.repr z i) • B i, ⟨fun i => Int.fract (B.repr z i),
      fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩, ?_⟩
    have hz : z - ∑ i, Int.fract (B.repr z i) • B i = ∑ i, ((⌊B.repr z i⌋ : ℤ) : ℝ) • B i := by
      set c := B.repr z with hc
      nth_rewrite 1 [← B.sum_repr z]
      rw [← hc]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, Int.self_sub_fract]
    rw [hz]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hB i
    rw [← ha, Int.cast_smul_eq_zsmul ℝ, ← map_zsmul]
    exact ⟨_, rfl⟩
  · obtain ⟨a, rfl⟩ := hl
    exact hper z a

end Periodic

end ReciprocityTheory.ChartRestriction.G.TB.ValAt
