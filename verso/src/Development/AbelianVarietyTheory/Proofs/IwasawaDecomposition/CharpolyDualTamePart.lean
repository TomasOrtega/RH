import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial Module

namespace GlobalTheory.WeilDeligne.LabDual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Rewrite using `[← LinearMap.charpoly_toMatrix f (finBasis ℂ V), ← LinearMap.charpoly_toMatrix f.dualMap (finBasis ℂ V).dualBasis, ← Matrix.charpoly_transpose, LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]`.
-/
theorem charpoly_dualMap (f : End ℂ V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix f.dualMap (finBasis ℂ V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

/- English proof (translation)
Set `K : Subgroup (Weil h)` to `(Wild E A).subgroupOf (Weil h)`. Set `P : Subgroup (End ℂ V)ˣ` to `K.map a.ρ.toHomUnits`. Establish `hfin : Finite P`. Use `Set.Finite.of_finite_image (f := Units.val) (a.smooth.finite_range.subset ?_) Units.val_injective.injOn` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩`.

Conclude with `⟨⟨σ, Wild_le_Ine hσ⟩, rfl⟩`. Use `Fintype.ofFinite P` as an intermediate fact. Establish `hc : (Fintype.card P : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Use `⟨(Fintype.card P : ℂ)⁻¹ • ∑ p : P, (p.1 : End ℂ V), fun v => ?_, fun v hv => ?_, fun σ hσ => ?_, fun f hf v => ?_⟩` and prove the remaining obligations. Use `a.mem_tameSpace.mpr fun σ hσ => ?_` and prove the remaining obligations.

Rewrite using `[← End.mul_apply, mul_smul_comm, Finset.mul_sum]`. Use `congr 2`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl`. Establish `: ∀ p : P, (p.1 : End ℂ V) v = v`. Introduce and unpack `⟨_, σ, hσ, rfl⟩`.

Conclude with `a.mem_tameSpace.mp hv σ hσ`. Simplify using `[this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]`. Rewrite using `[smul_mul_assoc, Finset.sum_mul]`. Use `congr 1`. Conclude with `Fintype.sum_equiv (Equiv.mulRight (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl`.

Establish `: ∀ p : P, f ((p.1 : End ℂ V) v) = f v`. Introduce and unpack `⟨_, σ, hσ, rfl⟩`. Use `LinearMap.congr_fun (a.dual.mem_tameSpace.mp hf σ⁻¹ (K.inv_mem hσ)) v` as an intermediate fact. Simplify using `using this`. Simplify using `[this, hc]`.
-/
theorem exists_proj (a : WDRep h V) : ∃ e : End ℂ V, (∀ v, e v ∈ a.tameSpace) ∧
    (∀ v ∈ a.tameSpace, e v = v) ∧
    (∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → e * a.ρ σ = e) ∧
    ∀ f ∈ a.dual.tameSpace, ∀ v, f (e v) = f v := by
  classical
  let K : Subgroup (Weil h) := (Wild E A).subgroupOf (Weil h)
  let P : Subgroup (End ℂ V)ˣ := K.map a.ρ.toHomUnits
  have hfin : Finite P := by
    refine Set.Finite.of_finite_image (f := Units.val) (a.smooth.finite_range.subset ?_)
      Units.val_injective.injOn
    rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨⟨σ, Wild_le_Ine hσ⟩, rfl⟩
  have := Fintype.ofFinite P
  have hc : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card P : ℂ)⁻¹ • ∑ p : P, (p.1 : End ℂ V), fun v => ?_, fun v hv => ?_,
    fun σ hσ => ?_, fun f hf v => ?_⟩
  · refine a.mem_tameSpace.mpr fun σ hσ => ?_
    rw [← End.mul_apply, mul_smul_comm, Finset.mul_sum]
    congr 2
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl
  · have : ∀ p : P, (p.1 : End ℂ V) v = v := by
      rintro ⟨_, σ, hσ, rfl⟩
      exact a.mem_tameSpace.mp hv σ hσ
    simp [this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  · rw [smul_mul_assoc, Finset.sum_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl
  · have : ∀ p : P, f ((p.1 : End ℂ V) v) = f v := by
      rintro ⟨_, σ, hσ, rfl⟩
      have := LinearMap.congr_fun (a.dual.mem_tameSpace.mp hf σ⁻¹ (K.inv_mem hσ)) v
      simpa using this
    simp [this, hc]

/- English proof (translation)
Take `⟨e, h1, h2, h3, h4⟩` from `exists_proj a`. Set `r : a.dual.tameSpace →ₗ[ℂ] Dual ℂ a.tameSpace` to `a.tameSpace.dualRestrict ∘ₗ a.dual.tameSpace.subtype`. Establish `hr : Function.Bijective r`. Use `⟨(injective_iff_map_eq_zero r).mpr fun f hf => ?_, fun φ => ?_⟩` and prove the remaining obligations. Use extensionality with `v`.

Rewrite using `[← h4 f.1 f.2 v]`. Conclude with `LinearMap.congr_fun hf ⟨e v, h1 v⟩`. Use `⟨⟨φ ∘ₗ e.codRestrict _ h1, a.dual.mem_tameSpace.mpr fun u hu => ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Conclude with `congrArg φ (Subtype.ext (LinearMap.congr_fun (h3 u⁻¹ ((Wild E A).inv_mem hu)) v))`.

Use extensionality with `v`. Conclude with `congrArg φ (Subtype.ext (h2 v v.2))`. Rewrite using `[← charpoly_dualMap (a.tamePart.ρ σ⁻¹), ← LinearEquiv.charpoly_conj (LinearEquiv.ofBijective r hr)]`. Use `congr 1`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Take `⟨v, rfl⟩` from `(LinearEquiv.ofBijective r hr).surjective v`. Rewrite using `[LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem charpoly_dual_tamePart (a : WDRep h V) (σ : Weil h) :
    (a.dual.tamePart.ρ σ).charpoly = (a.tamePart.ρ σ⁻¹).charpoly := by
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_proj a
  let r : a.dual.tameSpace →ₗ[ℂ] Dual ℂ a.tameSpace :=
    a.tameSpace.dualRestrict ∘ₗ a.dual.tameSpace.subtype
  have hr : Function.Bijective r := by
    refine ⟨(injective_iff_map_eq_zero r).mpr fun f hf => ?_, fun φ => ?_⟩
    · ext v
      rw [← h4 f.1 f.2 v]
      exact LinearMap.congr_fun hf ⟨e v, h1 v⟩
    · refine ⟨⟨φ ∘ₗ e.codRestrict _ h1, a.dual.mem_tameSpace.mpr fun u hu => ?_⟩, ?_⟩
      · ext v
        exact congrArg φ (Subtype.ext
          (LinearMap.congr_fun (h3 u⁻¹ ((Wild E A).inv_mem hu)) v))
      · ext v
        exact congrArg φ (Subtype.ext (h2 v v.2))
  rw [← charpoly_dualMap (a.tamePart.ρ σ⁻¹),
    ← LinearEquiv.charpoly_conj (LinearEquiv.ofBijective r hr)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := (LinearEquiv.ofBijective r hr).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

/- English proof (translation)
Take `⟨k, hk, -, hk1⟩` from `WD.exists_pow_tameEig x hγ`. Proceed by induction on `x using WD.ind with`. Consider the case `hP m a`. Establish `hγ'` using `Ine_le_Weil h hγ`. Take `⟨n, h0, -, hn⟩` from `a.tame_tamePart.exists_pow_eq_one (γ := ⟨γ, hγ'⟩) hγ`.

Establish `hp : n * k - 1 + 1 = n * k` using `Nat.sub_add_cancel (Nat.mul_pos h0 hk)`. Establish `h1 : a.tamePart.ρ (⟨γ, hγ'⟩ : Weil h)⁻¹ = a.tamePart.ρ ⟨γ, hγ'⟩ ^ (n * k - 1)`. Rewrite using `[← one_mul (a.tamePart.ρ _), ← one_pow k, ← hn, ← pow_mul, ← hp, pow_succ, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, hp]`. Establish `h2` using `GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ _ (n * k - 1) (LinearMap.toMatrix (finBasis ℂ _) (finBasis ℂ _) (a.tamePart.ρ ⟨γ, hγ'⟩))`. Rewrite `h2` using `[LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]`.

Rewrite `hk1` using `[WD.tameEig_mk _ hγ']`. Rewrite using `[WD.lpDual_mk, WD.tameEig_mk _ hγ', WD.tameEig_mk _ hγ', charpoly_dual_tamePart, h1, h2]`. Use `Multiset.map_congr rfl fun z hz => eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← pow_succ, hp, pow_mul', hk1 z hz, one_pow]`.
-/
theorem tameEig_lpDual (x : WD h) {γ : G E Ω} (hγ : γ ∈ Ine (F := E) A) :
    WD.tameEig (WD.lpDual x) γ = (WD.tameEig x γ).map (·⁻¹) := by
  obtain ⟨k, hk, -, hk1⟩ := WD.exists_pow_tameEig x hγ
  induction x using WD.ind with
  | hP m a =>
    have hγ' := Ine_le_Weil h hγ
    obtain ⟨n, h0, -, hn⟩ := a.tame_tamePart.exists_pow_eq_one (γ := ⟨γ, hγ'⟩) hγ
    have hp : n * k - 1 + 1 = n * k := Nat.sub_add_cancel (Nat.mul_pos h0 hk)
    have h1 : a.tamePart.ρ (⟨γ, hγ'⟩ : Weil h)⁻¹ = a.tamePart.ρ ⟨γ, hγ'⟩ ^ (n * k - 1) := by
      rw [← one_mul (a.tamePart.ρ _), ← one_pow k, ← hn, ← pow_mul, ← hp, pow_succ, mul_assoc,
        ← map_mul, mul_inv_cancel, map_one, mul_one, hp]
    have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ _ (n * k - 1)
      (LinearMap.toMatrix (finBasis ℂ _) (finBasis ℂ _) (a.tamePart.ρ ⟨γ, hγ'⟩))
    rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at h2
    rw [WD.tameEig_mk _ hγ'] at hk1
    rw [WD.lpDual_mk, WD.tameEig_mk _ hγ', WD.tameEig_mk _ hγ', charpoly_dual_tamePart, h1, h2]
    refine Multiset.map_congr rfl fun z hz => eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hp, pow_mul', hk1 z hz, one_pow]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h g _ τ γ x`. Distinguish the cases in `H : TeichmullerInertiaLabelCondition A w τ γ`. Use `Multiset.map_injective H.2.2.injective ?_` and prove the remaining obligations. Rewrite using `[WD.map_rootsBar_lab H, tameEig_lpDual x H.2.1, ← WD.map_rootsBar_lab H, Multiset.map_map, Multiset.map_map]`. Use `Multiset.map_congr rfl fun y _ => ?_` and prove the remaining obligations.

Use `show (τ y)⁻¹ = τ y⁻¹`. Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Rewrite using `[inv_zero, H.2.2.map_zero, inv_zero]`. Conclude with `inv_eq_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hy, map_one])`. Simplify using `[WD.lab_of_not H, rootsBar]`.
-/
theorem rootsBar_lab_lpDual : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (τ : Fbar g →* ℂ) (γ : G E Ω), ∀ x : WD h,
    rootsBar (WD.lab τ γ (WD.lpDual x)) = (rootsBar (WD.lab τ γ x)).map (·⁻¹) := by
  intro E Ω _ _ _ _ _ A w h g _ τ γ x
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · refine Multiset.map_injective H.2.2.injective ?_
    rw [WD.map_rootsBar_lab H, tameEig_lpDual x H.2.1, ← WD.map_rootsBar_lab H, Multiset.map_map,
      Multiset.map_map]
    refine Multiset.map_congr rfl fun y _ => ?_
    show (τ y)⁻¹ = τ y⁻¹
    rcases eq_or_ne y 0 with rfl | hy
    · rw [inv_zero, H.2.2.map_zero, inv_zero]
    · exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hy, map_one])
  · simp [WD.lab_of_not H, rootsBar]

end GlobalTheory.WeilDeligne.LabDual
