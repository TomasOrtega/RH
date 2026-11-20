import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourierTransformInvolution
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceEqZeroOfQZ
import GroundTheory.GlobalFields.SUnits

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

def ReflH (hZ : CR Z) (h : Hyp Z) : Sp k n ≃ₜ Sp k n where
  toFun := Refl (Z := Z)
  invFun := Refl (Z := Z)
  left_inv := Refl_Refl hZ h
  right_inv := Refl_Refl hZ h
  continuous_toFun := by
    show Continuous fun p : Sp k n => (p.1 - (2 : k) • Pr Z p.1, p.2)
    exact (continuous_fst.sub (((continuous_Pr Z).comp continuous_fst).const_smul (2 : k))).prodMk continuous_snd
  continuous_invFun := by
    show Continuous fun p : Sp k n => (p.1 - (2 : k) • Pr Z p.1, p.2)
    exact (continuous_fst.sub (((continuous_Pr Z).comp continuous_fst).const_smul (2 : k))).prodMk continuous_snd

/- English proof (translation)
Establish `hsurj : LinearMap.range ((qL Z).domRestrict (BzL Z)) = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `y`. Take `⟨c, hc, rfl⟩` from `PositivityTheory.RgUd.T.Nil.Four.Alg.qZ_surj hZ y`. Conclude with `⟨⟨c, Z_le_Bz Z hZ hc⟩, rfl⟩`.

Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker ((qL Z).domRestrict (BzL Z))`. Rewrite `hrn` using `[hsurj, finrank_top, Module.finrank_fin_fun]`. Establish `hker : LinearMap.ker ((qL Z).domRestrict (BzL Z)) = (B0 Z).comap (BzL Z).subtype`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap, Submodule.subtype_apply, B0, Submodule.mem_inf, x.2, true_and]`.

Establish `e : Module.finrank k (LinearMap.ker ((qL Z).domRestrict (BzL Z))) = Module.finrank k (B0 Z)`. Rewrite using `[hker]`. Conclude with `(Submodule.comapSubtypeEquivOfLe (inf_le_left : B0 Z ≤ BzL Z)).finrank_eq`. Establish `hS : Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = BzL Z`. Use extensionality with `x`.

Rewrite using `[Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]`. Both sides reduce to the same expression. Establish `hC : Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = Module.finrank k (BzL Z)`. Rewrite using `[← Subalgebra.finrank_toSubmodule, hS]`. Use `show Module.finrank k (B0 Z) = Module.finrank k _ - Module.finrank k _`.

Rewrite using `[hC]`. Use linear arithmetic over natural numbers and integers.
-/
theorem d_eq [CharZero k] (hZ : CR Z) : d Z = dB0 Z := by
  classical
  have hsurj : LinearMap.range ((qL Z).domRestrict (BzL Z)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨c, hc, rfl⟩ := PositivityTheory.RgUd.T.Nil.Four.Alg.qZ_surj hZ y
    exact ⟨⟨c, Z_le_Bz Z hZ hc⟩, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker ((qL Z).domRestrict (BzL Z))
  rw [hsurj, finrank_top, Module.finrank_fin_fun] at hrn
  have hker : LinearMap.ker ((qL Z).domRestrict (BzL Z)) = (B0 Z).comap (BzL Z).subtype := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap,
      Submodule.subtype_apply, B0, Submodule.mem_inf, x.2, true_and]
  have e : Module.finrank k (LinearMap.ker ((qL Z).domRestrict (BzL Z))) =
      Module.finrank k (B0 Z) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : B0 Z ≤ BzL Z)).finrank_eq
  have hS : Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) =
      BzL Z := by
    ext x
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    rfl
  have hC : Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) =
      Module.finrank k (BzL Z) := by
    rw [← Subalgebra.finrank_toSubmodule, hS]
  show Module.finrank k (B0 Z) = Module.finrank k _ - Module.finrank k _
  rw [hC]
  omega

/- English proof (translation)
Introduce `n Z hZ`. Use `borelize k`. Establish `h : Hyp Z` using `⟨PositivityTheory.RgUd.T.Nil.Four.Alg.piZ_mem hZ, PositivityTheory.RgUd.T.Nil.Four.Alg.qZ_piZ hZ, fun x c hc hq => PositivityTheory.RgUd.T.Nil.Four.Alg.piZ_eq hZ hc hq, fun w hw hb => PositivityTheory.RgUd.T.Nil.Four.Alg.trB_nondeg hZ hw hb⟩`. Take `⟨ψ, hψ⟩` from `exists_hasConductor_one k`. Set `ν : Measure k` to `Measure.addHaar`.

Establish `hcomp : ∀ (U : Set (Sp k n)) (e : Sp k n ≃ₜ Sp k n), (∀ x, e x ∈ U → x ∈ U) → ∀ f : Sp k n → ℂ, f ∈ supportedIn U → (fun p => f (e p)) ∈ supportedIn U`. Introduce `U e he f hf`. Rewrite `hf`, the goal using `[mem_supportedIn, GroundTheory.Automorphic.mem_locallyConstantCompactSupport]`. Take `⟨⟨hlc, hcs⟩, hsu⟩` from `hf`. Use `⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Conclude with `he x (hsu hx)`. Establish `hU : ∀ (e : Sp k n ≃ₜ Sp k n) (f : Sp k n → ℂ), f ∈ supportedIn (Set.univ : Set (Sp k n)) → (fun p => f (e p)) ∈ supportedIn (Set.univ : Set (Sp k n))` using `fun e => hcomp Set.univ e (fun _ _ => Set.mem_univ _)`. Establish `hRf : ∀ f : Sp k n → ℂ, f ∈ supportedIn (Set.univ : Set (Sp k n)) → (fun p => f (Refl (Z` using `Z) p)) ∈ supportedIn (Set.univ : Set (Sp k n)) := fun f hf => hU (ReflH hZ h) f hf`. Establish `hRU : ∀ f : Sp k n → ℂ, f ∈ supportedIn (UU : Set (Sp k n)) → (fun p => f (Refl (Z` using `Z) p)) ∈ supportedIn (UU : Set (Sp k n)) := fun f hf => hcomp UU (ReflH hZ h) (fun _ hx => hx) f hf`.

Take `⟨q, hq⟩` from `(supportedIn (Set.univ : Set (Sp k n))).exists_isCompl`. Set `Φ : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ` to `(phiS ψ ν hZ h hψ.continuous).comp ((supportedIn (Set.univ : Set (Sp k n))).projectionOnto q hq)`. Establish `hΦ : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ f = phi0 ψ ν hZ h f`. Introduce `f hf`. Establish `e1 : (supportedIn (Set.univ : Set (Sp k n))).projectionOnto q hq f = ⟨f, hf⟩` using `Submodule.linearProjOfIsCompl_apply_left hq ⟨f, hf⟩`.

Simplify using `only [Φ, LinearMap.comp_apply, e1]`. Both sides reduce to the same expression. Set `κ : ℂ` to `(((distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) : ℝ) : ℂ)⁻¹ * (((ν.real (𝒪[k] : Set k) ^ 2 * nabs k 1) ^ d Z : ℝ) : ℂ)`. Establish `hχ : (distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) ≠ 0`. Establish `e2` using `map_mul_eq_one (distribHaarChar k) (mul_inv_cancel (GeneralLinearGroup.det (Gu hZ h)))`.

Conclude with `left_ne_zero_of_mul_eq_one e2`. Establish `hO : IsOpen ((𝒪[k] : Set k))` using `(ValuativeRel.valuation k).isOpen_integer`. Establish `hC : IsCompact ((𝒪[k] : Set k))` using `isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[k])`. Establish `hν : 0 < ν.real (𝒪[k] : Set k)`. Rewrite using `[measureReal_def]`.

Conclude with `ENNReal.toReal_pos (hO.measure_ne_zero ν ⟨0, zero_mem _⟩) hC.measure_lt_top.ne`. Establish `hn1 : nabs k 1 = 1`. Simplify using `[nabs]`. Establish `hκ : κ ≠ 0`. Use `mul_ne_zero (inv_ne_zero ?_) ?_` and prove the remaining obligations.

Conclude with `hχ` after adjusting the coercions. Rewrite using `[hn1, mul_one]`. Conclude with `pow_ne_zero _ (pow_pos hν 2).ne'` after adjusting the coercions. Set `Φ' : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ` to `κ⁻¹ • (Φ.comp (LinearMap.funLeft ℂ ℂ (Refl (Z := Z))))`. Establish `hΦ' : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ' f = κ⁻¹ • phi0 ψ ν hZ h (fun p => f (Refl (Z` using `Z) p)) := by`.

Introduce `f hf`. Use `show κ⁻¹ • Φ (fun p => f (Refl (Z := Z) p)) = _`. Rewrite using `[hΦ _ (hRf f hf)]`. Use `⟨Φ, Φ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf`.

Rewrite using `[hΦ f hf]`. Conclude with `test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hf`. Introduce `f hf`. Rewrite using `[hΦ' f hf]`. Conclude with `Submodule.smul_mem _ _ (test_vector_mem_schwartz_bruhat ψ ν hZ h hψ (hRf f hf))`.

Introduce `f hf y hy p hp`. Rewrite using `[hΦ f hf]`. Conclude with `fourier_transform_vanishes_on_fibre ψ ν hZ h f hy hp`. Introduce `g hg f hf p hp`. Establish `hA : (fun p => f (act g p)) ∈ supportedIn (Set.univ : Set (Sp k n))` using `hU (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g) f hf`.

Rewrite using `[hΦ f hf, hΦ _ hA]`. Conclude with `fourier_transform_equivariant ψ ν hZ h hg f p`. Introduce `f hf`. Establish `hf'` using `supportedIn_mono (Set.subset_univ _) hf`. Rewrite using `[hΦ f hf']`.

Conclude with `fourier_transform_preserves_compact ψ ν hZ h hψ hf`. Introduce `f hf`. Establish `hf'` using `supportedIn_mono (Set.subset_univ _) hf`. Rewrite using `[hΦ' f hf']`. Conclude with `Submodule.smul_mem _ _ (fourier_transform_preserves_compact ψ ν hZ h hψ (hRU f hf))`.

Introduce `f hf p hp`. Establish `hR` using `hRf f hf`. Establish `hm` using `test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hR`. Rewrite using `[hΦ' f hf, map_smul, hΦ _ hm, Pi.smul_apply, fourier_transform_involution ψ ν hZ h hψ hR p, Refl_Refl hZ h, smul_eq_mul, ← mul_assoc]`. Express the relevant statement in the definitionally equal form `κ⁻¹ * κ * f p = f p`.

Rewrite using `[inv_mul_cancel₀ hκ, one_mul]`. Introduce `t f hf p hp`. Establish `hS : (fun p => f (sig Z t⁻¹ p)) ∈ supportedIn (Set.univ : Set (Sp k n))` using `hU (PositivityTheory.RgUd.T.Nil.Four.Alg.sigH hZ t⁻¹) f hf`. Rewrite using `[hΦ f hf, hΦ _ hS, ← d_eq hZ]`. Conclude with `fourier_transform_scaling ψ ν hZ h t f hp`.
-/
theorem phiP [CharZero k] : PhiP (k := k) := by
  intro n Z hZ
  borelize k
  have h : Hyp Z := ⟨PositivityTheory.RgUd.T.Nil.Four.Alg.piZ_mem hZ, PositivityTheory.RgUd.T.Nil.Four.Alg.qZ_piZ hZ,
    fun x c hc hq => PositivityTheory.RgUd.T.Nil.Four.Alg.piZ_eq hZ hc hq,
    fun w hw hb => PositivityTheory.RgUd.T.Nil.Four.Alg.trB_nondeg hZ hw hb⟩
  obtain ⟨ψ, hψ⟩ := exists_hasConductor_one k
  let ν : Measure k := Measure.addHaar
  have hcomp : ∀ (U : Set (Sp k n)) (e : Sp k n ≃ₜ Sp k n), (∀ x, e x ∈ U → x ∈ U) →
      ∀ f : Sp k n → ℂ, f ∈ supportedIn U → (fun p => f (e p)) ∈ supportedIn U := by
    intro U e he f hf
    rw [mem_supportedIn, GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
    obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
    refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
    intro x hx
    exact he x (hsu hx)
  have hU : ∀ (e : Sp k n ≃ₜ Sp k n) (f : Sp k n → ℂ), f ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun p => f (e p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun e => hcomp Set.univ e (fun _ _ => Set.mem_univ _)
  have hRf : ∀ f : Sp k n → ℂ, f ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun p => f (Refl (Z := Z) p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => hU (ReflH hZ h) f hf
  have hRU : ∀ f : Sp k n → ℂ, f ∈ supportedIn (UU : Set (Sp k n)) →
      (fun p => f (Refl (Z := Z) p)) ∈ supportedIn (UU : Set (Sp k n)) :=
    fun f hf => hcomp UU (ReflH hZ h) (fun _ hx => hx) f hf
  obtain ⟨q, hq⟩ := (supportedIn (Set.univ : Set (Sp k n))).exists_isCompl
  let Φ : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ :=
    (phiS ψ ν hZ h hψ.continuous).comp ((supportedIn (Set.univ : Set (Sp k n))).projectionOnto q hq)
  have hΦ : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ f = phi0 ψ ν hZ h f := by
    intro f hf
    have e1 : (supportedIn (Set.univ : Set (Sp k n))).projectionOnto q hq f = ⟨f, hf⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hq ⟨f, hf⟩
    simp only [Φ, LinearMap.comp_apply, e1]
    rfl
  let κ : ℂ := (((distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) : ℝ) : ℂ)⁻¹ *
    (((ν.real (𝒪[k] : Set k) ^ 2 * nabs k 1) ^ d Z : ℝ) : ℂ)
  have hχ : (distribHaarChar k (GeneralLinearGroup.det (Gu hZ h)) : NNReal) ≠ 0 := by
    have e2 := map_mul_eq_one (distribHaarChar k)
      (mul_inv_cancel (GeneralLinearGroup.det (Gu hZ h)))
    exact left_ne_zero_of_mul_eq_one e2
  have hO : IsOpen ((𝒪[k] : Set k)) := (ValuativeRel.valuation k).isOpen_integer
  have hC : IsCompact ((𝒪[k] : Set k)) :=
    isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[k])
  have hν : 0 < ν.real (𝒪[k] : Set k) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hO.measure_ne_zero ν ⟨0, zero_mem _⟩) hC.measure_lt_top.ne
  have hn1 : nabs k 1 = 1 := by
    simp [nabs]
  have hκ : κ ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) ?_
    · exact_mod_cast hχ
    · rw [hn1, mul_one]
      exact_mod_cast pow_ne_zero _ (pow_pos hν 2).ne'
  let Φ' : (Sp k n → ℂ) →ₗ[ℂ] Sp k n → ℂ :=
    κ⁻¹ • (Φ.comp (LinearMap.funLeft ℂ ℂ (Refl (Z := Z))))
  have hΦ' : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
      Φ' f = κ⁻¹ • phi0 ψ ν hZ h (fun p => f (Refl (Z := Z) p)) := by
    intro f hf
    show κ⁻¹ • Φ (fun p => f (Refl (Z := Z) p)) = _
    rw [hΦ _ (hRf f hf)]
  refine ⟨Φ, Φ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [hΦ f hf]
    exact test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hf
  · intro f hf
    rw [hΦ' f hf]
    exact Submodule.smul_mem _ _ (test_vector_mem_schwartz_bruhat ψ ν hZ h hψ (hRf f hf))
  · intro f hf y hy p hp
    rw [hΦ f hf]
    exact fourier_transform_vanishes_on_fibre ψ ν hZ h f hy hp
  · intro g hg f hf p hp
    have hA : (fun p => f (act g p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
      hU (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g) f hf
    rw [hΦ f hf, hΦ _ hA]
    exact fourier_transform_equivariant ψ ν hZ h hg f p
  · intro f hf
    have hf' := supportedIn_mono (Set.subset_univ _) hf
    rw [hΦ f hf']
    exact fourier_transform_preserves_compact ψ ν hZ h hψ hf
  · intro f hf
    have hf' := supportedIn_mono (Set.subset_univ _) hf
    rw [hΦ' f hf']
    exact Submodule.smul_mem _ _ (fourier_transform_preserves_compact ψ ν hZ h hψ (hRU f hf))
  · intro f hf p hp
    have hR := hRf f hf
    have hm := test_vector_mem_schwartz_bruhat ψ ν hZ h hψ hR
    rw [hΦ' f hf, map_smul, hΦ _ hm, Pi.smul_apply, fourier_transform_involution ψ ν hZ h hψ hR p,
      Refl_Refl hZ h, smul_eq_mul, ← mul_assoc]
    change κ⁻¹ * κ * f p = f p
    rw [inv_mul_cancel₀ hκ, one_mul]
  · intro t f hf p hp
    have hS : (fun p => f (sig Z t⁻¹ p)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
      hU (PositivityTheory.RgUd.T.Nil.Four.Alg.sigH hZ t⁻¹) f hf
    rw [hΦ f hf, hΦ _ hS, ← d_eq hZ]
    exact fourier_transform_scaling ψ ν hZ h t f hp

end PositivityTheory.RgUd.T.Nil.Four.Phi2
