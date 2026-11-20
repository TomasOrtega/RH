import Development.EtaleCohomology.EtaleSheaves.EtAICPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.DomOpenPf

/- English proof (translation)
Apply `IsAlgClosed.of_exists_root` to reduce the goal to its premises. Introduce `p hp hirr`. Use `set K := FractionRing T`. Use `set f := algebraMap T K`. Establish `hf : Function.Injective f` using `IsFractionRing.injective T K`.

Take `⟨b, hb₁, hb₂⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors T) p`. Use `set q := IsLocalization.integerNormalization (nonZeroDivisors T) p`. Establish `hb0 : (b : T) ≠ 0` using `nonZeroDivisors.ne_zero hb₁`. Establish `hdeg : q.natDegree = p.natDegree`. Rewrite using `[← natDegree_map_eq_of_injective hf q, hb₂, ← IsScalarTower.algebraMap_smul K b p, natDegree_smul_of_smul_regular]`.

Conclude with `IsSMulRegular.of_ne_zero (by simpa [f] using (map_ne_zero_iff f hf).mpr hb0)`. Establish `hpos : 0 < p.natDegree` using `Irreducible.natDegree_pos hirr`. Establish `hq0 : q ≠ 0` using `by intro h; rw [h] at hdeg; simp at hdeg; omega`. Take `⟨a, ha⟩` from `hT (integralNormalization q) (monic_integralNormalization hq0) (by rw [natDegree_integralNormalization]; omega)`. Establish `hlc : f q.leadingCoeff ≠ 0` using `(map_ne_zero_iff f hf).mpr (leadingCoeff_ne_zero.mpr hq0)`.

Use `⟨f a / f q.leadingCoeff, ?_⟩` and prove the remaining obligations. Establish `key` using `integralNormalization_eval₂_leadingCoeff_mul (p := q) (by omega) f (f a / f q.leadingCoeff)`. Rewrite `key` using `[mul_div_cancel₀ _ hlc, eval₂_at_apply, ha, map_zero]`. Establish `h2 : q.eval₂ f (f a / f q.leadingCoeff) = 0`. Break down `mul_eq_zero.mp key.symm with h | h` into its components or cases.

Conclude with `absurd (pow_eq_zero_iff'.mp h).1 hlc`. Conclude with `h`. Rewrite `h2` using `[eval₂_eq_eval_map, hb₂, ← IsScalarTower.algebraMap_smul K b p, eval_smul, smul_eq_mul]`. Conclude with `(mul_eq_zero.mp h2).resolve_left ((map_ne_zero_iff f hf).mpr hb0)`.
-/
theorem algClosed_of_AIC (T : Type) [CommRing T] [IsDomain T] (hT : AIC T) :
    IsAlgClosed (FractionRing T) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  set K := FractionRing T
  set f := algebraMap T K
  have hf : Function.Injective f := IsFractionRing.injective T K
  obtain ⟨b, hb₁, hb₂⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  have hb0 : (b : T) ≠ 0 := nonZeroDivisors.ne_zero hb₁
  have hdeg : q.natDegree = p.natDegree := by
    rw [← natDegree_map_eq_of_injective hf q, hb₂, ← IsScalarTower.algebraMap_smul K b p,
      natDegree_smul_of_smul_regular]
    exact IsSMulRegular.of_ne_zero (by simpa [f] using (map_ne_zero_iff f hf).mpr hb0)
  have hpos : 0 < p.natDegree := Irreducible.natDegree_pos hirr
  have hq0 : q ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg; omega
  obtain ⟨a, ha⟩ := hT (integralNormalization q) (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  have hlc : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hf).mpr (leadingCoeff_ne_zero.mpr hq0)
  refine ⟨f a / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (p := q) (by omega) f (f a / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hlc, eval₂_at_apply, ha, map_zero] at key
  have h2 : q.eval₂ f (f a / f q.leadingCoeff) = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hlc
    · exact h
  rw [eval₂_eq_eval_map, hb₂, ← IsScalarTower.algebraMap_smul K b p, eval_smul, smul_eq_mul] at h2
  exact (mul_eq_zero.mp h2).resolve_left ((map_ne_zero_iff f hf).mpr hb0)

/- English proof (translation)
Introduce `h`. Establish `hr : IsSMulRegular D s` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)`. Apply `one_ne_zero (α := D)` to reduce the goal to its premises. Apply `hr` to reduce the goal to its premises. Simplify using `[Algebra.smul_def, h]`.
-/
theorem algebraMap_ne_zero_of_flat (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [Nontrivial D]
    [Algebra T D] [Module.Flat T D] {s : T} (hs : s ≠ 0) : algebraMap T D s ≠ 0 := by
  intro h
  have hr : IsSMulRegular D s := Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  apply one_ne_zero (α := D)
  apply hr
  simp [Algebra.smul_def, h]

/- English proof (translation)
Use `haveI := algClosed_of_AIC T hT`. Set `M` to `nonZeroDivisors T`. Set `S` to `Localization (Algebra.algebraMapSubmonoid D M)`. Establish `hle : Algebra.algebraMapSubmonoid D M ≤ nonZeroDivisors D`. Introduce and unpack `_ ⟨s, hs, rfl⟩`.

Conclude with `mem_nonZeroDivisors_of_ne_zero (algebraMap_ne_zero_of_flat T D (nonZeroDivisors.ne_zero hs))`. Establish `: IsDomain S` using `IsLocalization.isDomain_localization hle`. Establish `: IsLocalization (M.map (algebraMap T D)) S` using `inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid D M) S)`. Establish `: Algebra.FormallyEtale (FractionRing T) S` using `Algebra.FormallyEtale.localization_map M (Rₘ := FractionRing T) (Sₘ := S) (S := D)`. Establish `: Algebra.EssFiniteType (FractionRing T) S` using `Algebra.EssFiniteType.of_comp T (FractionRing T) S`.

Set `e` to `Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) S`. Establish `hsub : Subsingleton (PrimeSpectrum S)`. Prove the components needed by the constructor for the conclusion. Introduce `p q`. Assume the negation of the conclusion as `hpq`.

Establish `h0 : ((fun r => if r = p then (1 : FractionRing T) else 0) * fun r => if r = q then 1 else 0) = 0`. Apply the tactic sequence `funext r; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs with h1 h2 <;> simp_all`. Establish `: e.symm (fun r => if r = p then (1 : FractionRing T) else 0) * e.symm (fun r => if r = q then 1 else 0) = 0` using `by rw [← map_mul, h0, map_zero]`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Use `congrFun (e.symm.injective (h.trans (map_zero _).symm)) p` as an intermediate fact.

Simplify using `at this`. Use `congrFun (e.symm.injective (h.trans (map_zero _).symm)) q` as an intermediate fact. Simplify using `at this`. Take `⟨p₀⟩ : Nonempty (PrimeSpectrum S)` from `inferInstance`. Use `set x := algebraMap D S a`.

Establish `hx : algebraMap (FractionRing T) S (e x p₀) = x`. Apply `e.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Rewrite using `[AlgEquiv.commutes]`. Simplify using `[Subsingleton.elim p p₀]`.

Generalize the expression as in `e x p₀ = c at hx`. Take `⟨⟨t, s⟩, hts⟩` from `IsLocalization.mk'_surjective M c`. Express the relevant statement in the definitionally equal form `IsLocalization.mk' (FractionRing T) t s = c at hts`. Use `⟨s, t, nonZeroDivisors.ne_zero s.2, ?_⟩` and prove the remaining obligations. Apply `IsLocalization.injective S hle` to reduce the goal to its premises.

Rewrite using `[map_mul, ← IsScalarTower.algebraMap_apply T D S, ← IsScalarTower.algebraMap_apply T D S, show algebraMap D S a = x from rfl, ← hx, ← hts, IsScalarTower.algebraMap_apply T (FractionRing T) S (s : T), IsScalarTower.algebraMap_apply T (FractionRing T) S t, ← map_mul, mul_comm, IsLo …`.
-/
theorem exists_frac (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) (a : D) :
    ∃ s t : T, s ≠ 0 ∧ algebraMap T D s * a = algebraMap T D t := by
  classical
  haveI := algClosed_of_AIC T hT
  let M := nonZeroDivisors T
  let S := Localization (Algebra.algebraMapSubmonoid D M)
  have hle : Algebra.algebraMapSubmonoid D M ≤ nonZeroDivisors D := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (algebraMap_ne_zero_of_flat T D (nonZeroDivisors.ne_zero hs))
  have : IsDomain S := IsLocalization.isDomain_localization hle
  have : IsLocalization (M.map (algebraMap T D)) S := inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid D M) S)
  have : Algebra.FormallyEtale (FractionRing T) S :=
    Algebra.FormallyEtale.localization_map M (Rₘ := FractionRing T) (Sₘ := S) (S := D)
  have : Algebra.EssFiniteType (FractionRing T) S := Algebra.EssFiniteType.of_comp T (FractionRing T) S
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) S
  have hsub : Subsingleton (PrimeSpectrum S) := by
    constructor
    intro p q
    by_contra hpq
    have h0 : ((fun r => if r = p then (1 : FractionRing T) else 0) * fun r => if r = q then 1 else 0) = 0 := by
      funext r; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs with h1 h2 <;> simp_all
    have : e.symm (fun r => if r = p then (1 : FractionRing T) else 0) * e.symm (fun r => if r = q then 1 else 0) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp this with h | h
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) p
      simp at this
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) q
      simp at this
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum S) := inferInstance
  set x := algebraMap D S a
  have hx : algebraMap (FractionRing T) S (e x p₀) = x := by
    apply e.injective
    funext p
    rw [AlgEquiv.commutes]
    simp [Subsingleton.elim p p₀]
  generalize e x p₀ = c at hx
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective M c
  change IsLocalization.mk' (FractionRing T) t s = c at hts
  refine ⟨s, t, nonZeroDivisors.ne_zero s.2, ?_⟩
  apply IsLocalization.injective S hle
  rw [map_mul, ← IsScalarTower.algebraMap_apply T D S, ← IsScalarTower.algebraMap_apply T D S,
    show algebraMap D S a = x from rfl, ← hx, ← hts,
    IsScalarTower.algebraMap_apply T (FractionRing T) S (s : T), IsScalarTower.algebraMap_apply T (FractionRing T) S t,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

/- English proof (translation)
Rewrite using `[Algebra.isEpi_iff_forall_one_tmul_eq]`. Introduce `a`. Take `⟨s, t, hs, hst⟩` from `exists_frac T D hT a`. Establish `hr : IsSMulRegular (TensorProduct T D D) s` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)`. Rewrite using `[← sub_eq_zero]`.

Apply `hr` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `s • (1 ⊗ₜ[T] a - a ⊗ₜ[T] 1) = s • (0 : TensorProduct T D D)`. Establish `hsa : s • a = t • (1 : D)` using `by rw [Algebra.smul_def, hst, Algebra.smul_def, mul_one]`. Establish `e1 : s • ((1 : D) ⊗ₜ[T] a) = t • ((1 : D) ⊗ₜ[T] (1 : D))`. Rewrite using `[← TensorProduct.tmul_smul, hsa, TensorProduct.tmul_smul]`.

Establish `e2 : s • (a ⊗ₜ[T] (1 : D)) = t • ((1 : D) ⊗ₜ[T] (1 : D))`. Rewrite using `[TensorProduct.smul_tmul', hsa, ← TensorProduct.smul_tmul']`. Rewrite using `[smul_zero, smul_sub, e1, e2, sub_self]`.
-/
theorem isEpi (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) : Algebra.IsEpi T D := by
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro a
  obtain ⟨s, t, hs, hst⟩ := exists_frac T D hT a
  have hr : IsSMulRegular (TensorProduct T D D) s :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  rw [← sub_eq_zero]
  apply hr
  change s • (1 ⊗ₜ[T] a - a ⊗ₜ[T] 1) = s • (0 : TensorProduct T D D)
  have hsa : s • a = t • (1 : D) := by rw [Algebra.smul_def, hst, Algebra.smul_def, mul_one]
  have e1 : s • ((1 : D) ⊗ₜ[T] a) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [← TensorProduct.tmul_smul, hsa, TensorProduct.tmul_smul]
  have e2 : s • (a ⊗ₜ[T] (1 : D)) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [TensorProduct.smul_tmul', hsa, ← TensorProduct.smul_tmul']
  rw [smul_zero, smul_sub, e1, e2, sub_self]

/- English proof (translation)
Introduce `T D _ _ _ _ _ _ hT`. Use `set f := CommRingCat.ofHom (algebraMap T D)`. Establish `: Algebra.IsEpi T D` using `isEpi T D hT`. Establish `: Epi f` using `CommRingCat.epi_iff_epi.mpr inferInstance`. Establish `: Mono (Spec.map f)` using `inferInstanceAs (Mono (Scheme.Spec.map f.op))`.

Establish `: Flat (Spec.map f)` using `Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)`. Establish `: LocallyOfFinitePresentation (Spec.map f)` using `(LocallyOfFinitePresentation.SpecMap_iff f).mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)`. Conclude with `IsOpenImmersion.of_flat_of_mono _`.
-/
theorem DomOpen_of : LateralTheory.E.EtAICPf.DomOpen := by
  intro T D _ _ _ _ _ _ hT
  set f := CommRingCat.ofHom (algebraMap T D)
  have : Algebra.IsEpi T D := isEpi T D hT
  have : Epi f := CommRingCat.epi_iff_epi.mpr inferInstance
  have : Mono (Spec.map f) := inferInstanceAs (Mono (Scheme.Spec.map f.op))
  have : Flat (Spec.map f) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map f) :=
    (LocallyOfFinitePresentation.SpecMap_iff f).mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact IsOpenImmersion.of_flat_of_mono _

end LateralTheory.E.DomOpenPf
