import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree

open Polynomial IsLocalRing NumberField

namespace GlobalTheory.UnramifiedEmbedding

/- English proof (translation)
Take `⟨P⟩ : Nonempty (StandardEtalePresentation R S)` from `inferInstance`. Use `P.hom_ext ?_` and prove the remaining obligations. Establish `h₁ : P.P.HasMap (χ₁ P.x)` using `P.hasMap.map χ₁`. Establish `h₂ : P.P.HasMap (χ₂ P.x)` using `P.hasMap.map χ₂`. Use `set y := χ₁ P.x with hy`.

Use `set d := χ₂ P.x - y with hd`. Establish `hdm : d ∈ maximalIdeal T`. Rewrite using `[← residue_eq_zero_iff, hd, map_sub, hy, h, sub_self]`. Take `⟨k, hk⟩` from `binomExpansion (P.f.map (algebraMap R T)) y d`. Establish `hu : IsUnit (aeval y (derivative P.f))` using `h₁.isUnit_derivative_f`.

Rewrite `hk` using `[show y + d = χ₂ P.x by rw [hd]; ring, eval_map_algebraMap, eval_map_algebraMap, derivative_map, eval_map_algebraMap, h₂.1, h₁.1, zero_add]`. Establish `hu' : IsUnit (aeval y (derivative P.f) + k * d)`. Assume the negation of the conclusion as `hn`. Establish `: aeval y (derivative P.f) + k * d - k * d ∈ maximalIdeal T` using `Ideal.sub_mem _ ((mem_maximalIdeal _).2 hn) (Ideal.mul_mem_left _ _ hdm)`. Rewrite `this` using `[add_sub_cancel_right]`.

Conclude with `(mem_maximalIdeal _).1 this hu`. Establish `h0 : d * (aeval y (derivative P.f) + k * d) = 0`. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Establish `: d = 0` using `(hu'.mul_left_eq_zero).1 h0`.

Rewrite `this` using `[hd, sub_eq_zero]`. Conclude with `this.symm`.
-/
theorem algHom_eq_of_residue_eq {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing T] [Algebra R S] [Algebra R T] [Algebra.IsStandardEtale R S] {χ₁ χ₂ : S →ₐ[R] T}
    (h : ∀ s, residue T (χ₁ s) = residue T (χ₂ s)) : χ₁ = χ₂ := by
  obtain ⟨P⟩ : Nonempty (StandardEtalePresentation R S) := inferInstance
  refine P.hom_ext ?_
  have h₁ : P.P.HasMap (χ₁ P.x) := P.hasMap.map χ₁
  have h₂ : P.P.HasMap (χ₂ P.x) := P.hasMap.map χ₂
  set y := χ₁ P.x with hy
  set d := χ₂ P.x - y with hd
  have hdm : d ∈ maximalIdeal T := by
    rw [← residue_eq_zero_iff, hd, map_sub, hy, h, sub_self]
  obtain ⟨k, hk⟩ := binomExpansion (P.f.map (algebraMap R T)) y d
  have hu : IsUnit (aeval y (derivative P.f)) := h₁.isUnit_derivative_f
  rw [show y + d = χ₂ P.x by rw [hd]; ring, eval_map_algebraMap, eval_map_algebraMap,
    derivative_map, eval_map_algebraMap, h₂.1, h₁.1, zero_add] at hk
  have hu' : IsUnit (aeval y (derivative P.f) + k * d) := by
    by_contra hn
    have : aeval y (derivative P.f) + k * d - k * d ∈ maximalIdeal T :=
      Ideal.sub_mem _ ((mem_maximalIdeal _).2 hn) (Ideal.mul_mem_left _ _ hdm)
    rw [add_sub_cancel_right] at this
    exact (mem_maximalIdeal _).1 this hu
  have h0 : d * (aeval y (derivative P.f) + k * d) = 0 := by
    rw [hk]; ring
  have : d = 0 := (hu'.mul_left_eq_zero).1 h0
  rw [hd, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.UnramifiedEmbedding

namespace GlobalTheory.UnramifiedEmbedding

/- English proof (translation)
Use `letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _`. Use `haveI : IsAlgClosed (O ⧸ maximalIdeal O) := ‹IsAlgClosed (ResidueField O)›`. Use `letI : Field (S ⧸ M) := Ideal.Quotient.field _`. Use `letI := (Ideal.quotientMap M (algebraMap O S) hM.ge).toAlgebra`. Use `⟨RingHom.injective _, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `hs : IsIntegral (O ⧸ maximalIdeal O) (Ideal.Quotient.mk M s)` using `(Algebra.IsIntegral.isIntegral (R := O) s).map_of_comp_eq (Ideal.Quotient.mk _) (Ideal.Quotient.mk M) (Ideal.quotientMap_comp_mk _)`. Conclude with `minpoly.mem_range_of_degree_eq_one _ _ (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hs))`.
-/
theorem quotientMap_bijective {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [Algebra O S] [Algebra.IsIntegral O S] [IsAlgClosed (ResidueField O)] (M : Ideal S)
    [M.IsMaximal] (hM : M.comap (algebraMap O S) = maximalIdeal O) :
    Function.Bijective (Ideal.quotientMap M (algebraMap O S) hM.ge) := by
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  haveI : IsAlgClosed (O ⧸ maximalIdeal O) := ‹IsAlgClosed (ResidueField O)›
  letI : Field (S ⧸ M) := Ideal.Quotient.field _
  letI := (Ideal.quotientMap M (algebraMap O S) hM.ge).toAlgebra
  refine ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hs : IsIntegral (O ⧸ maximalIdeal O) (Ideal.Quotient.mk M s) :=
    (Algebra.IsIntegral.isIntegral (R := O) s).map_of_comp_eq (Ideal.Quotient.mk _)
      (Ideal.Quotient.mk M) (Ideal.quotientMap_comp_mk _)
  exact minpoly.mem_range_of_degree_eq_one _ _
    (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hs))

/- English proof (translation)
Establish `hint : ∀ x : 𝓞 K₀, ∃ o : O, algebraMap O (FractionRing O) o = ι x` using `fun x => IsIntegrallyClosed.isIntegral_iff.1 (x.isIntegral_coe.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _))`. Use `choose g₀ hg₀ using hint`. Establish `hinj` using `IsFractionRing.injective O (FractionRing O)`. Set `ιO : 𝓞 K₀ →+* O` to `{ toFun := g₀ map_one' := hinj (by simp [hg₀]) map_mul' := fun x y => hinj (by simp [hg₀]) map_zero' := hinj (by simp [hg₀]) map_add' := fun x y => hinj (by simp [hg₀]) }`. Establish `hιO : ∀ x, algebraMap O (FractionRing O) (ιO x) = ι x` using `hg₀`.

Use `letI : Algebra (𝓞 K₀) O := ιO.toAlgebra`. Use `letI : Algebra O ℂ := (e.comp (algebraMap O (FractionRing O))).toAlgebra`. Establish `hOC : ∀ o : O, algebraMap O ℂ o = e (algebraMap O (FractionRing O) o)` using `fun _ => rfl`. Set `S` to `integralClosure O ℂ`. Establish `hOS : Function.Injective (algebraMap O S)` using `fun a b h => by`.

Use `congrArg (fun s : S => (s : ℂ)) h` as an intermediate fact. Simplify using `only [Subalgebra.coe_algebraMap, hOC] at this`. Conclude with `hinj (e.injective this)`. Take `⟨M, hMmax, hMc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) (maximalIdeal O) (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hOS]; exact bot_le)`. Set `σA : 𝓞 L →+* S` to `(σ.comp (algebraMap (𝓞 L) L)).codRestrict S fun a => (a.isIntegral_coe.map_of_comp_eq (Int.castRingHom O) σ (RingHom.ext_int _ _) :)`.

Establish `hσA : ∀ a, (σA a : ℂ) = σ a` using `fun _ => rfl`. Establish `hSR : ∀ r : 𝓞 K₀, σA (algebraMap (𝓞 K₀) (𝓞 L) r) = algebraMap O S (ιO r)` using `fun r => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hσA, Subalgebra.coe_algebraMap, hOC, hιO]`. Conclude with `congrArg (fun φ => φ (r : K₀)) hσ`.

Set `P` to `M.comap σA`. Establish `hlP : (l : 𝓞 L) ∈ P` using `by show σA l ∈ M`. Rewrite using `[map_natCast, ← map_natCast (algebraMap O S), ← Ideal.mem_comap, hMc]`. Conclude with `hl`. Use `haveI := hur P hlP`.

Use `haveI : Algebra.FinitePresentation (𝓞 K₀) (𝓞 L) := Algebra.FinitePresentation.of_finiteType.1 inferInstance`. Use `haveI : Module.Flat (𝓞 K₀) (𝓞 L) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 (by`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨⟨r, hr⟩, hrx⟩` from `hx`.

Establish `hr0 : r ≠ 0` using `nonZeroDivisors.ne_zero hr`. Establish `: algebraMap (𝓞 K₀) (𝓞 L) r * x = 0` using `by rw [← Algebra.smul_def]; exact hrx`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd ((FaithfulSMul.algebraMap_injective _ _) (h.trans (map_zero _).symm)) hr0`. Conclude with `h)`.

Take `⟨f, hfP, hfU⟩` from `Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := 𝓞 K₀) P`. Use `haveI : Algebra.FinitePresentation (𝓞 K₀) (Localization.Away f) := .trans _ (𝓞 L) _`. Use `haveI : Module.Flat (𝓞 K₀) (Localization.Away f) := .trans _ (𝓞 L) _`. Use `haveI : Algebra.Etale (𝓞 K₀) (Localization.Away f) := Algebra.Etale.of_formallyUnramified_of_flat`. Use `haveI : Algebra.IsEtaleAt (𝓞 K₀) P := Algebra.basicOpen_subset_etaleLocus_iff_etale.2 this (show (⟨P, inferInstance⟩ : PrimeSpectrum (𝓞 L)) ∈ PrimeSpectrum.basicOpen f from hfP)`.

Take `⟨g, hgP, hgE⟩` from `Algebra.IsEtaleAt.exists_isStandardEtale (R := 𝓞 K₀) P`. Use `letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _`. Set `q` to `Ideal.quotientMap M (algebraMap O S) hMc.ge`. Establish `hq` using `quotientMap_bijective M hMc`. Set `qe` to `RingEquiv.ofBijective q hq`.

Set `φ₀ : 𝓞 L →+* O ⧸ maximalIdeal O` to `qe.symm.toRingHom.comp ((Ideal.Quotient.mk M).comp σA)`. Establish `hφ₀ : ∀ a, q (φ₀ a) = Ideal.Quotient.mk M (σA a)` using `fun a => qe.apply_symm_apply _`. Establish `hφg : IsUnit (φ₀ g)`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Apply `hgP` to reduce the goal to its premises. Use `show σA g ∈ M`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← hφ₀, h0, map_zero]`. Set `φr : Localization.Away g →+* O ⧸ maximalIdeal O` to `IsLocalization.Away.lift g hφg`. Establish `hφr : ∀ a, φr (algebraMap _ _ a) = φ₀ a` using `fun a => IsLocalization.lift_eq _ _`.

Set `φ : Localization.Away g →ₐ[𝓞 K₀] O ⧸ maximalIdeal O` to `{ φr with commutes' := fun r => by`. Express the relevant statement in the definitionally equal form `φr (algebraMap (𝓞 K₀) (Localization.Away g) r) = _`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K₀) (𝓞 L) (Localization.Away g), hφr]`. Apply `hq.1` to reduce the goal to its premises. Rewrite using `[hφ₀, hSR]`.

Use `rfl }`. Use `haveI := hgE`. Take `⟨ψ, hψ⟩` from `GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal O) (Ideal.Quotient.mkₐ (𝓞 K₀) (maximalIdeal O)) Ideal.Quotient.mk_surjective (fun b => Ideal.Quotient.eq_zero_iff_mem.symm) φ`. Use `haveI := hMmax`. Set `T` to `Localization.AtPrime M`.

Use `letI : Algebra (𝓞 K₀) T := ((algebraMap S T).comp ((algebraMap O S).comp ιO)).toAlgebra`. Establish `hgT : IsUnit ((algebraMap S T).comp σA g)` using `(IsLocalization.AtPrime.isUnit_to_map_iff T M (σA g)).2 hgP`. Set `χ₂r : Localization.Away g →+* T` to `IsLocalization.Away.lift g hgT`. Establish `hχ₂r : ∀ a, χ₂r (algebraMap _ _ a) = algebraMap S T (σA a)` using `fun a => IsLocalization.lift_eq _ _`. Set `χ₁ : Localization.Away g →ₐ[𝓞 K₀] T` to `{ (algebraMap S T).comp ((algebraMap O S).comp ψ.toRingHom) with commutes' := fun r => by`.

Express the relevant statement in the definitionally equal form `algebraMap S T (algebraMap O S (ψ (algebraMap _ _ r))) = _`. Rewrite using `[ψ.commutes]`. Use `rfl }`. Set `χ₂ : Localization.Away g →ₐ[𝓞 K₀] T` to `{ χ₂r with commutes' := fun r => by`. Express the relevant statement in the definitionally equal form `χ₂r (algebraMap (𝓞 K₀) (Localization.Away g) r) = _`.

Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K₀) (𝓞 L) (Localization.Away g), hχ₂r, hSR]`. Use `rfl }`. Establish `hres : ∀ a : 𝓞 L, algebraMap O S (ψ (algebraMap _ (Localization.Away g) a)) - σA a ∈ M`. Introduce `a`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]`.

Establish `h1` using `congrArg (fun φ' : Localization.Away g →ₐ[𝓞 K₀] _ => φ' (algebraMap _ _ a)) hψ`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1`. Express the relevant statement in the definitionally equal form `q (Ideal.Quotient.mk _ (ψ _)) = _`. Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `q (φr _) = _`.

Rewrite using `[hφr, hφ₀]`. Establish `hχ : χ₁ = χ₂` using `algHom_eq_of_residue_eq (fun s => by`. Establish `: (residue T).comp χ₁.toRingHom = (residue T).comp χ₂.toRingHom`. Use `IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Express the relevant statement in the definitionally equal form `algebraMap S T _ - χ₂r (algebraMap _ _ a) ∈ _`. Rewrite using `[hχ₂r, ← map_sub]`. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff T M _).2 (hres a)`. Conclude with `congrArg (fun j => j s) this)`.

Establish `hA : ∀ a : 𝓞 L, σ a = e (algebraMap O (FractionRing O) (ψ (algebraMap _ (Localization.Away g) a)))`. Introduce `a`. Establish `h` using `congrArg (fun χ : Localization.Away g →ₐ[𝓞 K₀] T => χ (algebraMap _ _ a)) hχ`. Express the relevant statement in the definitionally equal form `algebraMap S T _ = χ₂r _ at h`. Rewrite `h` using `[hχ₂r]`.

Establish `h'` using `IsLocalization.injective T M.primeCompl_le_nonZeroDivisors h`. Establish `h''` using `congrArg (fun s : S => (s : ℂ)) h'`. Simplify using `only [Subalgebra.coe_algebraMap, hOC, hσA] at h''`. Conclude with `h''.symm`. Introduce and unpack `_ ⟨y, rfl⟩`.

Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 L) y`. Use `⟨algebraMap O _ (ψ (algebraMap _ (Localization.Away g) a)) / algebraMap O _ (ψ (algebraMap _ (Localization.Away g) b)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_div₀, ← hA, ← hA]`.
-/
theorem range_le_range_of_isUnramifiedAt
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [IsAlgClosed (ResidueField O)]
    (l : ℕ) [Fact l.Prime] (hl : (l : O) ∈ maximalIdeal O)
    (e : FractionRing O →+* ℂ)
    (K₀ L : Type) [Field K₀] [NumberField K₀] [Field L] [NumberField L] [Algebra K₀ L]
    (ι : K₀ →+* FractionRing O) (σ : L →+* ℂ) (hσ : σ.comp (algebraMap K₀ L) = e.comp ι)
    (hur : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (l : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 K₀) P) :
    σ.range ≤ e.range := by
  classical
  have hint : ∀ x : 𝓞 K₀, ∃ o : O, algebraMap O (FractionRing O) o = ι x := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1
      (x.isIntegral_coe.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _))
  choose g₀ hg₀ using hint
  have hinj := IsFractionRing.injective O (FractionRing O)
  let ιO : 𝓞 K₀ →+* O :=
    { toFun := g₀
      map_one' := hinj (by simp [hg₀])
      map_mul' := fun x y => hinj (by simp [hg₀])
      map_zero' := hinj (by simp [hg₀])
      map_add' := fun x y => hinj (by simp [hg₀]) }
  have hιO : ∀ x, algebraMap O (FractionRing O) (ιO x) = ι x := hg₀
  letI : Algebra (𝓞 K₀) O := ιO.toAlgebra
  letI : Algebra O ℂ := (e.comp (algebraMap O (FractionRing O))).toAlgebra
  have hOC : ∀ o : O, algebraMap O ℂ o = e (algebraMap O (FractionRing O) o) := fun _ => rfl
  let S := integralClosure O ℂ
  have hOS : Function.Injective (algebraMap O S) := fun a b h => by
    have := congrArg (fun s : S => (s : ℂ)) h
    simp only [Subalgebra.coe_algebraMap, hOC] at this
    exact hinj (e.injective this)
  obtain ⟨M, hMmax, hMc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) (maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hOS]; exact bot_le)
  let σA : 𝓞 L →+* S := (σ.comp (algebraMap (𝓞 L) L)).codRestrict S fun a =>
    (a.isIntegral_coe.map_of_comp_eq (Int.castRingHom O) σ (RingHom.ext_int _ _) :)
  have hσA : ∀ a, (σA a : ℂ) = σ a := fun _ => rfl
  have hSR : ∀ r : 𝓞 K₀, σA (algebraMap (𝓞 K₀) (𝓞 L) r) = algebraMap O S (ιO r) := fun r => by
    apply Subtype.ext
    rw [hσA, Subalgebra.coe_algebraMap, hOC, hιO]
    exact congrArg (fun φ => φ (r : K₀)) hσ
  let P := M.comap σA
  have hlP : (l : 𝓞 L) ∈ P := by
    show σA l ∈ M
    rw [map_natCast, ← map_natCast (algebraMap O S), ← Ideal.mem_comap, hMc]
    exact hl
  haveI := hur P hlP
  haveI : Algebra.FinitePresentation (𝓞 K₀) (𝓞 L) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Module.Flat (𝓞 K₀) (𝓞 L) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 (by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨r, hr⟩, hrx⟩ := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have : algebraMap (𝓞 K₀) (𝓞 L) r * x = 0 := by rw [← Algebra.smul_def]; exact hrx
    rcases mul_eq_zero.1 this with h | h
    · exact absurd ((FaithfulSMul.algebraMap_injective _ _) (h.trans (map_zero _).symm)) hr0
    · exact h)
  obtain ⟨f, hfP, hfU⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := 𝓞 K₀) P
  haveI : Algebra.FinitePresentation (𝓞 K₀) (Localization.Away f) :=
    .trans _ (𝓞 L) _
  haveI : Module.Flat (𝓞 K₀) (Localization.Away f) := .trans _ (𝓞 L) _
  haveI : Algebra.Etale (𝓞 K₀) (Localization.Away f) := Algebra.Etale.of_formallyUnramified_of_flat
  haveI : Algebra.IsEtaleAt (𝓞 K₀) P :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.2 this
      (show (⟨P, inferInstance⟩ : PrimeSpectrum (𝓞 L)) ∈ PrimeSpectrum.basicOpen f from hfP)
  obtain ⟨g, hgP, hgE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := 𝓞 K₀) P
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  let q := Ideal.quotientMap M (algebraMap O S) hMc.ge
  have hq := quotientMap_bijective M hMc
  let qe := RingEquiv.ofBijective q hq
  let φ₀ : 𝓞 L →+* O ⧸ maximalIdeal O := qe.symm.toRingHom.comp ((Ideal.Quotient.mk M).comp σA)
  have hφ₀ : ∀ a, q (φ₀ a) = Ideal.Quotient.mk M (σA a) := fun a => qe.apply_symm_apply _
  have hφg : IsUnit (φ₀ g) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hgP
    show σA g ∈ M
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφ₀, h0, map_zero]
  let φr : Localization.Away g →+* O ⧸ maximalIdeal O := IsLocalization.Away.lift g hφg
  have hφr : ∀ a, φr (algebraMap _ _ a) = φ₀ a := fun a => IsLocalization.lift_eq _ _
  let φ : Localization.Away g →ₐ[𝓞 K₀] O ⧸ maximalIdeal O :=
    { φr with
      commutes' := fun r => by
        change φr (algebraMap (𝓞 K₀) (Localization.Away g) r) = _
        rw [IsScalarTower.algebraMap_apply (𝓞 K₀) (𝓞 L) (Localization.Away g), hφr]
        apply hq.1
        rw [hφ₀, hSR]
        rfl }
  haveI := hgE
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal O)
    (Ideal.Quotient.mkₐ (𝓞 K₀) (maximalIdeal O)) Ideal.Quotient.mk_surjective
    (fun b => Ideal.Quotient.eq_zero_iff_mem.symm) φ
  haveI := hMmax
  let T := Localization.AtPrime M
  letI : Algebra (𝓞 K₀) T := ((algebraMap S T).comp ((algebraMap O S).comp ιO)).toAlgebra
  have hgT : IsUnit ((algebraMap S T).comp σA g) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff T M (σA g)).2 hgP
  let χ₂r : Localization.Away g →+* T := IsLocalization.Away.lift g hgT
  have hχ₂r : ∀ a, χ₂r (algebraMap _ _ a) = algebraMap S T (σA a) := fun a =>
    IsLocalization.lift_eq _ _
  let χ₁ : Localization.Away g →ₐ[𝓞 K₀] T :=
    { (algebraMap S T).comp ((algebraMap O S).comp ψ.toRingHom) with
      commutes' := fun r => by
        change algebraMap S T (algebraMap O S (ψ (algebraMap _ _ r))) = _
        rw [ψ.commutes]; rfl }
  let χ₂ : Localization.Away g →ₐ[𝓞 K₀] T :=
    { χ₂r with
      commutes' := fun r => by
        change χ₂r (algebraMap (𝓞 K₀) (Localization.Away g) r) = _
        rw [IsScalarTower.algebraMap_apply (𝓞 K₀) (𝓞 L) (Localization.Away g), hχ₂r, hSR]
        rfl }
  have hres : ∀ a : 𝓞 L,
      algebraMap O S (ψ (algebraMap _ (Localization.Away g) a)) - σA a ∈ M := by
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    have h1 := congrArg (fun φ' : Localization.Away g →ₐ[𝓞 K₀] _ => φ' (algebraMap _ _ a)) hψ
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1
    change q (Ideal.Quotient.mk _ (ψ _)) = _
    rw [h1]
    change q (φr _) = _
    rw [hφr, hφ₀]
  have hχ : χ₁ = χ₂ := algHom_eq_of_residue_eq (fun s => by
    have : (residue T).comp χ₁.toRingHom = (residue T).comp χ₂.toRingHom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply]
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      change algebraMap S T _ - χ₂r (algebraMap _ _ a) ∈ _
      rw [hχ₂r, ← map_sub]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T M _).2 (hres a)
    exact congrArg (fun j => j s) this)
  have hA : ∀ a : 𝓞 L,
      σ a = e (algebraMap O (FractionRing O) (ψ (algebraMap _ (Localization.Away g) a))) := by
    intro a
    have h := congrArg (fun χ : Localization.Away g →ₐ[𝓞 K₀] T => χ (algebraMap _ _ a)) hχ
    change algebraMap S T _ = χ₂r _ at h
    rw [hχ₂r] at h
    have h' := IsLocalization.injective T M.primeCompl_le_nonZeroDivisors h
    have h'' := congrArg (fun s : S => (s : ℂ)) h'
    simp only [Subalgebra.coe_algebraMap, hOC, hσA] at h''
    exact h''.symm
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
  refine ⟨algebraMap O _ (ψ (algebraMap _ (Localization.Away g) a)) /
    algebraMap O _ (ψ (algebraMap _ (Localization.Away g) b)), ?_⟩
  rw [map_div₀, map_div₀, ← hA, ← hA]

end GlobalTheory.UnramifiedEmbedding
