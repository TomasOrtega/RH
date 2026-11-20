import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open scoped commutatorElement

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `n hn g`. Establish `hc : ⁅g, n⁆ ∈ H` using `h (by`. Rewrite using `[commutator_def]`. Conclude with `Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))`.

Establish `he : g * n * g⁻¹ = ⁅g, n⁆ * n`. Rewrite using `[commutatorElement_def]`. Use `group`. Rewrite using `[he]`. Conclude with `H.mul_mem hc hn`.
-/
private theorem normal_of_comm {Γ : Type} [Group Γ] (H : Subgroup Γ) (h : commutator Γ ≤ H) : H.Normal := by
  constructor
  intro n hn g
  have hc : ⁅g, n⁆ ∈ H := h (by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
  have he : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]; group
  rw [he]
  exact H.mul_mem hc hn

open Polynomial in
/- English proof (translation)
Use `set p := minpoly ℚ y`. Establish `hint : IsIntegral ℚ y` using `(Algebra.IsAlgebraic.isAlgebraic y).isIntegral`. Establish `hp0 : p ≠ 0` using `minpoly.ne_zero hint`. Use `set w := starRingEnd ℂ (φ y)`. Establish `hw : aeval w p = 0`.

Establish `h1 : aeval (φ.toRatAlgHom y) p = φ.toRatAlgHom (aeval y p)` using `Polynomial.aeval_algHom_apply _ _ _`. Rewrite `h1` using `[minpoly.aeval, map_zero]`. Establish `h2 : aeval ((Complex.conjAe.toAlgHom.restrictScalars ℚ) (φ y)) p = (Complex.conjAe.toAlgHom.restrictScalars ℚ) (aeval (φ y) p)` using `Polynomial.aeval_algHom_apply _ _ _`. Establish `h3 : aeval (φ y) p = 0` using `h1`. Rewrite `h2` using `[h3, map_zero]`.

Conclude with `h2`. Use `set q := p.map (algebraMap ℚ Ω)`. Establish `hq0 : q ≠ 0` using `Polynomial.map_ne_zero hp0`. Establish `hq` using `C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := q))`. Establish `hmap : q.map φ = p.map (algebraMap ℚ ℂ)`.

Rewrite using `[Polynomial.map_map]`. Use `congr 1`. Conclude with `RingHom.ext_rat _ _`. Establish `hev` using `congrArg (fun P => (P.map φ).eval w) hq`. Simplify using `only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X, eval_mul, eval_C, eval_multiset_prod, eval_sub, eval_X] at hev`.

Rewrite `hev` using `[hmap, eval_map, ← aeval_def, hw]`. Establish `hlc : φ q.leadingCoeff ≠ 0` using `(map_ne_zero φ).mpr (leadingCoeff_ne_zero.mpr hq0)`. Establish `hprod` using `(mul_eq_zero.mp hev).resolve_left hlc`. Take `⟨r, -, hr⟩` from `Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)`. Conclude with `⟨r, (sub_eq_zero.mp hr).symm⟩`.
-/
private theorem exists_map_eq_conj_of_isAlgClosed_algebraic {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra.IsAlgebraic ℚ Ω]
    (φ : Ω →+* ℂ) (y : Ω) : ∃ z : Ω, φ z = starRingEnd ℂ (φ y) := by
  set p := minpoly ℚ y
  have hint : IsIntegral ℚ y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  set w := starRingEnd ℂ (φ y)
  have hw : aeval w p = 0 := by
    have h1 : aeval (φ.toRatAlgHom y) p = φ.toRatAlgHom (aeval y p) := Polynomial.aeval_algHom_apply _ _ _
    rw [minpoly.aeval, map_zero] at h1
    have h2 : aeval ((Complex.conjAe.toAlgHom.restrictScalars ℚ) (φ y)) p =
        (Complex.conjAe.toAlgHom.restrictScalars ℚ) (aeval (φ y) p) := Polynomial.aeval_algHom_apply _ _ _
    have h3 : aeval (φ y) p = 0 := h1
    rw [h3, map_zero] at h2
    exact h2
  set q := p.map (algebraMap ℚ Ω)
  have hq0 : q ≠ 0 := Polynomial.map_ne_zero hp0
  have hq := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := q))
  have hmap : q.map φ = p.map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hev := congrArg (fun P => (P.map φ).eval w) hq
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Multiset.map_map,
    Function.comp_def, Polynomial.map_sub, Polynomial.map_X, eval_mul, eval_C, eval_multiset_prod,
    eval_sub, eval_X] at hev
  rw [hmap, eval_map, ← aeval_def, hw] at hev
  have hlc : φ q.leadingCoeff ≠ 0 := (map_ne_zero φ).mpr (leadingCoeff_ne_zero.mpr hq0)
  have hprod := (mul_eq_zero.mp hev).resolve_left hlc
  obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
  exact ⟨r, (sub_eq_zero.mp hr).symm⟩

/- English proof (translation)
Use `choose c0 hc0 using hc`. Establish `inj : Function.Injective φ` using `φ.injective`. Set `cf : Ω →ₐ[F] Ω` to `{ toFun := c0 map_one' := inj (by rw [hc0, map_one, map_one]) map_mul' := fun a b => inj (by rw [hc0, map_mul, map_mul, map_mul, hc0, hc0]) map_zero' := inj (by rw [hc0, map_zero, map_zero]) map_add' := fun a b => inj (by rw [hc0, map_add, map_add, map_add, hc0, hc0]) commutes' : …`. Conclude with `⟨AlgEquiv.ofBijective cf (Algebra.IsAlgebraic.algHom_bijective cf), fun x => hc0 x⟩`.
-/
private theorem exists_algEquiv_map_eq_conj_of_exists_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (φ : Ω →+* ℂ) (hc : ∀ y : Ω, ∃ z : Ω, φ z = starRingEnd ℂ (φ y))
    (hF : ∀ a : F, starRingEnd ℂ (φ (algebraMap F Ω a)) = φ (algebraMap F Ω a)) :
    ∃ c : Ω ≃ₐ[F] Ω, ∀ x, φ (c x) = starRingEnd ℂ (φ x) := by
  choose c0 hc0 using hc
  have inj : Function.Injective φ := φ.injective
  let cf : Ω →ₐ[F] Ω :=
    { toFun := c0
      map_one' := inj (by rw [hc0, map_one, map_one])
      map_mul' := fun a b => inj (by rw [hc0, map_mul, map_mul, map_mul, hc0, hc0])
      map_zero' := inj (by rw [hc0, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [hc0, map_add, map_add, map_add, hc0, hc0])
      commutes' := fun a => inj (by rw [hc0, hF]) }
  exact ⟨AlgEquiv.ofBijective cf (Algebra.IsAlgebraic.algHom_bijective cf), fun x => hc0 x⟩

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ H hH`. Establish `hGE : IsGalois E Ω` using `inferInstance`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Use `haveI : Module.Finite (maximalRealSubfield E) E := Module.Finite.of_restrictScalars_finite ℚ (maximalRealSubfield E) E`.

Use `haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω`. Use `haveI : Algebra.IsAlgebraic (maximalRealSubfield E) Ω := Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω`. Use `haveI : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, inferInstance⟩`. Establish `hGF : IsGalois (maximalRealSubfield E) Ω` using `inferInstance`. Establish `hopen : IsOpen ((H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) : Subgroup (G E Ω)) : Set (G E Ω))` using `hH.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom (maximalRealSubfield E) E Ω)`.

Use `set H' : Subgroup (G E Ω) := H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) with hH'`. Establish `hclosed : IsClosed (H' : Set (G E Ω))` using `Subgroup.isClosed_of_isOpen H' hopen`. Establish `hcomm : commutator (G E Ω) ≤ H'`. Rewrite using `[commutator_def, Subgroup.commutator_le]`. Introduce `a _ b _`.

Rewrite using `[hH', Subgroup.mem_comap, map_commutatorElement]`. Apply `hH.comm` to reduce the goal to its premises. Rewrite using `[commutator_def]`. Conclude with `Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)`. Use `set M : IntermediateField E Ω := IntermediateField.fixedField H'`.

Establish `hfixM : M.fixingSubgroup = H'` using `InfiniteGalois.fixingSubgroup_fixedField ⟨H', hclosed⟩`. Use `haveI hfin : FiniteDimensional E M := (InfiniteGalois.isOpen_iff_finite M).mp (by rw [hfixM]; exact hopen)`. Use `haveI hgal : IsGalois E M := (InfiniteGalois.normal_iff_isGalois M).mp (by rw [hfixM]; exact normal_of_comm H' hcomm)`. Establish `hab : ∀ σ τ : Gal(M/E), σ * τ = τ * σ`. Introduce `σ τ`.

Take `⟨g, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (K₁ := M) Ω σ`. Take `⟨h, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (K₁ := M) Ω τ`. Establish `hk : ⁅g, h⁆ ∈ (AlgEquiv.restrictNormalHom (F` using `E) (K₁ := Ω) M).ker := by`. Rewrite using `[IntermediateField.restrictNormalHom_ker, hfixM]`. Apply `hcomm` to reduce the goal to its premises.

Rewrite using `[commutator_def]`. Conclude with `Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)`. Rewrite `hk` using `[MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]`. Conclude with `hk`. Use `haveI : IsMulCommutative Gal(M/E) := ⟨⟨hab⟩⟩`.

Use `haveI : IsAbelianGalois E M := ⟨⟩`. Use `haveI : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans E M }`. Use `set KF : IntermediateField (maximalRealSubfield E) Ω := IntermediateField.fixedField H`. Establish `hHclosed : IsClosed (H : Set (G (maximalRealSubfield E) Ω))` using `Subgroup.isClosed_of_isOpen H hH.isOpen`. Establish `hfixKF : KF.fixingSubgroup = H` using `InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩`.

Establish `hMeq : M = IntermediateField.adjoin E (KF : Set Ω)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E (KF : Set Ω))]`. Apply `IntermediateField.fixedField_le` to reduce the goal to its premises. Introduce `g hg`.

Rewrite using `[hH', Subgroup.mem_comap, ← hfixKF, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x (IntermediateField.subset_adjoin _ _ hx)`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `x hx`.

Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`. Introduce `g hg`. Conclude with `(IntermediateField.mem_fixedField_iff H x).mp hx _ hg`. Establish `hreal : ∀ x ∈ (KF : Set Ω), ∀ φ : Ω →+* ℂ, (φ x).im = 0`. Introduce `x hx φ`.

Take `⟨c, hc⟩` from `exists_algEquiv_map_eq_conj_of_exists_conj (F := maximalRealSubfield E) φ (exists_map_eq_conj_of_isAlgClosed_algebraic φ) (fun a => (mem_maximalRealSubfield_iff (a : E)).mp a.2 (φ.comp (algebraMap E Ω)))`. Establish `hcH : c ∈ H` using `hH.real φ c hc`. Establish `hcx : c x = x` using `(IntermediateField.mem_fixedField_iff H x).mp hx c hcH`. Rewrite using `[← Complex.conj_eq_iff_im, ← hc, hcx]`. Use `haveI hCM : IsCMField M := (GlobalTheory.CMSub.isCMField_sup_le_adjoin Ω E).2.2 M (KF : Set Ω) hreal hMeq`.

Use `haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) M⟩`. Use `⟨Fld.mk M, ?_⟩` and prove the remaining obligations. Introduce `g`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hg : g ∈ M.fixingSubgroup` using `(IntermediateField.mem_fixingSubgroup_iff _ _).mpr (fun x hx => h ⟨x, hx⟩)`. Rewrite `hg` using `[hfixM]`. Conclude with `hg`. Introduce `h x`. Establish `hg : g ∈ M.fixingSubgroup` using `by rw [hfixM]; exact h`.

Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x.1 x.2`.
-/
theorem exFld : ExFld := by
  intro E Ω _ _ _ _ _ _ H hH
  have hGE : IsGalois E Ω := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Module.Finite (maximalRealSubfield E) E :=
    Module.Finite.of_restrictScalars_finite ℚ (maximalRealSubfield E) E
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : Algebra.IsAlgebraic (maximalRealSubfield E) Ω := Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω
  haveI : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, inferInstance⟩
  have hGF : IsGalois (maximalRealSubfield E) Ω := inferInstance
  have hopen : IsOpen ((H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) : Subgroup (G E Ω)) :
      Set (G E Ω)) :=
    hH.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom (maximalRealSubfield E) E Ω)
  set H' : Subgroup (G E Ω) := H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) with hH'
  have hclosed : IsClosed (H' : Set (G E Ω)) := Subgroup.isClosed_of_isOpen H' hopen
  have hcomm : commutator (G E Ω) ≤ H' := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [hH', Subgroup.mem_comap, map_commutatorElement]
    apply hH.comm
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  set M : IntermediateField E Ω := IntermediateField.fixedField H'
  have hfixM : M.fixingSubgroup = H' := InfiniteGalois.fixingSubgroup_fixedField ⟨H', hclosed⟩
  haveI hfin : FiniteDimensional E M :=
    (InfiniteGalois.isOpen_iff_finite M).mp (by rw [hfixM]; exact hopen)
  haveI hgal : IsGalois E M :=
    (InfiniteGalois.normal_iff_isGalois M).mp (by rw [hfixM]; exact normal_of_comm H' hcomm)
  have hab : ∀ σ τ : Gal(M/E), σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := M) Ω σ
    obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := M) Ω τ
    have hk : ⁅g, h⁆ ∈ (AlgEquiv.restrictNormalHom (F := E) (K₁ := Ω) M).ker := by
      rw [IntermediateField.restrictNormalHom_ker, hfixM]
      apply hcomm
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hk
    exact hk
  haveI : IsMulCommutative Gal(M/E) := ⟨⟨hab⟩⟩
  haveI : IsAbelianGalois E M := ⟨⟩
  haveI : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans E M }
  set KF : IntermediateField (maximalRealSubfield E) Ω := IntermediateField.fixedField H
  have hHclosed : IsClosed (H : Set (G (maximalRealSubfield E) Ω)) := Subgroup.isClosed_of_isOpen H hH.isOpen
  have hfixKF : KF.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hMeq : M = IntermediateField.adjoin E (KF : Set Ω) := by
    apply le_antisymm
    · rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E (KF : Set Ω))]
      apply IntermediateField.fixedField_le
      intro g hg
      rw [hH', Subgroup.mem_comap, ← hfixKF, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x (IntermediateField.subset_adjoin _ _ hx)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (IntermediateField.mem_fixedField_iff H x).mp hx _ hg
  have hreal : ∀ x ∈ (KF : Set Ω), ∀ φ : Ω →+* ℂ, (φ x).im = 0 := by
    intro x hx φ
    obtain ⟨c, hc⟩ := exists_algEquiv_map_eq_conj_of_exists_conj (F := maximalRealSubfield E) φ (exists_map_eq_conj_of_isAlgClosed_algebraic φ) (fun a =>
      (mem_maximalRealSubfield_iff (a : E)).mp a.2 (φ.comp (algebraMap E Ω)))
    have hcH : c ∈ H := hH.real φ c hc
    have hcx : c x = x := (IntermediateField.mem_fixedField_iff H x).mp hx c hcH
    rw [← Complex.conj_eq_iff_im, ← hc, hcx]
  haveI hCM : IsCMField M := (GlobalTheory.CMSub.isCMField_sup_le_adjoin Ω E).2.2 M (KF : Set Ω) hreal hMeq
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) M⟩
  refine ⟨Fld.mk M, ?_⟩
  intro g
  constructor
  · intro h
    have hg : g ∈ M.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mpr (fun x hx => h ⟨x, hx⟩)
    rw [hfixM] at hg
    exact hg
  · intro h x
    have hg : g ∈ M.fixingSubgroup := by rw [hfixM]; exact h
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x.1 x.2

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
