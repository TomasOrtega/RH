import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.AcycResLevel

/- English proof (translation)
Set `I` to `injectiveResolution F`. Set `e0 : (res R F).X 0 ≅ I.cocomplex.X 0` to `I.cochainComplexXIso 0 0 rfl`. Set `e1 : (res R F).X 1 ≅ I.cocomplex.X 1` to `I.cochainComplexXIso 1 1 rfl`. Establish `hd : (res R F).d 0 1 = e0.hom ≫ I.cocomplex.d 0 1 ≫ e1.inv` using `I.cochainComplex_d 0 1 0 1 rfl rfl`. Establish `hψ : (φ ≫ e0.hom) ≫ I.cocomplex.d 0 1 = 0`.

Rewrite using `[← cancel_mono e1.inv, zero_comp]`. Rewrite `hφ` using `[hd]`. Simplify `hφ` using `only [Category.assoc]`. Take `⟨l, hl⟩` from `KernelFork.IsLimit.lift' I.isLimitKernelFork (φ ≫ e0.hom) hψ`. Set `l' : W ⟶ F` to `l`.

Use `⟨l', ?_⟩` and prove the remaining obligations. Set `ι0 : F ⟶ I.cocomplex.X 0` to `I.ι.f 0`. Establish `h1 : resι R F = ι0 ≫ e0.inv`. Express the relevant statement in the definitionally equal form `(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ I.ι'.f 0 = _`. Rewrite using `[InjectiveResolution.ι'_f_zero]`.

Simplify using `[e0, ι0]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Establish `h2 : l' ≫ ι0 = φ ≫ e0.hom` using `hl`. Rewrite using `[← Category.assoc, h2, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.
-/
theorem res_lift {R : Type} [CommRing R] (F : Shv R) {W : Shv R} (φ : W ⟶ (res R F).X 0)
    (hφ : φ ≫ (res R F).d 0 1 = 0) : ∃ g : W ⟶ F, g ≫ resι R F = φ := by
  let I := injectiveResolution F
  let e0 : (res R F).X 0 ≅ I.cocomplex.X 0 := I.cochainComplexXIso 0 0 rfl
  let e1 : (res R F).X 1 ≅ I.cocomplex.X 1 := I.cochainComplexXIso 1 1 rfl
  have hd : (res R F).d 0 1 = e0.hom ≫ I.cocomplex.d 0 1 ≫ e1.inv := I.cochainComplex_d 0 1 0 1 rfl rfl
  have hψ : (φ ≫ e0.hom) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [← cancel_mono e1.inv, zero_comp]
    rw [hd] at hφ
    simpa only [Category.assoc] using hφ
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' I.isLimitKernelFork (φ ≫ e0.hom) hψ
  let l' : W ⟶ F := l
  refine ⟨l', ?_⟩
  let ι0 : F ⟶ I.cocomplex.X 0 := I.ι.f 0
  have h1 : resι R F = ι0 ≫ e0.inv := by
    change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ I.ι'.f 0 = _
    rw [InjectiveResolution.ι'_f_zero]
    simp [e0, ι0]
    rfl
  rw [h1]
  have h2 : l' ≫ ι0 = φ ≫ e0.hom := hl
  rw [← Category.assoc, h2, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Take `⟨m, hm, b, rfl⟩` from `h`. Establish `hz : IsZero ((res R F).X m)` using `CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 m (by omega)`. Establish `hsd : (sgl G).d 0 1 = 0` using `(HomologicalComplex.isZero_single_obj_X _ 0 G 1 (by simp)).eq_of_tgt _ _`. Rewrite using `[δ_v m 0 (by omega) b 0 0 (add_zero 0) m 1 (by omega) rfl, hsd, zero_comp, smul_zero, add_zero]`. Rewrite using `[hz.eq_of_tgt (b.v 0 m (by omega)) 0, zero_comp]`.
-/
theorem cocycle0_v_eq_zero {R : Type} [CommRing R] (G F : Shv R) (a : Cochain (sgl G) (res R F) 0)
    (h : ∃ m, ∃ _ : m + 1 = 0, ∃ b : Cochain (sgl G) (res R F) m, δ m 0 b = a) : a.v 0 0 (add_zero 0) = 0 := by
  obtain ⟨m, hm, b, rfl⟩ := h
  have hz : IsZero ((res R F).X m) :=
    CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 m (by omega)
  have hsd : (sgl G).d 0 1 = 0 :=
    (HomologicalComplex.isZero_single_obj_X _ 0 G 1 (by simp)).eq_of_tgt _ _
  rw [δ_v m 0 (by omega) b 0 0 (add_zero 0) m 1 (by omega) rfl, hsd, zero_comp, smul_zero, add_zero]
  rw [hz.eq_of_tgt (b.v 0 m (by omega)) 0, zero_comp]

/- English proof (translation)
Introduce `R _ G Z hZ i`. Use `haveI : (res R Z).IsKInjective := inferInstanceAs ((injectiveResolution Z).cochainComplex.IsKInjective)`. Use `haveI : QuasiIso (resAug Z) := inferInstanceAs (QuasiIso (injectiveResolution Z).ι')`. Establish `h0 : (sgl Z).Acyclic` using `HomologicalComplex.acyclic_of_isZero _ ((CochainComplex.singleFunctor (Shv R) 0).map_isZero hZ)`. Establish `h1 : (res R Z).Acyclic`.

Rewrite using `[HomologicalComplex.acyclic_iff]`. Introduce `j`. Rewrite using `[HomologicalComplex.exactAt_iff_isZero_homology]`. Establish `h2` using `(h0 j)`. Rewrite `h2` using `[HomologicalComplex.exactAt_iff_isZero_homology]`.

Conclude with `h2.of_iso (asIso (HomologicalComplex.homologyMap (resAug Z) j)).symm`. Take `⟨H⟩` from `IsKInjective.nonempty_homotopy_zero (𝟙 (res R Z)) h1`. Establish `gen : ∀ a : Cochain (sgl G) (res R Z) i, δ i (i + 1) a = 0 → δ (i - 1) i (a.comp (Cochain.ofHomotopy H) (by omega)) = a`. Introduce `a ha`. Rewrite using `[δ_comp a (Cochain.ofHomotopy H) (by omega) (i + 1) 0 i (by omega) rfl (by omega), δ_ofHomotopy, ha, Cochain.zero_comp, smul_zero, add_zero, Cochain.ofHom_zero, sub_zero, Cochain.comp_id]`.

Establish `key : ∀ x : CohomologyClass (sgl G) (res R Z) i, x = 0`. Introduce `x`. Take `⟨α, rfl⟩` from `CohomologyClass.mk_surjective x`. Rewrite using `[CohomologyClass.mk_eq_zero_iff]`. Conclude with `⟨i - 1, by omega, _, gen α.1 (Cocycle.δ_eq_zero α (i + 1))⟩`.

Conclude with `⟨fun x y => (key x).trans (key y).symm⟩`.
-/
theorem ext_subsingleton_of_isZero : ∀ (R : Type) [CommRing R] (G Z : Shv R), IsZero Z → ∀ i : ℤ, Subsingleton (CohomologyClass (sgl G) (res R Z) i) := by
  intro R _ G Z hZ i
  haveI : (res R Z).IsKInjective := inferInstanceAs ((injectiveResolution Z).cochainComplex.IsKInjective)
  haveI : QuasiIso (resAug Z) := inferInstanceAs (QuasiIso (injectiveResolution Z).ι')
  have h0 : (sgl Z).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ ((CochainComplex.singleFunctor (Shv R) 0).map_isZero hZ)
  have h1 : (res R Z).Acyclic := by
    rw [HomologicalComplex.acyclic_iff]
    intro j
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have h2 := (h0 j)
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at h2
    exact h2.of_iso (asIso (HomologicalComplex.homologyMap (resAug Z) j)).symm
  obtain ⟨H⟩ := IsKInjective.nonempty_homotopy_zero (𝟙 (res R Z)) h1
  have gen : ∀ a : Cochain (sgl G) (res R Z) i, δ i (i + 1) a = 0 →
      δ (i - 1) i (a.comp (Cochain.ofHomotopy H) (by omega)) = a := by
    intro a ha
    rw [δ_comp a (Cochain.ofHomotopy H) (by omega) (i + 1) 0 i (by omega) rfl (by omega), δ_ofHomotopy, ha,
      Cochain.zero_comp, smul_zero, add_zero, Cochain.ofHom_zero, sub_zero, Cochain.comp_id]
  have key : ∀ x : CohomologyClass (sgl G) (res R Z) i, x = 0 := by
    intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨i - 1, by omega, _, gen α.1 (Cocycle.δ_eq_zero α (i + 1))⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

/- English proof (translation)
Introduce `R _ M k j hkj hj`. Establish `hw : M.iCycles k ≫ M.toCycles k j = 0`. Rewrite using `[← cancel_mono (M.iCycles j)]`. Simplify using the standard rewrite rules. Use `⟨hw, ?_⟩` and prove the remaining obligations.

Establish `hp : (ComplexShape.up ℤ).prev j = k` using `by simp; omega`. Establish `he : Epi (M.toCycles k j)`. Substitute `hp` using the available equality. Conclude with `hj.epi_toCycles`. Establish `hlim : IsLimit (KernelFork.ofι (M.iCycles k) hw)` using `KernelFork.IsLimit.ofι _ _ (fun φ hφ => M.liftCycles φ j (by simp; omega) (by`.

Use `congrArg (· ≫ M.iCycles j) hφ` as an intermediate fact. Simplify using `using this))`. Use the proof step `(fun φ hφ => by simp) (fun φ hφ m hm => by rw [← cancel_mono (M.iCycles k)]; simpa using hm)`. Conclude with `ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hlim) (by dsimp; infer_instance) he`.
-/
theorem cycles_shortExact : ∀ (R : Type) [CommRing R] (M : Cx R) (k j : ℤ), k + 1 = j → M.ExactAt j → ∃ h : M.iCycles k ≫ M.toCycles k j = 0, (ShortComplex.mk _ _ h).ShortExact := by
  intro R _ M k j hkj hj
  have hw : M.iCycles k ≫ M.toCycles k j = 0 := by
    rw [← cancel_mono (M.iCycles j)]; simp
  refine ⟨hw, ?_⟩
  have hp : (ComplexShape.up ℤ).prev j = k := by simp; omega
  have he : Epi (M.toCycles k j) := by
    subst hp
    exact hj.epi_toCycles
  have hlim : IsLimit (KernelFork.ofι (M.iCycles k) hw) :=
    KernelFork.IsLimit.ofι _ _ (fun φ hφ => M.liftCycles φ j (by simp; omega) (by
        have := congrArg (· ≫ M.iCycles j) hφ
        simpa using this))
      (fun φ hφ => by simp) (fun φ hφ m hm => by rw [← cancel_mono (M.iCycles k)]; simpa using hm)
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hlim) (by dsimp; infer_instance) he

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `R _ G S hS h1 f`. Take `⟨z, hz⟩` from `GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS`. Establish `hI3` using `GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₃`. Establish `hI2` using `GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₂`. Establish `hmono : Mono (resι R S.X₃)` using `hI3.2.2.2.2.2.1`.

Establish `hd3 : resι R S.X₃ ≫ (res R S.X₃).d 0 1 = 0` using `hI3.2.2.2.2.2.2.1`. Establish `hnat : resι R S.X₂ ≫ (resMap R S.g).f 0 = S.g ≫ resι R S.X₃` using `(hI2.2.2.2.2.2.2.2 S.X₃ S.g).2`. Set `e : (sgl G).X 0 ≅ G` to `HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G`. Establish `hz0 : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p)` using `fun p hp => HomologicalComplex.isZero_single_obj_X _ 0 G p hp`. Establish `hsd : (sgl G).d 0 1 = 0` using `(hz0 1 (by simp)).eq_of_tgt _ _`.

Set `a3 : Cochain (sgl G) (res R S.X₃) 0` to `Cochain.single (p := 0) (q := 0) (e.hom ≫ f ≫ resι R S.X₃) 0`. Establish `ha3 : δ 0 1 a3 = 0`. Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : p = 0`. Substitute `hp` using the available equality.

Take `rfl : q = 1` from `by omega`. Rewrite using `[δ_v 0 1 rfl a3 0 1 hpq 0 1 (by omega) rfl, Cochain.single_v, hsd, zero_comp, smul_zero, add_zero, Cochain.zero_v, Category.assoc, Category.assoc, hd3, comp_zero, comp_zero]`. Conclude with `(hz0 p hp).eq_of_src _ _`. Set `c3 : CohomologyClass (sgl G) (res R S.X₃) 0` to `CohomologyClass.mk (Cocycle.mk a3 1 rfl ha3)`. Establish `hc3 : HK.ext R (sgl G) z 0 (0 + 1) rfl c3 = 0` using `h1.elim _ _`.

Take `⟨w, hw⟩` from `((hz (sgl G) 0).2.1 c3).1 hc3`. Take `⟨β, rfl⟩` from `w.mk_surjective`. Establish `hw' : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0)) = c3` using `hw`. Establish `hdiff : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0) - Cocycle.mk a3 1 rfl ha3) = 0`. Rewrite using `[CohomologyClass.mk_sub, hw', sub_self]`.

Rewrite `hdiff` using `[CohomologyClass.mk_eq_zero_iff]`. Establish `hv` using `GlobalTheory.AcycResLevel.cocycle0_v_eq_zero G S.X₃ _ hdiff`. Establish `hv' : β.1.v 0 0 (add_zero 0) ≫ (resMap R S.g).f 0 = e.hom ≫ f ≫ resι R S.X₃`. Establish `h` using `hv`. Simplify using `[zcomp, a3, Cochain.comp_zero_cochain_v, sub_eq_zero] at h`.

Conclude with `h`. Establish `hb : β.1.v 0 0 (add_zero 0) ≫ (res R S.X₂).d 0 1 = 0`. Establish `h` using `congrArg (fun c => c.v 0 1 (by simp)) (Cocycle.δ_eq_zero β 1)`. Rewrite `h` using `[δ_v 0 1 rfl _ 0 1 (by simp) 0 1 (by simp) (by simp)]`. Rewrite `h` using `[hsd, zero_comp, smul_zero, add_zero, Cochain.zero_v]`.

Conclude with `h`. Take `⟨g', hg'⟩` from `GlobalTheory.AcycResLevel.res_lift S.X₂ (e.inv ≫ β.1.v 0 0 (add_zero 0)) (by rw [Category.assoc, hb, comp_zero])`. Use `⟨g', ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono (resι R S.X₃), ← cancel_epi e.hom, Category.assoc, ← hnat, ← Category.assoc g', hg', ← hv']`. Simplify using the standard rewrite rules.
-/
theorem lift_of_ext_one_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) (S : ShortComplex (Shv R)), S.ShortExact → Subsingleton (CohomologyClass (sgl G) (res R S.X₁) 1) → ∀ f : G ⟶ S.X₃, ∃ g : G ⟶ S.X₂, g ≫ S.g = f := by
  intro R _ G S hS h1 f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS
  have hI3 := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₃
  have hI2 := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₂
  have hmono : Mono (resι R S.X₃) := hI3.2.2.2.2.2.1
  have hd3 : resι R S.X₃ ≫ (res R S.X₃).d 0 1 = 0 := hI3.2.2.2.2.2.2.1
  have hnat : resι R S.X₂ ≫ (resMap R S.g).f 0 = S.g ≫ resι R S.X₃ := (hI2.2.2.2.2.2.2.2 S.X₃ S.g).2
  let e : (sgl G).X 0 ≅ G := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
  have hz0 : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ 0 G p hp
  have hsd : (sgl G).d 0 1 = 0 := (hz0 1 (by simp)).eq_of_tgt _ _
  let a3 : Cochain (sgl G) (res R S.X₃) 0 := Cochain.single (p := 0) (q := 0) (e.hom ≫ f ≫ resι R S.X₃) 0
  have ha3 : δ 0 1 a3 = 0 := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 1 := by omega
      rw [δ_v 0 1 rfl a3 0 1 hpq 0 1 (by omega) rfl, Cochain.single_v, hsd, zero_comp, smul_zero, add_zero,
        Cochain.zero_v, Category.assoc, Category.assoc, hd3, comp_zero, comp_zero]
    · exact (hz0 p hp).eq_of_src _ _
  let c3 : CohomologyClass (sgl G) (res R S.X₃) 0 := CohomologyClass.mk (Cocycle.mk a3 1 rfl ha3)
  have hc3 : HK.ext R (sgl G) z 0 (0 + 1) rfl c3 = 0 := h1.elim _ _
  obtain ⟨w, hw⟩ := ((hz (sgl G) 0).2.1 c3).1 hc3
  obtain ⟨β, rfl⟩ := w.mk_surjective
  have hw' : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0)) = c3 := hw
  have hdiff : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0) - Cocycle.mk a3 1 rfl ha3) = 0 := by
    rw [CohomologyClass.mk_sub, hw', sub_self]
  rw [CohomologyClass.mk_eq_zero_iff] at hdiff
  have hv := GlobalTheory.AcycResLevel.cocycle0_v_eq_zero G S.X₃ _ hdiff
  have hv' : β.1.v 0 0 (add_zero 0) ≫ (resMap R S.g).f 0 = e.hom ≫ f ≫ resι R S.X₃ := by
    have h := hv
    simp [zcomp, a3, Cochain.comp_zero_cochain_v, sub_eq_zero] at h
    exact h
  have hb : β.1.v 0 0 (add_zero 0) ≫ (res R S.X₂).d 0 1 = 0 := by
    have h := congrArg (fun c => c.v 0 1 (by simp)) (Cocycle.δ_eq_zero β 1)
    rw [δ_v 0 1 rfl _ 0 1 (by simp) 0 1 (by simp) (by simp)] at h
    rw [hsd, zero_comp, smul_zero, add_zero, Cochain.zero_v] at h
    exact h
  obtain ⟨g', hg'⟩ := GlobalTheory.AcycResLevel.res_lift S.X₂ (e.inv ≫ β.1.v 0 0 (add_zero 0))
    (by rw [Category.assoc, hb, comp_zero])
  refine ⟨g', ?_⟩
  rw [← cancel_mono (resι R S.X₃), ← cancel_epi e.hom, Category.assoc, ← hnat, ← Category.assoc g', hg', ← hv']
  simp

/- English proof (translation)
Introduce `R _ G S hS h2 h1 i hi`. Take `⟨z, hz⟩` from `GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS`. Establish `key : ∀ x : CohomologyClass (sgl G) (res R S.X₃) i, x = 0`. Introduce `x`. Establish `e` using `(hz (sgl G) i).2.1`.

Establish `h0 : HK.ext R (sgl G) z i (i + 1) rfl x = 0` using `(h1 (i + 1) (by omega)).elim _ _`. Take `⟨w, hw⟩` from `(e x).1 h0`. Rewrite using `[← hw, (h2 i hi).elim w 0, map_zero]`. Conclude with `⟨fun x y => (key x).trans (key y).symm⟩`.
-/
theorem ext_pos_subsingleton_of_shortExact : ∀ (R : Type) [CommRing R] (G : Shv R) (S : ShortComplex (Shv R)), S.ShortExact → (∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₂) i)) → (∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₁) i)) → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₃) i) := by
  intro R _ G S hS h2 h1 i hi
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS
  have key : ∀ x : CohomologyClass (sgl G) (res R S.X₃) i, x = 0 := by
    intro x
    have e := (hz (sgl G) i).2.1
    have h0 : HK.ext R (sgl G) z i (i + 1) rfl x = 0 := (h1 (i + 1) (by omega)).elim _ _
    obtain ⟨w, hw⟩ := (e x).1 h0
    rw [← hw, (h2 i hi).elim w 0, map_zero]
  exact ⟨fun x y => (key x).trans (key y).symm⟩

/- English proof (translation)
Introduce `R _ G M n hlift`. Establish `hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p)` using `fun p hp => HomologicalComplex.isZero_single_obj_X _ 0 G p hp`. Establish `hd : (sgl G).d 0 1 = 0` using `(hz 1 (by simp)).eq_of_tgt _ _`. Set `e : (sgl G).X 0 ≅ G` to `HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G`. Establish `gen : ∀ a : Cochain (sgl G) M n, δ n (n + 1) a = 0 → ∃ b : Cochain (sgl G) M (n - 1), δ (n - 1) n b = a`.

Introduce `a ha`. Establish `h` using `congrArg (fun c => c.v 0 (n + 1) (by simp)) ha`. Rewrite `h` using `[δ_v n (n + 1) rfl _ 0 (n + 1) (by simp) n 1 (by simp) (by simp)]`. Rewrite `h` using `[hd, zero_comp, smul_zero, add_zero, Cochain.zero_v]`. Establish `hf : (e.inv ≫ a.v 0 n (by simp)) ≫ M.d n (n + 1) = 0`.

Rewrite using `[Category.assoc, h, comp_zero]`. Take `⟨g, hg⟩` from `hlift _ hf`. Use `⟨Cochain.single (p := 0) (q := n - 1) (e.hom ≫ g) (n - 1), ?_⟩` and prove the remaining obligations. Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : p = 0`.

Substitute `hp` using the available equality. Take `rfl : n = q` from `by omega`. Rewrite using `[δ_v (n - 1) n (by omega) _ 0 n hpq (n - 1) 1 (by omega) rfl, Cochain.single_v, hd, zero_comp, smul_zero, add_zero, Category.assoc, hg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]`. Conclude with `(hz p hp).eq_of_src _ _`. Establish `key : ∀ x : CohomologyClass (sgl G) M n, x = 0`.

Introduce `x`. Take `⟨α, rfl⟩` from `CohomologyClass.mk_surjective x`. Take `⟨b, hb⟩` from `gen α.1 (Cocycle.δ_eq_zero α (n + 1))`. Rewrite using `[CohomologyClass.mk_eq_zero_iff]`. Conclude with `⟨n - 1, by omega, b, hb⟩`.

Conclude with `⟨fun x y => (key x).trans (key y).symm⟩`.
-/
theorem subsingleton_of_lifts : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (n : ℤ), (∀ f : G ⟶ M.X n, f ≫ M.d n (n + 1) = 0 → ∃ g : G ⟶ M.X (n - 1), g ≫ M.d (n - 1) n = f) → Subsingleton (CohomologyClass (sgl G) M n) := by
  intro R _ G M n hlift
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ 0 G p hp
  have hd : (sgl G).d 0 1 = 0 := (hz 1 (by simp)).eq_of_tgt _ _
  let e : (sgl G).X 0 ≅ G := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
  have gen : ∀ a : Cochain (sgl G) M n, δ n (n + 1) a = 0 → ∃ b : Cochain (sgl G) M (n - 1), δ (n - 1) n b = a := by
    intro a ha
    have h := congrArg (fun c => c.v 0 (n + 1) (by simp)) ha
    rw [δ_v n (n + 1) rfl _ 0 (n + 1) (by simp) n 1 (by simp) (by simp)] at h
    rw [hd, zero_comp, smul_zero, add_zero, Cochain.zero_v] at h
    have hf : (e.inv ≫ a.v 0 n (by simp)) ≫ M.d n (n + 1) = 0 := by
      rw [Category.assoc, h, comp_zero]
    obtain ⟨g, hg⟩ := hlift _ hf
    refine ⟨Cochain.single (p := 0) (q := n - 1) (e.hom ≫ g) (n - 1), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : n = q := by omega
      rw [δ_v (n - 1) n (by omega) _ 0 n hpq (n - 1) 1 (by omega) rfl, Cochain.single_v, hd, zero_comp,
        smul_zero, add_zero, Category.assoc, hg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · exact (hz p hp).eq_of_src _ _
  have key : ∀ x : CohomologyClass (sgl G) M n, x = 0 := by
    intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨b, hb⟩ := gen α.1 (Cocycle.δ_eq_zero α (n + 1))
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, b, hb⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.AcycResLevel

/- English proof (translation)
Introduce `R _ G M a _ hM hExt n`. Establish `hZ0 : ∀ k, k ≤ a → IsZero (M.cycles k)`. Introduce `k hk`. Take `⟨h, hS⟩` from `GlobalTheory.AcycResLevel.cycles_shortExact R M (k - 1) k (by omega) (hM k)`. Establish `: Epi (M.toCycles (k - 1) k)` using `hS.epi_g`.

Conclude with `IsZero.of_epi (M.toCycles (k - 1) k) (M.isZero_of_isStrictlyGE a (k - 1))`. Establish `hge : ∀ k, a ≤ k → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i)`. Introduce `k hk`. Proceed by induction on `k, hk using Int.le_induction with`. Consider the case `base => intro i _`.

Conclude with `GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 a le_rfl) i`. Consider the case `succ k hak ih`. Take `⟨h, hS⟩` from `GlobalTheory.AcycResLevel.cycles_shortExact R M k (k + 1) rfl (hM (k + 1))`. Conclude with `GlobalTheory.AcycResLevel.ext_pos_subsingleton_of_shortExact R G _ hS (hExt k) ih`. Establish `hZ : ∀ k, ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i)`.

Introduce `k`. Break down `le_or_gt k a with hk | hk` into its components or cases. Introduce `i _`. Conclude with `GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 k hk) i`. Conclude with `hge k hk.le`.

Use `GlobalTheory.AcycResLevel.subsingleton_of_lifts R G M n fun f hf => ?_` and prove the remaining obligations. Take `⟨h, hS⟩` from `GlobalTheory.AcycResLevel.cycles_shortExact R M (n - 1) n (by omega) (hM n)`. Take `⟨g, hg⟩` from `GlobalTheory.AcycResLevel.lift_of_ext_one_subsingleton R G _ hS ((hZ (n - 1) 1 one_pos)) (M.liftCycles f (n + 1) (by simp) hf)`. Use `⟨g, ?_⟩` and prove the remaining obligations. Use `congrArg (· ≫ M.iCycles n) hg` as an intermediate fact.

Simplify using `using this`.
-/
theorem GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  intro R _ G M a _ hM hExt n
  have hZ0 : ∀ k, k ≤ a → IsZero (M.cycles k) := by
    intro k hk
    obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M (k - 1) k (by omega) (hM k)
    have : Epi (M.toCycles (k - 1) k) := hS.epi_g
    exact IsZero.of_epi (M.toCycles (k - 1) k) (M.isZero_of_isStrictlyGE a (k - 1))
  have hge : ∀ k, a ≤ k → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i) := by
    intro k hk
    induction k, hk using Int.le_induction with
    | base => intro i _; exact GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 a le_rfl) i
    | succ k hak ih =>
      obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M k (k + 1) rfl (hM (k + 1))
      exact GlobalTheory.AcycResLevel.ext_pos_subsingleton_of_shortExact R G _ hS (hExt k) ih
  have hZ : ∀ k, ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i) := by
    intro k
    rcases le_or_gt k a with hk | hk
    · intro i _
      exact GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 k hk) i
    · exact hge k hk.le
  refine GlobalTheory.AcycResLevel.subsingleton_of_lifts R G M n fun f hf => ?_
  obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M (n - 1) n (by omega) (hM n)
  obtain ⟨g, hg⟩ := GlobalTheory.AcycResLevel.lift_of_ext_one_subsingleton R G _ hS ((hZ (n - 1) 1 one_pos)) (M.liftCycles f (n + 1) (by simp) hf)
  refine ⟨g, ?_⟩
  have := congrArg (· ≫ M.iCycles n) hg
  simpa using this
