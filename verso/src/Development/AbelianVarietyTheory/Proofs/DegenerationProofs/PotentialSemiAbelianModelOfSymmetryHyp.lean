import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalizationOfLeClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomPairDescendsToFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelOfProperBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SymSemistable

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_spMap {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Establish `h : IsUnit (((3 : ℕ) : V) * 2 + ((5 : ℕ) : V) * (-1))`. Establish `: ((3 : ℕ) : V) * 2 + ((5 : ℕ) : V) * (-1) = 1` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `isUnit_one`. Break down `IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h` into its components or cases.

Conclude with `⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩`. Conclude with `⟨5, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩`.
-/
theorem exists_odd_prime_isUnit (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : V) := by
  have h : IsUnit (((3 : ℕ) : V) * 2 + ((5 : ℕ) : V) * (-1)) := by
    have : ((3 : ℕ) : V) * 2 + ((5 : ℕ) : V) * (-1) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩

/- English proof (translation)
Take `⟨P', φ, hφ, hg, hm, t, ht⟩` from `GlobalTheory.abelianSchemeLaws_all.1.polBaseChange S S' f P`. Use `⟨P', φ, hg, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩` and prove the remaining obligations. Rewrite using `[(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]`. Both sides reduce to the same expression.
-/
theorem exists_polarised_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left),
      P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange S S' f P
  refine ⟨P', φ, hg, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

/- English proof (translation)
Set `j₁ : Ω₀ →+* K₁` to `j.codRestrict K₁ hj`. Establish `pA` using `isGrpPullback_pullback A (spMap (algebraMap K K₁))`. Establish `pB` using `isGrpPullback_pullback B (spMap j₁)`. Establish `qA` using `((isGrpPullback_pullback _ (spMap (algebraMap K₁ Ω))).comp pA).congr (f' := spMap (algebraMap K Ω)) (by rw [spMap_spMap]; rfl) rfl`. Establish `qB` using `((isGrpPullback_pullback _ (spMap (algebraMap K₁ Ω))).comp pB).congr (f' := spMap j) (by rw [spMap_spMap]; rfl) rfl`.

Take `⟨e₁, m₁, -⟩` from `grpPullback_iso qA hα`. Take `⟨e₂, m₂, -⟩` from `grpPullback_iso hβ qB`. Establish `m : IsMonHom (e₁ ≪≫ e₂).hom` using `inferInstanceAs (IsMonHom (e₁.hom ≫ e₂.hom))`. Take `⟨L, hL, i, r, mi, -, h⟩` from `GlobalTheory.homPair_descends_to_finite K₁ Ω _ _ (PolPull.isAbelianScheme_of_isGrpPullback hA pA) (PolPull.isAbelianScheme_of_isGrpPullback hB pB) (e₁ ≪≫ e₂).hom (e₁ ≪≫ e₂).inv m inferInstance`. Take `⟨h₁, h₂⟩` from `h 1`.

Simplify using `only [pow_one] at h₁ h₂`. Set `e` to `Iso.mk i r (h₁ (Iso.hom_inv_id _)) (h₂ (Iso.inv_hom_id _))`. Establish `me : IsMonHom e.hom` using `mi`. Establish `rA` using `((isGrpPullback_pullback _ (spMap (algebraMap K₁ L))).comp pA).congr (f' := spMap (algebraMap K L)) (by rw [spMap_spMap]; rfl) rfl`. Take `⟨e₃, m₃, -⟩` from `grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap K L))) rA`.

Establish `m' : IsMonHom (e₃ ≪≫ e).hom` using `inferInstanceAs (IsMonHom (e₃.hom ≫ e.hom))`. Conclude with `⟨L, inferInstance, inferInstance, Module.Finite.trans K₁ L, (algebraMap K₁ L).comp j₁, _, ((isGrpPullback_of_iso (e₃ ≪≫ e)).comp ((isGrpPullback_pullback _ (spMap (algebraMap K₁ L))).comp pB)).congr (by rw [Category.id_comp, spMap_spMap]) rfl⟩`.
-/
theorem exists_finite_common_pull {K Ω Ω₀ : Type} [Field K] [Field Ω] [Field Ω₀] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (K₁ : IntermediateField K Ω) [FiniteDimensional K K₁] (j : Ω₀ →+* Ω)
    (hj : ∀ x, j x ∈ K₁) (A : Over (Sp K)) (B : Over (Sp Ω₀)) (C : Over (Sp Ω)) [GrpObj A] [GrpObj B] [GrpObj C]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {α : C.left ⟶ A.left} {β : C.left ⟶ B.left}
    (hα : IsGrpPullback C A (spMap (algebraMap K Ω)) α) (hβ : IsGrpPullback C B (spMap j) β) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (j' : Ω₀ →+* L)
      (ψ : ((Over.pullback (spMap (algebraMap K L))).obj A).left ⟶ B.left),
      IsGrpPullback ((Over.pullback (spMap (algebraMap K L))).obj A) B (spMap j') ψ := by
  let j₁ : Ω₀ →+* K₁ := j.codRestrict K₁ hj
  have pA := isGrpPullback_pullback A (spMap (algebraMap K K₁))
  have pB := isGrpPullback_pullback B (spMap j₁)
  have qA := ((isGrpPullback_pullback _ (spMap (algebraMap K₁ Ω))).comp pA).congr
    (f' := spMap (algebraMap K Ω)) (by rw [spMap_spMap]; rfl) rfl
  have qB := ((isGrpPullback_pullback _ (spMap (algebraMap K₁ Ω))).comp pB).congr
    (f' := spMap j) (by rw [spMap_spMap]; rfl) rfl
  obtain ⟨e₁, m₁, -⟩ := grpPullback_iso qA hα
  obtain ⟨e₂, m₂, -⟩ := grpPullback_iso hβ qB
  have m : IsMonHom (e₁ ≪≫ e₂).hom := inferInstanceAs (IsMonHom (e₁.hom ≫ e₂.hom))
  obtain ⟨L, hL, i, r, mi, -, h⟩ := GlobalTheory.homPair_descends_to_finite K₁ Ω _ _
    (PolPull.isAbelianScheme_of_isGrpPullback hA pA) (PolPull.isAbelianScheme_of_isGrpPullback hB pB)
    (e₁ ≪≫ e₂).hom (e₁ ≪≫ e₂).inv m inferInstance
  obtain ⟨h₁, h₂⟩ := h 1
  simp only [pow_one] at h₁ h₂
  let e := Iso.mk i r (h₁ (Iso.hom_inv_id _)) (h₂ (Iso.inv_hom_id _))
  have me : IsMonHom e.hom := mi
  have rA := ((isGrpPullback_pullback _ (spMap (algebraMap K₁ L))).comp pA).congr
    (f' := spMap (algebraMap K L)) (by rw [spMap_spMap]; rfl) rfl
  obtain ⟨e₃, m₃, -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap K L))) rA
  have m' : IsMonHom (e₃ ≪≫ e).hom := inferInstanceAs (IsMonHom (e₃.hom ≫ e.hom))
  exact ⟨L, inferInstance, inferInstance, Module.Finite.trans K₁ L, (algebraMap K₁ L).comp j₁, _,
    ((isGrpPullback_of_iso (e₃ ≪≫ e)).comp ((isGrpPullback_pullback _ (spMap (algebraMap K₁ L))).comp pB)).congr
      (by rw [Category.id_comp, spMap_spMap]) rfl⟩

/- English proof (translation)
Take `⟨s, rfl⟩` from `fg`. Set `t : Finset Ω` to `insert z (s.image j)`. Set `K₁` to `IntermediateField.adjoin K (t : Set Ω)`. Use `⟨K₁, IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x => ?_⟩` and prove the remaining obligations. Establish `hle : o ≤ K₁.toSubfield.toSubring`.

Rewrite using `[ho, Subring.closure_le]`. Introduce and unpack `y (rfl | rfl)`. Conclude with `IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_insert_self _ _))`. Conclude with `K₁.inv_mem (natCast_mem K₁ n)`. Establish `hR : ∀ a ∈ Algebra.adjoin o (s : Set Ω₀), j a ∈ K₁` using `fun a ha => by`.

Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Conclude with `IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)))`. Consider the case `algebraMap c => rw [j.commutes]`. Conclude with `hle c.2`.

Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `K₁.add_mem ha hb`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `K₁.mul_mem ha hb`. Take `⟨a, ha, b, hb, rfl⟩` from `fr x`.

Rewrite using `[map_div₀]`. Conclude with `K₁.div_mem (hR a ha) (hR b hb)`.
-/
theorem exists_finite_range {K Ω Ω₀ : Type} [Field K] [Field Ω] [Field Ω₀] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (o : Subring Ω) (z : Ω) (n : ℕ) (ho : o = Subring.closure {z, (n : Ω)⁻¹}) [Algebra o Ω₀] (j : Ω₀ →ₐ[o] Ω)
    (R₀ : Subalgebra o Ω₀) (fg : R₀.FG) (fr : ∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) :
    ∃ K₁ : IntermediateField K Ω, FiniteDimensional K K₁ ∧ ∀ x, j x ∈ K₁ := by
  classical
  obtain ⟨s, rfl⟩ := fg
  let t : Finset Ω := insert z (s.image j)
  let K₁ := IntermediateField.adjoin K (t : Set Ω)
  refine ⟨K₁, IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x => ?_⟩
  have hle : o ≤ K₁.toSubfield.toSubring := by
    rw [ho, Subring.closure_le]
    rintro y (rfl | rfl)
    · exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    · exact K₁.inv_mem (natCast_mem K₁ n)
  have hR : ∀ a ∈ Algebra.adjoin o (s : Set Ω₀), j a ∈ K₁ := fun a ha => by
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin _ _
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)))
    | algebraMap c => rw [j.commutes]; exact hle c.2
    | add a b _ _ ha hb => rw [map_add]; exact K₁.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K₁.mul_mem ha hb
  obtain ⟨a, ha, b, hb, rfl⟩ := fr x
  rw [map_div₀]
  exact K₁.div_mem (hR a ha) (hR b hb)

/- English proof (translation)
Establish `hle : o ≤ (c.range.comap d).map o.subtype`. Use `ho.le.trans (Subring.closure_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `y (rfl | rfl)`. Conclude with `⟨z, hz, rfl⟩`. Establish `hm : (n : Ω)⁻¹ ∈ o` using `ho.ge (Subring.subset_closure (Or.inr rfl))`.

Take `⟨u, hu⟩` from `hn.exists_left_inv`. Establish `e₁ : (⟨_, hm⟩ : o) * n = 1` using `Subtype.ext (by simp [hn₀])`. Establish `e₂ : d ⟨_, hm⟩ * n = 1` using `by simpa using congrArg d e₁`. Establish `e₃ : c u * n = 1` using `by simpa using congrArg c hu`. Use `⟨⟨_, hm⟩, ⟨u, ?_⟩, rfl⟩` and prove the remaining obligations.

Rewrite using `[eq_inv_of_mul_eq_one_left e₂, eq_inv_of_mul_eq_one_left e₃]`. Establish `hr : ∀ x, d x ∈ c.range` using `fun x => by`. Take `⟨y, hy, e⟩` from `hle x.2`. Conclude with `(Subtype.ext e : y = x) ▸ hy`. Set `E : W ≃+* c.range` to `RingEquiv.ofBijective c.rangeRestrict ⟨fun a b h => hc (congrArg Subtype.val h), c.rangeRestrict_surjective⟩`.

Use `⟨E.symm.toRingHom.comp (d.codRestrict c.range hr), RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (E.apply_symm_apply (d.codRestrict c.range hr x))`.
-/
theorem exists_factor {Ω W L : Type} [Field Ω] [CharZero Ω] [CommRing W] [Field L] (c : W →+* L) (hc : Function.Injective c)
    (o : Subring Ω) (z : o) (n : ℕ) (hn₀ : n ≠ 0) (ho : o = Subring.closure {(z : Ω), (n : Ω)⁻¹}) (d : o →+* L)
    (hz : d z ∈ Set.range c) (hn : IsUnit (n : W)) : ∃ β : o →+* W, c.comp β = d := by
  have hle : o ≤ (c.range.comap d).map o.subtype := by
    refine ho.le.trans (Subring.closure_le.2 ?_)
    rintro y (rfl | rfl)
    · exact ⟨z, hz, rfl⟩
    · have hm : (n : Ω)⁻¹ ∈ o := ho.ge (Subring.subset_closure (Or.inr rfl))
      obtain ⟨u, hu⟩ := hn.exists_left_inv
      have e₁ : (⟨_, hm⟩ : o) * n = 1 := Subtype.ext (by simp [hn₀])
      have e₂ : d ⟨_, hm⟩ * n = 1 := by simpa using congrArg d e₁
      have e₃ : c u * n = 1 := by simpa using congrArg c hu
      refine ⟨⟨_, hm⟩, ⟨u, ?_⟩, rfl⟩
      rw [eq_inv_of_mul_eq_one_left e₂, eq_inv_of_mul_eq_one_left e₃]
  have hr : ∀ x, d x ∈ c.range := fun x => by
    obtain ⟨y, hy, e⟩ := hle x.2
    exact (Subtype.ext e : y = x) ▸ hy
  let E : W ≃+* c.range := RingEquiv.ofBijective c.rangeRestrict
    ⟨fun a b h => hc (congrArg Subtype.val h), c.rangeRestrict_surjective⟩
  refine ⟨E.symm.toRingHom.comp (d.codRestrict c.range hr), RingHom.ext fun x => ?_⟩
  exact congrArg Subtype.val (E.apply_symm_apply (d.codRestrict c.range hr x))

/- English proof (translation)
Introduce `V K _ _ _ _ _ _ _ _ Q hS`. Take `⟨n, np, nodd, nu⟩` from `exists_odd_prime_isUnit V`. Take `⟨a, fam⟩` from `GlobalTheory.T.exists_proper_semiAbelian_family' Q.g n np nodd`. Set `Ω` to `AlgebraicClosure K`. Take `⟨o, ze, ded, ft, no, prim, ho⟩` from `GlobalTheory.CycAway.exists_base Ω n a np`.

Take `⟨P, α, hg, hα, hL⟩` from `exists_polarised_pull (spMap (algebraMap K Ω)) Q`. Establish `hSP : letI` using `P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L := by`. Use `letI := Q.isAb.comm`. Use `letI := P.isAb.comm`. Conclude with `GlobalTheory.SymBaseChange.hypS_baseChange _ _ Q.A P.A _ α Q.L P.L Q.isLB P.isLB hα hL hS`.

Establish `lev` using `GlobalTheory.nonempty_level_of_isAlgClosed Ω P (n ^ a) _ (by exact_mod_cast pow_ne_zero a np.ne_zero) prim`. Take `⟨Ω₀, _, _, j, R₀, Q₀, φ, fg, fr, hg₀, hφ, hS₀, lev₀⟩` from `GlobalTheory.SymLevelDescent.descends_to_fg_field o Ω P (n ^ a) ze hSP lev`. Use `haveI : GlobalTheory.ZH.ArithBase o Ω₀ := ⟨ded, ft, RingHom.charZero j.toRingHom, fun x y h => Subtype.ext (by`. Use `congrArg j h` as an intermediate fact. Rewrite using `[j.commutes, j.commutes] at this)⟩` and apply the resulting hypothesis.

Take `⟨Z, s, x, G, _, χ, hs, hx, hG, hχ⟩` from `fam o Ω₀ R₀ fg fr Q₀ ze (hg₀.trans hg) no hS₀ lev₀`. Take `⟨K₁, hK₁, hj⟩` from `exists_finite_range (K := K) o _ n ho j R₀ fg fr`. Take `⟨L, _, _, _, j', ψ, hψ⟩` from `exists_finite_common_pull K₁ j.toRingHom hj Q.A Q₀.A P.A Q.isAb Q₀.isAb hα hφ`. Take `⟨W, _, _, _, cW, _, _, _, sq, fin, -, loc, int, -⟩` from `GlobalTheory.SS.exists_complete_dvr_finite_extension V K L`. Establish `hz : (ze : o) ^ (n ^ a) = 1` using `Subtype.ext (by simpa using congrArg Units.val prim.pow_eq_one)`.

Take `⟨β, hβ⟩` from `exists_factor (algebraMap W L) (IsFractionRing.injective W L) o ze n np.ne_zero ho (j'.comp (algebraMap o Ω₀)) (int _ ⟨Polynomial.X ^ (n ^ a) - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ (pow_ne_zero a np.ne_zero), by`. Rewrite using `[Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, ← map_pow, hz, map_one, map_one, sub_self]⟩)`. Use the proof step `(by simpa using nu.map (algebraMap V W))`. Take `⟨G', _, e, hG', he⟩` from `GlobalTheory.SS.exists_semiAbelian_model_of_proper_base o W L β Z s (spMap j' ≫ x) G _ _ hs (by rw [Category.assoc, hx, spMap_spMap, hβ]) hG (hψ.comp hχ)`. Conclude with `⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, sq, fin, loc, cW, G', inferInstance, ⟨e, he⟩, hG'⟩`.
-/
theorem potModel_semiAbelian_of_hypS : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (Q : Out.PolAV (Sp K)), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) → PotModel V K Q.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ Q hS
  obtain ⟨n, np, nodd, nu⟩ := exists_odd_prime_isUnit V
  obtain ⟨a, fam⟩ := GlobalTheory.T.exists_proper_semiAbelian_family' Q.g n np nodd
  let Ω := AlgebraicClosure K
  obtain ⟨o, ze, ded, ft, no, prim, ho⟩ := GlobalTheory.CycAway.exists_base Ω n a np
  obtain ⟨P, α, hg, hα, hL⟩ := exists_polarised_pull (spMap (algebraMap K Ω)) Q
  have hSP : letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L := by
    letI := Q.isAb.comm
    letI := P.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ Q.A P.A _ α Q.L P.L Q.isLB P.isLB hα hL hS
  have lev := GlobalTheory.nonempty_level_of_isAlgClosed Ω P (n ^ a) _ (by exact_mod_cast pow_ne_zero a np.ne_zero) prim
  obtain ⟨Ω₀, _, _, j, R₀, Q₀, φ, fg, fr, hg₀, hφ, hS₀, lev₀⟩ := GlobalTheory.SymLevelDescent.descends_to_fg_field o Ω P (n ^ a) ze hSP lev
  haveI : GlobalTheory.ZH.ArithBase o Ω₀ := ⟨ded, ft, RingHom.charZero j.toRingHom, fun x y h => Subtype.ext (by
    have := congrArg j h
    rwa [j.commutes, j.commutes] at this)⟩
  obtain ⟨Z, s, x, G, _, χ, hs, hx, hG, hχ⟩ := fam o Ω₀ R₀ fg fr Q₀ ze (hg₀.trans hg) no hS₀ lev₀
  obtain ⟨K₁, hK₁, hj⟩ := exists_finite_range (K := K) o _ n ho j R₀ fg fr
  obtain ⟨L, _, _, _, j', ψ, hψ⟩ := exists_finite_common_pull K₁ j.toRingHom hj Q.A Q₀.A P.A Q.isAb Q₀.isAb hα hφ
  obtain ⟨W, _, _, _, cW, _, _, _, sq, fin, -, loc, int, -⟩ := GlobalTheory.SS.exists_complete_dvr_finite_extension V K L
  have hz : (ze : o) ^ (n ^ a) = 1 := Subtype.ext (by simpa using congrArg Units.val prim.pow_eq_one)
  obtain ⟨β, hβ⟩ := exists_factor (algebraMap W L) (IsFractionRing.injective W L) o ze n np.ne_zero ho
    (j'.comp (algebraMap o Ω₀)) (int _ ⟨Polynomial.X ^ (n ^ a) - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero a np.ne_zero), by
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, ← map_pow, hz, map_one, map_one, sub_self]⟩)
    (by simpa using nu.map (algebraMap V W))
  obtain ⟨G', _, e, hG', he⟩ := GlobalTheory.SS.exists_semiAbelian_model_of_proper_base o W L β Z s (spMap j' ≫ x) G _ _ hs
    (by rw [Category.assoc, hx, spMap_spMap, hβ]) hG (hψ.comp hχ)
  exact ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, sq, fin, loc, cW, G', inferInstance, ⟨e, he⟩, hG'⟩

end GlobalTheory.SymSemistable
