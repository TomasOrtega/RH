import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1AffineStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CechBCInj

/- English proof (translation)
Use `letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj`. Establish `hP` using `GlobalTheory.AbLaw.CubeGen.isAb_baseChange hG f`. Set `e : Over.mk snd ≅ (Over.pullback f).obj G` to `Over.isoMk h.isoPullback (by simp)`. Use `letI gr : GrpObj (Over.mk snd) := GrpObj.ofIso e.symm`. Use `⟨gr, GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso e ?_ hP⟩` and prove the remaining obligations.

Use `haveI : IsMonHom e.symm.hom := inferInstance`. Conclude with `isMonHom_inv_of_iso e.symm`.
-/
theorem grp_of_isPullback {X S' P : Scheme.{0}} (G : Over X) [GrpObj G] (hG : IsAbelianScheme G) (f : S' ⟶ X)
    (fst : P ⟶ G.left) (snd : P ⟶ S') (h : IsPullback fst snd G.hom f) :
    ∃ _ : GrpObj (Over.mk snd), IsAbelianScheme (Over.mk snd) := by
  letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj
  have hP := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hG f
  let e : Over.mk snd ≅ (Over.pullback f).obj G := Over.isoMk h.isoPullback (by simp)
  letI gr : GrpObj (Over.mk snd) := GrpObj.ofIso e.symm
  refine ⟨gr, GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso e ?_ hP⟩
  haveI : IsMonHom e.symm.hom := inferInstance
  exact isMonHom_inv_of_iso e.symm

/- English proof (translation)
Establish `h1` using `(isPullback_morphismRestrict p U.1).flip`. Establish `h2 : IsPullback U.1.ι U.2.isoSpec.hom (𝟙 X) (U.2.isoSpec.inv ≫ U.1.ι)` using `IsPullback.of_vert_isIso ⟨by simp⟩`. Establish `h3` using `h1.paste_vert h2`. Rewrite `h3` using `[Category.comp_id]`. Establish `e : chart U = U.2.isoSpec.inv ≫ U.1.ι` using `(IsAffineOpen.isoSpec_inv_ι U.2).symm`.

Rewrite using `[e]`. Conclude with `h3`.
-/
theorem restrict_isPullback {X T : Scheme.{0}} (p : T ⟶ X) (U : X.affineOpens) :
    IsPullback (p ⁻¹ᵁ U.1).ι ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) p (chart U) := by
  have h1 := (isPullback_morphismRestrict p U.1).flip
  have h2 : IsPullback U.1.ι U.2.isoSpec.hom (𝟙 X) (U.2.isoSpec.inv ≫ U.1.ι) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have h3 := h1.paste_vert h2
  rw [Category.comp_id] at h3
  have e : chart U = U.2.isoSpec.inv ≫ U.1.ι := (IsAffineOpen.isoSpec_inv_ι U.2).symm
  rw [e]
  exact h3

/- English proof (translation)
Use `show ((p.appLE U.1 O hO) ≫ T.presheaf.map (homOfLE h).op).hom r = _`. Rewrite using `[Scheme.Hom.appLE_map]`.
-/
theorem resG_appLE' {X T : Scheme.{0}} (p : T ⟶ X) (U : X.affineOpens) {O O' : T.Opens} (hO : O ≤ p ⁻¹ᵁ U.1)
    (h : O' ≤ O) (r : Γ(X, U.1)) :
    resG T h ((p.appLE U.1 O hO).hom r) = (p.appLE U.1 O' (h.trans hO)).hom r := by
  show ((p.appLE U.1 O hO) ≫ T.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]

/- English proof (translation)
Establish `key : ∃ l : List (R × M), (∀ p ∈ l, p.1 ∈ I) ∧ x = (l.map fun p => p.1 • p.2).sum`. Use `Submodule.smul_induction_on hx (fun r hr n _ => ⟨[(r, n)], by simpa using hr, by simp⟩) ?_` and prove the remaining obligations. Introduce and unpack `a b ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩`. Use `⟨l₁ ++ l₂, fun p hp => ?_, by simp⟩` and prove the remaining obligations. Break down `List.mem_append.1 hp with h | h` into its components or cases.

Use `exacts [h₁ p h, h₂ p h]`. Take `⟨l, hl, rfl⟩` from `key`. Use `⟨l.length, fun k => l[k].1, fun k => l[k].2, fun k => hl _ (List.getElem_mem _), ?_⟩` and prove the remaining obligations. Conclude with `(Fin.sum_univ_fun_getElem l (fun p => p.1 • p.2)).symm`.
-/
theorem exists_fin_sum {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (x : M)
    (hx : x ∈ I • (⊤ : Submodule R M)) :
    ∃ (N : ℕ) (r : Fin N → R) (y : Fin N → M), (∀ k, r k ∈ I) ∧ x = ∑ k, r k • y k := by
  have key : ∃ l : List (R × M), (∀ p ∈ l, p.1 ∈ I) ∧ x = (l.map fun p => p.1 • p.2).sum := by
    refine Submodule.smul_induction_on hx (fun r hr n _ => ⟨[(r, n)], by simpa using hr, by simp⟩) ?_
    rintro a b ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
    refine ⟨l₁ ++ l₂, fun p hp => ?_, by simp⟩
    rcases List.mem_append.1 hp with h | h
    exacts [h₁ p h, h₂ p h]
  obtain ⟨l, hl, rfl⟩ := key
  refine ⟨l.length, fun k => l[k].1, fun k => l[k].2, fun k => hl _ (List.getElem_mem _), ?_⟩
  exact (Fin.sum_univ_fun_getElem l (fun p => p.1 • p.2)).symm

/- English proof (translation)
Introduce `E _ _ _ H X t hP U J W hWa hcov hWU m hm A ι hpb c hc hcob`. Establish `sq` using `restrict_isPullback t.G.hom U`. Take `⟨inst, hAb⟩` from `grp_of_isPullback t.G (GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hP) (chart U) _ _ sq`. Establish `hsq : ι ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U`. Rewrite using `[hpb.w, Category.assoc]`.

Set `ι'` to `sq.lift ι (A.hom ≫ spMap (Ideal.Quotient.mk m)) hsq`. Establish `hι' : ι' ≫ (t.G.hom ⁻¹ᵁ U.1).ι = ι` using `sq.lift_fst _ _ _`. Establish `hw : ι' ≫ ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom : (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = A.hom ≫ spMap (Ideal.Quotient.mk m)` using `sq.lift_snd _ _ _`. Establish `hpb' : IsPullback ι' A.hom (Over.mk ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom : (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1))).hom (spMap (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m)))` using `IsPullback.of_right (by rw [hι']; exact hpb) hw sq`. Take `⟨Φ, hlin, hinj, hsurj, hnat⟩` from `GlobalTheory.T.cech_comparison_structure_h1_affine X t.G.left t.G.hom t.semi.separated U J W hWa hcov hWU`.

Establish `h0` using `hnat _ (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m)) A.left A.hom ι ι' hι' hpb'.w c hc hcob`. Establish `hmem` using `GlobalTheory.T.structure_h1_nakayama_closed_fibre _ _ hAb m hm A.left A.hom ι' hpb' (Φ c) h0`. Take `⟨N, r, y, hr, hy⟩` from `exists_fin_sum m _ hmem`. Use `choose e he hΦe using hsurj`. Set `ρ : ∀ i i' : J, Γ(X, U.1) →+* Γ(t.G.left, W i ⊓ W i')` to `fun i i' => (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom`.

Set `c' : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')` to `fun i i' => c i i' - ∑ k, ρ i i' (r k) * e (y k) i i'`. Establish `hc' : (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c' i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c' i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : …`. Introduce `i i' i''`. Simplify using `only [c', ρ, map_sub, map_sum, map_mul, resG_appLE']`. Rewrite using `[← hc i i' i'']`.

Use `fun k => he (y k) i i' i''` as an intermediate fact. Simplify using `only [← this, mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hΦ : Φ c' = 0`. Rewrite using `[hlin c hc N r (fun k => e (y k)) (fun k => he (y k))]`.

Simplify using `only [hΦe, ← hy, sub_self]`. Take `⟨h, hh⟩` from `hinj c' hc' hΦ`. Use `⟨h, N, r, fun k => e (y k), hr, fun k => he (y k), fun i i' => ?_⟩` and prove the remaining obligations. Use `hh i i'` as an intermediate fact. Simplify using `only [c'] at this`.

Rewrite `this` using `[sub_eq_iff_eq_add]`. Conclude with `this`.
-/
theorem cocycle_mem_coboundary_add_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) (ι : A.left ⟶ t.G.left), IsPullback ι A.hom t.G.hom (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∃ (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP U J W hWa hcov hWU m hm A ι hpb c hc hcob
  have sq := restrict_isPullback t.G.hom U
  obtain ⟨inst, hAb⟩ := grp_of_isPullback t.G
    (GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hP) (chart U) _ _ sq
  have hsq : ι ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hpb.w, Category.assoc]
  let ι' := sq.lift ι (A.hom ≫ spMap (Ideal.Quotient.mk m)) hsq
  have hι' : ι' ≫ (t.G.hom ⁻¹ᵁ U.1).ι = ι := sq.lift_fst _ _ _
  have hw : ι' ≫ ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom : (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) =
      A.hom ≫ spMap (Ideal.Quotient.mk m) := sq.lift_snd _ _ _
  have hpb' : IsPullback ι' A.hom (Over.mk ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom :
      (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1))).hom (spMap (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m))) :=
    IsPullback.of_right (by rw [hι']; exact hpb) hw sq
  obtain ⟨Φ, hlin, hinj, hsurj, hnat⟩ := GlobalTheory.T.cech_comparison_structure_h1_affine X t.G.left t.G.hom t.semi.separated U J W hWa hcov hWU
  have h0 := hnat _ (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m)) A.left A.hom ι ι' hι' hpb'.w c hc hcob
  have hmem := GlobalTheory.T.structure_h1_nakayama_closed_fibre _ _ hAb m hm A.left A.hom ι' hpb' (Φ c) h0
  obtain ⟨N, r, y, hr, hy⟩ := exists_fin_sum m _ hmem
  choose e he hΦe using hsurj
  let ρ : ∀ i i' : J, Γ(X, U.1) →+* Γ(t.G.left, W i ⊓ W i') := fun i i' =>
    (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom
  let c' : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i') := fun i i' => c i i' - ∑ k, ρ i i' (r k) * e (y k) i i'
  have hc' : (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c' i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c' i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c' i i'')) := by
    intro i i' i''
    simp only [c', ρ, map_sub, map_sum, map_mul, resG_appLE']
    rw [← hc i i' i'']
    have := fun k => he (y k) i i' i''
    simp only [← this, mul_add, Finset.sum_add_distrib]
    ring
  have hΦ : Φ c' = 0 := by
    rw [hlin c hc N r (fun k => e (y k)) (fun k => he (y k))]
    simp only [hΦe, ← hy, sub_self]
  obtain ⟨h, hh⟩ := hinj c' hc' hΦ
  refine ⟨h, N, r, fun k => e (y k), hr, fun k => he (y k), fun i i' => ?_⟩
  have := hh i i'
  simp only [c'] at this
  rw [sub_eq_iff_eq_add] at this
  exact this

end GlobalTheory.CechBCInj
