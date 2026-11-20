import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCorrFormPullTensorForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimensionStatement

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.FrobAdjoint

/- English proof (translation)
Introduce `p _ k _ _ hk A _ _ hA σ V m hσ hV y hy`. Take `⟨e, he, -⟩` from `GlobalTheory.deRhamVectorExtension p`. Establish `hn : IsNilpotent (p : k)` using `⟨1, by rw [pow_one, hk]⟩`. Take `⟨g, hg⟩ : ∃ g, SmoothOfRelativeDimension g A.hom` from `GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA`. Take `⟨G, t, -⟩` from `GlobalTheory.AbelianTower.exists_pDivGroup_tower p k hn A g hA hg`.

Set `A₁` to `(Over.pullback (spMap (frobR p k hk))).obj A`. Establish `hπ : IsGrpPullback A₁ A _ _` using `isGrpPullback_pullback A (spMap (frobR p k hk))`. Establish `hA₁ : IsAbelianScheme A₁` using `isAbelianScheme_pullback_obj _ A hA`. Take `⟨F, hFm, hF⟩` from `GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP p k hk A A₁ _ hπ`. Take `⟨t₁, ht⟩` from `exists_tower hk t hπ`.

Establish `mπ` using `grpMor_of_isGrpPullback hπ`. Establish `hid : (frobR p k hk).comp σ = RingHom.id k` using `RingHom.ext fun x => (frobR_apply p k hk _).trans (hσ x)`. Establish `hb : spMap (frobR p k hk) ≫ spMap σ = 𝟙 _` using `by rw [← GlobalTheory.Cris.spMap_comp, hid, GlobalTheory.Cris.spMap_id]`. Establish `mc` using `m.comp mπ`. Set `V₁ : A₁ ⟶ A` to `Over.homMk (_ ≫ V) (mc.w.trans (by rw [hb, Category.comp_id]))`.

Establish `hm : IsMonHom V₁` using `isMonHom_of_mul _ fun T x x' => by`. Establish `hw : (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) = T.hom` using `by rw [hb, Category.comp_id]`. Set `j : Over.mk (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) ⟶ T` to `Over.homMk (𝟙 _) (by simpa using hw.symm)`. Establish `h` using `mc.mul T x x' (j ≫ x ≫ V₁) (j ≫ x' ≫ V₁) (by simp [j, V₁]) (by simp [j, V₁])`. Rewrite `h` using `[← MonObj.comp_mul]`.

Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Simplify `h.symm` using `[j, V₁]`. Establish `hFV : F ≫ V₁ = 𝟙 A ^ p` using `Over.OverMorphism.ext (by`. Express the relevant statement in the definitionally equal form `F.left ≫ _ ≫ V = _`. Rewrite using `[← Category.assoc, hF, hV])`.

Establish `h0 : primPull (dp0 k) (𝟙 _) V₁ y = 0`. Establish `h1` using `GrpMor.pull_pull m mπ (homMor (dp0 k) (𝟙 _) V₁) (fun r => RingHom.congr_fun hid r) rfl y`. Rewrite `h1` using `[hy, map_zero]`. Conclude with `h1.symm`. Establish `h1 : rigExtMap (verschiebung hk G) (e hn hA t y) = 0`.

Rewrite using `[← map_eq_verschiebung hk t t₁ ht F V₁ hF hFV, ← he.primPull hn hA₁ hA t₁ t, h0, map_zero]`. Take `⟨-, -, -, -, -, h2, h3⟩` from `rigExt_field_of_charP p k hk G`. Establish `h4 : e hn hA t y ∈ Submodule.span k (Set.range (absFrob hk G).rig)` using `h3 ▸ h2 ▸ h1`. Establish `h5 : ∀ z, e hn hA t (frobDR p k hk A z) = (absFrob hk G).rig (e hn hA t z)` using `fun z => by`. Rewrite using `[(t.eq_semiOf_iff t (frobMor p k hk A (cast_left p k hk A)) (absFrob hk G)).2 (absFrob_y hk t)]`.

Conclude with `he hn hn hA hA t t _ z`. Establish `h6 : ∀ u ∈ Submodule.span k (Set.range (absFrob hk G).rig), ∃ z, e hn hA t (frobDR p k hk A z) = u` using `fun u hu => by`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨v, rfl⟩` from `hu`.

Conclude with `⟨(e hn hA t).symm v, by rw [h5, LinearEquiv.apply_symm_apply]⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨a, rfl⟩` from `hu`. Take `⟨b, rfl⟩` from `hv`.

Conclude with `⟨a + b, by rw [map_add, map_add]⟩`. Consider the case `smul l u _ hu`. Take `⟨a, rfl⟩` from `hu`. Take `⟨r, rfl⟩` from `IsAlgClosed.exists_pow_nat_eq l (Fact.out : p.Prime).pos`. Conclude with `⟨r • a, by rw [map_smulₛₗ, map_smul, frobR_apply]⟩`.

Take `⟨z, hz⟩` from `h6 _ h4`. Conclude with `⟨z, (e hn hA t).injective hz⟩`.
-/
theorem UpperTheory.Gal.Ord.rankV :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k) (V : A.left ⟶ A.left) (m : SMor A σ V), (∀ x, σ x ^ p = x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ V = ((𝟙 A) ^ p : A ⟶ A).left → ∀ y, m.pull y = 0 → ∃ z, frobDR p k hk A z = y := by
  intro p _ k _ _ hk A _ _ hA σ V m hσ hV y hy
  obtain ⟨e, he, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hn : IsNilpotent (p : k) := ⟨1, by rw [pow_one, hk]⟩
  obtain ⟨g, hg⟩ : ∃ g, SmoothOfRelativeDimension g A.hom := GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA
  obtain ⟨G, t, -⟩ := GlobalTheory.AbelianTower.exists_pDivGroup_tower p k hn A g hA hg
  let A₁ := (Over.pullback (spMap (frobR p k hk))).obj A
  have hπ : IsGrpPullback A₁ A _ _ := isGrpPullback_pullback A (spMap (frobR p k hk))
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj _ A hA
  obtain ⟨F, hFm, hF⟩ := GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP p k hk A A₁ _ hπ
  obtain ⟨t₁, ht⟩ := exists_tower hk t hπ
  have mπ := grpMor_of_isGrpPullback hπ
  have hid : (frobR p k hk).comp σ = RingHom.id k := RingHom.ext fun x => (frobR_apply p k hk _).trans (hσ x)
  have hb : spMap (frobR p k hk) ≫ spMap σ = 𝟙 _ := by rw [← GlobalTheory.Cris.spMap_comp, hid, GlobalTheory.Cris.spMap_id]
  have mc := m.comp mπ
  let V₁ : A₁ ⟶ A := Over.homMk (_ ≫ V) (mc.w.trans (by rw [hb, Category.comp_id]))
  have hm : IsMonHom V₁ := isMonHom_of_mul _ fun T x x' => by
    have hw : (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) = T.hom := by rw [hb, Category.comp_id]
    let j : Over.mk (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) ⟶ T := Over.homMk (𝟙 _) (by simpa using hw.symm)
    have h := mc.mul T x x' (j ≫ x ≫ V₁) (j ≫ x' ≫ V₁) (by simp [j, V₁]) (by simp [j, V₁])
    rw [← MonObj.comp_mul] at h
    refine Over.OverMorphism.ext ?_
    simpa [j, V₁] using h.symm
  have hFV : F ≫ V₁ = 𝟙 A ^ p := Over.OverMorphism.ext (by
    change F.left ≫ _ ≫ V = _
    rw [← Category.assoc, hF, hV])
  have h0 : primPull (dp0 k) (𝟙 _) V₁ y = 0 := by
    have h1 := GrpMor.pull_pull m mπ (homMor (dp0 k) (𝟙 _) V₁) (fun r => RingHom.congr_fun hid r) rfl y
    rw [hy, map_zero] at h1
    exact h1.symm
  have h1 : rigExtMap (verschiebung hk G) (e hn hA t y) = 0 := by
    rw [← map_eq_verschiebung hk t t₁ ht F V₁ hF hFV, ← he.primPull hn hA₁ hA t₁ t, h0, map_zero]
  obtain ⟨-, -, -, -, -, h2, h3⟩ := rigExt_field_of_charP p k hk G
  have h4 : e hn hA t y ∈ Submodule.span k (Set.range (absFrob hk G).rig) := h3 ▸ h2 ▸ h1
  have h5 : ∀ z, e hn hA t (frobDR p k hk A z) = (absFrob hk G).rig (e hn hA t z) := fun z => by
    rw [(t.eq_semiOf_iff t (frobMor p k hk A (cast_left p k hk A)) (absFrob hk G)).2 (absFrob_y hk t)]
    exact he hn hn hA hA t t _ z
  have h6 : ∀ u ∈ Submodule.span k (Set.range (absFrob hk G).rig), ∃ z, e hn hA t (frobDR p k hk A z) = u := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      exact ⟨(e hn hA t).symm v, by rw [h5, LinearEquiv.apply_symm_apply]⟩
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      exact ⟨a + b, by rw [map_add, map_add]⟩
    | smul l u _ hu =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨r, rfl⟩ := IsAlgClosed.exists_pow_nat_eq l (Fact.out : p.Prime).pos
      exact ⟨r • a, by rw [map_smulₛₗ, map_smul, frobR_apply]⟩
  obtain ⟨z, hz⟩ := h6 _ h4
  exact ⟨z, (e hn hA t).injective hz⟩
