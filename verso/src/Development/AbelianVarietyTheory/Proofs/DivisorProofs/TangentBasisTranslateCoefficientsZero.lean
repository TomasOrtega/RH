import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartValueTranslateProdTangentsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VertSpanZero

/- English proof (translation)
The claim follows from `GlobalTheory.T.eps_part_value_translate_prod_tangents`.
-/
theorem snd_valR_mul_prod : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (g' : tEpsG (g ≫ G.hom) ⟶ G), g'.left = spMap (algebraMap S (DualNumber S)) ≫ g → ∀ (n : ℕ) (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G)), (∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) → ∀ (O : G.left.Opens), ⊤ ≤ g ⁻¹ᵁ O → ∀ f : Γ(G.left, O), (valR (g' * (List.ofFn u).prod).left O f).snd = ∑ a, (valR (g' * u a).left O f).snd := GlobalTheory.T.eps_part_value_translate_prod_tangents

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

/- English proof (translation)
Use `⟨fun _ => 1, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `show (1 : tEpsG x ⟶ t.G).left = spMap (epsMul 0) ≫ e i`. Rewrite using `[epsMul_zero', spMap_comp_eq, Category.assoc, (he i).2]`. Set `k : tEpsG x ⟶ Over.mk x` to `Over.homMk (spMap (algebraMap S (DualNumber S))) rfl`. Conclude with `congrArg CommaMorphism.left (MonObj.comp_one k).symm`.

Simplify using the standard rewrite rules.
-/
theorem isCombAtG_zero {S : Type} [CommRing S] (x : Sp S ⟶ X) {n : ℕ} (e : Fin n → (Sp (DualNumber S) ⟶ t.G.left))
    (he : ∀ i, IsTanAtG t x (e i)) : IsCombAtG t x e 0 (1 : tEpsG x ⟶ t.G).left := by
  refine ⟨fun _ => 1, fun i => ?_, ?_⟩
  · show (1 : tEpsG x ⟶ t.G).left = spMap (epsMul 0) ≫ e i
    rw [epsMul_zero', spMap_comp_eq, Category.assoc, (he i).2]
    let k : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
    exact congrArg CommaMorphism.left (MonObj.comp_one k).symm
  · simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.w (1 : tEpsG x ⟶ t.G), congrArg CommaMorphism.left (MonObj.comp_one (redOver x))⟩`.
-/
theorem isTanAtG_one {S : Type} [CommRing S] (x : Sp S ⟶ X) : IsTanAtG t x (1 : tEpsG x ⟶ t.G).left :=
  ⟨Over.w (1 : tEpsG x ⟶ t.G), congrArg CommaMorphism.left (MonObj.comp_one (redOver x))⟩

/- English proof (translation)
Establish `e1 : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ`. Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `e2 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom`. Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Category.assoc, hv.1, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e2, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hv.2]`. Set `k : Over.mk (spMap φ ≫ x) ⟶ Over.mk x` to `Over.homMk (spMap φ) rfl`. Conclude with `congrArg CommaMorphism.left (MonObj.comp_one k)`.
-/
theorem isTanAtG_bc {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X}
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) : IsTanAtG t (spMap φ ≫ x) (spMap (dualMap φ) ≫ v) := by
  have e1 : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have e2 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  constructor
  · rw [Category.assoc, hv.1, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e2, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hv.2]
    let k : Over.mk (spMap φ ≫ x) ⟶ Over.mk x := Over.homMk (spMap φ) rfl
    exact congrArg CommaMorphism.left (MonObj.comp_one k)

/- English proof (translation)
Establish `hB2` using `hB.2 S φ`. Rewrite `hB2` using `[← hy]`. Establish `hT : ∀ i, IsTanAtG t (y ≫ t.G.hom) (spMap (dualMap φ) ≫ v i)` using `fun i => hy ▸ isTanAtG_bc t φ (hB.1 i)`. Set `g' : tEpsG (y ≫ t.G.hom) ⟶ t.G` to `Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ y) (Category.assoc _ _ _)`. Establish `hwt' : ∀ a, ∃ g₁ v₁ : tEpsG (y ≫ t.G.hom) ⟶ t.G, g₁.left = spMap (algebraMap S (DualNumber S)) ≫ y ∧ v₁.left = spMap (dualMap φ) ≫ v a ∧ (g₁ * v₁).left = wt a` using `hwt`.

Use `choose g₁ v₁ hg₁ hv₁ hw₁ using hwt'`. Establish `hg₁' : ∀ a, g₁ a = g'` using `fun a => Over.OverMorphism.ext (hg₁ a)`. Establish `ek : ∀ a, spMap (epsMul (d a)) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S))` using `fun a => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, epsMul_comp_algebraMap]`. Set `k : Fin n → (tEpsG (y ≫ t.G.hom) ⟶ tEpsG (y ≫ t.G.hom))` to `fun a => Over.homMk (spMap (epsMul (d a))) (by`. Express the relevant statement in the definitionally equal form `_ ≫ spMap (algebraMap S (DualNumber S)) ≫ y ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y ≫ t.G.hom`.

Rewrite using `[← Category.assoc, ek])`. Establish `hkg : ∀ a, k a ≫ g' = g'` using `fun a => Over.OverMorphism.ext (by`. Express the relevant statement in the definitionally equal form `spMap (epsMul (d a)) ≫ spMap (algebraMap S (DualNumber S)) ≫ y = spMap (algebraMap S (DualNumber S)) ≫ y`. Rewrite using `[← Category.assoc, ek])`. Set `u : Fin n → (tEpsG (y ≫ t.G.hom) ⟶ t.G)` to `fun a => k a ≫ v₁ a`.

Establish `hul : ∀ a, (u a).left = spMap (epsMul (d a)) ≫ spMap (dualMap φ) ≫ v a` using `fun a => by`. Express the relevant statement in the definitionally equal form `spMap (epsMul (d a)) ≫ (v₁ a).left = _`. Rewrite using `[hv₁ a]`. Establish `hu : ∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (y ≫ t.G.hom) ⟶ t.G).left` using `fun a => by`. Rewrite using `[hul a, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_epsMul]`.

Conclude with `(hT a).2`. Establish `hmul : ∀ a, (g' * u a).left = spMap (epsMul (d a)) ≫ wt a` using `fun a => by`. Rewrite using `[← hw₁ a, hg₁' a]`. Express the relevant statement in the definitionally equal form `(g' * (k a ≫ v₁ a)).left = (k a ≫ (g' * v₁ a)).left`. Rewrite using `[MonObj.comp_mul, hkg a]`.

Establish `hwtV : ∀ a, ⊤ ≤ wt a ⁻¹ᵁ V` using `fun a => GlobalTheory.CechKS.le_preimage_of_red (GlobalTheory.LogKSLin.translate_red (hB.1 a) hy (hwt a)) hyV`. Establish `hred` using `red_mul_prod y g' rfl u hu`. Establish `hTV` using `GlobalTheory.CechKS.le_preimage_of_red hred hyV`. Establish `hg'V : ⊤ ≤ g'.left ⁻¹ᵁ V` using `GlobalTheory.Points.le_preimage_comp (spMap (algebraMap S (DualNumber S))) y hyV (GlobalTheory.Points.le_preimage_top _)`. Establish `hsnd : ∀ f, (valR (g' * (List.ofFn u).prod).left V f).snd = 0` using `fun f => by`.

Rewrite using `[snd_valR_mul_prod _ t.G S y g' rfl n u hu V hyV f]`. Repeatedly rewrite using `[hmul, fun a => snd_valR_epsMul (wt a) V (hwtV a) (d a) f]`. Conclude with `hd f`. Establish `hval : ∀ f, valR (g' * (List.ofFn u).prod).left V f = valR g'.left V f` using `fun f => by`. Establish `h1` using `GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom S S S).toRingHom _ V hTV f`.

Rewrite `h1` using `[hred]`. Establish `h2 : valR g'.left V f = algebraMap S (DualNumber S) (valR y V f)` using `GlobalTheory.Points.valR_spMap_comp (algebraMap S (DualNumber S)) y V hyV f`. Rewrite using `[h2]`. Use `ext`. Simplify `h1.symm` using `[TrivSqZeroExt.algebraMap_eq_inl]`.

Simplify `hsnd f` using `[TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hTeq` using `GlobalTheory.Points.ext_of_valR hV hTV hg'V hval`. Establish `hP : (List.ofFn u).prod = 1` using `mul_eq_left.mp (Over.OverMorphism.ext hTeq)`. Establish `hc1 : IsCombAtG t (y ≫ t.G.hom) (fun i => spMap (dualMap φ) ≫ v i) d (1 : tEpsG (y ≫ t.G.hom) ⟶ t.G).left` using `⟨u, hul, by rw [hP]⟩`. Conclude with `(hB2 _ (isTanAtG_one t _)).unique hc1 (isCombAtG_zero t _ _ hT)`.
-/
theorem coeffs_zero_at (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (hB : GlobalTheory.LineNorm.IsTanBasis t (chart U) v) {S : Type} [CommRing S] (y : Sp S ⟶ t.G.left)
    (φ : Γ(X, U.1) →+* S) (hy : y ≫ t.G.hom = spMap φ ≫ chart U) (wt : Fin n → (Sp (DualNumber S) ⟶ t.G.left))
    (hwt : ∀ a, IsTranslate t φ y (v a) (wt a)) (V : t.G.left.Opens) (hV : IsAffineOpen V) (hyV : ⊤ ≤ y ⁻¹ᵁ V)
    (d : Fin n → S) (hd : ∀ f : Γ(t.G.left, V), ∑ a, d a * (valR (wt a) V f).snd = 0) : d = 0 := by
  have hB2 := hB.2 S φ
  rw [← hy] at hB2
  have hT : ∀ i, IsTanAtG t (y ≫ t.G.hom) (spMap (dualMap φ) ≫ v i) := fun i => hy ▸ isTanAtG_bc t φ (hB.1 i)
  let g' : tEpsG (y ≫ t.G.hom) ⟶ t.G := Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ y) (Category.assoc _ _ _)
  have hwt' : ∀ a, ∃ g₁ v₁ : tEpsG (y ≫ t.G.hom) ⟶ t.G, g₁.left = spMap (algebraMap S (DualNumber S)) ≫ y ∧
      v₁.left = spMap (dualMap φ) ≫ v a ∧ (g₁ * v₁).left = wt a := hwt
  choose g₁ v₁ hg₁ hv₁ hw₁ using hwt'
  have hg₁' : ∀ a, g₁ a = g' := fun a => Over.OverMorphism.ext (hg₁ a)
  have ek : ∀ a, spMap (epsMul (d a)) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) :=
    fun a => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, epsMul_comp_algebraMap]
  let k : Fin n → (tEpsG (y ≫ t.G.hom) ⟶ tEpsG (y ≫ t.G.hom)) := fun a =>
    Over.homMk (spMap (epsMul (d a))) (by
      change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ y ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y ≫ t.G.hom
      rw [← Category.assoc, ek])
  have hkg : ∀ a, k a ≫ g' = g' := fun a => Over.OverMorphism.ext (by
    change spMap (epsMul (d a)) ≫ spMap (algebraMap S (DualNumber S)) ≫ y = spMap (algebraMap S (DualNumber S)) ≫ y
    rw [← Category.assoc, ek])
  let u : Fin n → (tEpsG (y ≫ t.G.hom) ⟶ t.G) := fun a => k a ≫ v₁ a
  have hul : ∀ a, (u a).left = spMap (epsMul (d a)) ≫ spMap (dualMap φ) ≫ v a := fun a => by
    change spMap (epsMul (d a)) ≫ (v₁ a).left = _
    rw [hv₁ a]
  have hu : ∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left =
      (1 : Over.mk (y ≫ t.G.hom) ⟶ t.G).left := fun a => by
    rw [hul a, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_epsMul]
    exact (hT a).2
  have hmul : ∀ a, (g' * u a).left = spMap (epsMul (d a)) ≫ wt a := fun a => by
    rw [← hw₁ a, hg₁' a]
    change (g' * (k a ≫ v₁ a)).left = (k a ≫ (g' * v₁ a)).left
    rw [MonObj.comp_mul, hkg a]
  have hwtV : ∀ a, ⊤ ≤ wt a ⁻¹ᵁ V := fun a =>
    GlobalTheory.CechKS.le_preimage_of_red (GlobalTheory.LogKSLin.translate_red (hB.1 a) hy (hwt a)) hyV
  have hred := red_mul_prod y g' rfl u hu
  have hTV := GlobalTheory.CechKS.le_preimage_of_red hred hyV
  have hg'V : ⊤ ≤ g'.left ⁻¹ᵁ V :=
    GlobalTheory.Points.le_preimage_comp (spMap (algebraMap S (DualNumber S))) y hyV (GlobalTheory.Points.le_preimage_top _)
  have hsnd : ∀ f, (valR (g' * (List.ofFn u).prod).left V f).snd = 0 := fun f => by
    rw [snd_valR_mul_prod _ t.G S y g' rfl n u hu V hyV f]
    simp_rw [hmul, fun a => snd_valR_epsMul (wt a) V (hwtV a) (d a) f]
    exact hd f
  have hval : ∀ f, valR (g' * (List.ofFn u).prod).left V f = valR g'.left V f := fun f => by
    have h1 := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom S S S).toRingHom _ V hTV f
    rw [hred] at h1
    have h2 : valR g'.left V f = algebraMap S (DualNumber S) (valR y V f) :=
      GlobalTheory.Points.valR_spMap_comp (algebraMap S (DualNumber S)) y V hyV f
    rw [h2]
    ext
    · simpa [TrivSqZeroExt.algebraMap_eq_inl] using h1.symm
    · simpa [TrivSqZeroExt.algebraMap_eq_inl] using hsnd f
  have hTeq := GlobalTheory.Points.ext_of_valR hV hTV hg'V hval
  have hP : (List.ofFn u).prod = 1 := mul_eq_left.mp (Over.OverMorphism.ext hTeq)
  have hc1 : IsCombAtG t (y ≫ t.G.hom) (fun i => spMap (dualMap φ) ≫ v i) d (1 : tEpsG (y ≫ t.G.hom) ⟶ t.G).left :=
    ⟨u, hul, by rw [hP]⟩
  exact (hB2 _ (isTanAtG_one t _)).unique hc1 (isCombAtG_zero t _ _ hT)

end GlobalTheory.VertSpanZero

open GlobalTheory.VertSpanZero in

/- English proof (translation)
Introduce `E _ _ _ H X t U n v hv hb S _ g₀ W hWU hg₀ c hc`. Establish `hB` using `GlobalTheory.LineNorm.isTanBasis_of_basis E H X t Γ(X, U.1) (chart U) n v hv hb`. Establish `key : ∀ (J : Ideal S) (_ : J.IsMaximal) (a : Fin n), algebraMap S (Localization.AtPrime J) (c a) = 0`. Introduce `J _`. Set `ρ` to `algebraMap S (Localization.AtPrime J)`.

Establish `hyW : ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ W` using `GlobalTheory.Points.le_preimage_comp (spMap ρ) g₀ hg₀ (GlobalTheory.Points.le_preimage_top _)`. Take `⟨V, hVa, hzV, hVW⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp t.G.left.isBasis_affineOpens) (show (spMap ρ ≫ g₀).base (IsLocalRing.closedPoint (Localization.AtPrime J)) ∈ W from hyW trivial)`. Establish `hyV` using `le_preimage_of_closedPoint (spMap ρ ≫ g₀) V hzV`. Establish `hyU : ⊤ ≤ ((spMap ρ ≫ g₀) ≫ t.G.hom) ⁻¹ᵁ U.1` using `GlobalTheory.Points.le_preimage_comp _ t.G.hom (hVW.trans hWU) hyV`. Set `φ : Γ(X, U.1) →+* Localization.AtPrime J` to `(GlobalTheory.Points.valMap _ U.1 hyU).hom`.

Establish `hy : (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ ≫ chart U` using `(GlobalTheory.Points.specMap_valMap_fromSpec U.2 _ hyU).symm`. Establish `hex` using `fun a => (existsUnique_isTranslate t φ hy (hv a)).exists`. Use `choose wt hwt using hex`. Use `coeffs_zero_at t U v hB (spMap ρ ≫ g₀) φ hy wt hwt V hVa hyV (fun a => ρ (c a)) (hc _ ρ φ wt hy hwt V hVW hyV)` as an intermediate fact. Conclude with `fun a => congrFun this a`.

Use function extensionality and compare the values at `a`. Conclude with `eq_zero_of_localization (c a) fun J hJ => key J hJ a`.
-/
theorem GlobalTheory.VertSpan.coeffs_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left) (W : t.G.left.Opens), W ≤ t.G.hom ⁻¹ᵁ U.1 → ⊤ ≤ g₀ ⁻¹ᵁ W → ∀ c : Fin n → S, (∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), ∑ a, ρ (c a) * (valR (wt a) O f).snd = 0) → c = 0 := by
  intro E _ _ _ H X t U n v hv hb S _ g₀ W hWU hg₀ c hc
  have hB := GlobalTheory.LineNorm.isTanBasis_of_basis E H X t Γ(X, U.1) (chart U) n v hv hb
  have key : ∀ (J : Ideal S) (_ : J.IsMaximal) (a : Fin n), algebraMap S (Localization.AtPrime J) (c a) = 0 := by
    intro J _
    let ρ := algebraMap S (Localization.AtPrime J)
    have hyW : ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ W :=
      GlobalTheory.Points.le_preimage_comp (spMap ρ) g₀ hg₀ (GlobalTheory.Points.le_preimage_top _)
    obtain ⟨V, hVa, hzV, hVW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp t.G.left.isBasis_affineOpens)
      (show (spMap ρ ≫ g₀).base (IsLocalRing.closedPoint (Localization.AtPrime J)) ∈ W from hyW trivial)
    have hyV := le_preimage_of_closedPoint (spMap ρ ≫ g₀) V hzV
    have hyU : ⊤ ≤ ((spMap ρ ≫ g₀) ≫ t.G.hom) ⁻¹ᵁ U.1 :=
      GlobalTheory.Points.le_preimage_comp _ t.G.hom (hVW.trans hWU) hyV
    let φ : Γ(X, U.1) →+* Localization.AtPrime J := (GlobalTheory.Points.valMap _ U.1 hyU).hom
    have hy : (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ ≫ chart U :=
      (GlobalTheory.Points.specMap_valMap_fromSpec U.2 _ hyU).symm
    have hex := fun a => (existsUnique_isTranslate t φ hy (hv a)).exists
    choose wt hwt using hex
    have := coeffs_zero_at t U v hB (spMap ρ ≫ g₀) φ hy wt hwt V hVa hyV (fun a => ρ (c a))
      (hc _ ρ φ wt hy hwt V hVW hyV)
    exact fun a => congrFun this a
  funext a
  exact eq_zero_of_localization (c a) fun J hJ => key J hJ a
