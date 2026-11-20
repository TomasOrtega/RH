import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTranslateCoefficientsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompProdOfFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TranslGerm

open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res valR_comp)

/- English proof (translation)
Take `⟨g₀, hg₀⟩ : ∃ g₀, g₀ = z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left` from `⟨_, rfl⟩`. Establish `hg₀O : ⊤ ≤ g₀ ⁻¹ᵁ O` using `by rw [hg₀]; exact hz`. Take `⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : DualNumber S →+* C, z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left = spMap ψ₀` from `⟨(Spec.preimage (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left)).hom, (Spec.map_preimage _).symm⟩`. Set `ψ : DualNumber Γ(X, U.1) →+* C` to `ψ₀.comp (dualMap φ)`. Establish `hd : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) = (algebraMap S (DualNumber S)).comp φ`.

Apply the tactic sequence `apply RingHom.ext; intro s; ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hbase : g₀ ≫ t.G.hom = spMap (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) ≫ chart U`. Establish `e1 : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ t.G.hom = (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ (tEpsG (spMap φ ≫ chart U)).hom` using `(Over.w _).trans (Over.w _).symm`. Rewrite using `[hg₀, Category.assoc, e1, ← Category.assoc, hψ₀]`. Use `show spMap ψ₀ ≫ spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ chart U = _`.

Rewrite using `[← Category.assoc, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, GlobalTheory.KSLin.spMap_comp_spMap]`. Use `congr 2`. Simplify using `only [ψ, RingHom.comp_assoc, hd]`. Set `a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U)` to `Over.homMk (spMap ψ) (by show spMap ψ ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom`. Rewrite using `[hbase, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap])`.

Use `choose w hw using fun b => (existsUnique_isTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) hbase (hv b)).exists`. Take `⟨h1, h2⟩` from `GlobalTheory.FirstOrderValue.valR_mul_comb E H X t U n v hv r x hx C ψ g₀ a w rfl hw O f hg₀O`. Set `zO : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (spMap φ ≫ chart U) ⊗ t.G` to `Over.homMk z (by show z ≫ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).hom = g₀ ≫ t.G.hom`. Rewrite using `[hg₀, ← Over.w (snd (tEpsG (spMap φ ≫ chart U)) t.G), Category.assoc])`. Establish `hzs : zO ≫ snd (tEpsG (spMap φ ≫ chart U)) t.G = (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)` using `Over.OverMorphism.ext hg₀.symm`.

Establish `hzf : zO ≫ fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P = a ≫ x`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ P.left = spMap ψ ≫ x.left`. Rewrite using `[hP, ← Category.assoc, hψ₀, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap]`. Establish `hτ : zO ≫ lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G] = (a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)`.

Rewrite using `[← Category.assoc, comp_lift, hzs, hzf]`. Both sides reduce to the same expression. Establish `hτl : z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left = ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left` using `congrArg Over.Hom.left hτ`. Rewrite using `[hτl, ← hg₀]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[h2, hψ₀]`. Use `congr 1`. Establish `hε : ψ DualNumber.eps = ψ₀ DualNumber.eps` using `by simp [ψ, dualMap]`. Establish `hsp : valR (spMap ψ₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) = ψ₀ DualNumber.eps` using `GlobalTheory.Points.valR_specMap (CommRingCat.ofHom ψ₀) _`. Rewrite using `[hsp, ← hε, valR_eq _ _ hg₀O, map_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← valR_eq _ _ hg₀O, ← valR_eq _ _ hg₀O, GlobalTheory.LogKSLin.valR_base U hO hbase hg₀O, hδv b O hO f C _ g₀ (w b) hbase hg₀O (hw b)]`. Both sides reduce to the same expression.
-/
theorem point_formula {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {U : X.affineOpens} {n : ℕ} {v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)}
    (hv : ∀ a, IsTanAtG t (chart U) (v a))
    {δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)}
    (hδv : ∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S]
      (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left),
      g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w →
      valR g₀ O (δ a O f) = (valR w O f).snd)
    {r : Fin n → Γ(X, U.1)} {x : tEpsG (chart U) ⟶ t.G} (hx : IsCombAtG t (chart U) v r x.left)
    {S : Type} [CommRing S] {φ : Γ(X, U.1) →+* S} {P : tEpsG (spMap φ ≫ chart U) ⟶ t.G}
    (hP : P.left = spMap (dualMap φ) ≫ x.left) {O : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1)
    (f : Γ(t.G.left, O)) {C : Type} [CommRing C] (z : Sp C ⟶ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left)
    (hz : ⊤ ≤ z ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O)) :
    ⊤ ≤ (z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
        μ[t.G]).left) ⁻¹ᵁ O ∧
    valR (z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
        μ[t.G]).left) O f =
      valR (z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left) O f +
      valR (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left) ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) *
        valR (z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left) O
          (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by

  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left := ⟨_, rfl⟩
  have hg₀O : ⊤ ≤ g₀ ⁻¹ᵁ O := by rw [hg₀]; exact hz
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : DualNumber S →+* C, z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left = spMap ψ₀ :=
    ⟨(Spec.preimage (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left)).hom, (Spec.map_preimage _).symm⟩
  let ψ : DualNumber Γ(X, U.1) →+* C := ψ₀.comp (dualMap φ)
  have hd : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) = (algebraMap S (DualNumber S)).comp φ := by
    apply RingHom.ext; intro s; ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hbase : g₀ ≫ t.G.hom = spMap (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) ≫ chart U := by
    have e1 : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ t.G.hom =
        (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ (tEpsG (spMap φ ≫ chart U)).hom :=
      (Over.w _).trans (Over.w _).symm
    rw [hg₀, Category.assoc, e1, ← Category.assoc, hψ₀]
    show spMap ψ₀ ≫ spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ chart U = _
    rw [← Category.assoc, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, GlobalTheory.KSLin.spMap_comp_spMap]
    congr 2
    simp only [ψ, RingHom.comp_assoc, hd]
  let a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U) := Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom
    rw [hbase, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap])
  choose w hw using fun b => (existsUnique_isTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))))
    hbase (hv b)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.FirstOrderValue.valR_mul_comb E H X t U n v hv r x hx C ψ g₀ a w rfl hw O f hg₀O

  let zO : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (spMap φ ≫ chart U) ⊗ t.G := Over.homMk z (by
    show z ≫ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).hom = g₀ ≫ t.G.hom
    rw [hg₀, ← Over.w (snd (tEpsG (spMap φ ≫ chart U)) t.G), Category.assoc])
  have hzs : zO ≫ snd (tEpsG (spMap φ ≫ chart U)) t.G = (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) :=
    Over.OverMorphism.ext hg₀.symm
  have hzf : zO ≫ fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P = a ≫ x := by
    apply Over.OverMorphism.ext
    show z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ P.left = spMap ψ ≫ x.left
    rw [hP, ← Category.assoc, hψ₀, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap]
  have hτ : zO ≫ lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G] =
      (a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) := by
    rw [← Category.assoc, comp_lift, hzs, hzf]
    rfl
  have hτl : z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
      μ[t.G]).left = ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left :=
    congrArg Over.Hom.left hτ
  rw [hτl, ← hg₀]
  refine ⟨h1, ?_⟩
  rw [h2, hψ₀]
  congr 1
  have hε : ψ DualNumber.eps = ψ₀ DualNumber.eps := by simp [ψ, dualMap]
  have hsp : valR (spMap ψ₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) =
      ψ₀ DualNumber.eps := GlobalTheory.Points.valR_specMap (CommRingCat.ofHom ψ₀) _
  rw [hsp, ← hε, valR_eq _ _ hg₀O, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, ← valR_eq _ _ hg₀O, ← valR_eq _ _ hg₀O, GlobalTheory.LogKSLin.valR_base U hO hbase hg₀O,
    hδv b O hO f C _ g₀ (w b) hbase hg₀O (hw b)]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H X t U n v hv δ _ _ hδv r x hx S _ φ P hP O hO f y hy`. Establish `key` using `fun (C : Type) [CommRing C] z hz => point_formula hv hδv hx hP hO f (C := C) z hz`. Establish `hVτ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left ⁻¹ᵁ O`. Introduce `y' hy'`. Take `⟨W, hW, hyW, hWV⟩` from `exists_isAffineOpen_mem_and_subset hy'`.

Establish `hz : ⊤ ≤ hW.fromSpec ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O)` using `GlobalTheory.Points.le_preimage_mono _ hWV hW.fromSpec_preimage_self.ge`. Take `⟨p, rfl⟩ : y' ∈ Set.range hW.fromSpec` from `by rw [hW.range_fromSpec]; exact hyW`. Use `(key Γ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left, W) hW.fromSpec hz).1 (Set.mem_univ p)` as an intermediate fact. Conclude with `this`. Establish `hVπ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ ⊤` using `fun _ _ => trivial`.

Establish `hAB : ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVτ).op).hom (((lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left.app O).hom f) = ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom f + ((tEpsG (spMap φ ≫ ch …`. Use `GlobalTheory.CechInv.ext_of_valR _ _ _ fun C _ z hz => ?_` and prove the remaining obligations. Rewrite using `[valR_res _ hVτ hz, ← valR_comp, (key C z hz).2, valR_add _ _ hz, valR_mul _ _ hz, valR_res _ hVπ hz, ← valR_comp, ← valR_comp, ← valR_comp]`. Establish `hτy` using `hVτ hy`. Rewrite using `[gs_eq _ y O hτy, gs_eq _ y O hy, gs_eq _ y ⊤ trivial, gs_eq _ y O hy, ← TopCat.Presheaf.germ_res_apply _ (homOfLE hVτ) y hy, hAB, map_add, map_mul, TopCat.Presheaf.germ_res_apply _ (homOfLE hVπ) y hy]`.
-/
theorem transl_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (r : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v r x.left → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (P : tEpsG (spMap φ ≫ chart U) ⟶ t.G), P.left = spMap (dualMap φ) ≫ x.left → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (f : Γ(t.G.left, O)) (y : (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left), (snd (tEpsG (spMap φ ≫ chart U)) t.G).left.base y ∈ O → gs (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left y O f = gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O f + gs (fst (tEpsG (spMap φ ≫ chart U)) t.G).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) * gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
  intro E _ _ _ H X t U n v hv δ _ _ hδv r x hx S _ φ P hP O hO f y hy
  have key := fun (C : Type) [CommRing C] z hz => point_formula hv hδv hx hP hO f (C := C) z hz

  have hVτ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤
      (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left ⁻¹ᵁ O := by
    intro y' hy'
    obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hy'
    have hz : ⊤ ≤ hW.fromSpec ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O) :=
      GlobalTheory.Points.le_preimage_mono _ hWV hW.fromSpec_preimage_self.ge
    obtain ⟨p, rfl⟩ : y' ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have := (key Γ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left, W) hW.fromSpec hz).1 (Set.mem_univ p)
    exact this
  have hVπ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ ⊤ :=
    fun _ _ => trivial

  have hAB : ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVτ).op).hom
      (((lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left.app O).hom f) =
      ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom f +
      ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVπ).op).hom
        (((fst (tEpsG (spMap φ ≫ chart U)) t.G).left.app ⊤).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps)) *
      ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
    refine GlobalTheory.CechInv.ext_of_valR _ _ _ fun C _ z hz => ?_
    rw [valR_res _ hVτ hz, ← valR_comp, (key C z hz).2, valR_add _ _ hz, valR_mul _ _ hz, valR_res _ hVπ hz,
      ← valR_comp, ← valR_comp, ← valR_comp]
  have hτy := hVτ hy
  rw [gs_eq _ y O hτy, gs_eq _ y O hy, gs_eq _ y ⊤ trivial, gs_eq _ y O hy,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE hVτ) y hy, hAB, map_add, map_mul,
    TopCat.Presheaf.germ_res_apply _ (homOfLE hVπ) y hy]

end GlobalTheory.TranslGerm
