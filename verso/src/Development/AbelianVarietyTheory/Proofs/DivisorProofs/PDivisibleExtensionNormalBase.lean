import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOfLocalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderHopfComultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCartierDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualIntegralCounitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfGenericPolarizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPrechartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTorsionPrechartCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSpreadsOutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairingFunctorialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFunctionsGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFunctionDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderFiniteProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderComultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderHopfIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfHopfOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureHopfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianLocalPointDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDivisibilityMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDivisibilityCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureMultiplicationMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivisibleGroupModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleModelGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleModelUniqueIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePDivisibleEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinesCompAndMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleModelActionPolarizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOmegaComparisonNearZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaComparisonEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaRankOfTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentRankEqOmegaRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTypeExtendsAffineNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelPDivisibleExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelPDivisibleExtensionTateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleExtensionOfGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelPDivisiblePropertiesExtendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateExtensionSurjectivePointsStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

/- English proof (translation)
Introduce `hR hD hC E _ _ _ H Dw p _ X Z _ _ g tZ hX t₀ m₀ ht₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hP₀ U t m`. Use `haveI : CharZero (Kbar X) := ht₀.charZero`. Take `⟨⟨mK, hmK⟩, -⟩` from `GlobalTheory.sabMap_cancel_and_comp_over E H Z (Sp U.Bp) (Sp (Kbar X)) tZ t t₀ (U.toX ≫ g) (genPt X ≫ g) (spMap (algebraMap U.Bp (Kbar X))) m m₀ (by rw [← Category.assoc, AffOp.val_toX])`. Establish `hab₀ : abLocus t₀.G = Set.univ` using `Set.eq_univ_of_forall fun s K _ _ x _ => by haveI : IsProper t₀.G.hom := ht₀.1 infer_instance`. Establish `hbij₀ : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra (Kbar X) B], Function.Bijective (θ₀.pt n B)` using `fun n B _ _ => hP₀.interior n B (by rw [hab₀]; exact Set.subset_univ _)`.

Establish `hcard` using `GlobalTheory.T.card_tors_generic_fibre_eq_pow_mul_height p U.Bp (Kbar X) t.G t₀.G mK.φ mK.cart GG₀ θ₀ hbij₀`. Take `⟨GG, θ, hht, hθ⟩` from `GlobalTheory.T.exists_p_divisible_group_model p U.Bp (Kbar X) t.G t.semi GG₀.height hcard`. Take `⟨e, he⟩` from `GlobalTheory.T.p_divisible_model_unique_iso p U.Bp (Kbar X) t.G t.semi t₀.G mK.φ mK.cart GG θ hθ GG₀ θ₀ hbij₀`. Establish `hact` using `fun a : 𝓞 E => GlobalTheory.T.exists_unique_p_divisible_endomorphism p U.Bp (Kbar X) t.G t.semi GG θ hθ (t.act.act a) (t.act.hom a)`. Use `choose actF hactF hactU using hact`.

Take `⟨r1, r2, r3⟩` from `GlobalTheory.T.intertwines_comp_and_mul p U.Bp t.G GG θ`. Establish `h0 : actF 0 = 0`. Establish `e1 : actF 0 = actF 0 + actF 0` using `(hactU 0 _ (by`. Use `r3 _ _ _ _ (hactF 0) (hactF 0)` as an intermediate fact. Rewrite using `[← t.act.add, add_zero] at this)).symm` and apply the resulting hypothesis.

Conclude with `(left_eq_add.1 e1)`. Set `act : Action (𝓞 E) GG` to `{ toFun := actF map_one' := (hactU 1 (𝟙 GG) (by rw [t.act.one]; exact r1)).symm map_mul' := fun a b => by`. Use `(hactU (a * b) _ ?_).symm` and prove the remaining obligations. Rewrite using `[mul_comm a b, t.act.mul]`. Conclude with `r2 _ _ _ _ (hactF b) (hactF a)`.

Use the proof step `map_zero' := h0`. Use the proof step `map_add' := fun a b => (hactU (a + b) _ (by rw [t.act.add]; exact r3 _ _ _ _ (hactF a) (hactF b))).symm }`. Establish `hactI : ∀ a, θ.Intertwines (t.act.act a) (act a)` using `hactF`. Take `⟨φ, hφ⟩` from `GlobalTheory.T.pel_p_divisible_extension E H Dw p U.Bp (Kbar X) t t₀ mK GG₀ act₀ pol₀ θ₀ ε₀ τ₀ ht₀ hP₀ GG θ e hθ he`. Use `haveI : CharZero U.Bp := (algebraMap U.Bp (Kbar X)).charZero`.

Establish `hnz : θ.IsOpenNearZero` using `fun n => by`. Take `⟨V, hV⟩` from `(hθ n).opn`. Use `⟨⊤, V, fun _ _ => trivial, fun B _ _ => ?_⟩` and prove the remaining obligations. Establish `h' : {z : Tors t.G (p ^ n) B | Set.range z.1.left ⊆ (⊤ : t.G.left.Opens)} = Set.univ` using `Set.eq_univ_of_forall fun z x _ => trivial`. Rewrite using `[h']`.

Conclude with `hV B`. Take `⟨c, hc⟩` from `GlobalTheory.T.exists_omega_comparison_near_zero p U.Bp t.G t.semi GG θ hnz`. Establish `hpr : IsProper (pullback.snd t.G.hom (spMap (algebraMap U.Bp (Kbar X))))` using `by haveI : IsProper t₀.G.hom := ht₀.1`. Establish `h' : pullback.snd t.G.hom (spMap (algebraMap U.Bp (Kbar X))) = mK.cart.1.isoPullback.inv ≫ t₀.G.hom`. Rewrite using `[Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]`.

Rewrite using `[h']`. Use `infer_instance`. Establish `h1` using `hcard 1`. Rewrite `h1` using `[pow_one, Nat.one_mul, hP₀.height]`. Establish `hrank` using `GlobalTheory.T.omega_rank_of_torsion_count U.Bp (Kbar X) t.G t.semi hpr p _ (Fact.out : p.Prime) h1`.

Establish `hdi : IsIso (dualHom _ _ e.inv)` using `⟨⟨dualHom _ _ e.hom, by rw [← dualHom_comp, e.hom_inv_id, dualHom_id], by rw [← dualHom_comp, e.inv_hom_id, dualHom_id]⟩⟩`. Establish `hiso : IsIso (PDivGroup.baseChangeMap (Kbar X) φ)`. Establish `h' : PDivGroup.baseChangeMap (Kbar X) φ = e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange (Kbar X) GG).hom`. Rewrite using `[hφ, Iso.inv_hom_id_assoc]`. Rewrite using `[h']`.

Use `infer_instance`. Use `haveI : IsIso φ := GlobalTheory.T.isIso_of_generic_polarization p U.Bp (Kbar X) GG φ _ (hht.trans hP₀.height) hiso fun k _ _ _ _ => ((GlobalTheory.T.cotangent_rank_eq_omega_rank p U.Bp t.G GG θ c hc k).trans (hrank k)).ge`. Set `pol : GG ≅ GG.dual` to `asIso φ`. Take `⟨ε, τ, hε, hτ⟩` from `GlobalTheory.T.tate_module_extension_of_generic p U.Bp (Kbar X) GG GG₀ e Dw.La ε₀ τ₀`. Establish `hactc : ∀ a, (act₀ a : GG₀ ⟶ GG₀) ≫ e.hom = e.hom ≫ PDivGroup.baseChangeMap (Kbar X) (act a : GG ⟶ GG)` using `fun a => GlobalTheory.T.p_divisible_model_action_polarization p U.Bp (Kbar X) t.G t.semi t₀.G mK.φ mK.cart GG θ hθ GG₀ θ₀ e he hbij₀ (t.act.act a) (t₀.act.act a) (act a) (act₀ a) (mK.act a) (hactI a) (hP₀.equivariant a)`.

Take `⟨hadj, hskew, hprim, hlin, hpair⟩` from `GlobalTheory.T.pel_p_divisible_properties_extend E H Dw p U.Bp (Kbar X) t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hP₀ GG act pol ε τ e hε hactc hφ hτ`. Establish `hp0 : ((p : ℕ) : Kbar X) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Use `⟨GG, act, pol, θ, ε, τ, ⟨hht.trans hP₀.height, hactI, GlobalTheory.T.generic_type_extends_affine_normal hR hD hC E H Dw p X Z g tZ hX t₀ ⟨m₀⟩ ht₀ U t ⟨m⟩ GG θ hθ, hnz, ⟨c, hc, fun a w w' h => GlobalTheory.T.omega_comparison_equivariant p U.Bp t.G GG θ c hc (t.act.act a) (act a) ( …` and prove the remaining obligations. Introduce `n B _ _ _ _ z z' hz a`. Use `he n B z z' ?_ a` and prove the remaining obligations.

Use `m.cart.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hmK]`. Conclude with `hz`. Establish `w1` using `Over.w z.1`. Establish `w2` using `Over.w z'.1`.

Rewrite using `[Category.assoc, mK.cart.1.w, ← Category.assoc, w2, w1]`. Use `show spMap (algebraMap U.Bp B) = spMap (algebraMap (Kbar X) B) ≫ spMap (algebraMap U.Bp (Kbar X))`. Rewrite using `[IsScalarTower.algebraMap_eq U.Bp (Kbar X) B]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem propG_affine : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    (X Z : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z) (tZ : SAB H Z), GlobalTheory.IsNormalScheme X →
    ∀ (t₀ : SAB H (Sp (Kbar X))) (m₀ : SABMap t₀ tZ (genPt X ≫ g)), IsOfType Dw t₀ →
    ∀ (GG₀ : PDivGroup p (Kbar X)) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀)
      (ε₀ : (PDivGroup.mu p (Kbar X)).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ →
    ∀ (U : AffOp X) (t : SAB H (Sp U.Bp)) (m : SABMap t tZ (U.toX ≫ g)),
      ∃ (GG : PDivGroup p U.Bp) (act : Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (θ : TorsionMap t.G GG)
        (ε : (PDivGroup.mu p U.Bp).Tate) (τ : Dw.La →+ GG.Tate),
        IsPropG Dw t GG act pol θ ε τ ∧ IsRestr m.φ act pol θ ε τ m₀.φ act₀ pol₀ θ₀ ε₀ τ₀ := by
  intro hR hD hC E _ _ _ H Dw p _ X Z _ _ g tZ hX t₀ m₀ ht₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hP₀ U t m
  haveI : CharZero (Kbar X) := ht₀.charZero

  obtain ⟨⟨mK, hmK⟩, -⟩ := GlobalTheory.sabMap_cancel_and_comp_over E H Z (Sp U.Bp) (Sp (Kbar X)) tZ t t₀ (U.toX ≫ g)
    (genPt X ≫ g) (spMap (algebraMap U.Bp (Kbar X))) m m₀ (by rw [← Category.assoc, AffOp.val_toX])

  have hab₀ : abLocus t₀.G = Set.univ := Set.eq_univ_of_forall fun s K _ _ x _ => by
    haveI : IsProper t₀.G.hom := ht₀.1
    infer_instance
  have hbij₀ : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra (Kbar X) B], Function.Bijective (θ₀.pt n B) :=
    fun n B _ _ => hP₀.interior n B (by rw [hab₀]; exact Set.subset_univ _)
  have hcard := GlobalTheory.T.card_tors_generic_fibre_eq_pow_mul_height p U.Bp (Kbar X) t.G t₀.G mK.φ mK.cart GG₀ θ₀ hbij₀
  obtain ⟨GG, θ, hht, hθ⟩ := GlobalTheory.T.exists_p_divisible_group_model p U.Bp (Kbar X) t.G t.semi GG₀.height hcard
  obtain ⟨e, he⟩ := GlobalTheory.T.p_divisible_model_unique_iso p U.Bp (Kbar X) t.G t.semi t₀.G mK.φ mK.cart GG θ hθ GG₀ θ₀ hbij₀

  have hact := fun a : 𝓞 E => GlobalTheory.T.exists_unique_p_divisible_endomorphism p U.Bp (Kbar X) t.G t.semi GG θ hθ (t.act.act a) (t.act.hom a)
  choose actF hactF hactU using hact
  obtain ⟨r1, r2, r3⟩ := GlobalTheory.T.intertwines_comp_and_mul p U.Bp t.G GG θ
  have h0 : actF 0 = 0 := by
    have e1 : actF 0 = actF 0 + actF 0 := (hactU 0 _ (by
      have := r3 _ _ _ _ (hactF 0) (hactF 0)
      rwa [← t.act.add, add_zero] at this)).symm
    exact (left_eq_add.1 e1)
  let act : Action (𝓞 E) GG :=
    { toFun := actF
      map_one' := (hactU 1 (𝟙 GG) (by rw [t.act.one]; exact r1)).symm
      map_mul' := fun a b => by
        refine (hactU (a * b) _ ?_).symm
        rw [mul_comm a b, t.act.mul]
        exact r2 _ _ _ _ (hactF b) (hactF a)
      map_zero' := h0
      map_add' := fun a b => (hactU (a + b) _ (by rw [t.act.add]; exact r3 _ _ _ _ (hactF a) (hactF b))).symm }
  have hactI : ∀ a, θ.Intertwines (t.act.act a) (act a) := hactF

  obtain ⟨φ, hφ⟩ := GlobalTheory.T.pel_p_divisible_extension E H Dw p U.Bp (Kbar X) t t₀ mK GG₀ act₀ pol₀ θ₀ ε₀ τ₀ ht₀ hP₀ GG θ e hθ he
  haveI : CharZero U.Bp := (algebraMap U.Bp (Kbar X)).charZero
  have hnz : θ.IsOpenNearZero := fun n => by
    obtain ⟨V, hV⟩ := (hθ n).opn
    refine ⟨⊤, V, fun _ _ => trivial, fun B _ _ => ?_⟩
    have h' : {z : Tors t.G (p ^ n) B | Set.range z.1.left ⊆ (⊤ : t.G.left.Opens)} = Set.univ :=
      Set.eq_univ_of_forall fun z x _ => trivial
    rw [h']
    exact hV B
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_omega_comparison_near_zero p U.Bp t.G t.semi GG θ hnz
  have hpr : IsProper (pullback.snd t.G.hom (spMap (algebraMap U.Bp (Kbar X)))) := by
    haveI : IsProper t₀.G.hom := ht₀.1
    have h' : pullback.snd t.G.hom (spMap (algebraMap U.Bp (Kbar X))) = mK.cart.1.isoPullback.inv ≫ t₀.G.hom := by
      rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
    rw [h']
    infer_instance
  have h1 := hcard 1
  rw [pow_one, Nat.one_mul, hP₀.height] at h1
  have hrank := GlobalTheory.T.omega_rank_of_torsion_count U.Bp (Kbar X) t.G t.semi hpr p _ (Fact.out : p.Prime) h1
  have hdi : IsIso (dualHom _ _ e.inv) := ⟨⟨dualHom _ _ e.hom, by rw [← dualHom_comp, e.hom_inv_id, dualHom_id],
    by rw [← dualHom_comp, e.inv_hom_id, dualHom_id]⟩⟩
  have hiso : IsIso (PDivGroup.baseChangeMap (Kbar X) φ) := by
    have h' : PDivGroup.baseChangeMap (Kbar X) φ = e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange (Kbar X) GG).hom := by
      rw [hφ, Iso.inv_hom_id_assoc]
    rw [h']
    infer_instance
  haveI : IsIso φ := GlobalTheory.T.isIso_of_generic_polarization p U.Bp (Kbar X) GG φ _ (hht.trans hP₀.height) hiso fun k _ _ _ _ =>
    ((GlobalTheory.T.cotangent_rank_eq_omega_rank p U.Bp t.G GG θ c hc k).trans (hrank k)).ge
  let pol : GG ≅ GG.dual := asIso φ

  obtain ⟨ε, τ, hε, hτ⟩ := GlobalTheory.T.tate_module_extension_of_generic p U.Bp (Kbar X) GG GG₀ e Dw.La ε₀ τ₀
  have hactc : ∀ a, (act₀ a : GG₀ ⟶ GG₀) ≫ e.hom = e.hom ≫ PDivGroup.baseChangeMap (Kbar X) (act a : GG ⟶ GG) :=
    fun a => GlobalTheory.T.p_divisible_model_action_polarization p U.Bp (Kbar X) t.G t.semi t₀.G mK.φ mK.cart GG θ hθ GG₀ θ₀ e he hbij₀ (t.act.act a)
      (t₀.act.act a) (act a) (act₀ a) (mK.act a) (hactI a) (hP₀.equivariant a)
  obtain ⟨hadj, hskew, hprim, hlin, hpair⟩ := GlobalTheory.T.pel_p_divisible_properties_extend E H Dw p U.Bp (Kbar X) t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hP₀ GG act pol
    ε τ e hε hactc hφ hτ
  have hp0 : ((p : ℕ) : Kbar X) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine ⟨GG, act, pol, θ, ε, τ, ⟨hht.trans hP₀.height, hactI,
    GlobalTheory.T.generic_type_extends_affine_normal hR hD hC E H Dw p X Z g tZ hX t₀ ⟨m₀⟩ ht₀ U t ⟨m⟩ GG θ hθ, hnz,
    ⟨c, hc, fun a w w' h => GlobalTheory.T.omega_comparison_equivariant p U.Bp t.G GG θ c hc (t.act.act a) (act a) (t.act.hom a) (hactI a) w w' h⟩,
    hadj, hskew, hprim, hlin, hpair,
    fun n k _ _ hk φ' => GlobalTheory.T.tate_extension_surjective_points p U.Bp (Kbar X) GG GG₀ e Dw.La τ₀ τ hτ (fun n φ => hP₀.onto n (Kbar X) hp0 φ) n k hk φ',
    fun n k _ _ _ hk hab x x' y u h1 h2 => GlobalTheory.T.pel_p_divisible_extension_tate E H Dw p U.Bp (Kbar X) t t₀ mK GG₀ act₀ pol₀ θ₀ ε₀ τ₀ ht₀ hP₀ GG θ e
      hθ he φ hφ τ hτ n k hk hab x x' y u h1 h2⟩, ⟨hε, e, hactc, hφ, hτ, ?_⟩⟩
  intro n B _ _ _ _ z z' hz a
  refine he n B z z' ?_ a
  refine m.cart.1.hom_ext ?_ ?_
  · rw [Category.assoc, hmK]
    exact hz
  · have w1 := Over.w z.1
    have w2 := Over.w z'.1
    rw [Category.assoc, mK.cart.1.w, ← Category.assoc, w2, w1]
    show spMap (algebraMap U.Bp B) = spMap (algebraMap (Kbar X) B) ≫ spMap (algebraMap U.Bp (Kbar X))
    rw [IsScalarTower.algebraMap_eq U.Bp (Kbar X) B]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.GroupBplus.Aff
