import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTensorDiagonalComplementOverBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDomainRelationLiftCommutingSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyEqualOrUnit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.MVExact
open GlobalTheory.EtC.FreeMonoEpi

variable {R : Type} [CommRing R]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-φ) x = -Sec.map φ x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

/- English proof (translation)
Establish `e : ∀ z : Sec (M ⊞ N) U, z = Sec.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) z` using `fun z => by`. Rewrite using `[biprod.total]`. Both sides reduce to the same expression. Rewrite using `[e x, e y, sec_map_add, sec_map_add, sec_map_comp, sec_map_comp, sec_map_comp, sec_map_comp, h1, h2]`.
-/
theorem sec_biprod_ext {M N : Shv R} {U : Scheme.{0}} (x y : Sec (M ⊞ N) U)
    (h1 : Sec.map biprod.fst x = Sec.map biprod.fst y) (h2 : Sec.map biprod.snd x = Sec.map biprod.snd y) : x = y := by
  have e : ∀ z : Sec (M ⊞ N) U, z = Sec.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) z := fun z => by
    rw [biprod.total]; rfl
  rw [e x, e y, sec_map_add, sec_map_add, sec_map_comp, sec_map_comp, sec_map_comp, sec_map_comp, h1, h2]

/- English proof (translation)
The claim follows from `Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)`.
-/
theorem gsum_add (P : PSh) (V : Scheme.{0}) (a b : P.obj (op V) →₀ ULift.{1} R) :
    gsum R P V (a + b) = gsum R P V a + gsum R P V b :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

/- English proof (translation)
Rewrite using `[gsum, Finsupp.sum_neg_index (h := fun x r => r • freeGen R P V x) (fun _ => zero_smul _ _)]`. Simplify using `only [neg_smul]`. Rewrite using `[Finsupp.sum, Finset.sum_neg_distrib]`. Both sides reduce to the same expression.
-/
theorem gsum_neg (P : PSh) (V : Scheme.{0}) (a : P.obj (op V) →₀ ULift.{1} R) :
    gsum R P V (-a) = -gsum R P V a := by
  rw [gsum, Finsupp.sum_neg_index (h := fun x r => r • freeGen R P V x) (fun _ => zero_smul _ _)]
  simp only [neg_smul]
  rw [Finsupp.sum, Finset.sum_neg_distrib]; rfl

/- English proof (translation)
Rewrite using `[← Finsupp.mapDomain_comp]`. Use `congr 1`.
-/
theorem md_comp {M : Type 1} [AddCommMonoid M] (X : Scheme.{0}) {W' W V : Scheme.{0}} (k'' : W' ⟶ W) (k' : W ⟶ V)
    (c : (V ⟶ X) →₀ M) :
    Finsupp.mapDomain (fun x : W ⟶ X => k'' ≫ x) (Finsupp.mapDomain ((yoneda.obj X).map k'.op) c) =
      Finsupp.mapDomain ((yoneda.obj X).map (k'' ≫ k').op) c := by
  rw [← Finsupp.mapDomain_comp]
  congr 1

/- English proof (translation)
Rewrite using `[GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]`. Introduce `T b hb`. Establish `h2` using `(GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₂) T).1 (Sec.map biprod.fst b)`. Establish `h3` using `(GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₃) T).1 (Sec.map biprod.snd b)`. Apply `FreeMonoEpi.loc_trans` to reduce the goal to its premises.

Use `FreeMonoEpi.loc_mono (GlobalTheory.EtC.loc_and T _ _ h2 h3) ?_` and prove the remaining obligations. Introduce and unpack `V k ⟨⟨c2, hc2⟩, ⟨c3, hc3⟩⟩`. Express the relevant statement in the definitionally equal form `Sec.res k (Sec.map biprod.fst b) = gsum R _ V c2 at hc2`. Express the relevant statement in the definitionally equal form `Sec.res k (Sec.map biprod.snd b) = gsum R _ V c3 at hc3`. Establish `key : gsum R (yoneda.obj X₄) V (Finsupp.mapDomain ((yoneda.map c).app (op V)) c2 + Finsupp.mapDomain ((yoneda.map d).app (op V)) c3) = 0`.

Establish `e0 : Sec.res k (Sec.map (biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d))) b) = 0`. Establish `: Sec.map (biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d))) b = 0` using `hb`. Rewrite using `[this]`. Conclude with `map_zero _`. Rewrite using `[gsum_add, ← map_gsum, ← map_gsum, ← hc2, ← hc3, ← map_res, ← map_res, ← sec_map_comp, ← sec_map_comp, ← sec_map_add, ← biprod.desc_eq, map_res, e0]`.

Apply `FreeMonoEpi.loc_trans` to reduce the goal to its premises. Use `FreeMonoEpi.loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₄) V).2 _ key) ?_` and prove the remaining obligations. Introduce `W k' hk'`. Use `set c2' := Finsupp.mapDomain ((yoneda.obj X₂).map k'.op) c2 with hc2'`. Use `set c3' := Finsupp.mapDomain ((yoneda.obj X₃).map k'.op) c3 with hc3'`.

Establish `rel : Finsupp.mapDomain (fun x : W ⟶ X₂ => x ≫ c) c2' + Finsupp.mapDomain (fun y : W ⟶ X₃ => y ≫ d) c3' = 0`. Rewrite using `[← hk', Finsupp.mapDomain_add, hc2', hc3', ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]`. Apply the tactic sequence `congr 2 <;> (funext x; simp)`. Establish `hl : Loc W fun W' k'' => ∀ i : c3'.support × c3'.support, i.1.1 ≫ d = i.2.1 ≫ d → k'' ≫ i.1.1 = k'' ≫ i.2.1 ∨ G W' (k'' ≫ i.1.1 ≫ d)` using `FreeMonoEpi.loc_fin _ fun i => by`. Distinguish the cases in `h : i.1.1 ≫ d = i.2.1 ≫ d`.

Conclude with `FreeMonoEpi.loc_mono (hp W _ _ h) fun _ _ e _ => e`. Conclude with `FreeMonoEpi.loc_all fun _ _ e => absurd e h`. Use `FreeMonoEpi.loc_mono hl ?_` and prove the remaining obligations. Introduce `W' k'' hk''`. Take `⟨a, ha1, ha2⟩` from `GlobalTheory.T.mapDomain_relation_lift_commuting_square (ULift.{1} R) (W ⟶ X₂) (W ⟶ X₃) (W ⟶ X₄) (W' ⟶ X₁) (W' ⟶ X₂) (W' ⟶ X₃) (W' ⟶ X₄) (· ≫ c) (· ≫ d) (· ≫ u) (· ≫ v) (· ≫ c) (· ≫ d) (k'' ≫ ·) (k'' ≫ ·) (k'' ≫ ·) (G W') (fun x => by simp) (fun y => by simp) (fun x => by simp [h …`.

Break down `hk'' (⟨y, hy⟩, ⟨y', hy'⟩) h with e | e` into its components or cases. Conclude with `Or.inl e`. Conclude with `Or.inr (by simpa using e))`. Use `⟨gsum R (yoneda.obj X₁) W' a, ?_⟩` and prove the remaining obligations. Apply `sec_biprod_ext` to reduce the goal to its premises.

Rewrite using `[← sec_map_comp, biprod.lift_fst, map_gsum, map_res, res_comp, hc2, res_gsum']`. Use `congr 1`. Express the relevant statement in the definitionally equal form `Finsupp.mapDomain (fun x : W' ⟶ X₁ => x ≫ u) a = _`. Rewrite using `[ha1, hc2', md_comp]`. Rewrite using `[← sec_map_comp, biprod.lift_snd, sec_map_neg, map_gsum, map_res, res_comp, hc3, res_gsum']`.

Establish `ha2' : Finsupp.mapDomain ((yoneda.map v).app (op W')) a = -Finsupp.mapDomain ((yoneda.obj X₃).map (k'' ≫ k').op) c3`. Use `ha2.trans ?_` and prove the remaining obligations. Rewrite using `[hc3', md_comp]`. Rewrite using `[ha2', gsum_neg, neg_neg]`.
-/
theorem exact_abstract (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (u : X₁ ⟶ X₂) (v : X₁ ⟶ X₃) (c : X₂ ⟶ X₄)
    (d : X₃ ⟶ X₄) (G : ∀ V : Scheme.{0}, (V ⟶ X₄) → Prop) (hsq : u ≫ c = v ≫ d) [Mono c]
    (hc : ∀ V (x : V ⟶ X₂), G V (x ≫ c)) (hd : ∀ V (y : V ⟶ X₃), G V (y ≫ d) → ∃ x, x ≫ v = y)
    (hp : ∀ T (y y' : T ⟶ X₃), y ≫ d = y' ≫ d → Loc T fun V k => k ≫ y = k ≫ y' ∨ G V (k ≫ y ≫ d))
    (w : biprod.lift ((free R).map (yoneda.map u)) (-(free R).map (yoneda.map v)) ≫
      biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) :
    (ShortComplex.mk _ _ w).Exact := by
  classical
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro T b hb
  have h2 := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₂) T).1 (Sec.map biprod.fst b)
  have h3 := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₃) T).1 (Sec.map biprod.snd b)
  apply FreeMonoEpi.loc_trans
  refine FreeMonoEpi.loc_mono (GlobalTheory.EtC.loc_and T _ _ h2 h3) ?_
  rintro V k ⟨⟨c2, hc2⟩, ⟨c3, hc3⟩⟩
  change Sec.res k (Sec.map biprod.fst b) = gsum R _ V c2 at hc2
  change Sec.res k (Sec.map biprod.snd b) = gsum R _ V c3 at hc3
  have key : gsum R (yoneda.obj X₄) V (Finsupp.mapDomain ((yoneda.map c).app (op V)) c2 +
      Finsupp.mapDomain ((yoneda.map d).app (op V)) c3) = 0 := by
    have e0 : Sec.res k (Sec.map (biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d))) b) = 0 := by
      have : Sec.map (biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d))) b = 0 := hb
      rw [this]; exact map_zero _
    rw [gsum_add, ← map_gsum, ← map_gsum, ← hc2, ← hc3, ← map_res, ← map_res, ← sec_map_comp, ← sec_map_comp,
      ← sec_map_add, ← biprod.desc_eq, map_res, e0]
  apply FreeMonoEpi.loc_trans
  refine FreeMonoEpi.loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₄) V).2 _ key) ?_
  intro W k' hk'
  set c2' := Finsupp.mapDomain ((yoneda.obj X₂).map k'.op) c2 with hc2'
  set c3' := Finsupp.mapDomain ((yoneda.obj X₃).map k'.op) c3 with hc3'
  have rel : Finsupp.mapDomain (fun x : W ⟶ X₂ => x ≫ c) c2' + Finsupp.mapDomain (fun y : W ⟶ X₃ => y ≫ d) c3' = 0 := by
    rw [← hk', Finsupp.mapDomain_add, hc2', hc3', ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp,
      ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 2 <;> (funext x; simp)
  have hl : Loc W fun W' k'' => ∀ i : c3'.support × c3'.support, i.1.1 ≫ d = i.2.1 ≫ d →
      k'' ≫ i.1.1 = k'' ≫ i.2.1 ∨ G W' (k'' ≫ i.1.1 ≫ d) :=
    FreeMonoEpi.loc_fin _ fun i => by
      by_cases h : i.1.1 ≫ d = i.2.1 ≫ d
      · exact FreeMonoEpi.loc_mono (hp W _ _ h) fun _ _ e _ => e
      · exact FreeMonoEpi.loc_all fun _ _ e => absurd e h
  refine FreeMonoEpi.loc_mono hl ?_
  intro W' k'' hk''
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.mapDomain_relation_lift_commuting_square (ULift.{1} R) (W ⟶ X₂) (W ⟶ X₃) (W ⟶ X₄) (W' ⟶ X₁) (W' ⟶ X₂) (W' ⟶ X₃) (W' ⟶ X₄)
    (· ≫ c) (· ≫ d) (· ≫ u) (· ≫ v) (· ≫ c) (· ≫ d) (k'' ≫ ·) (k'' ≫ ·) (k'' ≫ ·) (G W')
    (fun x => by simp) (fun y => by simp) (fun x => by simp [hsq]) (fun x y h => (cancel_mono c).1 h) (hc W') (hd W')
    c2' c3' rel (fun y hy y' hy' h => by
      rcases hk'' (⟨y, hy⟩, ⟨y', hy'⟩) h with e | e
      · exact Or.inl e
      · exact Or.inr (by simpa using e))
  refine ⟨gsum R (yoneda.obj X₁) W' a, ?_⟩
  apply sec_biprod_ext
  · rw [← sec_map_comp, biprod.lift_fst, map_gsum, map_res, res_comp, hc2, res_gsum']
    congr 1
    change Finsupp.mapDomain (fun x : W' ⟶ X₁ => x ≫ u) a = _
    rw [ha1, hc2', md_comp]
  · rw [← sec_map_comp, biprod.lift_snd, sec_map_neg, map_gsum, map_res, res_comp, hc3, res_gsum']
    have ha2' : Finsupp.mapDomain ((yoneda.map v).app (op W')) a =
        -Finsupp.mapDomain ((yoneda.obj X₃).map (k'' ≫ k').op) c3 := by
      refine ha2.trans ?_
      rw [hc3', md_comp]
    rw [ha2', gsum_neg, neg_neg]

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]`.
-/
theorem rho_comp {B C : CommRingCat.{0}} (h : B ⟶ C) {V : Scheme.{0}} (y : V ⟶ Spec C) :
    (Scheme.ΓSpecIso B).inv ≫ (y ≫ Spec.map h).appTop = h ≫ (Scheme.ΓSpecIso C).inv ≫ y.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/- English proof (translation)
Rewrite using `[rho_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]`.
-/
theorem rho_toSpec {B : CommRingCat.{0}} {V : Scheme.{0}} (φ : B ⟶ Γ(V, ⊤)) :
    (Scheme.ΓSpecIso B).inv ≫ (V.toSpecΓ ≫ Spec.map φ).appTop = φ := by
  rw [rho_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

/- English proof (translation)
The claim follows from `ext_to_Spec (by simp only [Scheme.Γ_map_op]; exact (rho_toSpec _).symm)`.
-/
theorem eq_toSpec {B : Type} [CommRing B] {V : Scheme.{0}} (y : V ⟶ Spec (CommRingCat.of B)) :
    y = V.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop) :=
  ext_to_Spec (by simp only [Scheme.Γ_map_op]; exact (rho_toSpec _).symm)

/- English proof (translation)
Rewrite using `[rho_comp, CommRingCat.hom_comp, RingHom.comp_apply]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit g).map _`.
-/
theorem unit_of_away {B : Type} [CommRing B] (g : B) {V : Scheme.{0}}
    (x : V ⟶ Spec (CommRingCat.of (Localization.Away g))) :
    IsUnit (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (x ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))).appTop).hom g) := by
  rw [rho_comp, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit g).map _

/- English proof (translation)
Set `ψ` to `IsLocalization.Away.lift (S := Localization.Away g) g hy`. Use `⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ : CommRingCat.of _ ⟶ Γ(V, ⊤)), ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← Spec.map_comp, eq_toSpec y]`. Use `congr 2`. Use extensionality with `b`.

Simplify using `[ψ]`.
-/
theorem lift_away {B : Type} [CommRing B] (g : B) {V : Scheme.{0}} (y : V ⟶ Spec (CommRingCat.of B))
    (hy : IsUnit (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop).hom g)) :
    ∃ x : V ⟶ Spec (CommRingCat.of (Localization.Away g)),
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) = y := by
  let ψ := IsLocalization.Away.lift (S := Localization.Away g) g hy
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ : CommRingCat.of _ ⟶ Γ(V, ⊤)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, eq_toSpec y]
  congr 2
  ext b
  simp [ψ]

/- English proof (translation)
Introduce `R _ A A' _ _ _ _ f h1 h2`. Take `⟨e, u, he, hu⟩` from `GlobalTheory.T.etale_tensor_diagonal_complement_over_basicOpen A A' f h1 h2`. Establish `hsq : Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) = Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap A A') …`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `a`. Simplify using `[Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]`. Establish `w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec. …`. Rewrite using `[biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hsq, add_neg_cancel]`. Use `⟨w, exact_abstract R _ _ _ _ (fun V z => IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ z.appTop).hom f)) hsq (fun V x => unit_of_away f x) (fun V y hy => ?_) (fun T y y' h => GlobalTheory.T.locally_equal_or_unit A A' f e u he hu T y y' h) w⟩` and prove the remaining obligations.

Rewrite `hy` using `[rho_comp, CommRingCat.hom_comp, RingHom.comp_apply]`. Conclude with `lift_away (algebraMap A A' f) y hy`.
-/
theorem mv_exact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) w).Exact := by
  intro R _ A A' _ _ _ _ f h1 h2
  obtain ⟨e, u, he, hu⟩ := GlobalTheory.T.etale_tensor_diagonal_complement_over_basicOpen A A' f h1 h2
  have hsq : Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) =
      Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A A')) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, hsq, add_neg_cancel]
  refine ⟨w, exact_abstract R _ _ _ _
    (fun V z => IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ z.appTop).hom f)) hsq
    (fun V x => unit_of_away f x) (fun V y hy => ?_) (fun T y y' h => GlobalTheory.T.locally_equal_or_unit A A' f e u he hu T y y' h) w⟩
  rw [rho_comp, CommRingCat.hom_comp, RingHom.comp_apply] at hy
  exact lift_away (algebraMap A A' f) y hy

end GlobalTheory.EtC.MVExact
