import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MatchingSectionsExist

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec

def unitMap {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left) :
    (𝟙_ (Over S') ⊗ G').left ⟶ (𝟙_ (Over S) ⊗ G).left :=
  (snd (𝟙_ (Over S')) G').left ≫ F ≫ (λ_ G).inv.left

/- English proof (translation)
Rewrite using `[unitMap, Category.assoc, Category.assoc, unit_inv_snd, Category.comp_id]`.
-/
theorem unitMap_snd {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left) :
    unitMap F ≫ (snd (𝟙_ (Over S)) G).left = (snd (𝟙_ (Over S')) G').left ≫ F := by
  rw [unitMap, Category.assoc, Category.assoc, unit_inv_snd, Category.comp_id]

/- English proof (translation)
Rewrite using `[unitMap, ← Category.assoc _ F, ← Category.assoc r', ← h, Category.assoc, snd_unit_inv, Category.comp_id]`.
-/
theorem eq_unitMap {S S' Z : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left)
    {r' : Z ⟶ (𝟙_ (Over S') ⊗ G').left} {r : Z ⟶ (𝟙_ (Over S) ⊗ G).left}
    (h : r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F) : r = r' ≫ unitMap F := by
  rw [unitMap, ← Category.assoc _ F, ← Category.assoc r', ← h, Category.assoc, snd_unit_inv, Category.comp_id]

/- English proof (translation)
The claim follows from `((Category.comp_id _).symm.trans (Over.w (fst (𝟙_ (Over S)) G))).trans (Over.w (snd (𝟙_ (Over S)) G)).symm`.
-/
theorem fst_unit {S : Scheme.{0}} (G : Over S) :
    (fst (𝟙_ (Over S)) G).left = (snd (𝟙_ (Over S)) G).left ≫ G.hom :=
  ((Category.comp_id _).symm.trans (Over.w (fst (𝟙_ (Over S)) G))).trans (Over.w (snd (𝟙_ (Over S)) G)).symm

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

/- English proof (translation)
Establish `push : pushHom pb D'.P.A (cP D' _ α') = cP D _ α` using `Over.OverMorphism.ext (by show (D'.P.A.hom ≫ (D'.c α').left) ≫ β = (D'.P.A.hom ≫ spMap φ) ≫ (D.c α).left`. Rewrite using `[Category.assoc, hc, Category.assoc])`. Set `ρ` to `pushHom pb D'.P.A (𝟙 _)`. Establish `hρ : ρ.left = β` using `Category.id_comp _`. Use `fin_cases i`.

Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`. Establish `e₁ : pushHom pb _ (𝟙 _ * cP D' _ α') = ρ ≫ (𝟙 _ * cP D _ α)`. Rewrite using `[map_mul, push, MonObj.comp_mul, comp_cP, Category.comp_id]`. Conclude with `(congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)`. Establish `e₁ : pushHom pb _ (cP D' _ α') = ρ ≫ cP D _ α` using `by rw [push, comp_cP]`.

Conclude with `(congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)`. Establish `e₁ : pushHom pb D'.P.A 1 = ρ ≫ (1 : D.P.A ⟶ D.P.A)` using `by rw [map_one, MonObj.comp_one]`. Conclude with `(congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)`.
-/
theorem famφB_comp {φ : R →+* V} {D : DegPre R} {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left}
    (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {α' : D'.X} {α : D.X}
    (hc : (D'.c α').left ≫ β = spMap φ ≫ (D.c α).left) (i : Fin 4) :
    D'.famφB α' i ≫ β = β ≫ D.famφB α i := by
  have push : pushHom pb D'.P.A (cP D' _ α') = cP D _ α := Over.OverMorphism.ext (by
    show (D'.P.A.hom ≫ (D'.c α').left) ≫ β = (D'.P.A.hom ≫ spMap φ) ≫ (D.c α).left
    rw [Category.assoc, hc, Category.assoc])
  let ρ := pushHom pb D'.P.A (𝟙 _)
  have hρ : ρ.left = β := Category.id_comp _
  fin_cases i
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e₁ : pushHom pb _ (𝟙 _ * cP D' _ α') = ρ ≫ (𝟙 _ * cP D _ α) := by
      rw [map_mul, push, MonObj.comp_mul, comp_cP, Category.comp_id]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb _ (cP D' _ α') = ρ ≫ cP D _ α := by rw [push, comp_cP]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb D'.P.A 1 = ρ ≫ (1 : D.P.A ⟶ D.P.A) := by rw [map_one, MonObj.comp_one]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)

/- English proof (translation)
Establish `a₀ : p.left ≫ D.famφB α 0 = p.left` using `Category.comp_id _`. Establish `a₁ : p.left ≫ D.famφB α 1 = D.Oφ p α 0` using `congrArg (fun z => z.left) ((MonObj.comp_mul p (𝟙 _) (cP D _ α)).trans (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))`. Establish `a₂ : p.left ≫ D.famφB α 2 = D.Oφ p α 1` using `congrArg (fun z => z.left) (comp_cP D p α)`. Establish `a₃ : p.left ≫ D.famφB α 3 = D.Oφ p α 3` using `congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) p)`. Establish `a₄ : D.Oφ p α 2 = p.left` using `rfl`.

Rewrite using `[Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]`. Use `module`.
-/
theorem prod_fam {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (k : ℕ)
    {M : Type} [CommGroup M] (ω : (T.left ⟶ D.P.A.left) → M) (α : D.X) :
    (∏ a, ω (p.left ≫ D.famφB α a) ^ DegPre.famε k a) * ∏ a, ω (D.Oφ p α a) ^ Oinvε a =
      ω p.left ^ k := by
  have a₀ : p.left ≫ D.famφB α 0 = p.left := Category.comp_id _
  have a₁ : p.left ≫ D.famφB α 1 = D.Oφ p α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul p (𝟙 _) (cP D _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : p.left ≫ D.famφB α 2 = D.Oφ p α 1 :=
    congrArg (fun z => z.left) (comp_cP D p α)
  have a₃ : p.left ≫ D.famφB α 3 = D.Oφ p α 3 :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) p)
  have a₄ : D.Oφ p α 2 = p.left := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

omit [IsDomain R] [IsDomain V] in
/- English proof (translation)
Establish `hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ` using `Ideal.map_le_iff_le_comap.1 (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hI _)`. Use `⟨pullback.lift ((fstG I' e G').left ≫ F) (pullback.snd G'.hom (thick V I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) ?_, pullback.lift_fst _ _ _⟩` and prove the remaining obligations. Establish `e2 : (fstG I' e G').left ≫ G'.hom = pullback.snd G'.hom (thick _ I' e) ≫ thick _ I' e` using `pullback.condition`. Rewrite using `[Category.assoc, hF, ← Category.assoc, e2, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem exists_level {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I')
    {G : Over (Spec (CommRingCat.of R))} {G' : Over (Spec (CommRingCat.of V))} {F : G'.left ⟶ G.left}
    (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (e : ℕ) :
    ∃ m : (thickObj V I' e G').left ⟶ (thickObj R I e G).left,
      m ≫ (fstG I e G).left = (fstG I' e G').left ≫ F := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    Ideal.map_le_iff_le_comap.1 (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hI _)
  refine ⟨pullback.lift ((fstG I' e G').left ≫ F)
    (pullback.snd G'.hom (thick V I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) ?_, pullback.lift_fst _ _ _⟩
  have e2 : (fstG I' e G').left ≫ G'.hom = pullback.snd G'.hom (thick _ I' e) ≫ thick _ I' e := pullback.condition
  rw [Category.assoc, hF, ← Category.assoc, e2, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `R V _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F C k σ f hE`. Establish `hcG : ∀ _ : Fin 1, (snd (𝟙_ _) G').left ≫ F = unitMap F ≫ (snd (𝟙_ _) G).left` using `fun _ => (unitMap_snd F).symm`. Establish `hcB : ∀ α i, famφT D' (𝟙_ _) α i ≫ C.β = unitMap C.β ≫ famφT D (𝟙_ _) (C.xe α) i` using `fun α i => by`. Rewrite using `[famφT_eq, famφT_eq, ← Category.assoc (unitMap _), unitMap_snd, Category.assoc, Category.assoc, famφB_comp C.pbB (C.c_pr α)]`. Take `⟨σ', hσ, -⟩` from `SecPull.existsUnique_secPull _ _ _ _ U.P.L.L U'.P.L.L F U.P.L.isLB U'.P.L.isLB C.wL C.wL_map.gen (Fin 1) (fun _ => (snd (𝟙_ _) G').left) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ)) (unitMap F) hcG σ`.

Use `choose f' hf using fun α => (SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L C.β D.P.isLB D'.P.isLB C.v C.v_gen (Fin 4) (famφT D' (𝟙_ _) α) (famφT D (𝟙_ _) (C.xe α)) (DegPre.famε k) (unitMap C.β) (hcB α) (f (C.xe α))).exists`. Establish `Hσ : ∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))). …`. Introduce `Z r' r hr z J J' hJ hJ'`. Use `sec_val C.wL _ _ _ (unitMap F) hcG σ σ' r' z (hσ Z r' z) hJ hJ'` as an intermediate fact. Rewrite `this` using `[← eq_unitMap F hr, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, om, Category.assoc, ← hr]`.

Conclude with `this`. Establish `Hf : ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, om C.v z J J' (r' ≫ famφT D' (𝟙_ _) α …`. Introduce `α Z r' r hr z J J' hJ hJ'`. Use `sec_val C.v _ _ _ (unitMap C.β) (hcB α) (f (C.xe α)) (f' α) r' z (hf α Z r' z) hJ hJ'` as an intermediate fact. Rewrite `this` using `[← eq_unitMap C.β hr]`.

Conclude with `this`. Use `⟨σ', f', fun e => ?_, Hσ, fun α Z r' r hr z J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Use `swap`. Use `Hf α Z r' r hr z J J' hJ hJ'` as an intermediate fact. Simplify using `only [om, Category.assoc] at this`.

Conclude with `this`. Take `⟨S, hS⟩` from `hE e`. Take `⟨m, hm⟩` from `exists_level hI C.pb.1.w e`. Use `⟨S.map C.xe.symm.toEquiv.toEmbedding, fun Z x' rG' rB' hG' hB' _ z JG' J' hJG' hJ' => ?_⟩` and prove the remaining obligations. Use `choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)`.

Use `choose JG hJG using fun ψ : Z ⟶ G.left => exists_chart U.P.L.isLB (ψ z)`. Establish `hJ : Good D.P.L z J` using `hJ`. Establish `hJG : Good U.P.L.L z JG` using `hJG`. Take `⟨x, hx⟩ : ∃ x : Z ⟶ (thickObj R I e G).left, x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F` from `⟨x' ≫ m, by rw [Category.assoc, hm]⟩`. Take `⟨hq, hlev⟩` from `C.lev e Z x' x hx`.

Take `⟨hT, hW⟩` from `hlev z J J' hJ hJ'`. Establish `hW` using `hW (JG (x ≫ (fstG I e G).left)) (JG' (x' ≫ (fstG I' e G').left)) (hJG _) (hJG' _)`. Establish `rG₁ : (rG' ≫ unitMap F) ≫ (snd _ G).left = rG' ≫ (snd _ G').left ≫ F`. Rewrite using `[Category.assoc, unitMap_snd]`. Establish `rB₁ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = rB' ≫ (snd _ D'.P.A).left ≫ C.β`.

Rewrite using `[Category.assoc, unitMap_snd]`. Establish `rG₂ : (rG' ≫ unitMap F) ≫ (snd _ G).left = x ≫ (fstG I e G).left`. Rewrite using `[rG₁, hx, ← Category.assoc, hG', Category.assoc]`. Establish `rB₂ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left`. Rewrite using `[rB₁, ← hq, ← Category.assoc, hB', Category.assoc]`.

Establish `rBG : (rB' ≫ unitMap C.β) ≫ (fst _ D.P.A).left = (rG' ≫ unitMap F) ≫ (fst _ G).left`. Rewrite using `[fst_unit, fst_unit, ← Category.assoc, ← Category.assoc, rG₂, rB₂, Category.assoc, Category.assoc]`. Conclude with `congrArg (x ≫ ·) ((Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm)`. Take `⟨h0, hsum⟩` from `hS Z x _ _ rG₂ rB₂ rBG z JG J hJG hJ`. Establish `hF` using `fun α => Hf α Z rB' _ rB₁ z J J' hJ hJ'`.

Establish `Sg` using `Hσ Z rG' _ rG₁ z JG JG' hJG hJG'`. Rewrite `Sg` using `[rG₂, hG']`. Establish `hω : ∀ α, (∏ i : Fin 4, om C.v z J J' (rB' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i) * ∏ i : Fin 4, gw C.v (x' ≫ D'.Oφ (U'.gt e).pG α i) z (J (x' ≫ D'.Oφ (U'.gt e).pG α i ≫ C.β)) (J' (x' ≫ D'.Oφ (U'.gt e).pG α i)) ^ Oinvε i = gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG. …`. Introduce `α`. Use `prod_fam (U'.gt e).pG k (fun ψ => om C.v z J J' (x' ≫ ψ)) α` as an intermediate fact.

Establish `e₁ : ∀ i, rB' ≫ famφT D' (𝟙_ _) α i = x' ≫ (U'.gt e).pG.left ≫ D'.famφB α i` using `fun i => by`. Rewrite using `[famφT_eq, ← Category.assoc, hB', Category.assoc]`. Rewrite using `[← hq, ← Category.assoc x' _ C.β]`. Use `Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_) (Finset.prod_congr rfl fun i _ => ?_)) this` and prove the remaining obligations. Rewrite using `[e₁]`.

Rewrite using `[← Category.assoc x' _ C.β]`. Both sides reduce to the same expression. Use `⟨fun α' hα => ?_, ?_⟩` and prove the remaining obligations. Establish `hi : C.xe α' ∉ S` using `fun hc => hα (Finset.mem_map.2 ⟨C.xe α', hc, C.xe.symm_apply_apply α'⟩)`. Conclude with `(Units.mul_right_eq_zero _).1 ((hF α').symm.trans (h0 _ hi))`.

Use `(gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k).mul_right_inj.1 ?_` and prove the remaining obligations. Rewrite using `[← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul, _root_.mul_assoc, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← Sg, hsum, Finset.sum_map, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Take `⟨α', rfl⟩` from `C.xe.surjective y`. Establish `e₀ : C.xe.symm.toEquiv.toEmbedding (C.xe α') = α'` using `C.xe.symm_apply_apply α'`.

Rewrite using `[e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expT_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → ∃ (σ' : U'.SecGT (𝟙_ _) k) (f' : ∀ α, SecBT D' (𝟙_ _) k α), U'.ExpT (𝟙_ _) k σ' f' ∧ (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') ∧ ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, gw C.v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ C.β)) (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
  intro R V _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F C k σ f hE
  classical
  have hcG : ∀ _ : Fin 1, (snd (𝟙_ _) G').left ≫ F = unitMap F ≫ (snd (𝟙_ _) G).left :=
    fun _ => (unitMap_snd F).symm
  have hcB : ∀ α i, famφT D' (𝟙_ _) α i ≫ C.β = unitMap C.β ≫ famφT D (𝟙_ _) (C.xe α) i := fun α i => by
    rw [famφT_eq, famφT_eq, ← Category.assoc (unitMap _), unitMap_snd, Category.assoc, Category.assoc,
      famφB_comp C.pbB (C.c_pr α)]
  obtain ⟨σ', hσ, -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.P.L.L U'.P.L.L F U.P.L.isLB U'.P.L.isLB C.wL
    C.wL_map.gen (Fin 1) (fun _ => (snd (𝟙_ _) G').left) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ))
    (unitMap F) hcG σ
  choose f' hf using fun α => (SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L C.β D.P.isLB D'.P.isLB C.v
    C.v_gen (Fin 4) (famφT D' (𝟙_ _) α) (famφT D (𝟙_ _) (C.xe α)) (DegPre.famε k)
    (unitMap C.β) (hcB α) (f (C.xe α))).exists
  have Hσ : ∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J' := by
    intro Z r' r hr z J J' hJ hJ'
    have := sec_val C.wL _ _ _ (unitMap F) hcG σ σ' r' z (hσ Z r' z) hJ hJ'
    rw [← eq_unitMap F hr, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, om, Category.assoc, ← hr] at this
    exact this
  have Hf : ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, om C.v z J J' (r' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
    intro α Z r' r hr z J J' hJ hJ'
    have := sec_val C.v _ _ _ (unitMap C.β) (hcB α) (f (C.xe α)) (f' α) r' z (hf α Z r' z) hJ hJ'
    rw [← eq_unitMap C.β hr] at this
    exact this
  refine ⟨σ', f', fun e => ?_, Hσ, fun α Z r' r hr z J J' hJ hJ' => ?_⟩
  swap
  · have := Hf α Z r' r hr z J J' hJ hJ'
    simp only [om, Category.assoc] at this
    exact this
  obtain ⟨S, hS⟩ := hE e
  obtain ⟨m, hm⟩ := exists_level hI C.pb.1.w e
  refine ⟨S.map C.xe.symm.toEquiv.toEmbedding, fun Z x' rG' rB' hG' hB' _ z JG' J' hJG' hJ' => ?_⟩
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose JG hJG using fun ψ : Z ⟶ G.left => exists_chart U.P.L.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  have hJG : Good U.P.L.L z JG := hJG
  obtain ⟨x, hx⟩ : ∃ x : Z ⟶ (thickObj R I e G).left, x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F :=
    ⟨x' ≫ m, by rw [Category.assoc, hm]⟩
  obtain ⟨hq, hlev⟩ := C.lev e Z x' x hx
  obtain ⟨hT, hW⟩ := hlev z J J' hJ hJ'
  have hW := hW (JG (x ≫ (fstG I e G).left)) (JG' (x' ≫ (fstG I' e G').left)) (hJG _) (hJG' _)
  have rG₁ : (rG' ≫ unitMap F) ≫ (snd _ G).left = rG' ≫ (snd _ G').left ≫ F := by
    rw [Category.assoc, unitMap_snd]
  have rB₁ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = rB' ≫ (snd _ D'.P.A).left ≫ C.β := by
    rw [Category.assoc, unitMap_snd]
  have rG₂ : (rG' ≫ unitMap F) ≫ (snd _ G).left = x ≫ (fstG I e G).left := by
    rw [rG₁, hx, ← Category.assoc, hG', Category.assoc]
  have rB₂ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left := by
    rw [rB₁, ← hq, ← Category.assoc, hB', Category.assoc]
  have rBG : (rB' ≫ unitMap C.β) ≫ (fst _ D.P.A).left = (rG' ≫ unitMap F) ≫ (fst _ G).left := by
    rw [fst_unit, fst_unit, ← Category.assoc, ← Category.assoc, rG₂, rB₂, Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) ((Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm)
  obtain ⟨h0, hsum⟩ := hS Z x _ _ rG₂ rB₂ rBG z JG J hJG hJ
  have hF := fun α => Hf α Z rB' _ rB₁ z J J' hJ hJ'
  have Sg := Hσ Z rG' _ rG₁ z JG JG' hJG hJG'
  rw [rG₂, hG'] at Sg
  have hω : ∀ α, (∏ i : Fin 4, om C.v z J J' (rB' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i) *
      ∏ i : Fin 4, gw C.v (x' ≫ D'.Oφ (U'.gt e).pG α i) z (J (x' ≫ D'.Oφ (U'.gt e).pG α i ≫ C.β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG α i)) ^ Oinvε i =
      gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k := by
    intro α
    have := prod_fam (U'.gt e).pG k (fun ψ => om C.v z J J' (x' ≫ ψ)) α
    have e₁ : ∀ i, rB' ≫ famφT D' (𝟙_ _) α i = x' ≫ (U'.gt e).pG.left ≫ D'.famφB α i := fun i => by
      rw [famφT_eq, ← Category.assoc, hB', Category.assoc]
    rw [← hq, ← Category.assoc x' _ C.β]
    refine Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_)
      (Finset.prod_congr rfl fun i _ => ?_)) this
    · rw [e₁]
    · rw [← Category.assoc x' _ C.β]; rfl
  refine ⟨fun α' hα => ?_, ?_⟩
  · have hi : C.xe α' ∉ S := fun hc => hα (Finset.mem_map.2 ⟨C.xe α', hc, C.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').symm.trans (h0 _ hi))
  · refine (gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul,
      _root_.mul_assoc, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← Sg, hsum, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨α', rfl⟩ := C.xe.surjective y
    have e₀ : C.xe.symm.toEquiv.toEmbedding (C.xe α') = α' := C.xe.symm_apply_apply α'
    rw [e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul]
    ring

end GlobalTheory.ExpCmp
end
