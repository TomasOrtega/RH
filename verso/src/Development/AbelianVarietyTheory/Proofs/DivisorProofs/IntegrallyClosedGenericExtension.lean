import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.HTLocWeil

/- English proof (translation)
Set `c' : (FractionRing R)ˣ` to `Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c`. Establish `hc' : c' ^ N = 1` using `by rw [← map_pow, hc, map_one]`. Establish `hint : ∀ x : (FractionRing R)ˣ, x ^ N = 1 → ∃ r : R, algebraMap R (FractionRing R) r = x` using `fun x hx => by`. Establish `: IsIntegral R (x : FractionRing R)` using `IsIntegral.of_pow hN (by`. Rewrite using `[← Units.val_pow_eq_pow_val, hx, Units.val_one]`.

Conclude with `isIntegral_one)`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 this`. Take `⟨r, hr⟩` from `hint c' hc'`. Take `⟨r', hr'⟩` from `hint c'⁻¹ (by rw [inv_pow, hc', inv_one])`. Establish `h1 : r * r' = 1` using `IsFractionRing.injective R (FractionRing R) (by`.

Rewrite using `[map_mul, hr, hr', map_one, Units.mul_inv])`. Use `⟨⟨r, r', h1, by rw [mul_comm, h1]⟩, ?_⟩` and prove the remaining obligations. Establish `: Units.map (algebraMap R (FractionRing R)).toMonoidHom ⟨r, r', h1, by rw [mul_comm, h1]⟩ = c'` using `Units.ext hr`. Rewrite using `[this]`. Use extensionality with `: 1`.

Use `show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom (c : Γ(Sp (FractionRing R), ⊤))) = c`. Rewrite using `[← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]`.
-/
theorem unit_of_root {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {N : ℕ} (hN : 0 < N)
    (c : Γ(Sp (FractionRing R), ⊤)ˣ) (hc : c ^ N = 1) :
    ∃ u : Rˣ, unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = c := by
  let c' : (FractionRing R)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c
  have hc' : c' ^ N = 1 := by rw [← map_pow, hc, map_one]
  have hint : ∀ x : (FractionRing R)ˣ, x ^ N = 1 → ∃ r : R, algebraMap R (FractionRing R) r = x := fun x hx => by
    have : IsIntegral R (x : FractionRing R) := IsIntegral.of_pow hN (by
      rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]; exact isIntegral_one)
    exact IsIntegrallyClosed.isIntegral_iff.1 this
  obtain ⟨r, hr⟩ := hint c' hc'
  obtain ⟨r', hr'⟩ := hint c'⁻¹ (by rw [inv_pow, hc', inv_one])
  have h1 : r * r' = 1 := IsFractionRing.injective R (FractionRing R) (by
    rw [map_mul, hr, hr', map_one, Units.mul_inv])
  refine ⟨⟨r, r', h1, by rw [mul_comm, h1]⟩, ?_⟩
  have : Units.map (algebraMap R (FractionRing R)).toMonoidHom ⟨r, r', h1, by rw [mul_comm, h1]⟩ = c' := Units.ext hr
  rw [this]
  ext : 1
  show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom (c : Γ(Sp (FractionRing R), ⊤))) = c
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

/- English proof (translation)
Use extensionality with `: 1`. Use `congrArg (fun z : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z : Γ(Sp R, ⊤))) h` as an intermediate fact. Simplify `this` using `[unitOn, ← CommRingCat.comp_apply]`.
-/
theorem unitOn_inj {R : Type} [CommRing R] {u v : Rˣ} (h : unitOn u = unitOn v) : u = v := by
  ext : 1
  have := congrArg (fun z : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z : Γ(Sp R, ⊤))) h
  simpa [unitOn, ← CommRingCat.comp_apply] using this

end GlobalTheory.HTLocWeil

namespace GlobalTheory.HTLocWeil

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
  {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype)
  {T : Scheme.{0}} (y : T ⟶ Xo'.XF c')

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.homMk (Y.m.cart.1.lift w.left y (Over.w w)) (Y.m.cart.1.lift_snd _ _ _), Y.m.cart.1.lift_fst _ _ _⟩`.
-/
theorem lift_ex (w : Over.mk (y ≫ Y.j) ⟶ Y.t.G) : ∃ σ : Over.mk y ⟶ Y.oF.t.G, σ.left ≫ Y.m.φ = w.left :=
  ⟨Over.homMk (Y.m.cart.1.lift w.left y (Over.w w)) (Y.m.cart.1.lift_snd _ _ _), Y.m.cart.1.lift_fst _ _ _⟩

variable {Y y}

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (Y.m.cart.1.hom_ext h (by rw [Over.w σ, Over.w σ']))`.
-/
theorem lift_uniq {σ σ' : Over.mk y ⟶ Y.oF.t.G} (h : σ.left ≫ Y.m.φ = σ'.left ≫ Y.m.φ) : σ = σ' :=
  Over.OverMorphism.ext (Y.m.cart.1.hom_ext h (by rw [Over.w σ, Over.w σ']))

/- English proof (translation)
The claim follows from `Y.m.cart.2 (Over.mk y) σ σ' w w' h h'`.
-/
theorem mul_map {σ σ' : Over.mk y ⟶ Y.oF.t.G} {w w' : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ)
    (h' : w'.left = σ'.left ≫ Y.m.φ) : (w * w').left = (σ * σ').left ≫ Y.m.φ :=
  Y.m.cart.2 (Over.mk y) σ σ' w w' h h'

/- English proof (translation)
Set `z : Over.mk (y ≫ Y.j) ⟶ Y.t.G` to `Over.homMk ((1 : Over.mk y ⟶ Y.oF.t.G).left ≫ Y.m.φ) (by`. Rewrite using `[Category.assoc, Y.m.cart.1.w, ← Category.assoc, Over.w (1 : Over.mk y ⟶ Y.oF.t.G)]`. Use the proof step `rfl)`. Establish `hz : (z * z).left = z.left`. Rewrite using `[mul_map (σ := 1) (σ' := 1) rfl rfl, _root_.mul_one]`.

Both sides reduce to the same expression. Establish `: z = 1`. Establish `e : z * z = z * 1` using `by rw [_root_.mul_one]; exact Over.OverMorphism.ext hz`. Conclude with `mul_left_cancel e`. Rewrite using `[← this]`.

Both sides reduce to the same expression.
-/
theorem one_map : (1 : Over.mk (y ≫ Y.j) ⟶ Y.t.G).left = (1 : Over.mk y ⟶ Y.oF.t.G).left ≫ Y.m.φ := by
  let z : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk ((1 : Over.mk y ⟶ Y.oF.t.G).left ≫ Y.m.φ) (by
    rw [Category.assoc, Y.m.cart.1.w, ← Category.assoc, Over.w (1 : Over.mk y ⟶ Y.oF.t.G)]; rfl)
  have hz : (z * z).left = z.left := by
    rw [mul_map (σ := 1) (σ' := 1) rfl rfl, _root_.mul_one]; rfl
  have : z = 1 := by
    have e : z * z = z * 1 := by rw [_root_.mul_one]; exact Over.OverMorphism.ext hz
    exact mul_left_cancel e
  rw [← this]; rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `one_map`. Consider the case `succ k ih => rw [pow_succ, pow_succ]`. Conclude with `mul_map ih h`.
-/
theorem pow_map {σ : Over.mk y ⟶ Y.oF.t.G} {w : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ) (k : ℕ) :
    (w ^ k).left = (σ ^ k).left ≫ Y.m.φ := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact one_map
  | succ k ih => rw [pow_succ, pow_succ]; exact mul_map ih h

/- English proof (translation)
The claim follows from `lift_uniq (by rw [← pow_map h, hw, one_map])`.
-/
theorem tors_lift {σ : Over.mk y ⟶ Y.oF.t.G} {w : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ) {k : ℕ}
    (hw : w ^ k = 1) : σ ^ k = 1 :=
  lift_uniq (by rw [← pow_map h, hw, one_map])

end GlobalTheory.HTLocWeil

namespace GlobalTheory.HTLocWeil

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[pow_zero, zero_smul]`. Use `Y.oF.etaA_ker 0` as an intermediate fact. Rewrite `this` using `[smul_zero]`.

Conclude with `this.symm`. Consider the case `succ k ih => rw [pow_succ, ih, succ_nsmul, Y.oF.etaA_add]`.
-/
theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
    {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype) (a : Dw.La)
    (k : ℕ) : Y.oF.etaA a ^ k = Y.oF.etaA (k • a) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_smul]
    have := Y.oF.etaA_ker 0
    rw [smul_zero] at this
    exact this.symm
  | succ k ih => rw [pow_succ, ih, succ_nsmul, Y.oF.etaA_add]

/- English proof (translation)
Introduce `E _ _ _ H Dw l' Xo' c' W Y p _ n hA R _ _ _ ξ y hy a`. Establish `hN : 0 < p ^ n` using `pow_pos (Fact.out : p.Prime).pos n`. Set `P : Out.PolAV (Xo'.XF c')` to `GlobalTheory.Obj.toPolAV Y.oF`. Establish `hG` using `GlobalTheory.laws_without_cohomology.1`. Set `e0 : Over.mk y ⟶ Y.oF.t.G` to `toUnit (Over.mk y) ≫ Y.oF.etaA a`.

Establish `he0 : e0 ^ (p ^ n) = 1` using `by show (toUnit (Over.mk y) ≫ Y.oF.etaA a) ^ (p ^ n) = 1`. Rewrite using `[← MonObj.comp_pow, etaA_pow, ← hA, Y.oF.etaA_ker, MonObj.comp_one]`. Set `good : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ → Prop` to `fun w u => ∃ σ : Over.mk y ⟶ Y.oF.t.G, σ.left ≫ Y.m.φ = w ∧ σ ^ (p ^ n) = 1 ∧ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u))`. Set `κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ` to `fun w => if h : ∃ u, good w u then h.choose else 1`. Establish `ex : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → ∃ u, good (σ.left ≫ Y.m.φ) u` using `fun σ hσ => by`.

Take `⟨c, hc, -⟩` from `GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) e0 σ he0 hσ`. Take `⟨u, hu⟩` from `unit_of_root hN c (GlobalTheory.TorsCoord.pow_eq_one_of_weilIs hG P hc he0)`. Conclude with `⟨u, σ, rfl, hσ, hu ▸ hc⟩`. Establish `val : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ))))` using `fun σ hσ => by`. Establish `h` using `ex σ hσ`.

Establish `hk : κ (σ.left ≫ Y.m.φ) = h.choose` using `dif_pos h`. Take `⟨σ', e1, -, h2⟩` from `h.choose_spec`. Rewrite using `[hk]`. Conclude with `(lift_uniq e1) ▸ h2`. Establish `uniq : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → ∀ u v : Rˣ, Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u)) → Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ (unitOn (Units.map (algebraMap R (Fr …` using `fun σ hσ u v hu hv => by`.

Use `(GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) e0 σ he0 hσ).unique hu hv` as an intermediate fact. Use `unitOn_inj this` as an intermediate fact. Use extensionality with `: 1`. Conclude with `IsFractionRing.injective R (FractionRing R) (congrArg Units.val this)`. Use `⟨κ, fun w w' hw hw' => ?_, fun e σ he hσ => ?_⟩` and prove the remaining obligations.

Establish `hwy : ∀ v : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ ξ) ⟶ Y.t.G, v.left ≫ Y.t.G.hom = y ≫ Y.j` using `fun v => by rw [Over.w v]; exact hy`. Set `w₁ : Over.mk (y ≫ Y.j) ⟶ Y.t.G` to `Over.homMk w.left (hwy w)`. Set `w₁' : Over.mk (y ≫ Y.j) ⟶ Y.t.G` to `Over.homMk w'.left (hwy w')`. Take `⟨σ, hσ⟩` from `lift_ex Y y w₁`. Take `⟨σ', hσ'⟩` from `lift_ex Y y w₁'`.

Establish `t1 : σ ^ (p ^ n) = 1` using `tors_lift hσ.symm (HTMap.tors_of (g := 𝟙 _) (show w₁.left = 𝟙 _ ≫ w.left from (Category.id_comp _).symm) hw)`. Establish `t2 : σ' ^ (p ^ n) = 1` using `tors_lift hσ'.symm (HTMap.tors_of (g := 𝟙 _) (show w₁'.left = 𝟙 _ ≫ w'.left from (Category.id_comp _).symm) hw')`. Establish `t3 : (σ * σ') ^ (p ^ n) = 1` using `by rw [mul_pow, t1, t2, _root_.one_mul]`. Establish `hm : (w * w').left = (σ * σ').left ≫ Y.m.φ`. Rewrite using `[HTMap.mul_of (g := 𝟙 _) (w₁ := w₁) (w₂ := w₁') (w₁' := w) (w₂' := w') (Category.id_comp _).symm (Category.id_comp _).symm, Category.id_comp]`.

Conclude with `mul_map hσ.symm hσ'.symm`. Establish `v1` using `val σ t1`. Establish `v2` using `val σ' t2`. Rewrite `v1` using `[hσ]`. Rewrite `v2` using `[hσ']`.

Establish `v3` using `val (σ * σ') t3`. Rewrite `v3` using `[← hm]`. Establish `sk` using `(GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk y)).1`. Establish `v4` using `sk _ _ _ (GlobalTheory.weilIs_mul_left hG _ P (p ^ n) (Over.mk y) σ σ' e0 _ _ (sk _ _ _ v1) (sk _ _ _ v2))`. Use `uniq _ t3 _ _ v3 ?_` and prove the remaining obligations.

Establish `ceq : unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w.left * κ w'.left)) = ((unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w.left)))⁻¹ * (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w'.left)))⁻¹)⁻¹`. Simplify using `only [mul_inv, inv_inv, unitOn, map_mul]`. Rewrite using `[ceq]`. Conclude with `v4`. Establish `he' : e = e0` using `Over.OverMorphism.ext (by`.

Rewrite using `[he]`. Use `show _ = (toUnit (Over.mk y)).left ≫ _`. Use `congr 1)`. Rewrite using `[he']`. Conclude with `val σ hσ`.
-/
theorem weil_kappa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ)))) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n hA R _ _ _ ξ y hy a
  classical
  have hN : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  let P : Out.PolAV (Xo'.XF c') := GlobalTheory.Obj.toPolAV Y.oF
  have hG := GlobalTheory.laws_without_cohomology.1
  let e0 : Over.mk y ⟶ Y.oF.t.G := toUnit (Over.mk y) ≫ Y.oF.etaA a
  have he0 : e0 ^ (p ^ n) = 1 := by
    show (toUnit (Over.mk y) ≫ Y.oF.etaA a) ^ (p ^ n) = 1
    rw [← MonObj.comp_pow, etaA_pow, ← hA, Y.oF.etaA_ker, MonObj.comp_one]
  let good : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ → Prop := fun w u =>
    ∃ σ : Over.mk y ⟶ Y.oF.t.G, σ.left ≫ Y.m.φ = w ∧ σ ^ (p ^ n) = 1 ∧
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u))
  let κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ := fun w => if h : ∃ u, good w u then h.choose else 1

  have ex : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → ∃ u, good (σ.left ≫ Y.m.φ) u := fun σ hσ => by
    obtain ⟨c, hc, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) e0 σ he0 hσ
    obtain ⟨u, hu⟩ := unit_of_root hN c (GlobalTheory.TorsCoord.pow_eq_one_of_weilIs hG P hc he0)
    exact ⟨u, σ, rfl, hσ, hu ▸ hc⟩
  have val : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 →
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ)))) := fun σ hσ => by
    have h := ex σ hσ
    have hk : κ (σ.left ≫ Y.m.φ) = h.choose := dif_pos h
    obtain ⟨σ', e1, -, h2⟩ := h.choose_spec
    rw [hk]
    exact (lift_uniq e1) ▸ h2
  have uniq : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → ∀ u v : Rˣ,
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u)) →
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) → u = v := fun σ hσ u v hu hv => by
    have := (GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) e0 σ he0 hσ).unique hu hv
    have := unitOn_inj this
    ext : 1
    exact IsFractionRing.injective R (FractionRing R) (congrArg Units.val this)
  refine ⟨κ, fun w w' hw hw' => ?_, fun e σ he hσ => ?_⟩
  ·
    have hwy : ∀ v : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ ξ) ⟶ Y.t.G,
        v.left ≫ Y.t.G.hom = y ≫ Y.j := fun v => by rw [Over.w v]; exact hy
    let w₁ : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk w.left (hwy w)
    let w₁' : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk w'.left (hwy w')
    obtain ⟨σ, hσ⟩ := lift_ex Y y w₁
    obtain ⟨σ', hσ'⟩ := lift_ex Y y w₁'
    have t1 : σ ^ (p ^ n) = 1 := tors_lift hσ.symm (HTMap.tors_of (g := 𝟙 _)
      (show w₁.left = 𝟙 _ ≫ w.left from (Category.id_comp _).symm) hw)
    have t2 : σ' ^ (p ^ n) = 1 := tors_lift hσ'.symm (HTMap.tors_of (g := 𝟙 _)
      (show w₁'.left = 𝟙 _ ≫ w'.left from (Category.id_comp _).symm) hw')
    have t3 : (σ * σ') ^ (p ^ n) = 1 := by rw [mul_pow, t1, t2, _root_.one_mul]
    have hm : (w * w').left = (σ * σ').left ≫ Y.m.φ := by
      rw [HTMap.mul_of (g := 𝟙 _) (w₁ := w₁) (w₂ := w₁') (w₁' := w) (w₂' := w') (Category.id_comp _).symm (Category.id_comp _).symm,
        Category.id_comp]
      exact mul_map hσ.symm hσ'.symm
    have v1 := val σ t1
    have v2 := val σ' t2
    rw [hσ] at v1
    rw [hσ'] at v2
    have v3 := val (σ * σ') t3
    rw [← hm] at v3
    have sk := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk y)).1
    have v4 := sk _ _ _ (GlobalTheory.weilIs_mul_left hG _ P (p ^ n) (Over.mk y) σ σ' e0 _ _ (sk _ _ _ v1) (sk _ _ _ v2))
    refine uniq _ t3 _ _ v3 ?_
    have ceq : unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w.left * κ w'.left)) =
        ((unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w.left)))⁻¹ *
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w'.left)))⁻¹)⁻¹ := by
      simp only [mul_inv, inv_inv, unitOn, map_mul]
    rw [ceq]
    exact v4
  · have he' : e = e0 := Over.OverMorphism.ext (by
      rw [he]; show _ = (toUnit (Over.mk y)).left ≫ _; congr 1)
    rw [he']
    exact val σ hσ

end GlobalTheory.HTLocWeil
