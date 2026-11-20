import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ETors

open GlobalTheory.BXOf GlobalTheory.TorusExt ReciprocityTheory.ChartRestriction.G.DVR

/- English proof (translation)
Establish `hN : cubN θ n 1 b d ∈ H` using `H.prod_mem fun i _ => hθ _ (P.mul_mem P.one_mem (P.pow_mem hb i)) _ hb _ hd`. Establish `key : ∀ j : ℕ, ∃ r ∈ H, cubN θ n 1 b (d ^ j) = cubN θ n 1 b d ^ j * r ^ n`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact ⟨1, H.one_mem, by rw [pow_zero, C.N_one]; simp⟩`.

Consider the case `succ j ih`. Take `⟨r, hr, e⟩` from `ih`. Establish `a` using `C.N_add n 1 b (d ^ j) d`. Rewrite `a` using `[hn, _root_.mul_one (1 : A), C.face, _root_.mul_one, _root_.one_mul, e, ← pow_succ]`. Use `⟨r * (θ b (d ^ j) d)⁻¹, H.mul_mem hr (H.inv_mem (hθ _ hb _ (P.pow_mem hd j) _ hd)), ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_mul_inv_of_mul_eq a, mul_pow, inv_pow, pow_succ (cubN θ n 1 b d), ← _root_.mul_assoc, mul_right_comm (cubN θ n 1 b d ^ j)]`. Take `⟨r, hr, e⟩` from `key n`. Conclude with `⟨_ * r, H.mul_mem hN hr, by rw [e, mul_pow]⟩`.
-/
theorem cubN_pow_eq_pow {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (C : IsCub θ) (P : Subgroup A)
    (H : Subgroup U) (hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, θ x y z ∈ H) {n : ℕ} {b d : A} (hb : b ∈ P) (hd : d ∈ P)
    (hn : b ^ n = 1) : ∃ h ∈ H, cubN θ n 1 b (d ^ n) = h ^ n := by
  have hN : cubN θ n 1 b d ∈ H := H.prod_mem fun i _ => hθ _ (P.mul_mem P.one_mem (P.pow_mem hb i)) _ hb _ hd
  have key : ∀ j : ℕ, ∃ r ∈ H, cubN θ n 1 b (d ^ j) = cubN θ n 1 b d ^ j * r ^ n := by
    intro j
    induction j with
    | zero => exact ⟨1, H.one_mem, by rw [pow_zero, C.N_one]; simp⟩
    | succ j ih =>
      obtain ⟨r, hr, e⟩ := ih
      have a := C.N_add n 1 b (d ^ j) d
      rw [hn, _root_.mul_one (1 : A), C.face, _root_.mul_one, _root_.one_mul, e, ← pow_succ] at a
      refine ⟨r * (θ b (d ^ j) d)⁻¹, H.mul_mem hr (H.inv_mem (hθ _ hb _ (P.pow_mem hd j) _ hd)), ?_⟩
      rw [eq_mul_inv_of_mul_eq a, mul_pow, inv_pow, pow_succ (cubN θ n 1 b d), ← _root_.mul_assoc,
        mul_right_comm (cubN θ n 1 b d ^ j)]
  obtain ⟨r, hr, e⟩ := key n
  exact ⟨_ * r, H.mul_mem hN hr, by rw [e, mul_pow]⟩

/- English proof (translation)
Establish `e` using `val_nat ht σ hJ hJ r`. Establish `hdel : ∀ k, del L σ J J (r ≫ φ k) = 1` using `fun k => by`. Rewrite using `[← del_id hL hJ (r ≫ φ k)]`. Unfold `del`. Rewrite using `[← Category.assoc, hr, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]`.

Rewrite `e` using `[hr, Finset.prod_eq_one (fun k _ => by rw [hdel, one_zpow]), _root_.one_mul]`. Conclude with `e.symm`.
-/
theorem sig_val_fixed {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {F : Type} [Field F] (σ : F →+* F)
    {J : (Spec (CommRingCat.of F) ⟶ X) → L.ι} (hJ : Good L (closedPoint F) J) (r : Spec (CommRingCat.of F) ⟶ Y)
    (hr : Spec.map (CommRingCat.ofHom σ) ≫ r = r) :
    Units.map σ.toMonoidHom (sig F (val t r (closedPoint F) J)) = sig F (val t r (closedPoint F) J) := by
  have e := val_nat ht σ hJ hJ r
  have hdel : ∀ k, del L σ J J (r ≫ φ k) = 1 := fun k => by
    rw [← del_id hL hJ (r ≫ φ k)]
    unfold del
    rw [← Category.assoc, hr, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rw [hr, Finset.prod_eq_one (fun k _ => by rw [hdel, one_zpow]), _root_.one_mul] at e
  exact e.symm

/- English proof (translation)
Take `⟨β, -, -, ⟨g, gm⟩, -, -, c, -⟩` from `h`. Set `x : (Fin T.r → ℤ) → (Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap iw) ⟶ T.B)` to `fun v => toUnit _ ≫ T.c₀ v`. Establish `xl : ∀ v, (x v).left = spMap iw ≫ (T.c₀ v).left` using `fun v => by show (𝟙 _ ≫ spMap iw) ≫ _ = _`. Rewrite using `[Category.id_comp]`. Establish `xa : ∀ v v', x (v + v') = x v * x v'` using `fun v v' => by show toUnit _ ≫ T.c₀ (v + v') = _`.

Rewrite using `[T.c₀_add]`. Conclude with `MonObj.comp_mul _ _ _`. Establish `w : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 _ ≫ spMap iw`. Rewrite using `[Category.assoc, Over.w]`. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm`.

Set `d : 𝟙_ (Over (Sp R)) ⟶ Q.B` to `Over.homMk (g.lift _ _ w) (g.lift_snd _ _ w)`. Establish `hd : (x (e a)).left = d.left ≫ β` using `(xl _).trans (g.lift_fst _ _ w).symm`. Establish `key : ∀ k : ℕ, (x (((k + 1 : ℕ) : ℤ) • e a)).left = (d ^ (k + 1)).left ≫ β`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using hd`. Consider the case `succ k ih`. Rewrite using `[Nat.cast_succ (k + 1), add_smul, one_smul, xa, pow_succ d (k + 1)]`. Conclude with `gm _ _ _ _ _ ih hd`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`.

Use `⟨d, Over.OverMorphism.ext (g.hom_ext ?_ ?_)⟩` and prove the remaining obligations. Rewrite using `[c, ← key, xl]`. Rewrite using `[Over.w, Over.w]`.
-/
theorem exists_c_eq_pow {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {R : Type} [CommRing R]
    [IsDomain R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) {n : ℕ}
    (hn : 1 ≤ n) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (h : DataFrom T iw s ε n Q e) (a : Q.X) :
    ∃ d : 𝟙_ (Over (Sp R)) ⟶ Q.B, Q.c a = d ^ n := by
  obtain ⟨β, -, -, ⟨g, gm⟩, -, -, c, -⟩ := h
  let x : (Fin T.r → ℤ) → (Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap iw) ⟶ T.B) := fun v => toUnit _ ≫ T.c₀ v
  have xl : ∀ v, (x v).left = spMap iw ≫ (T.c₀ v).left := fun v => by
    show (𝟙 _ ≫ spMap iw) ≫ _ = _
    rw [Category.id_comp]
  have xa : ∀ v v', x (v + v') = x v * x v' := fun v v' => by
    show toUnit _ ≫ T.c₀ (v + v') = _
    rw [T.c₀_add]; exact MonObj.comp_mul _ _ _
  have w : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 _ ≫ spMap iw := by
    rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (g.lift _ _ w) (g.lift_snd _ _ w)
  have hd : (x (e a)).left = d.left ≫ β := (xl _).trans (g.lift_fst _ _ w).symm
  have key : ∀ k : ℕ, (x (((k + 1 : ℕ) : ℤ) • e a)).left = (d ^ (k + 1)).left ≫ β := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      rw [Nat.cast_succ (k + 1), add_smul, one_smul, xa, pow_succ d (k + 1)]
      exact gm _ _ _ _ _ ih hd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨d, Over.OverMorphism.ext (g.hom_ext ?_ ?_)⟩
  · rw [c, ← key, xl]
  · rw [Over.w, Over.w]

attribute [local instance] gtGroup

/- English proof (translation)
Establish `C : IsCub (th D (T` using `TF (R := R) F) y J) := isCub_cubV D.cub hJ`. Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, zero_val χ hJ]`. Simplify using `[cubN]`. Consider the case `succ k ih`.

Establish `a` using `add_val (k • t) t χ hJ`. Rewrite `a` using `[nsmul_b, C.s01, C.s12]`. Simplify using `only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢`. Rewrite using `[succ_nsmul, pow_succ, ← ih, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, a, mul_right_comm]`.
-/
theorem charVal_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (t : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) (k : ℕ) :
    charVal (k • t) χ y J * cubN (th D y J) k 1 t.b (cP D _ χ) = charVal t χ y J ^ k := by
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  induction k with
  | zero => rw [zero_nsmul, zero_val χ hJ]; simp [cubN]
  | succ k ih =>
    have a := add_val (k • t) t χ hJ
    rw [nsmul_b, C.s01, C.s12] at a
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [succ_nsmul, pow_succ, ← ih, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, a, mul_right_comm]

/- English proof (translation)
Introduce `o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ hζ Q e hQ _ D' F σ t ht ⟨z, hz, hz0⟩ hb`. Use `set K := AlgebraicClosure (FractionRing R) with hK`. Establish `hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) K` using `RingHom.ext fun x => σ.commutes x`. Establish `hnt : n • t = 0` using `((isNsmul_iff_eq _ _ _).1 hz).symm.trans ((isZero_iff_eq _).1 hz0)`. Use `choose J hJ using fun ψ : (TF (R := R) K).left ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (ψ (closedPoint K))`.

Use `replace hJ : Good D'.toPre.P.L (Z := (TF (R := R) K).left) (closedPoint K) J := hJ`. It suffices to establish `H : ∀ χ, σ.toAlgHom.toRingHom (sig K (charVal t χ (closedPoint K) J) : K) = (sig K (charVal t χ (closedPoint K) J) : K) from ((eq_gtExt_iff _ hσ t t).1 (gtExt_eq_self_of_charVal_fixed R D'.toPre K _ hσ t hb J hJ H).symm).2`. Set `H : Subgroup ((TF (R` to `R) K).left.presheaf.stalk (closedPoint K))ˣ := MonoidHom.eqLocus ((Units.map σ.toAlgHom.toRingHom.toMonoidHom).comp (sig K)) (sig K)`. Set `P : Subgroup (TF (R` to `R) K ⟶ D'.toPre.P.A) := { carrier := {x | extMap _ hσ ≫ x = x} mul_mem' := fun {a b} ha hb => (MonObj.comp_mul _ _ _).trans (congrArg₂ (· * ·) ha hb) one_mem' := MonObj.comp_one _ inv_mem' := fun {a} ha => (GrpObj.comp_inv _ _).trans (congrArg (·⁻¹) ha) }`. Establish `hP : ∀ d : 𝟙_ (Over (Sp R)) ⟶ D'.toPre.P.A, toUnit _ ≫ d ∈ P` using `fun d => by show extMap _ hσ ≫ toUnit _ ≫ d = toUnit _ ≫ d`.

Rewrite using `[← Category.assoc, toUnit_unique (extMap _ hσ ≫ toUnit _) (toUnit _)]`. Establish `hbP : t.b ∈ P` using `Over.OverMorphism.ext hb`. Establish `hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, th D'.toPre (T` using `TF (R := R) K) (closedPoint K) J x y z ∈ H := by`. Introduce `x hx y hy z hz`. Use `sig_val_fixed D'.toPre.P.isLB D'.toPre.cub.isGen _ hJ (lift x (lift y z)).left ?_` and prove the remaining obligations.

Use `show (extMap _ hσ ≫ lift x (lift y z)).left = _`. Rewrite using `[comp_lift, comp_lift, hx, hy, hz]`. Establish `C : IsCub (th D'.toPre (T` using `TF (R := R) K) (closedPoint K) J) := isCub_cubV D'.toPre.cub hJ`. Use `F.o.onB.hom F.e` as an intermediate fact. Use `F.o.onB.hom (star F.e)` as an intermediate fact.

Use `F.o.onB.hom F.f` as an intermediate fact. Use `F.inc_hom` as an intermediate fact. Establish `hr` using `F.o.onB.rosati (star F.e)`. Rewrite `hr` using `[star_star]`. Take `⟨u, hu, u₀⟩` from `exists_ros GlobalTheory.SemiRigid.globalFns D'.toPre.P.isAb D'.toPre.P.isLB _ _ hr`.

Establish `rel : ∀ χ, ∃ h ∈ H, charVal t χ (closedPoint K) J = charVal t (star F.e • χ) (closedPoint K) J * h`. Introduce `χ`. Use `⟨val u (lift (cP D'.toPre _ χ) t.b).left (closedPoint K) J, ?_, ?_⟩` and prove the remaining obligations. Use `sig_val_fixed D'.toPre.P.isLB hu _ hJ (lift (cP D'.toPre _ χ) t.b).left ?_ show (extMap _ hσ ≫ lift (cP D'.toPre _ χ) t.b).left = _` and prove the remaining obligations. Rewrite using `[comp_lift, comp_cP, hbP]`.

Use `(val_corr hJ (ht.2 u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))` and prove the remaining obligations. Rewrite using `[val_pull hJ, Category.id_comp]`. Both sides reduce to the same expression. Establish `root : ∀ w : ((TF (R` using `R) K).left.presheaf.stalk (closedPoint K))ˣ, w ^ n = 1 → w ∈ H := by`. Introduce `w hw`.

Establish `hinj : Function.Injective ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)))` using `(algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R _)`. Establish `hζ'` using `hζ.map_of_injective hinj`. Establish `: NeZero n` using `⟨by omega⟩`. Establish `hw' : (sig K w : K) ^ n = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one]`.

Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one hw'`. Establish `e : σ (sig K w : K) = (sig K w : K)` using `(congrArg σ hi.symm).trans ((map_pow σ _ i).trans ((congrArg (· ^ i) (σ.commutes _)).trans hi))`. Conclude with `Units.ext e`. Establish `img : ∀ a : Q.X, charVal t (F.f • F.xi a) (closedPoint K) J ∈ H`. Introduce `a`.

Take `⟨d, hd⟩` from `exists_c_eq_pow T iw s ε hn Q e hQ a`. Establish `hc : cP D'.toPre (TF (R` using `R) K) (F.f • F.xi a) = (toUnit _ ≫ (d ≫ F.inc) ≫ F.o.onB.act F.f) ^ n := by`. Rewrite using `[cP, F.o.c_lin, F.c_xi, hd, MonObj.pow_comp, MonObj.pow_comp, MonObj.comp_pow]`. Establish `hbn : t.b ^ n = 1` using `by rw [← nsmul_b, hnt, zero_b]`. Take `⟨h, hh, e₁⟩` from `cubN_pow_eq_pow C P H hθ hbP (hP ((d ≫ F.inc) ≫ F.o.onB.act F.f)) hbn`.

Establish `e₂` using `charVal_pow t (F.f • F.xi a) hJ n`. Rewrite `e₂` using `[hnt, zero_val (D := D'.toPre) (F := K) _ hJ, _root_.one_mul, hc, e₁]`. Use `H.mul_mem (root (charVal t (F.f • F.xi a) (closedPoint K) J * h⁻¹) (by rw [mul_pow, ← e₂, inv_pow, mul_inv_cancel])) hh` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis. Introduce `χ`.

Take `⟨a, ha⟩` from `F.onto χ`. Take `⟨h, hh, e₁⟩` from `rel χ`. Take `⟨h', hh', e₂⟩` from `rel (F.f • F.xi a)`. Establish `m : charVal t χ (closedPoint K) J ∈ H`. Rewrite using `[e₁, ha, eq_mul_inv_of_mul_eq e₂.symm]`.

Conclude with `H.mul_mem (H.mul_mem (img a) (H.inv_mem hh')) hh`. Conclude with `congrArg Units.val m`.
-/
theorem corr_pullGen_of_torsion : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)), ∀ t : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtAct F.o F.e t t → (∃ z : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtF.IsNsmul n t z ∧ z.IsZero) → spMap σ.toAlgHom.toRingHom ≫ t.b.left = t.b.left → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (t.s χ) (LB.pullGen D'.toPre.P.L _ _ (t.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ hζ Q e hQ _ D' F σ t ht ⟨z, hz, hz0⟩ hb
  set K := AlgebraicClosure (FractionRing R) with hK
  have hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) K :=
    RingHom.ext fun x => σ.commutes x
  have hnt : n • t = 0 := ((isNsmul_iff_eq _ _ _).1 hz).symm.trans ((isZero_iff_eq _).1 hz0)
  choose J hJ using fun ψ : (TF (R := R) K).left ⟶ D'.toPre.P.A.left =>
    exists_chart D'.toPre.P.isLB (ψ (closedPoint K))
  replace hJ : Good D'.toPre.P.L (Z := (TF (R := R) K).left) (closedPoint K) J := hJ
  suffices H : ∀ χ, σ.toAlgHom.toRingHom (sig K (charVal t χ (closedPoint K) J) : K) =
      (sig K (charVal t χ (closedPoint K) J) : K) from
    ((eq_gtExt_iff _ hσ t t).1 (gtExt_eq_self_of_charVal_fixed R D'.toPre K _ hσ t hb J hJ H).symm).2
  let H : Subgroup ((TF (R := R) K).left.presheaf.stalk (closedPoint K))ˣ :=
    MonoidHom.eqLocus ((Units.map σ.toAlgHom.toRingHom.toMonoidHom).comp (sig K)) (sig K)
  let P : Subgroup (TF (R := R) K ⟶ D'.toPre.P.A) :=
    { carrier := {x | extMap _ hσ ≫ x = x}
      mul_mem' := fun {a b} ha hb => (MonObj.comp_mul _ _ _).trans (congrArg₂ (· * ·) ha hb)
      one_mem' := MonObj.comp_one _
      inv_mem' := fun {a} ha => (GrpObj.comp_inv _ _).trans (congrArg (·⁻¹) ha) }
  have hP : ∀ d : 𝟙_ (Over (Sp R)) ⟶ D'.toPre.P.A, toUnit _ ≫ d ∈ P := fun d => by
    show extMap _ hσ ≫ toUnit _ ≫ d = toUnit _ ≫ d
    rw [← Category.assoc, toUnit_unique (extMap _ hσ ≫ toUnit _) (toUnit _)]
  have hbP : t.b ∈ P := Over.OverMorphism.ext hb
  have hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, th D'.toPre (T := TF (R := R) K) (closedPoint K) J x y z ∈ H := by
    intro x hx y hy z hz
    refine sig_val_fixed D'.toPre.P.isLB D'.toPre.cub.isGen _ hJ (lift x (lift y z)).left ?_
    show (extMap _ hσ ≫ lift x (lift y z)).left = _
    rw [comp_lift, comp_lift, hx, hy, hz]
  have C : IsCub (th D'.toPre (T := TF (R := R) K) (closedPoint K) J) := isCub_cubV D'.toPre.cub hJ

  have := F.o.onB.hom F.e
  have := F.o.onB.hom (star F.e)
  have := F.o.onB.hom F.f
  have := F.inc_hom
  have hr := F.o.onB.rosati (star F.e)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros GlobalTheory.SemiRigid.globalFns D'.toPre.P.isAb D'.toPre.P.isLB _ _ hr
  have rel : ∀ χ, ∃ h ∈ H, charVal t χ (closedPoint K) J = charVal t (star F.e • χ) (closedPoint K) J * h := by
    intro χ
    refine ⟨val u (lift (cP D'.toPre _ χ) t.b).left (closedPoint K) J, ?_, ?_⟩
    · refine sig_val_fixed D'.toPre.P.isLB hu _ hJ (lift (cP D'.toPre _ χ) t.b).left ?_
      show (extMap _ hσ ≫ lift (cP D'.toPre _ χ) t.b).left = _
      rw [comp_lift, comp_cP, hbP]
    · refine (val_corr hJ (ht.2 u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      rw [val_pull hJ, Category.id_comp]; rfl

  have root : ∀ w : ((TF (R := R) K).left.presheaf.stalk (closedPoint K))ˣ, w ^ n = 1 → w ∈ H := by
    intro w hw
    have hinj : Function.Injective ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))) :=
      (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R _)
    have hζ' := hζ.map_of_injective hinj
    have : NeZero n := ⟨by omega⟩
    have hw' : (sig K w : K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hw'
    have e : σ (sig K w : K) = (sig K w : K) :=
      (congrArg σ hi.symm).trans ((map_pow σ _ i).trans ((congrArg (· ^ i) (σ.commutes _)).trans hi))
    exact Units.ext e

  have img : ∀ a : Q.X, charVal t (F.f • F.xi a) (closedPoint K) J ∈ H := by
    intro a
    obtain ⟨d, hd⟩ := exists_c_eq_pow T iw s ε hn Q e hQ a
    have hc : cP D'.toPre (TF (R := R) K) (F.f • F.xi a) = (toUnit _ ≫ (d ≫ F.inc) ≫ F.o.onB.act F.f) ^ n := by
      rw [cP, F.o.c_lin, F.c_xi, hd, MonObj.pow_comp, MonObj.pow_comp, MonObj.comp_pow]
    have hbn : t.b ^ n = 1 := by rw [← nsmul_b, hnt, zero_b]
    obtain ⟨h, hh, e₁⟩ := cubN_pow_eq_pow C P H hθ hbP (hP ((d ≫ F.inc) ≫ F.o.onB.act F.f)) hbn
    have e₂ := charVal_pow t (F.f • F.xi a) hJ n
    rw [hnt, zero_val (D := D'.toPre) (F := K) _ hJ, _root_.one_mul, hc, e₁] at e₂
    have := H.mul_mem (root (charVal t (F.f • F.xi a) (closedPoint K) J * h⁻¹)
      (by rw [mul_pow, ← e₂, inv_pow, mul_inv_cancel])) hh
    rwa [inv_mul_cancel_right] at this
  intro χ
  obtain ⟨a, ha⟩ := F.onto χ
  obtain ⟨h, hh, e₁⟩ := rel χ
  obtain ⟨h', hh', e₂⟩ := rel (F.f • F.xi a)
  have m : charVal t χ (closedPoint K) J ∈ H := by
    rw [e₁, ha, eq_mul_inv_of_mul_eq e₂.symm]
    exact H.mul_mem (H.mul_mem (img a) (H.inv_mem hh')) hh
  exact congrArg Units.val m

end GlobalTheory.Mum.ETors
