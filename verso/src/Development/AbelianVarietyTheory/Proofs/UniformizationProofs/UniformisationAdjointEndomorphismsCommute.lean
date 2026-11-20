import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfNonempty
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationDataStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPointStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndomorphismTorusExtensionPeriodOfAdjointStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Balanced
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

section Defs
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : UnifPre I D A G}

def KeepsIota (E : EndU U) (h : D.toPre.X →+ D.toPre.X) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g'

def KeepsTors (E : EndU U) (h : D.toPre.X →+ D.toPre.X) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x, p'.y = h p.y → E.Act p.g p'.g → QkToAkU U F k p x →
    QkToAkU U F k p' (x ≫ E.aA)

variable (U) {F : Type} [Field F] [Algebra (FractionRing R) F]

def toG (x : TFK (R := R) F ⟶ A.A) : Sp F ⟶ G.left := x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)

/- English proof (translation)
Use `(cancel_mono U.gen.inv).1 (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)`. Conclude with `(Over.w (x ≫ U.gen.inv)).trans (Over.w (x' ≫ U.gen.inv)).symm`.
-/
theorem toG_injective {x x' : TFK (R := R) F ⟶ A.A} (h : toG U x = toG U x') : x = x' := by
  refine (cancel_mono U.gen.inv).1 (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
  · exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  · exact (Over.w (x ≫ U.gen.inv)).trans (Over.w (x' ≫ U.gen.inv)).symm

/- English proof (translation)
Rewrite using `[toG, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc]`. Conclude with `congrArg (· ≫ jK R) ((Category.assoc _ _ _).symm.trans (Over.w (x ≫ U.gen.inv)))`.
-/
theorem toG_over (x : TFK (R := R) F ⟶ A.A) : toG U x ≫ G.hom = jFK (R := R) F ≫ jK R := by
  rw [toG, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ jK R) ((Category.assoc _ _ _).symm.trans (Over.w (x ≫ U.gen.inv)))

/- English proof (translation)
Set `y : TFK (R` to `R) F ⟶ (Over.pullback (jK R)).obj G := Over.homMk (pullback.lift s (jFK (R := R) F) hs) (pullback.lift_snd _ _ _)`. Use `⟨y ≫ U.gen.hom, ?_⟩` and prove the remaining obligations. Establish `e : (y ≫ U.gen.hom).left ≫ U.gen.inv.left = y.left`. Rewrite using `[← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans (pullback.lift_fst _ _ _))`.
-/
theorem exists_toG (s : Sp F ⟶ G.left) (hs : s ≫ G.hom = jFK (R := R) F ≫ jK R) :
    ∃ x : TFK (R := R) F ⟶ A.A, toG U x = s := by
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift s (jFK (R := R) F) hs) (pullback.lift_snd _ _ _)
  refine ⟨y ≫ U.gen.hom, ?_⟩
  have e : (y ≫ U.gen.hom).left ≫ U.gen.inv.left = y.left := by
    rw [← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans (pullback.lift_fst _ _ _))

variable {U} in
/- English proof (translation)
Establish `e : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG`. Rewrite using `[Iso.eq_inv_comp, ← Category.assoc, ← E.ext, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Establish `e' : E.aA.left ≫ U.gen.inv.left = U.gen.inv.left ≫ ((Over.pullback (jK R)).map E.aG).left` using `congrArg (fun q => q.left) e`. Establish `e₂ : ((Over.pullback (jK R)).map E.aG).left ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ E.aG.left` using `pullback.lift_fst _ _ _`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [toG, Over.comp_left, Category.assoc]`. Use `_ = _ := by rw [e', Category.assoc, e₂, toG, Category.assoc, Category.assoc]`.
-/
theorem toG_act (E : EndU U) (x : TFK (R := R) F ⟶ A.A) : toG U (x ≫ E.aA) = toG U x ≫ E.aG.left := by
  have e : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← E.ext, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e' : E.aA.left ≫ U.gen.inv.left = U.gen.inv.left ≫ ((Over.pullback (jK R)).map E.aG).left :=
    congrArg (fun q => q.left) e
  have e₂ : ((Over.pullback (jK R)).map E.aG).left ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ E.aG.left :=
    pullback.lift_fst _ _ _
  calc toG U (x ≫ E.aA) = x.left ≫ (E.aA.left ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK R) := by
        simp only [toG, Over.comp_left, Category.assoc]
    _ = _ := by rw [e', Category.assoc, e₂, toG, Category.assoc, Category.assoc]

end Defs

section Field
variable (hL : LL) {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (hG : IsSemiAbelian G) {U : Unif I D A G} (E : EndU U.toUnifPre) {h : D.toPre.X →+ D.toPre.X}
  {F F' : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F']
  [Algebra (FractionRing R) F']

include hL hR hG in
/- English proof (translation)
Take `⟨ex, add, -⟩` from `GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hR D A G hG U F E E E`. Use `choose a ha hu using ex`. Use `⟨AddMonoidHom.mk' a fun g g' => (isAdd_iff_eq _ _ _).1 (add g g' _ _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (ha g) (ha g') (ha _)), fun g g' => ⟨hu g g', fun e => e ▸ ha g⟩⟩` and prove the remaining obligations.
-/
theorem exists_actHom (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ α : GtPtF D.toPre F →+ GtPtF D.toPre F, ∀ g g', E.Act g g' ↔ g' = α g := by
  obtain ⟨ex, add, -⟩ := GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hR D A G hG U F E E E
  choose a ha hu using ex
  refine ⟨AddMonoidHom.mk' a fun g g' => (isAdd_iff_eq _ _ _).1
    (add g g' _ _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (ha g) (ha g') (ha _)), fun g g' => ⟨hu g g', fun e => e ▸ ha g⟩⟩

variable (σ : F →ₐ[FractionRing R] F')

omit [CharZero R] [IsAlgClosed F] [IsAlgClosed F'] in
/- English proof (translation)
The claim follows from `σ.comp_algebraMap`.
-/
theorem hom_comp : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' :=
  σ.comp_algebraMap

def extPt (x : TFK (R := R) F ⟶ A.A) : TFK (R := R) F' ⟶ A.A :=
  Over.homMk (spMap σ.toRingHom ≫ x.left) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w x)).trans
    ((extMap_jFK σ.toRingHom (hom_comp σ)).trans (Category.id_comp _))))

omit [CharZero R] [IsAlgClosed F] [IsAlgClosed F'] in
include σ in
/- English proof (translation)
Introduce `y g g' hy ha` and use `by have hB := D.tau_bimult rw [isIota_iff_eq hB] at hy ⊢ have := H y _ _ ((isIota_iff_eq hB _ _).2 (by rw [hy, gtExt_iota])) (act_gtExt σ.toRingHom (hom_comp σ) E ha) rw [isIota_iff_eq hB, ← gtExt_iota σ.toRingHom (hom_comp σ)] at this exact gtExt_injective _ _ _ this`.
-/
theorem keepsIota_down (H : KeepsIota E h F') : KeepsIota E h F := fun y g g' hy ha => by
  have hB := D.tau_bimult
  rw [isIota_iff_eq hB] at hy ⊢
  have := H y _ _ ((isIota_iff_eq hB _ _).2 (by rw [hy, gtExt_iota])) (act_gtExt σ.toRingHom (hom_comp σ) E ha)
  rw [isIota_iff_eq hB, ← gtExt_iota σ.toRingHom (hom_comp σ)] at this
  exact gtExt_injective _ _ _ this

omit [IsAlgClosed F'] in
include hL hR hG σ in
/- English proof (translation)
Introduce `y g g' hy ha` and use `by have hB := D.tau_bimult obtain ⟨α, hα⟩ := exists_actHom hL hR hG E F have a := (hα (iota hB F y) _).2 rfl have b := act_gtExt σ.toRingHom (hom_comp σ) E a rw [(isIota_iff_eq hB _ _).1 (H y _ _ (isIota_iota hB y) a), gtExt_iota, gtExt_iota] at b rw [isIota_iff_eq hB] at hy ⊢ ex …`.
-/
theorem keepsIota_up (H : KeepsIota E h F) : KeepsIota E h F' := fun y g g' hy ha => by
  have hB := D.tau_bimult
  obtain ⟨α, hα⟩ := exists_actHom hL hR hG E F
  have a := (hα (iota hB F y) _).2 rfl
  have b := act_gtExt σ.toRingHom (hom_comp σ) E a
  rw [(isIota_iff_eq hB _ _).1 (H y _ _ (isIota_iota hB y) a), gtExt_iota, gtExt_iota] at b
  rw [isIota_iff_eq hB] at hy ⊢
  exact act_unique E ha (hy ▸ b)

include hL hR hG σ in
/- English proof (translation)
Introduce `k hk p p' x hy ha hx` and use `by have hB := D.tau_bimult have X := GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R I hR D A G hG U F F' σ k hk refine (X p' _ (x ≫ E.aA) (extPt σ x ≫ E.aA) ((qkExt_iff hB _ (hom_comp σ) _ _).2 rfl) (Category.assoc _ _ _)).2 ?_ exact H k hk (qkExt hB _ (hom_comp σ) p) _ _ hy …`.
-/
theorem keepsTors_down (H : KeepsTors E h F') : KeepsTors E h F := fun k hk p p' x hy ha hx => by
  have hB := D.tau_bimult
  have X := GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R I hR D A G hG U F F' σ k hk
  refine (X p' _ (x ≫ E.aA) (extPt σ x ≫ E.aA) ((qkExt_iff hB _ (hom_comp σ) _ _).2 rfl) (Category.assoc _ _ _)).2 ?_
  exact H k hk (qkExt hB _ (hom_comp σ) p) _ _ hy (act_gtExt _ (hom_comp σ) E ha)
    ((X p _ x _ ((qkExt_iff hB _ (hom_comp σ) _ _).2 rfl) rfl).1 hx)

include hL hR in
/- English proof (translation)
Establish `hB` using `D.tau_bimult`. Establish `c` using `GlobalTheory.UT.card_qk hL R I hR D F k hk`. Establish `c'` using `GlobalTheory.UT.card_qk hL R I hR D F' k hk`. Set `e : Quot (QkPt.Equiv D.toPre F (k` to `k)) → Quot (QkPt.Equiv D.toPre F' (k := k)) := Quot.map (qkExt hB σ.toRingHom (hom_comp σ)) fun _ _ => qkExt_congr hB _ _`. Establish `inj : Function.Injective e`.

Introduce and unpack `⟨a⟩ ⟨b⟩ hab`. Take `⟨z, hy, hg⟩` from `(equiv_iff hB _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eq.1 hab))`. Use `Quot.sound ((equiv_iff hB _ _).2 ⟨z, hy, gtExt_injective σ.toRingHom (hom_comp σ) _ ?_⟩)` and prove the remaining obligations. Rewrite using `[map_add, gtExt_iota]`. Conclude with `hg`.

Establish `: Finite (Quot (QkPt.Equiv D.toPre F' (k` using `k))) := Nat.finite_of_card_ne_zero (by rw [c']; exact pow_ne_zero _ (by omega))`. Take `⟨⟨q⟩, hq⟩` from `((Nat.bijective_iff_injective_and_card e).2 ⟨inj, c.trans c'.symm⟩).2 (Quot.mk _ p)`. Conclude with `⟨q, (equiv_equivalence hB).eqvGen_iff.1 (Quot.eq.1 hq)⟩`.
-/
theorem exists_equiv_qkExt (k : ℕ) (hk : 1 ≤ k) (p : QkPt D.toPre F' k) :
    ∃ q : QkPt D.toPre F k, QkPt.Equiv D.toPre F' (qkExt D.tau_bimult σ.toRingHom (hom_comp σ) q) p := by
  have hB := D.tau_bimult
  have c := GlobalTheory.UT.card_qk hL R I hR D F k hk
  have c' := GlobalTheory.UT.card_qk hL R I hR D F' k hk
  let e : Quot (QkPt.Equiv D.toPre F (k := k)) → Quot (QkPt.Equiv D.toPre F' (k := k)) :=
    Quot.map (qkExt hB σ.toRingHom (hom_comp σ)) fun _ _ => qkExt_congr hB _ _
  have inj : Function.Injective e := by
    rintro ⟨a⟩ ⟨b⟩ hab
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eq.1 hab))
    refine Quot.sound ((equiv_iff hB _ _).2 ⟨z, hy, gtExt_injective σ.toRingHom (hom_comp σ) _ ?_⟩)
    rw [map_add, gtExt_iota]
    exact hg
  have : Finite (Quot (QkPt.Equiv D.toPre F' (k := k))) :=
    Nat.finite_of_card_ne_zero (by rw [c']; exact pow_ne_zero _ (by omega))
  obtain ⟨⟨q⟩, hq⟩ := ((Nat.bijective_iff_injective_and_card e).2 ⟨inj, c.trans c'.symm⟩).2 (Quot.mk _ p)
  exact ⟨q, (equiv_equivalence hB).eqvGen_iff.1 (Quot.eq.1 hq)⟩

include hL hR hG σ in
/- English proof (translation)
Introduce `k hk p p' x hy ha hx` and use `by have hB := D.tau_bimult have X := GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R I hR D A G hG U F F' σ k hk obtain ⟨α, hα⟩ := exists_actHom hL hR hG E F obtain ⟨α', hα'⟩ := exists_actHom hL hR hG E F' obtain ⟨f, hf, -⟩ := GlobalTheory.T.uniformisation_torsion_identificati …`.
-/
theorem keepsTors_up (H₁ : KeepsIota E h F) (H : KeepsTors E h F) : KeepsTors E h F' := fun k hk p p' x hy ha hx => by
  have hB := D.tau_bimult
  have X := GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R I hR D A G hG U F F' σ k hk
  obtain ⟨α, hα⟩ := exists_actHom hL hR hG E F
  obtain ⟨α', hα'⟩ := exists_actHom hL hR hG E F'
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D A G hG U F k hk
  obtain ⟨f', hf', -, he', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D A G hG U F' k hk
  obtain ⟨q, hq⟩ := exists_equiv_qkExt hL hR σ k hk p
  have hι : ∀ y, α (iota hB F y) = iota hB F (h y) := fun y =>
    (isIota_iff_eq hB _ _).1 (H₁ y _ _ (isIota_iota hB y) ((hα _ _).2 rfl))
  have hι' : ∀ y, α' (iota hB F' y) = iota hB F' (h y) := fun y =>
    (isIota_iff_eq hB _ _).1 (keepsIota_up hL hR hG E σ H₁ y _ _ (isIota_iota hB y) ((hα' _ _).2 rfl))
  let q' : QkPt D.toPre F k := qkMk hB (h q.y) (α q.g) (by rw [← map_nsmul, qk_nsmul hB, hι])
  have a := H k hk q q' (f q) rfl ((hα _ _).2 rfl) ((hf _ _).2 rfl)
  have b : extPt σ (f q) = x := ((hf' _ _).1 ((X q _ (f q) _ ((qkExt_iff hB _ (hom_comp σ) _ _).2 rfl) rfl).1
    ((hf _ _).2 rfl))).trans (((he' _ _).2 hq).trans ((hf' _ _).1 hx).symm)
  have c := (hf' _ _).1 ((X q' _ _ (extPt σ (f q) ≫ E.aA) ((qkExt_iff hB _ (hom_comp σ) _ _).2 rfl)
    (Category.assoc _ _ _)).1 a)
  rw [b] at c
  refine (hf' _ _).2 (c.trans ((he' _ _).2 ?_))
  obtain ⟨z, hz, hg⟩ := (equiv_iff hB _ _).1 hq
  refine (equiv_iff hB _ _).2 ⟨h z, ?_, ?_⟩
  · rw [hy, hz, map_add, map_nsmul]; rfl
  · rw [(hα' _ _).1 ha, hg, map_add, hι']
    exact congrArg (· + _) ((hα' _ _).1 (act_gtExt σ.toRingHom (hom_comp σ) E ((hα q.g _).2 rfl))).symm

end Field

/- English proof (translation)
Rewrite using `[MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom, MonObj.one_eq_one, _root_.mul_one]`. Use `mul_hom := by`. Establish `h : ∀ k : G ⟶ G, [IsMonHom k] → (k ⊗ₘ k) ≫ μ[G] = (fst G G ≫ k) * (snd G G ≫ k)` using `fun k _ => by`. Rewrite using `[MonObj.mul_eq_mul, MonObj.comp_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[MonObj.comp_mul, IsMonHom.mul_hom, IsMonHom.mul_hom, h, h, MonObj.mul_eq_mul, MonObj.comp_mul]`. Simplify using `only [← Category.assoc, tensorHom_fst, tensorHom_snd, MonObj.comp_mul]`. Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
theorem isMonHom_mul {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) where
  one_hom := by
    rw [MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom, MonObj.one_eq_one, _root_.mul_one]
  mul_hom := by
    have h : ∀ k : G ⟶ G, [IsMonHom k] → (k ⊗ₘ k) ≫ μ[G] = (fst G G ≫ k) * (snd G G ≫ k) := fun k _ => by
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
      simp
    rw [MonObj.comp_mul, IsMonHom.mul_hom, IsMonHom.mul_hom, h, h, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [← Category.assoc, tensorHom_fst, tensorHom_snd, MonObj.comp_mul]
    exact mul_mul_mul_comm _ _ _ _

section Main
variable (hL : LL) {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (hG : IsSemiAbelian G) {U : Unif I D A G}

include hL hR hG in

/- English proof (translation)
Establish `hB` using `D.tau_bimult`. Take `⟨M, mG, -, -, -, mAct⟩` from `(GlobalTheory.IntEnd.exists_nsmul_and_neg hL R I hR D A G hG U).1 m`. Take `⟨-, -, hsum⟩` from `(GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hR D A G hG U F E M E₁).2.2.2.2.1 (by rw [eG, mG])`. Establish `sum : ∀ g g' : GtPtF D.toPre F, E.Act g g' → E₁.Act g (g' + m • g)` using `fun g g' ha => hsum g g' _ _ ha ((mAct F _ _).2 ((isNsmul_iff_eq _ _ _).2 rfl)) ((isAdd_iff_eq _ _ _).2 rfl)`. Use `⟨fun y g g' hy ha => ?_, fun k hk p p' x hy ha hx => ?_⟩` and prove the remaining obligations.

Use `(isIota_iff_eq hB _ _).1 (H₁ y _ _ hy (sum g g' ha))` as an intermediate fact. Rewrite `this` using `[eh, map_add, map_nsmul, (isIota_iff_eq hB _ _).1 hy]`. Conclude with `(isIota_iff_eq hB _ _).2 (add_right_cancel this)`. Take `⟨f, hf, -, -, hadd, -⟩` from `GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D A G hG U F k hk`. Set `q : ℕ → QkPt D.toPre F k` to `fun n => qkMk hB (n • p.y) (n • p.g) (by`.

Rewrite using `[smul_comm, qk_nsmul hB, map_nsmul])`. Establish `hq : ∀ n, f (q n) = f p ^ n` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero`. Use `hadd _ _ _ (qkAdd_qkAdd hB (q 0) (q 0))` as an intermediate fact.

Rewrite `this` using `[show qkAdd hB (q 0) (q 0) = q 0 from qk_ext (add_nsmul p.y 0 0).symm (add_nsmul p.g 0 0).symm]`. Conclude with `(mul_eq_left.1 this.symm).trans (pow_zero _).symm`. Consider the case `succ n ih`. Use `hadd _ _ _ (qkAdd_qkAdd hB (q n) p)` as an intermediate fact. Rewrite `this` using `[show qkAdd hB (q n) p = q (n + 1) from qk_ext (succ_nsmul p.y n).symm (succ_nsmul p.g n).symm]`.

Rewrite using `[this, ih, pow_succ]`. Establish `a` using `(hf _ _).1 (H₂ k hk p (qkAdd hB p' (q m)) x (by rw [eh, ← hy]; rfl) (sum _ _ ha) hx)`. Establish `b : x ≫ (E.aA * 𝟙 A.A ^ m) = (x ≫ E.aA) * x ^ m` using `(map_mul (preHom x) _ _).trans (congrArg _ ((map_pow (preHom x) _ _).trans (congrArg (· ^ m) (Category.comp_id x))))`. Rewrite `a` using `[hadd _ _ _ (qkAdd_qkAdd hB p' (q m)), hq, eA, b, ← (hf _ _).1 hx]`. Conclude with `(hf _ _).2 (mul_right_cancel a)`.
-/
theorem keeps_of_add (E : EndU U.toUnifPre) (h : D.toPre.X →+ D.toPre.X) (m : ℕ) (E₁ : EndU U.toUnifPre)
    (h₁ : D.toPre.X →+ D.toPre.X) (eG : E₁.aG = E.aG * 𝟙 G ^ m) (eA : E₁.aA = E.aA * 𝟙 A.A ^ m)
    (eh : ∀ y, h₁ y = h y + m • y) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (H₁ : KeepsIota E₁ h₁ F) (H₂ : KeepsTors E₁ h₁ F) : KeepsIota E h F ∧ KeepsTors E h F := by
  have hB := D.tau_bimult
  obtain ⟨M, mG, -, -, -, mAct⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL R I hR D A G hG U).1 m
  obtain ⟨-, -, hsum⟩ := (GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hR D A G hG U F E M E₁).2.2.2.2.1 (by rw [eG, mG])
  have sum : ∀ g g' : GtPtF D.toPre F, E.Act g g' → E₁.Act g (g' + m • g) := fun g g' ha =>
    hsum g g' _ _ ha ((mAct F _ _).2 ((isNsmul_iff_eq _ _ _).2 rfl)) ((isAdd_iff_eq _ _ _).2 rfl)
  refine ⟨fun y g g' hy ha => ?_, fun k hk p p' x hy ha hx => ?_⟩
  · have := (isIota_iff_eq hB _ _).1 (H₁ y _ _ hy (sum g g' ha))
    rw [eh, map_add, map_nsmul, (isIota_iff_eq hB _ _).1 hy] at this
    exact (isIota_iff_eq hB _ _).2 (add_right_cancel this)
  · obtain ⟨f, hf, -, -, hadd, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D A G hG U F k hk
    let q : ℕ → QkPt D.toPre F k := fun n => qkMk hB (n • p.y) (n • p.g) (by
      rw [smul_comm, qk_nsmul hB, map_nsmul])
    have hq : ∀ n, f (q n) = f p ^ n := fun n => by
      induction n with
      | zero =>
        have := hadd _ _ _ (qkAdd_qkAdd hB (q 0) (q 0))
        rw [show qkAdd hB (q 0) (q 0) = q 0 from qk_ext (add_nsmul p.y 0 0).symm (add_nsmul p.g 0 0).symm] at this
        exact (mul_eq_left.1 this.symm).trans (pow_zero _).symm
      | succ n ih =>
        have := hadd _ _ _ (qkAdd_qkAdd hB (q n) p)
        rw [show qkAdd hB (q n) p = q (n + 1) from qk_ext (succ_nsmul p.y n).symm (succ_nsmul p.g n).symm] at this
        rw [this, ih, pow_succ]
    have a := (hf _ _).1 (H₂ k hk p (qkAdd hB p' (q m)) x (by rw [eh, ← hy]; rfl) (sum _ _ ha) hx)
    have b : x ≫ (E.aA * 𝟙 A.A ^ m) = (x ≫ E.aA) * x ^ m :=
      (map_mul (preHom x) _ _).trans (congrArg _ ((map_pow (preHom x) _ _).trans
        (congrArg (· ^ m) (Category.comp_id x))))
    rw [hadd _ _ _ (qkAdd_qkAdd hB p' (q m)), hq, eA, b, ← (hf _ _).1 hx] at a
    exact (hf _ _).2 (mul_right_cancel a)

include hL hR hG in

/- English proof (translation)
Take `⟨M, mG, mA, -, mh, -⟩` from `(GlobalTheory.IntEnd.exists_nsmul_and_neg hL R I hR D A G hG U).1 m`. Use `E.homG` as an intermediate fact. Use `M.homG` as an intermediate fact. Use `E.homA` as an intermediate fact. Use `M.homA` as an intermediate fact.

Use `U.gen_hom` as an intermediate fact. Take `⟨E₁, eG, eA⟩` from `GlobalTheory.T.exists_endomorphism_action_uniformization_data hL R I hR D A G hG U (E.aG * M.aG) (E.aA * M.aA) (isMonHom_mul _ _) (isMonHom_mul _ _) (by`. Rewrite using `[Functor.map_mul, MonObj.mul_comp, MonObj.comp_mul, E.ext, M.ext])`. Take `⟨-, eh, -⟩` from `(GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hR D A G hG U (AlgebraicClosure (FractionRing R)) E M E₁).2.2.2.2.1 eG`. Conclude with `⟨E₁, mG ▸ eG, mA ▸ eA, fun y => by rw [eh, AddMonoidHom.add_apply, mh]⟩`.
-/
theorem exists_add (E : EndU U.toUnifPre) (m : ℕ) : ∃ E₁ : EndU U.toUnifPre, E₁.aG = E.aG * 𝟙 G ^ m ∧
    E₁.aA = E.aA * 𝟙 A.A ^ m ∧ ∀ y, E₁.h y = E.h y + m • y := by
  obtain ⟨M, mG, mA, -, mh, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL R I hR D A G hG U).1 m
  have := E.homG
  have := M.homG
  have := E.homA
  have := M.homA
  have := U.gen_hom
  obtain ⟨E₁, eG, eA⟩ := GlobalTheory.T.exists_endomorphism_action_uniformization_data hL R I hR D A G hG U (E.aG * M.aG) (E.aA * M.aA) (isMonHom_mul _ _)
    (isMonHom_mul _ _) (by
    rw [Functor.map_mul, MonObj.mul_comp, MonObj.comp_mul, E.ext, M.ext])
  obtain ⟨-, eh, -⟩ := (GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hR D A G hG U (AlgebraicClosure (FractionRing R)) E M E₁).2.2.2.2.1 eG
  exact ⟨E₁, mG ▸ eG, mA ▸ eA, fun y => by rw [eh, AddMonoidHom.add_apply, mh]⟩

include hL hR hG in

/- English proof (translation)
Take `⟨V, _, _, _, φ, hV, hφ, hI⟩` from `GlobalTheory.adic_base_embeds_valuation_algebraic_closure.1 R I hR`. Establish `: CharZero V` using `charZero_of_injective_ringHom hφ`. Establish `hR' : AdmBase V (maximalIdeal V)` using `⟨inferInstance, inferInstance, inferInstance, hV⟩`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Take `⟨v, hv⟩` from `GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ`.

Take `⟨D', hD, A', U', hG', hU, hpt, hend⟩` from `GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R I hR D A G hG U V φ hV hφ hI`. Use `choose Q hQ using QForm.exists_QVal hϖ D'`. Set `Ω` to `AlgebraicClosure (FractionRing V)`. Set `ψ : R →+* Ω` to `((algebraMap (FractionRing V) Ω).comp (algebraMap V (FractionRing V))).comp φ`. Establish `hψ : Function.Injective ψ` using `((algebraMap (FractionRing V) Ω).injective.comp (IsFractionRing.injective V (FractionRing V))).comp hφ`.

Set `_ : Algebra (FractionRing R) Ω` to `(IsFractionRing.lift hψ).toAlgebra`. Establish `hF : ∀ r : R, algebraMap (FractionRing R) Ω (algebraMap R _ r) = algebraMap (FractionRing V) Ω (algebraMap V _ (φ r))` using `fun r => IsFractionRing.lift_algebraMap hψ r`. Take `⟨ex, -, io, ns⟩` from `hpt Ω hF`. Take `⟨E₁, eG, eh, ea⟩` from `hend E`. Take `⟨E₁', eG', eh', -⟩` from `hend E'`.

Establish `inj : ∀ {a : D'.toPre.X →+ D'.toPre.X} {b : D.toPre.X →+ D.toPre.X}, (∀ χ, hD.xe (a χ) = b (hD.xe χ)) → Function.Injective b → Function.Injective a` using `fun e hb x y hxy => hD.xe.injective (hb (by rw [← e, ← e, hxy]))`. Establish `adj' : LBIso (cubeLB _ ![fst _ _ ≫ E₁.aG, snd _ _] U'.LG.L) (cubeLB _ ![fst _ _, snd _ _ ≫ E₁'.aG] U'.LG.L)`. Rewrite using `[eG, eG']`. Take `⟨wL, hw, -⟩` from `hU.lg`. Use `adj_pull (specOf φ) G U.LG.isLB U'.LG.isLB ?_ _ _ adj` and prove the remaining obligations.

Establish `e : LBIso U'.LG.L (U.LG.L.pull ((Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ)))` using `⟨wL, hw⟩`. Rewrite `e` using `[show (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) = pullback.fst G.hom (specOf φ) from Category.id_comp _]`. Then use the resulting hypothesis. Establish `kid` using `GlobalTheory.T.endomorphism_torusExtension_period_of_adjoint hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D' Q hQ Ω v hv A' _ hG' U' E₁ E₁' (inj eh hE) (inj eh' hE') adj'`. Establish `key` using `GlobalTheory.T.torsionPoint_endomorphism_image_eq_moved_gtPoint hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D' Q hQ Ω v hv A' _ hG' U' E₁ (inj eh hE)`. Use `choose π hπ _ using ex`.

Use `⟨Ω, inferInstance, inferInstance, inferInstance, fun y g g' hy ha => ?_, fun k hk p p' x _ ha hx => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hD.xe.surjective y`. Rewrite using `[← eh']`. Conclude with `(io _ _ _ (hπ g')).2 (kid y _ _ ((io _ _ _ (hπ g)).1 hy) ((ea Ω hF _ _ _ _ (hπ g) (hπ g')).1 ha))`. Take `⟨f, hf, -⟩` from `GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D A G hG U Ω k hk`.

Take `⟨f', hf', -⟩` from `GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hR' D' A' _ hG' U' Ω k hk`. Set `ρ : QkPt D.toPre Ω k → QkPt D'.toPre Ω k` to `fun p => ⟨hD.xe.symm p.y, π p.g, by`. Take `⟨s, a, b⟩` from `p.eq`. Conclude with `⟨π s, (ns k _ _ _ _ (hπ _) (hπ _)).1 a, (io _ _ _ (hπ _)).1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩`. Establish `tr : ∀ (q : QkPt D.toPre Ω k) (z : TFK (R` using `R) Ω ⟶ A.A), QkToAkU U.toUnifPre Ω k q z → toG U'.toUnifPre (f' (ρ q)) ≫ pullback.fst G.hom (specOf φ) = toG U.toUnifPre z := fun q z hz => by`.

Establish `w : toG U.toUnifPre z ≫ G.hom = (jFK (R` using `V) Ω ≫ jK V) ≫ specOf φ := by`. Rewrite using `[toG_over]`. Simplify using `only [jFK, jK, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Conclude with `RingHom.ext hF`.

Take `⟨z', hz'⟩` from `exists_toG U'.toUnifPre (pullback.lift _ _ w) (pullback.lift_snd _ _ _)`. Establish `e : toG U'.toUnifPre z' ≫ pullback.fst G.hom (specOf φ) = toG U.toUnifPre z`. Rewrite using `[hz']`. Conclude with `pullback.lift_fst _ _ _`. Rewrite using `[← (hf' _ _).1 (hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D A G U _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A' D' hD U' hU Ω hF k hk q z (ρ q) z' rfl (hπ _) (by`.

Use `Eq.trans ?_ e` and prove the remaining obligations. Simplify using `only [toG, Category.assoc]`. Conclude with `congrArg (fun t => _ ≫ _ ≫ _ ≫ t) (Category.id_comp _)) hz)]`. Conclude with `e`. Take `⟨r, rg, hr⟩` from `key k hk (ρ p) _ ((hf' _ _).2 rfl) (π p'.g) ((ea Ω hF _ _ _ _ (hπ _) (hπ _)).1 ha)`.

Establish `hB'` using `D'.tau_bimult`. Take `rfl : r = ρ p'` from `qk_ext (GlobalTheory.IotaInj.main hL V _ hR' D' Ω _ _ (k • r.g) ((isIota_iff_eq hB' _ _).2 (qk_nsmul hB' r)) ((isIota_iff_eq hB' _ _).2 (rg ▸ qk_nsmul hB' (ρ p')))) rg`. Use `(hf _ _).2 (toG_injective U.toUnifPre ?_)` and prove the remaining obligations. Rewrite using `[← tr p' _ ((hf _ _).2 rfl), ← (hf' _ _).1 hr, toG_act, toG_act, ← tr p x hx, eG, Category.assoc, Category.assoc]`. Conclude with `congrArg (_ ≫ ·) (pullback.lift_fst _ _ _).symm`.
-/
theorem exists_keeps (h₁ : TwistBCSpanStatement) (h₂ : TWM.VRatioGtStatement) (h₃ : TWStatement) (h₄ : UUStatement)
    (E E' : EndU U.toUnifPre) (hE : Function.Injective E.h) (hE' : Function.Injective E'.h)
    (adj : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L)) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra (FractionRing R) Ω),
      KeepsIota E E'.h Ω ∧ KeepsTors E E'.h Ω := by
  obtain ⟨V, _, _, _, φ, hV, hφ, hI⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.1 R I hR
  have : CharZero V := charZero_of_injective_ringHom hφ
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  obtain ⟨D', hD, A', U', hG', hU, hpt, hend⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R I hR D A G hG U V φ hV hφ hI
  choose Q hQ using QForm.exists_QVal hϖ D'
  let Ω := AlgebraicClosure (FractionRing V)
  let ψ : R →+* Ω := ((algebraMap (FractionRing V) Ω).comp (algebraMap V (FractionRing V))).comp φ
  have hψ : Function.Injective ψ :=
    ((algebraMap (FractionRing V) Ω).injective.comp (IsFractionRing.injective V (FractionRing V))).comp hφ
  let _ : Algebra (FractionRing R) Ω := (IsFractionRing.lift hψ).toAlgebra
  have hF : ∀ r : R, algebraMap (FractionRing R) Ω (algebraMap R _ r) =
      algebraMap (FractionRing V) Ω (algebraMap V _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hψ r
  obtain ⟨ex, -, io, ns⟩ := hpt Ω hF
  obtain ⟨E₁, eG, eh, ea⟩ := hend E
  obtain ⟨E₁', eG', eh', -⟩ := hend E'
  have inj : ∀ {a : D'.toPre.X →+ D'.toPre.X} {b : D.toPre.X →+ D.toPre.X}, (∀ χ, hD.xe (a χ) = b (hD.xe χ)) →
      Function.Injective b → Function.Injective a := fun e hb x y hxy =>
    hD.xe.injective (hb (by rw [← e, ← e, hxy]))
  have adj' : LBIso (cubeLB _ ![fst _ _ ≫ E₁.aG, snd _ _] U'.LG.L) (cubeLB _ ![fst _ _, snd _ _ ≫ E₁'.aG] U'.LG.L) := by
    rw [eG, eG']
    obtain ⟨wL, hw, -⟩ := hU.lg
    refine adj_pull (specOf φ) G U.LG.isLB U'.LG.isLB ?_ _ _ adj
    have e : LBIso U'.LG.L (U.LG.L.pull ((Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf φ))) := ⟨wL, hw⟩
    rwa [show (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (specOf φ) from Category.id_comp _] at e
  have kid := GlobalTheory.T.endomorphism_torusExtension_period_of_adjoint hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D' Q hQ Ω v hv A' _ hG' U' E₁ E₁' (inj eh hE) (inj eh' hE') adj'
  have key := GlobalTheory.T.torsionPoint_endomorphism_image_eq_moved_gtPoint hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D' Q hQ Ω v hv A' _ hG' U' E₁ (inj eh hE)
  choose π hπ _ using ex
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, fun y g g' hy ha => ?_, fun k hk p p' x _ ha hx => ?_⟩
  · obtain ⟨y, rfl⟩ := hD.xe.surjective y
    rw [← eh']
    exact (io _ _ _ (hπ g')).2 (kid y _ _ ((io _ _ _ (hπ g)).1 hy) ((ea Ω hF _ _ _ _ (hπ g) (hπ g')).1 ha))
  · obtain ⟨f, hf, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D A G hG U Ω k hk
    obtain ⟨f', hf', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hR' D' A' _ hG' U' Ω k hk
    let ρ : QkPt D.toPre Ω k → QkPt D'.toPre Ω k := fun p => ⟨hD.xe.symm p.y, π p.g, by
      obtain ⟨s, a, b⟩ := p.eq
      exact ⟨π s, (ns k _ _ _ _ (hπ _) (hπ _)).1 a, (io _ _ _ (hπ _)).1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
    have tr : ∀ (q : QkPt D.toPre Ω k) (z : TFK (R := R) Ω ⟶ A.A), QkToAkU U.toUnifPre Ω k q z →
        toG U'.toUnifPre (f' (ρ q)) ≫ pullback.fst G.hom (specOf φ) = toG U.toUnifPre z := fun q z hz => by
      have w : toG U.toUnifPre z ≫ G.hom = (jFK (R := V) Ω ≫ jK V) ≫ specOf φ := by
        rw [toG_over]
        simp only [jFK, jK, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact RingHom.ext hF
      obtain ⟨z', hz'⟩ := exists_toG U'.toUnifPre (pullback.lift _ _ w) (pullback.lift_snd _ _ _)
      have e : toG U'.toUnifPre z' ≫ pullback.fst G.hom (specOf φ) = toG U.toUnifPre z := by
        rw [hz']; exact pullback.lift_fst _ _ _
      rw [← (hf' _ _).1 (hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D A G U _ (Iso.refl _)
        (inferInstanceAs (IsMonHom (𝟙 _))) A' D' hD U' hU Ω hF k hk q z (ρ q) z' rfl (hπ _) (by
          refine Eq.trans ?_ e
          simp only [toG, Category.assoc]
          exact congrArg (fun t => _ ≫ _ ≫ _ ≫ t) (Category.id_comp _)) hz)]
      exact e
    obtain ⟨r, rg, hr⟩ := key k hk (ρ p) _ ((hf' _ _).2 rfl) (π p'.g) ((ea Ω hF _ _ _ _ (hπ _) (hπ _)).1 ha)
    have hB' := D'.tau_bimult
    obtain rfl : r = ρ p' := qk_ext (GlobalTheory.IotaInj.main hL V _ hR' D' Ω _ _ (k • r.g)
      ((isIota_iff_eq hB' _ _).2 (qk_nsmul hB' r)) ((isIota_iff_eq hB' _ _).2 (rg ▸ qk_nsmul hB' (ρ p')))) rg
    refine (hf _ _).2 (toG_injective U.toUnifPre ?_)
    rw [← tr p' _ ((hf _ _).2 rfl), ← (hf' _ _).1 hr, toG_act, toG_act, ← tr p x hx, eG, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _).symm

end Main

/- English proof (translation)
Introduce `hL h₁ h₂ h₃ h₄ R _ _ _ I hR D A G _ _ hG U F _ _ _ E E' adj`. Take `⟨m, hm, hm'⟩` from `exists_add_injective E.h E'.h`. Take `⟨E₁, eG, eA, eh⟩` from `exists_add hL hR hG E m`. Take `⟨E₁', eG', -, eh'⟩` from `exists_add hL hR hG E' m`. Take `⟨Ω, _, _, _, a, b⟩` from `exists_keeps hL hR hG h₁ h₂ h₃ h₄ E₁ E₁' (funext eh ▸ hm) (funext eh' ▸ hm') (by rw [eG, eG']; exact adj_add U.LG U.cubG _ _ adj m)`.

Set `σ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] Ω` to `IsAlgClosed.lift`. Set `τ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F` to `IsAlgClosed.lift`. Establish `a'` using `keepsIota_down E₁ σ a`. Conclude with `keeps_of_add hL hR hG E E'.h m E₁ E₁'.h eG eA eh' F (keepsIota_up hL hR hG E₁ τ a') (keepsTors_up hL hR hG E₁ τ a' (keepsTors_down hL hR hG E₁ σ b))`.
-/
theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → (∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g') ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x, p'.y = E'.h p.y → E.Act p.g p'.g → QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' (x ≫ E.aA) := by
  intro hL h₁ h₂ h₃ h₄ R _ _ _ I hR D A G _ _ hG U F _ _ _ E E' adj
  obtain ⟨m, hm, hm'⟩ := exists_add_injective E.h E'.h
  obtain ⟨E₁, eG, eA, eh⟩ := exists_add hL hR hG E m
  obtain ⟨E₁', eG', -, eh'⟩ := exists_add hL hR hG E' m
  obtain ⟨Ω, _, _, _, a, b⟩ := exists_keeps hL hR hG h₁ h₂ h₃ h₄ E₁ E₁' (funext eh ▸ hm) (funext eh' ▸ hm')
    (by rw [eG, eG']; exact adj_add U.LG U.cubG _ _ adj m)
  let σ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] Ω := IsAlgClosed.lift
  let τ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F := IsAlgClosed.lift
  have a' := keepsIota_down E₁ σ a
  exact keeps_of_add hL hR hG E E'.h m E₁ E₁'.h eG eA eh' F (keepsIota_up hL hR hG E₁ τ a')
    (keepsTors_up hL hR hG E₁ τ a' (keepsTors_down hL hR hG E₁ σ b))

end GlobalTheory.Balanced
end
