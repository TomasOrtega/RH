import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCoverStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section Val

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem sec_sub_id_eq_val (E : SqExt R) {x : Sp E.B ⟶ X} (hx : x ≫ s = spMap (algebraMap R E.B))
    (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (h : spMap ((E.π : E.C →+* E.B).comp (AlgHom.id R E.C : E.C →+* E.C)) ≫ y = x) (f : Z1 (O (dp0 R) s)) :
    ev f (E.secHom hx E.i E.π_i) - ev f (Thick.trivHom (hx := hy) (T := E.thick x hx) (AlgHom.id R E.C) h) =
      E.val y hy f := by
  subst h
  rfl

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem val_congr (E : SqExt R) {y y' : Sp E.C ⟶ X} (e : y = y') (hy : y ≫ s = spMap (algebraMap R E.C))
    (hy' : y' ≫ s = spMap (algebraMap R E.C)) (f : Z1 (O (dp0 R) s)) : E.val y hy f = E.val y' hy' f := by
  subst e
  rfl

end Val

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

/- English proof (translation)
The claim follows from `sec_sub_id_eq_val (SqExt.ofModule K P.B P.B) P.w (P.trx v) (P.tr v).w ((P.isTransl_trx v).red hv) f`.
-/
theorem ev_sec_sub_ev_tan_eq_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v)
    (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) :
    ev f P.sec - ev f (P.tan hv) = (SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f :=
  sec_sub_id_eq_val (SqExt.ofModule K P.B P.B) P.w (P.trx v) (P.tr v).w ((P.isTransl_trx v).red hv) f

/- English proof (translation)
The claim follows from `RingHom.ext fun c ↦ by ext <;> simp [dualMap]`.
-/
theorem dualMap_id (B : Type) [CommRing B] : dualMap (RingHom.id B) = RingHom.id (DualNumber B) :=
  RingHom.ext fun c ↦ by ext <;> simp [dualMap]

@[reducible] def Pt.origin (A : Over (Sp K)) [GrpObj A] : GPt A where
  B := K
  x := η[A].left
  w := by
    rw [Category.comp_id, Over.w η[A]]
    exact (Cris.spMap_id K).symm

/- English proof (translation)
Use `⟨1, Over.homMk (spMap (dualMap (algebraMap K K)) ≫ v.left) (by` and prove the remaining obligations. Rewrite using `[Category.assoc, Over.w v]`. Express the relevant statement in the definitionally equal form `spMap _ ≫ spMap _ = spMap _`. Rewrite using `[← Cris.spMap_comp, dualMap_comp_algebraMap]), rfl, rfl, ?_⟩`. Rewrite using `[_root_.one_mul]`.

Express the relevant statement in the definitionally equal form `spMap (dualMap (RingHom.id K)) ≫ v.left = v.left`. Rewrite using `[dualMap_id, Cris.spMap_id, Category.id_comp]`.
-/
theorem isTransl_origin (v : epsR K ⟶ A) : IsTransl (algebraMap K K) η[A].left v v.left := by
  refine ⟨1, Over.homMk (spMap (dualMap (algebraMap K K)) ≫ v.left) (by
      rw [Category.assoc, Over.w v]
      change spMap _ ≫ spMap _ = spMap _
      rw [← Cris.spMap_comp, dualMap_comp_algebraMap]), rfl, rfl, ?_⟩
  rw [_root_.one_mul]
  change spMap (dualMap (RingHom.id K)) ≫ v.left = v.left
  rw [dualMap_id, Cris.spMap_id, Category.id_comp]

/- English proof (translation)
The claim follows from `((Pt.origin A).isTransl_trx v).unique (isTransl_origin v)`.
-/
theorem origin_trx (v : epsR K ⟶ A) : (Pt.origin A).trx v = v.left :=
  ((Pt.origin A).isTransl_trx v).unique (isTransl_origin v)

end GlobalTheory.CechKS

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def tanFn (v : epsR K ⟶ A) (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) : PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ ((SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f).snd

/- English proof (translation)
Introduce `P Q φ _`. Apply the tactic sequence `have := (SqExt.ofModule K P.B P.B).val_map (SqExt.ofModule K Q.B Q.B) (dualAlg φ.ρ) φ.ρ (fun c ↦ (fst_dualAlg φ.ρ c).symm) (fun b ↦ by ext <;> simp) (P.trx v) (P.tr v).w (Q.trx v) (Q.tr v).w (φ.tr v).pt ω`. Simplify using `only [tanFn]`. Rewrite using `[this, snd_dualAlg]`.
-/
theorem isNat_tanFn (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) : IsNat ⊤ (tanFn v ω.1) := by
  intro P Q φ _
  have := (SqExt.ofModule K P.B P.B).val_map (SqExt.ofModule K Q.B Q.B) (dualAlg φ.ρ) φ.ρ
    (fun c ↦ (fst_dualAlg φ.ρ c).symm) (fun b ↦ by ext <;> simp) (P.trx v) (P.tr v).w (Q.trx v) (Q.tr v).w
    (φ.tr v).pt ω
  simp only [tanFn]
  rw [this, snd_dualAlg]

/- English proof (translation)
Take `⟨g, hg⟩` from `GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ ⊤) ⊤ (fun _ ↦ le_rfl) (le_iSup_of_le () le_rfl) (tanFn v ω.1) (fun _ ↦ isNat_tanFn v ω)`. Take `⟨g₀, rfl⟩` from `(GlobalTheory.globalFns_holds (Sp K) A hA).2 g`. Establish `key : ∀ Q : GPt A, tanFn v ω.1 Q = algebraMap K Q.B (valR (𝟙 (Sp K)) ⊤ g₀)`. Introduce `Q`. Rewrite using `[hg () Q (fun _ _ ↦ trivial)]`.

Establish `e1 : valR Q.x ⊤ (A.hom.appTop.hom g₀) = valR (Q.x ≫ A.hom) ⊤ g₀`. Rewrite using `[GlobalTheory.Points.valR_comp Q.x A.hom ⊤ g₀]`. Both sides reduce to the same expression. Establish `e2 : Q.x ≫ A.hom = spMap (algebraMap K Q.B) ≫ 𝟙 (Sp K)` using `(Category.comp_id (Q.x ≫ A.hom)).symm.trans ((Category.assoc _ _ _).trans (Q.w.trans (Category.comp_id _).symm))`. Rewrite using `[e1, e2, GlobalTheory.Points.valR_spMap_comp _ _ _ (GlobalTheory.Points.le_preimage_top _)]`.

Establish `h0 : tanFn v ω.1 (Pt.origin A) = tanVal v ω`. Simplify using `only [tanFn]`. Rewrite using `[tanVal_apply]`. Conclude with `congrArg TrivSqZeroExt.snd (val_congr (SqExt.dual K) (origin_trx v) _ _ ω.1)`. Rewrite using `[key, ← h0, key]`.

Both sides reduce to the same expression.
-/
theorem tanFn_eq (hA : IsAbelianScheme A) (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A) :
    tanFn v ω.1 P = algebraMap K P.B (tanVal v ω) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ ⊤) ⊤ (fun _ ↦ le_rfl)
    (le_iSup_of_le () le_rfl) (tanFn v ω.1) (fun _ ↦ isNat_tanFn v ω)
  obtain ⟨g₀, rfl⟩ := (GlobalTheory.globalFns_holds (Sp K) A hA).2 g
  have key : ∀ Q : GPt A, tanFn v ω.1 Q = algebraMap K Q.B (valR (𝟙 (Sp K)) ⊤ g₀) := by
    intro Q
    rw [hg () Q (fun _ _ ↦ trivial)]
    have e1 : valR Q.x ⊤ (A.hom.appTop.hom g₀) = valR (Q.x ≫ A.hom) ⊤ g₀ := by
      rw [GlobalTheory.Points.valR_comp Q.x A.hom ⊤ g₀]; rfl
    have e2 : Q.x ≫ A.hom = spMap (algebraMap K Q.B) ≫ 𝟙 (Sp K) :=
      (Category.comp_id (Q.x ≫ A.hom)).symm.trans ((Category.assoc _ _ _).trans (Q.w.trans (Category.comp_id _).symm))
    rw [e1, e2, GlobalTheory.Points.valR_spMap_comp _ _ _ (GlobalTheory.Points.le_preimage_top _)]
  have h0 : tanFn v ω.1 (Pt.origin A) = tanVal v ω := by
    simp only [tanFn]
    rw [tanVal_apply]
    exact congrArg TrivSqZeroExt.snd (val_congr (SqExt.dual K) (origin_trx v) _ _ ω.1)
  rw [key, ← h0, key]
  rfl

/- English proof (translation)
Introduce `K _ A _ hA v hv ω P`. Rewrite using `[ev_sec_sub_ev_tan_eq_val P hv ω.1]`. Use `ext`. Rewrite using `[TrivSqZeroExt.fst_inr]`. Conclude with `SqExt.π_val (SqExt.ofModule K P.B P.B) _ _ ω`.

Conclude with `tanFn_eq hA v ω P`.
-/
theorem ev_sec_sub_ev_tan : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (v : epsR K ⟶ A) (hv : IsTangent v) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A),
    ev ω.1 P.sec - ev ω.1 (P.tan hv) = (TrivSqZeroExt.inr (algebraMap K P.B (tanVal v ω)) : DualNumber P.B) := by
  intro K _ A _ hA v hv ω P
  rw [ev_sec_sub_ev_tan_eq_val P hv ω.1]
  ext
  · rw [TrivSqZeroExt.fst_inr]; exact SqExt.π_val (SqExt.ofModule K P.B P.B) _ _ ω
  · exact tanFn_eq hA v ω P

end GlobalTheory.CechKS
