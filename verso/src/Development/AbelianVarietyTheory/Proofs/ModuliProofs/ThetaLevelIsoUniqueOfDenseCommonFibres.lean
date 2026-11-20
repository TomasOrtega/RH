import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordOfRatio
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemIdealOfOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbedding
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfMemRange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfCompat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixGeometricTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.TUniq
open ReciprocityTheory.ChartRestriction.G.Out

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o}

omit [CommRing o] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨pullback.lift a c h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`.
-/
theorem exists_lift {A T : Over S} {Z : Scheme.{0}} (a : Z ⟶ T.left) (c : Z ⟶ A.left) (h : a ≫ T.hom = c ≫ A.hom) :
    ∃ y : Z ⟶ (T ⊗ A).left, y ≫ (fst T A).left = a ∧ y ≫ (snd T A).left = c :=
  ⟨pullback.lift a c h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

omit [CommRing o] in
/- English proof (translation)
Establish `h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom` using `(IsPullback.of_hasPullback T.hom A.hom).flip`. Establish `h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom` using `(IsPullback.of_hasPullback T'.hom A.hom).flip`. Use `IsPullback.of_right ?_ ?_ h1` and prove the remaining obligations. Rewrite using `[← Over.comp_left, whiskerRight_snd, Over.w h]`. Conclude with `h2`.

Rewrite using `[← Over.comp_left, ← Over.comp_left, whiskerRight_fst]`.
-/
theorem isPullback_whisker (A : Over S) {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

/- English proof (translation)
Set `k : Over.mk x ⟶ T` to `Over.homMk x₀ hx`. Take `⟨σ₀, H₀, c₀⟩` from `GlobalTheory.emb_baseChange h₂ o g N' J b S s t m T _ k σ hT (inferInstanceAs (IsAffine (Spec _))) H`. Establish `: IsIso (show (baseOver (Sp K)).left ⟶ (Over.mk x).left from 𝟙 (Sp K))` using `inferInstanceAs (IsIso (𝟙 (Sp K)))`. Take `⟨σ₁, H₁, c₁⟩` from `emb_move h hm (T := baseOver _) (T₀ := Over.mk x) (show (baseOver (Sp K)).left ⟶ (Over.mk x).left from 𝟙 (Sp K)) rfl H₀`. Use `⟨σ₁, H₁, fun B _ y₁ y e₁ e₂ w => ?_⟩` and prove the remaining obligations.

Take `⟨y₀, a₁, a₂⟩` from `exists_lift (A := t.A) (T := Over.mk x) (y₁ ≫ (fst (baseOver _) u.A).left) (y₁ ≫ (snd (baseOver _) u.A).left ≫ ψ) (by`. Rewrite using `[Category.assoc, Category.assoc, Category.assoc, h.1.1.w, ← Category.assoc (snd (baseOver _) u.A).left, Over.w, ← Over.w (fst (baseOver _) u.A)]`. Conclude with `congrArg (fun q => y₁ ≫ q ≫ x) (Category.comp_id _).symm)`. Rewrite using `[c₁ B y₁ y₀ (a₁.trans (congrArg _ (Category.comp_id _).symm)) a₂, c₀]`. Establish `e : y₀ ≫ (k ▷ t.A).left = y` using `ThetaPtMove.psi_ext (by rw [Category.assoc, (isPullback_whisker t.A k).w, ← Category.assoc, a₁, e₁, Category.assoc]; rfl) (by rw [Category.assoc, VVRank.whisker_snd_left, a₂, e₂])`.

Rewrite using `[e]`.
-/
theorem emb_fibre (h₂ : Laws2) {t : TObj g (N' ^ 2) J b s} {m : ℕ} (hm : m ∣ N') {T : Over S} (hT : IsAffine T.left)
    {σ} (H : t.Emb m T σ) {K : Type} [Field K] {su : Sp K ⟶ Sp o} {u : TObj g (N' ^ 2) J b su} {x : Sp K ⟶ S}
    {ψ : u.A.left ⟶ t.A.left} (h : MapBy u t x ψ) (x₀ : Sp K ⟶ T.left) (hx : x₀ ≫ T.hom = x) :
    ∃ σ₁, u.Emb m (baseOver _) σ₁ ∧ ∀ (B : Type) [Field B] (y₁ : Sp B ⟶ (baseOver _ ⊗ u.A).left)
      (y : Sp B ⟶ (T ⊗ t.A).left), y ≫ (fst T t.A).left = y₁ ≫ (fst _ u.A).left ≫ x₀ →
        y ≫ (snd T t.A).left = y₁ ≫ (snd _ u.A).left ≫ ψ → ∀ w, SecCoord _ σ₁ y₁ w ↔ SecCoord _ σ y w := by
  let k : Over.mk x ⟶ T := Over.homMk x₀ hx
  obtain ⟨σ₀, H₀, c₀⟩ := GlobalTheory.emb_baseChange h₂ o g N' J b S s t m T _ k σ hT (inferInstanceAs (IsAffine (Spec _))) H
  have : IsIso (show (baseOver (Sp K)).left ⟶ (Over.mk x).left from 𝟙 (Sp K)) := inferInstanceAs (IsIso (𝟙 (Sp K)))
  obtain ⟨σ₁, H₁, c₁⟩ := emb_move h hm (T := baseOver _) (T₀ := Over.mk x)
    (show (baseOver (Sp K)).left ⟶ (Over.mk x).left from 𝟙 (Sp K)) rfl H₀
  refine ⟨σ₁, H₁, fun B _ y₁ y e₁ e₂ w => ?_⟩
  obtain ⟨y₀, a₁, a₂⟩ := exists_lift (A := t.A) (T := Over.mk x) (y₁ ≫ (fst (baseOver _) u.A).left)
    (y₁ ≫ (snd (baseOver _) u.A).left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, Category.assoc, h.1.1.w, ← Category.assoc (snd (baseOver _) u.A).left,
        Over.w, ← Over.w (fst (baseOver _) u.A)]
      exact congrArg (fun q => y₁ ≫ q ≫ x) (Category.comp_id _).symm)
  rw [c₁ B y₁ y₀ (a₁.trans (congrArg _ (Category.comp_id _).symm)) a₂, c₀]
  have e : y₀ ≫ (k ▷ t.A).left = y := ThetaPtMove.psi_ext
    (by rw [Category.assoc, (isPullback_whisker t.A k).w, ← Category.assoc, a₁, e₁, Category.assoc]; rfl)
    (by rw [Category.assoc, VVRank.whisker_snd_left, a₂, e₂])
  rw [e]

/- English proof (translation)
Take `⟨σ₁, H₁, c₁⟩` from `emb_fibre h₂ hm hT H h x₀ hx`. Take `⟨σ₁', H₁', c₁'⟩` from `emb_fibre h₂ hm hT H' h' x₀ hx`. Take `⟨y₁, a₁, a₂⟩` from `exists_lift (A := u.A) (T := baseOver _) (z ≫ u.A.hom) z (Category.comp_id _)`. Establish `: Subsingleton (baseOver (Sp K)).left` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Use `(c₁' B y₁ y' ?_ ?_ w).1 (emb_unique h₁.globalFns u ho H₁ H₁' y₁ ((c₁ B y₁ y ?_ ?_ w).2 hw))` and prove the remaining obligations.

Rewrite using `[← Category.assoc, a₁, e₁', Category.assoc]`. Rewrite using `[← Category.assoc, a₂, e₂']`. Rewrite using `[← Category.assoc, a₁, e₁, Category.assoc]`. Rewrite using `[← Category.assoc, a₂, e₂]`.
-/
theorem coord_agree (h₁ : Laws) (h₂ : Laws2) {t t' : TObj g (N' ^ 2) J b s} {m : ℕ} (hm : m ∣ N') (ho : Odd m)
    {T : Over S} (hT : IsAffine T.left) {σ σ'} (H : t.Emb m T σ) (H' : t'.Emb m T σ') {K : Type} [Field K]
    {su : Sp K ⟶ Sp o} {u : TObj g (N' ^ 2) J b su} {x : Sp K ⟶ S} {ψ : u.A.left ⟶ t.A.left}
    {ψ' : u.A.left ⟶ t'.A.left} (h : MapBy u t x ψ) (h' : MapBy u t' x ψ') (x₀ : Sp K ⟶ T.left) (hx : x₀ ≫ T.hom = x)
    {B : Type} [Field B] (z : Sp B ⟶ u.A.left) {y : Sp B ⟶ (T ⊗ t.A).left} {y' : Sp B ⟶ (T ⊗ t'.A).left}
    (e₁ : y ≫ (fst T t.A).left = z ≫ u.A.hom ≫ x₀) (e₂ : y ≫ (snd T t.A).left = z ≫ ψ)
    (e₁' : y' ≫ (fst T t'.A).left = z ≫ u.A.hom ≫ x₀) (e₂' : y' ≫ (snd T t'.A).left = z ≫ ψ') {w}
    (hw : SecCoord _ σ y w) : SecCoord _ σ' y' w := by
  obtain ⟨σ₁, H₁, c₁⟩ := emb_fibre h₂ hm hT H h x₀ hx
  obtain ⟨σ₁', H₁', c₁'⟩ := emb_fibre h₂ hm hT H' h' x₀ hx
  obtain ⟨y₁, a₁, a₂⟩ := exists_lift (A := u.A) (T := baseOver _) (z ≫ u.A.hom) z (Category.comp_id _)
  have : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine (c₁' B y₁ y' ?_ ?_ w).1 (emb_unique h₁.globalFns u ho H₁ H₁' y₁ ((c₁ B y₁ y ?_ ?_ w).2 hw))
  · rw [← Category.assoc, a₁, e₁', Category.assoc]
  · rw [← Category.assoc, a₂, e₂']
  · rw [← Category.assoc, a₁, e₁, Category.assoc]
  · rw [← Category.assoc, a₂, e₂]

/- English proof (translation)
Set `k : Over.mk x' ⟶ Over.mk x` to `Over.homMk (spMap φ) e`. Take `⟨σ', H', c⟩` from `GlobalTheory.emb_baseChange h₂ o g N' J b S s t m _ _ k σ (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) H`. Take `⟨th, ⟨-, P₁, P₂⟩, c'⟩` from `RepBC.projRep_baseChange R R' _ φ I _ _ _ _ _ _ σ P (isPullback_whisker t.A k)`. Use `⟨σ', H', GlobalTheory.ZM.ideals_homogeneous.2.2 R' _ (I.map (MvPolynomial.map φ)) _ _ _ σ' ⟨LB.isLB_linComb t.isLB _ _, fun B _ β y v hy hv => P₁ B β y v hy ((c' B y v).2 ((c B y v).1 hv)), fun B _ β v hv hF => ?_⟩⟩` and prove the remaining obligations. Simplify using `only [c, ← c']`.

Conclude with `P₂ B β v hv hF`.
-/
theorem emb_shrink (h₂ : Laws2) {t : TObj g (N' ^ 2) J b s} {m : ℕ} {R R' : Type} [CommRing R] [CommRing R']
    {x : Sp R ⟶ S} {x' : Sp R' ⟶ S} (φ : R →+* R') (e : spMap φ ≫ x = x') {σ I} (H : t.Emb m (Over.mk x) σ)
    (P : ProjRep I (fst (Over.mk x) t.A).left _ σ) : ∃ σ', t.Emb m (Over.mk x') σ' ∧
      ProjRep (idealOf (fst (Over.mk x') t.A).left _ σ' (𝟙 _)) (fst (Over.mk x') t.A).left _ σ' := by
  let k : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap φ) e
  obtain ⟨σ', H', c⟩ := GlobalTheory.emb_baseChange h₂ o g N' J b S s t m _ _ k σ (inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _))) H
  obtain ⟨th, ⟨-, P₁, P₂⟩, c'⟩ := RepBC.projRep_baseChange R R' _ φ I _ _ _ _ _ _ σ P (isPullback_whisker t.A k)
  refine ⟨σ', H', GlobalTheory.ZM.ideals_homogeneous.2.2 R' _ (I.map (MvPolynomial.map φ)) _ _ _ σ' ⟨LB.isLB_linComb t.isLB _ _,
    fun B _ β y v hy hv => P₁ B β y v hy ((c' B y v).2 ((c B y v).1 hv)), fun B _ β v hv hF => ?_⟩⟩
  simp only [c, ← c']
  exact P₂ B β v hv hF

/- English proof (translation)
Establish `one : ∀ t : TObj g (N' ^ 2) J b s, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (σ : _), IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.Emb m (Over.mk x) σ ∧ ProjRep (idealOf (fst (Over.mk x) t.A).left _ σ (𝟙 _)) (fst (Over.mk x) t.A).left _ σ` using `fun t => by`. Take `⟨R, _, x, v, hx, ⟨q, rfl⟩, H⟩` from `GlobalTheory.ThetaLocal.exists_hasTh h₁ h₂ o g N' J b S s t ho p`. Take `⟨R', _, φ, σ, hφ, ⟨q', rfl⟩, H₁, H₂⟩` from `GlobalTheory.ZM.EmbedLocal.exists_emb_projRep h₁ h₂ o g N' J b S s t m R x v hm h2 H q`. Conclude with `⟨R', inferInstance, spMap φ ≫ x, σ, inferInstance, ⟨q', rfl⟩, H₁, H₂⟩`. Take `⟨R, _, x, σ, hx, hp, H, P⟩` from `one t`.

Take `⟨R', _, x', σ', hx', hp', H', P'⟩` from `one t'`. Take `⟨Q, y, hy, hq, hr⟩` from `Scheme.exists_affine_mem_range_and_range_subset (U := x.opensRange ⊓ x'.opensRange) (x := p) ⟨hp, hp'⟩`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (IsOpenImmersion.lift x y fun z hz => (hr hz).1)`. Take `⟨φ', hφ'⟩` from `Spec.map_surjective (IsOpenImmersion.lift x' y fun z hz => (hr hz).2)`. Take `⟨τ, a, c⟩` from `emb_shrink h₂ (x' := (y : Sp Q ⟶ S)) φ.hom ((congrArg (· ≫ x) hφ).trans (IsOpenImmersion.lift_fac _ _ _)) H P`.

Take `⟨τ', a', c'⟩` from `emb_shrink h₂ (x' := (y : Sp Q ⟶ S)) φ'.hom ((congrArg (· ≫ x') hφ').trans (IsOpenImmersion.lift_fac _ _ _)) H' P'`. Conclude with `⟨Q, inferInstance, y, τ, τ', hy, hq, a, a', c, c'⟩`.
-/
theorem exists_common_emb (h₁ : Laws) (h₂ : Laws2) (t t' : TObj g (N' ^ 2) J b s) {m : ℕ} (h2 : 2 ≤ m)
    (hm : m ^ 2 ∣ N') (ho : Odd N') (p : S) : ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (σ : _) (σ' : _),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.Emb m (Over.mk x) σ ∧ t'.Emb m (Over.mk x) σ' ∧
      ProjRep (idealOf (fst (Over.mk x) t.A).left _ σ (𝟙 _)) (fst (Over.mk x) t.A).left _ σ ∧
      ProjRep (idealOf (fst (Over.mk x) t'.A).left _ σ' (𝟙 _)) (fst (Over.mk x) t'.A).left _ σ' := by
  have one : ∀ t : TObj g (N' ^ 2) J b s, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (σ : _),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.Emb m (Over.mk x) σ ∧
      ProjRep (idealOf (fst (Over.mk x) t.A).left _ σ (𝟙 _)) (fst (Over.mk x) t.A).left _ σ := fun t => by
    obtain ⟨R, _, x, v, hx, ⟨q, rfl⟩, H⟩ := GlobalTheory.ThetaLocal.exists_hasTh h₁ h₂ o g N' J b S s t ho p
    obtain ⟨R', _, φ, σ, hφ, ⟨q', rfl⟩, H₁, H₂⟩ := GlobalTheory.ZM.EmbedLocal.exists_emb_projRep h₁ h₂ o g N' J b S s t m R x v hm h2 H q
    exact ⟨R', inferInstance, spMap φ ≫ x, σ, inferInstance, ⟨q', rfl⟩, H₁, H₂⟩
  obtain ⟨R, _, x, σ, hx, hp, H, P⟩ := one t
  obtain ⟨R', _, x', σ', hx', hp', H', P'⟩ := one t'
  obtain ⟨Q, y, hy, hq, hr⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (U := x.opensRange ⊓ x'.opensRange) (x := p) ⟨hp, hp'⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift x y fun z hz => (hr hz).1)
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (IsOpenImmersion.lift x' y fun z hz => (hr hz).2)
  obtain ⟨τ, a, c⟩ := emb_shrink h₂ (x' := (y : Sp Q ⟶ S)) φ.hom
    ((congrArg (· ≫ x) hφ).trans (IsOpenImmersion.lift_fac _ _ _)) H P
  obtain ⟨τ', a', c'⟩ := emb_shrink h₂ (x' := (y : Sp Q ⟶ S)) φ'.hom
    ((congrArg (· ≫ x') hφ').trans (IsOpenImmersion.lift_fac _ _ _)) H' P'
  exact ⟨Q, inferInstance, y, τ, τ', hy, hq, a, a', c, c'⟩

/- English proof (translation)
Simplify using `only [idealOf, Ideal.mem_iInf] at hF`. Conclude with `hF B _ β y v ⟨hy, by rw [Category.comp_id]; exact hv⟩`.
-/
theorem ProjRep.eval_of_mem_idealOf {R σ : Type} [CommRing R] {Y : Scheme.{0}} {q : Y ⟶ Sp R} {M : LB Y}
    {th : σ → M.Sec} {F : MvPolynomial σ R} (hF : F ∈ idealOf q M th (𝟙 Y)) {B : Type} [CommRing B] {β : R →+* B}
    {y : Sp B ⟶ Y} {v : σ → B} (hy : y ≫ q = spMap β) (hv : SecCoord M th y v) : MvPolynomial.eval₂ β v F = 0 := by
  simp only [idealOf, Ideal.mem_iInf] at hF
  exact hF B _ β y v ⟨hy, by rw [Category.comp_id]; exact hv⟩

/- English proof (translation)
Introduce `F hF`. Rewrite using `[← MvPolynomial.sum_homogeneousComponent F]`. Use `Ideal.sum_mem _ fun e _ => ?_` and prove the remaining obligations. Establish `hF'` using `GlobalTheory.ZM.ideals_homogeneous.1 R _ _ _ _ _ σ' _ (LB.isLB_linComb t'.isLB _ _) F hF e`. Use `t.ab.smooth` as an intermediate fact.

Establish `: Smooth (fst (Over.mk x) t.A).left` using `inferInstanceAs (Smooth (pullback.fst x t.A.hom))`. Establish `: IsReduced (Over.mk x).left` using `isReduced_of_isOpenImmersion x`. Use `GlobalTheory.ZM.DenseFib.mem_idealOf_of_dense R _ _ _ _ σ (x ⁻¹' Sg) _ e (GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) t.A).left) inferInstance inferInstance (LB.isLB_linComb t.isLB _ _) (hd.preimage x.isOpenEmbedding.isOpenMap) (MvPolynomial.homogeneousComponen …` and prove the remaining obligations. Take `⟨Ω, _, _, i, su, u, ψ, ψ', a, a'⟩` from `hg K (spMap β ≫ x) (by`. Introduce and unpack `_ ⟨q, rfl⟩`.

Conclude with `hβ ⟨q, rfl⟩)`. Establish `w : (spMap i ≫ y ≫ (snd (Over.mk x) t.A).left) ≫ t.A.hom = 𝟙 _ ≫ spMap i ≫ spMap β ≫ x`. Rewrite using `[Category.id_comp, ← hy, Category.assoc, Category.assoc, Category.assoc, Over.w]`. Conclude with `congrArg (fun q => spMap i ≫ y ≫ q) (Over.w (fst (Over.mk x) t.A)).symm`. Establish `z₁` using `a.1.1.lift_fst _ _ w`.

Establish `z₂` using `a.1.1.lift_snd _ _ w`. Take `⟨y', c₁, c₂⟩` from `exists_lift (A := t'.A) (T := Over.mk x) (spMap i ≫ spMap β) (a.1.1.lift _ _ w ≫ ψ') (by`. Rewrite using `[Category.assoc _ ψ', a'.1.1.w, ← Category.assoc _ u.A.hom, z₂, Category.id_comp, Category.assoc]`. Use the proof step `rfl)`. Establish `hv'` using `coord_agree h₁ h₂ hm ho (inferInstanceAs (IsAffine (Spec _))) H H' a a' (spMap i ≫ spMap β) (Category.assoc _ _ _) (a.1.1.lift _ _ w) (y := spMap i ≫ y) (y' := y') (by rw [← Category.assoc _ u.A.hom, z₂, Category.id_comp, Category.assoc, hy]) (by rw [z₁, Category.assoc]) (by rw [ …`.

Use `ProjRep.eval_of_mem_idealOf hF' (β := i.comp β) (c₁.trans (spMap_comp _ _).symm) hv'` as an intermediate fact. Apply `i.injective` to reduce the goal to its premises. Rewrite using `[map_zero, MvPolynomial.eval₂_comp_left]`. Conclude with `this`.
-/
theorem idealOf_le [IsReduced S] (h₁ : Laws) (h₂ : Laws2) {t t' : TObj g (N' ^ 2) J b s} {Sg : Set S} (hd : Dense Sg)
    (hg : GeoGood t t' Sg) {m : ℕ} (hm : m ∣ N') (ho : Odd m) {R : Type} [CommRing R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] {σ σ'} (H : t.Emb m (Over.mk x) σ) (H' : t'.Emb m (Over.mk x) σ') :
    idealOf (fst (Over.mk x) t'.A).left _ σ' (𝟙 _) ≤ idealOf (fst (Over.mk x) t.A).left _ σ (𝟙 _) := by
  intro F hF
  rw [← MvPolynomial.sum_homogeneousComponent F]
  refine Ideal.sum_mem _ fun e _ => ?_
  have hF' := GlobalTheory.ZM.ideals_homogeneous.1 R _ _ _ _ _ σ' _ (LB.isLB_linComb t'.isLB _ _) F hF e
  have := t.ab.smooth
  have : Smooth (fst (Over.mk x) t.A).left := inferInstanceAs (Smooth (pullback.fst x t.A.hom))
  have : IsReduced (Over.mk x).left := isReduced_of_isOpenImmersion x
  refine GlobalTheory.ZM.DenseFib.mem_idealOf_of_dense R _ _ _ _ σ (x ⁻¹' Sg) _ e (GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) t.A).left)
    inferInstance inferInstance (LB.isLB_linComb t.isLB _ _) (hd.preimage x.isOpenEmbedding.isOpenMap)
    (MvPolynomial.homogeneousComponent_isHomogeneous e F) fun K _ _ β y v hy hβ hv => ?_
  obtain ⟨Ω, _, _, i, su, u, ψ, ψ', a, a'⟩ := hg K (spMap β ≫ x) (by
    rintro _ ⟨q, rfl⟩
    exact hβ ⟨q, rfl⟩)
  have w : (spMap i ≫ y ≫ (snd (Over.mk x) t.A).left) ≫ t.A.hom = 𝟙 _ ≫ spMap i ≫ spMap β ≫ x := by
    rw [Category.id_comp, ← hy, Category.assoc, Category.assoc, Category.assoc, Over.w]
    exact congrArg (fun q => spMap i ≫ y ≫ q) (Over.w (fst (Over.mk x) t.A)).symm
  have z₁ := a.1.1.lift_fst _ _ w
  have z₂ := a.1.1.lift_snd _ _ w
  obtain ⟨y', c₁, c₂⟩ := exists_lift (A := t'.A) (T := Over.mk x) (spMap i ≫ spMap β) (a.1.1.lift _ _ w ≫ ψ') (by
    rw [Category.assoc _ ψ', a'.1.1.w, ← Category.assoc _ u.A.hom, z₂, Category.id_comp, Category.assoc]
    rfl)
  have hv' := coord_agree h₁ h₂ hm ho (inferInstanceAs (IsAffine (Spec _))) H H' a a' (spMap i ≫ spMap β)
    (Category.assoc _ _ _) (a.1.1.lift _ _ w) (y := spMap i ≫ y) (y' := y')
    (by rw [← Category.assoc _ u.A.hom, z₂, Category.id_comp, Category.assoc, hy])
    (by rw [z₁, Category.assoc]) (by rw [← Category.assoc _ u.A.hom, z₂, Category.id_comp, c₁]) c₂
    (Coord.baseChange hv i)
  have := ProjRep.eval_of_mem_idealOf hF' (β := i.comp β) (c₁.trans (spMap_comp _ _).symm) hv'
  apply i.injective
  rw [map_zero, MvPolynomial.eval₂_comp_left]
  exact this

/- English proof (translation)
Establish `hm' : m ∣ N'` using `(dvd_pow_self m two_ne_zero).trans hm`. Establish `ho' : Odd m` using `ho.of_dvd_nat hm'`. Take `⟨R, _, x, σ, σ', hx, ⟨q, hq⟩, H, H', P, P'⟩` from `exists_common_emb h₁ h₂ t t' h2 hm ho (t.A.hom p)`. Take `⟨f, f₁, -, f₂, -⟩` from `GlobalTheory.ZM.RepMap.exists_map_of_coord R _ _ _ _ _ (fst (Over.mk x) t.A).left _ _ σ' σ P' P.1 fun B _ β y v hy hv => ⟨(P.2.1 B β y v hy hv).1, fun F hF => (P.2.1 B β y v hy hv).2 F (idealOf_le h₁ h₂ hd hg hm' ho' x H H' hF)⟩`. Establish `w : ∀ A : Over S, (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x` using `fun A => (Over.w _).trans (Over.w (fst (Over.mk x) A)).symm`.

Use `⟨_, (snd (Over.mk x) t.A).left, f ≫ (snd (Over.mk x) t'.A).left, inferInstanceAs (IsOpenImmersion (pullback.snd x t.A.hom)), ?_, ?_, fun K _ _ su u x₁ ψ ψ' a a' B _ z y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, -, hz⟩` from `Scheme.Pullback.exists_preimage_pullback (f := x) (g := t.A.hom) q p hq`. Conclude with `⟨z, hz⟩`. Rewrite using `[Category.assoc, w, w, ← Category.assoc, f₁]`. Establish `e₀ : (y ≫ (fst (Over.mk x) t.A).left) ≫ x = z ≫ u.A.hom ≫ x₁`.

Rewrite using `[Category.assoc, ← w, ← Category.assoc, hy, Category.assoc, a.1.1.w]`. Establish `hr : Set.range x₁ ⊆ Set.range x`. Introduce and unpack `_ ⟨r, rfl⟩`. Use `⟨(y ≫ (fst (Over.mk x) t.A).left) (default : PrimeSpectrum B), ?_⟩` and prove the remaining obligations. Conclude with `(congrArg (fun q => q (default : PrimeSpectrum B)) (e₀.trans (Category.assoc _ _ _).symm)).trans (congrArg x₁ (Subsingleton.elim (α := PrimeSpectrum K) _ _))`.

Establish `l` using `IsOpenImmersion.lift_fac x x₁ hr`. Establish `e₁ : y ≫ (fst (Over.mk x) t.A).left = z ≫ u.A.hom ≫ IsOpenImmersion.lift x x₁ hr`. Rewrite using `[← cancel_mono x, e₀, Category.assoc, Category.assoc, l]`. Take `⟨y', c₁, c₂⟩` from `exists_lift (A := t'.A) (T := Over.mk x) (y ≫ (fst (Over.mk x) t.A).left) (z ≫ ψ') (by`. Rewrite using `[Category.assoc z, a'.1.1.w]`.

Conclude with `e₀)`. Take `⟨k, hk⟩` from `exists_chart P.1 (y (default : PrimeSpectrum B))`. Take `⟨v, hv⟩` from `SegreCoord.exists_secCoord (th := σ) P.1 (x := y) (k := k) fun r => by`. Rewrite using `[Subsingleton.elim (α := PrimeSpectrum B) r default]`. Conclude with `hk`.

Establish `hv'` using `coord_agree h₁ h₂ hm' ho' (inferInstanceAs (IsAffine (Spec _))) H H' a a' _ l z e₁ hy (c₁.trans e₁) c₂ hv`. Take `⟨β, hβ⟩` from `Spec.map_surjective (y ≫ (fst (Over.mk x) t.A).left)`. Take `⟨k₁, k₂⟩` from `P'.2.1 B β.hom y' v (c₁.trans hβ.symm) hv'`. Establish `e : y ≫ f = y'` using `(P'.2.2 B β.hom v k₁ k₂).unique ⟨by rw [Category.assoc, f₁]; exact hβ.symm, (f₂ B y v).1 hv⟩ ⟨c₁.trans hβ.symm, hv'⟩`. Rewrite using `[← Category.assoc, e, c₂]`.
-/
theorem exists_local_compat [IsReduced S] (h₁ : Laws) (h₂ : Laws2) {t t' : TObj g (N' ^ 2) J b s} {Sg : Set S}
    (hd : Dense Sg) (hg : GeoGood t t' Sg) {m : ℕ} (h2 : 2 ≤ m) (hm : m ^ 2 ∣ N') (ho : Odd N') (p : t.A.left) :
    ∃ (X : Scheme.{0}) (c : X ⟶ t.A.left) (f : X ⟶ t'.A.left), IsOpenImmersion c ∧ p ∈ Set.range c ∧
      Compat t t' c f := by
  have hm' : m ∣ N' := (dvd_pow_self m two_ne_zero).trans hm
  have ho' : Odd m := ho.of_dvd_nat hm'
  obtain ⟨R, _, x, σ, σ', hx, ⟨q, hq⟩, H, H', P, P'⟩ := exists_common_emb h₁ h₂ t t' h2 hm ho (t.A.hom p)
  obtain ⟨f, f₁, -, f₂, -⟩ := GlobalTheory.ZM.RepMap.exists_map_of_coord R _ _ _ _ _ (fst (Over.mk x) t.A).left _ _ σ' σ P' P.1
    fun B _ β y v hy hv => ⟨(P.2.1 B β y v hy hv).1,
      fun F hF => (P.2.1 B β y v hy hv).2 F (idealOf_le h₁ h₂ hd hg hm' ho' x H H' hF)⟩
  have w : ∀ A : Over S, (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x := fun A =>
    (Over.w _).trans (Over.w (fst (Over.mk x) A)).symm
  refine ⟨_, (snd (Over.mk x) t.A).left, f ≫ (snd (Over.mk x) t'.A).left,
    inferInstanceAs (IsOpenImmersion (pullback.snd x t.A.hom)), ?_, ?_,
    fun K _ _ su u x₁ ψ ψ' a a' B _ z y hy => ?_⟩
  · obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := t.A.hom) q p hq
    exact ⟨z, hz⟩
  · rw [Category.assoc, w, w, ← Category.assoc, f₁]
  have e₀ : (y ≫ (fst (Over.mk x) t.A).left) ≫ x = z ≫ u.A.hom ≫ x₁ := by
    rw [Category.assoc, ← w, ← Category.assoc, hy, Category.assoc, a.1.1.w]
  have hr : Set.range x₁ ⊆ Set.range x := by
    rintro _ ⟨r, rfl⟩
    refine ⟨(y ≫ (fst (Over.mk x) t.A).left) (default : PrimeSpectrum B), ?_⟩
    exact (congrArg (fun q => q (default : PrimeSpectrum B)) (e₀.trans (Category.assoc _ _ _).symm)).trans
      (congrArg x₁ (Subsingleton.elim (α := PrimeSpectrum K) _ _))
  have l := IsOpenImmersion.lift_fac x x₁ hr
  have e₁ : y ≫ (fst (Over.mk x) t.A).left = z ≫ u.A.hom ≫ IsOpenImmersion.lift x x₁ hr := by
    rw [← cancel_mono x, e₀, Category.assoc, Category.assoc, l]
  obtain ⟨y', c₁, c₂⟩ := exists_lift (A := t'.A) (T := Over.mk x) (y ≫ (fst (Over.mk x) t.A).left) (z ≫ ψ') (by
    rw [Category.assoc z, a'.1.1.w]
    exact e₀)
  obtain ⟨k, hk⟩ := exists_chart P.1 (y (default : PrimeSpectrum B))
  obtain ⟨v, hv⟩ := SegreCoord.exists_secCoord (th := σ) P.1 (x := y) (k := k) fun r => by
    rw [Subsingleton.elim (α := PrimeSpectrum B) r default]; exact hk
  have hv' := coord_agree h₁ h₂ hm' ho' (inferInstanceAs (IsAffine (Spec _))) H H' a a' _ l z e₁ hy
    (c₁.trans e₁) c₂ hv
  obtain ⟨β, hβ⟩ := Spec.map_surjective (y ≫ (fst (Over.mk x) t.A).left)
  obtain ⟨k₁, k₂⟩ := P'.2.1 B β.hom y' v (c₁.trans hβ.symm) hv'
  have e : y ≫ f = y' := (P'.2.2 B β.hom v k₁ k₂).unique
    ⟨by rw [Category.assoc, f₁]; exact hβ.symm, (f₂ B y v).1 hv⟩ ⟨c₁.trans hβ.symm, hv'⟩
  rw [← Category.assoc, e, c₂]

/- English proof (translation)
Establish `inv : ∀ {t t' : TObj g k J b s} {φ : t.A.left ⟶ t'.A.left} {φ' : t'.A.left ⟶ t.A.left}, GeoGood t t' Sg → Compat t t' (𝟙 _) φ → Compat t' t (𝟙 _) φ' → φ ≫ φ' = 𝟙 _` using `fun {t t' φ φ'} hg h h' => by`. Use `t.ab.smooth` as an intermediate fact. Use `t.ab.proper` as an intermediate fact. Use `GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom` as an intermediate fact. Use `ext_of_geoGood hd hg t.A.hom t.A.hom (by rw [Category.assoc, h'.1, Category.id_comp, h.1, Category.id_comp]) (Category.id_comp _) fun K _ _ su u x ψ ψ' a a' y hy => ?_` and prove the remaining obligations.

Rewrite using `[← a.1.1.lift_fst y (𝟙 _) (hy.trans (Category.id_comp _).symm), Category.assoc, Category.assoc, ← Category.assoc ψ, h.fibre a a', h'.fibre a' a, Category.comp_id]`. Use `t.ab.smooth` as an intermediate fact. Use `t'.ab.proper` as an intermediate fact. Use `GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom` as an intermediate fact. Establish `w : φ ≫ t'.A.hom = t.A.hom` using `h.1.trans (Category.id_comp _)`.

Set `e : t.A ≅ t'.A` to `Over.isoMk ⟨φ, φ', inv hg h h', inv hg.symm h' h⟩ w`. Establish `sec : ∀ (c : S ⟶ t.A.left) (c' : S ⟶ t'.A.left), c ≫ t.A.hom = 𝟙 _ → c' ≫ t'.A.hom = 𝟙 _ → (∀ (K : Type) [Field K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S) (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' → ∃ z : Sp K ⟶ u.A.lef …` using `fun c c' hc hc' H => ext_of_geoGood hd hg (𝟙 S) t'.A.hom (by rw [Category.assoc, w, hc]) hc' fun K _ _ su u x ψ ψ' a a' y hy => by`. Take `⟨z, z₁, z₂⟩` from `H K su u x ψ ψ' a a'`. Rewrite `hy` using `[Category.comp_id]`. Rewrite using `[hy, ← Category.assoc, z₁, z₂, Category.assoc, h.fibre a a']`.

Establish `one : ∀ A : Over S, ∀ [GrpObj A], (1 : baseOver S ⟶ A).left = (η[A]).left` using `fun A _ => Category.id_comp _`. Establish `: IsMonHom e.hom` using `h₁.rigidity S t.A t'.A t.ab t'.ab e.hom (Over.OverMorphism.ext (sec _ _ (Over.w _) (Over.w _) fun K _ su u x ψ ψ' a a' => by`. Establish `hτ : x ≫ (baseOver S).hom = (baseOver (Sp K)).hom ≫ x` using `(Category.comp_id _).trans (Category.id_comp _).symm`. Use `⟨(1 : baseOver _ ⟶ u.A).left, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(congrArg _ (one _).symm).trans (ThetaPtMove.over_one a.1 (T := baseOver _) (T₀ := baseOver S) x hτ)`.

Conclude with `(congrArg _ (one _).symm).trans (ThetaPtMove.over_one a'.1 (T := baseOver _) (T₀ := baseOver S) x hτ)))`. Use `⟨isGrpPullback_of_iso e, fun i => (sec _ _ (Over.w _) (Over.w _) fun K _ su u x ψ ψ' a a' => ⟨(u.pt i).left, (a.2.2.1 i).symm, (a'.2.2.1 i).symm⟩).trans (Category.id_comp _).symm, fun j => ?_⟩` and prove the remaining obligations. Use `ext_of_geoGood hd hg t.A.hom t'.A.hom (by rw [Category.assoc, w, Over.w]) (by rw [Category.assoc, Over.w, w]) fun K _ _ su u x ψ ψ' a a' y hy => ?_` and prove the remaining obligations. Rewrite using `[← a.1.1.lift_fst y (𝟙 _) (hy.trans (Category.id_comp _).symm), Category.assoc, Category.assoc, ← Category.assoc ψ, ← Category.assoc ψ, ← a.2.2.2, Category.assoc, h.fibre a a', a'.2.2.2]`.
-/
theorem parts_of_compat [IsReduced S] (h₁ : Laws) {k : ℕ} {b : TBase o k} {t t' : TObj g k J b s} {Sg : Set S}
    (hd : Dense Sg) (hg : GeoGood t t' Sg) {φ : t.A.left ⟶ t'.A.left} {φ' : t'.A.left ⟶ t.A.left}
    (h : Compat t t' (𝟙 _) φ) (h' : Compat t' t (𝟙 _) φ') : IsGrpPullback t.A t'.A (𝟙 _) φ ∧
      (∀ i, (t.pt i).left ≫ φ = 𝟙 _ ≫ (t'.pt i).left) ∧ ∀ j, (t.act j).left ≫ φ = φ ≫ (t'.act j).left := by
  have inv : ∀ {t t' : TObj g k J b s} {φ : t.A.left ⟶ t'.A.left} {φ' : t'.A.left ⟶ t.A.left}, GeoGood t t' Sg →
      Compat t t' (𝟙 _) φ → Compat t' t (𝟙 _) φ' → φ ≫ φ' = 𝟙 _ := fun {t t' φ φ'} hg h h' => by
    have := t.ab.smooth
    have := t.ab.proper
    have := GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom
    refine ext_of_geoGood hd hg t.A.hom t.A.hom
      (by rw [Category.assoc, h'.1, Category.id_comp, h.1, Category.id_comp]) (Category.id_comp _)
      fun K _ _ su u x ψ ψ' a a' y hy => ?_
    rw [← a.1.1.lift_fst y (𝟙 _) (hy.trans (Category.id_comp _).symm), Category.assoc, Category.assoc,
      ← Category.assoc ψ, h.fibre a a', h'.fibre a' a, Category.comp_id]
  have := t.ab.smooth
  have := t'.ab.proper
  have := GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom
  have w : φ ≫ t'.A.hom = t.A.hom := h.1.trans (Category.id_comp _)
  let e : t.A ≅ t'.A := Over.isoMk ⟨φ, φ', inv hg h h', inv hg.symm h' h⟩ w
  have sec : ∀ (c : S ⟶ t.A.left) (c' : S ⟶ t'.A.left), c ≫ t.A.hom = 𝟙 _ → c' ≫ t'.A.hom = 𝟙 _ →
      (∀ (K : Type) [Field K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S) (ψ : u.A.left ⟶ t.A.left)
        (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
          ∃ z : Sp K ⟶ u.A.left, x ≫ c = z ≫ ψ ∧ x ≫ c' = z ≫ ψ') → c ≫ φ = c' := fun c c' hc hc' H =>
    ext_of_geoGood hd hg (𝟙 S) t'.A.hom (by rw [Category.assoc, w, hc]) hc' fun K _ _ su u x ψ ψ' a a' y hy => by
      obtain ⟨z, z₁, z₂⟩ := H K su u x ψ ψ' a a'
      rw [Category.comp_id] at hy
      rw [hy, ← Category.assoc, z₁, z₂, Category.assoc, h.fibre a a']
  have one : ∀ A : Over S, ∀ [GrpObj A], (1 : baseOver S ⟶ A).left = (η[A]).left := fun A _ => Category.id_comp _
  have : IsMonHom e.hom := h₁.rigidity S t.A t'.A t.ab t'.ab e.hom (Over.OverMorphism.ext (sec _ _ (Over.w _) (Over.w _)
    fun K _ su u x ψ ψ' a a' => by
      have hτ : x ≫ (baseOver S).hom = (baseOver (Sp K)).hom ≫ x :=
        (Category.comp_id _).trans (Category.id_comp _).symm
      refine ⟨(1 : baseOver _ ⟶ u.A).left, ?_, ?_⟩
      · exact (congrArg _ (one _).symm).trans
          (ThetaPtMove.over_one a.1 (T := baseOver _) (T₀ := baseOver S) x hτ)
      · exact (congrArg _ (one _).symm).trans
          (ThetaPtMove.over_one a'.1 (T := baseOver _) (T₀ := baseOver S) x hτ)))
  refine ⟨isGrpPullback_of_iso e, fun i => (sec _ _ (Over.w _) (Over.w _) fun K _ su u x ψ ψ' a a' =>
    ⟨(u.pt i).left, (a.2.2.1 i).symm, (a'.2.2.1 i).symm⟩).trans (Category.id_comp _).symm, fun j => ?_⟩
  refine ext_of_geoGood hd hg t.A.hom t'.A.hom (by rw [Category.assoc, w, Over.w]) (by rw [Category.assoc, Over.w, w])
    fun K _ _ su u x ψ ψ' a a' y hy => ?_
  rw [← a.1.1.lift_fst y (𝟙 _) (hy.trans (Category.id_comp _).symm), Category.assoc, Category.assoc,
    ← Category.assoc ψ, ← Category.assoc ψ, ← a.2.2.2, Category.assoc, h.fibre a a', a'.2.2.2]

/- English proof (translation)
Introduce `h₁ h₂ o _ g N' J b m R _ _ β t t' h2 hm ho hd`. Establish `hg` using `GlobalTheory.TUniq.geoGood_commonFibres o g (N' ^ 2) J b _ _ t t'`. Establish `h3 : 3 ≤ N' ^ 2`. Use `Nat.le_of_dvd ho.pos hm` as an intermediate fact. Establish `: 2 ≤ N'` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Use `⟨?_, GlobalTheory.TUniq.tObj_rigid h₁ o g _ J b _ _ _ _ t t' _ h3⟩` and prove the remaining obligations. Take `⟨φ, h⟩` from `exists_compat_of_local hd hg (exists_local_compat h₁ h₂ hd hg h2 hm ho)`. Take `⟨φ', h'⟩` from `exists_compat_of_local hd hg.symm (exists_local_compat h₁ h₂ hd hg.symm h2 hm ho)`. Take `⟨a₁, a₂, a₃⟩` from `parts_of_compat h₁ hd hg h h'`.

Conclude with `⟨φ, a₁, GlobalTheory.TUniq.lbIso_of_compat o g _ J b R _ t t' _ φ hd hg h a₁, a₂, a₃⟩`.
-/
theorem iso_unique_of_dense : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (m : ℕ) (R : Type) [CommRing R] [IsReduced R] (β : o →+* R) (t t' : TObj g (N' ^ 2) J b (spMap β)), 2 ≤ m → m ^ 2 ∣ N' → Odd N' → Dense {p : Sp R | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (u : TObj g (N' ^ 2) J b (x ≫ spMap β)), p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x} → TMap t t' (𝟙 _) ∧ ∀ φ φ' : t.A.left ⟶ t'.A.left, IsGrpPullback t.A t'.A (𝟙 _) φ → IsGrpPullback t.A t'.A (𝟙 _) φ' → LBIso t.L (t'.L.pull φ) → LBIso t.L (t'.L.pull φ') → (∀ i, (t.pt i).left ≫ φ = (t.pt i).left ≫ φ') → φ = φ' := by
  intro h₁ h₂ o _ g N' J b m R _ _ β t t' h2 hm ho hd
  have hg := GlobalTheory.TUniq.geoGood_commonFibres o g (N' ^ 2) J b _ _ t t'
  have h3 : 3 ≤ N' ^ 2 := by
    have := Nat.le_of_dvd ho.pos hm
    have : 2 ≤ N' := by nlinarith
    nlinarith
  refine ⟨?_, GlobalTheory.TUniq.tObj_rigid h₁ o g _ J b _ _ _ _ t t' _ h3⟩
  obtain ⟨φ, h⟩ := exists_compat_of_local hd hg (exists_local_compat h₁ h₂ hd hg h2 hm ho)
  obtain ⟨φ', h'⟩ := exists_compat_of_local hd hg.symm (exists_local_compat h₁ h₂ hd hg.symm h2 hm ho)
  obtain ⟨a₁, a₂, a₃⟩ := parts_of_compat h₁ hd hg h h'
  exact ⟨φ, a₁, GlobalTheory.TUniq.lbIso_of_compat o g _ J b R _ t t' _ φ hd hg h a₁, a₂, a₃⟩

end GlobalTheory.TUniq
