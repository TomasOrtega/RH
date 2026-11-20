import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationIffDualNumberPoint
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS.TangentAt

def dval {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    DualNumber ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)

/- English proof (translation)
Simplify using `only [dval, ← Scheme.Hom.appLE_comp_appLE v t U V ⊤ e hV, CommRingCat.hom_comp, RingHom.comp_apply]`.
-/
theorem dval_comp {X Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (t : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (v ≫ t) ⁻¹ᵁ U) (V : X.Opens) (e : V ≤ t ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) (f : Γ(Y, U)) :
    dval (v ≫ t) U h f = dval v V hV ((t.appLE U V e).hom f) := by
  simp only [dval, ← Scheme.Hom.appLE_comp_appLE v t U V ⊤ e hV, CommRingCat.hom_comp, RingHom.comp_apply]

/- English proof (translation)
Establish `key` using `congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key`. Rewrite using `[← key]`. Both sides reduce to the same expression.
-/
private theorem ΓSpecIso_appLE_spMap_top {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e : (⊤ : (Sp S).Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Scheme.Hom.appLE (spMap φ) ⊤ ⊤ e).hom a) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
  have key := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  rw [← key]
  rfl

/- English proof (translation)
Establish `h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U` using `fun x _ => h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))`. Rewrite using `[valAt', dif_pos h', valAt, dval, ← Scheme.Hom.appLE_comp_appLE _ v U ⊤ ⊤ h (fun _ _ => trivial), CommRingCat.hom_comp, RingHom.comp_apply]`. Conclude with `(ΓSpecIso_appLE_spMap_top (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom _ _).symm`.
-/
theorem fst_dval {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    (dval v U h f).fst = valAt' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) U f := by
  have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := fun x _ =>
    h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))
  rw [valAt', dif_pos h', valAt, dval, ← Scheme.Hom.appLE_comp_appLE _ v U ⊤ ⊤ h (fun _ _ => trivial),
    CommRingCat.hom_comp, RingHom.comp_apply]
  exact (ΓSpecIso_appLE_spMap_top (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom _ _).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Assume the negation of the conclusion as `hne`. Conclude with `hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))`. Introduce `h0`.

Establish `hsq : x * x = 0`. Apply the tactic sequence `ext <;> simp [h0]`. Conclude with `hp.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.zero_mem)`.
-/
private theorem mem_prime_dualNumber_iff_fst_eq_zero (p : Ideal (DualNumber ℂ)) (hp : p.IsPrime) (x : DualNumber ℂ) :
    x ∈ p ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra hne
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx
      (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))
  · intro h0
    have hsq : x * x = 0 := by
      ext <;> simp [h0]
    exact hp.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.zero_mem)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv x _`. Conclude with `hv (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))`. Introduce `hv y _`. Set `x : ↥(Sp ℂ)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)`.

Establish `e : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x = y`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use extensionality with `a`. Conclude with `(mem_prime_dualNumber_iff_fst_eq_zero _ (PrimeSpectrum.isPrime _) a).trans (mem_prime_dualNumber_iff_fst_eq_zero _ (show PrimeSpectrum (DualNumber ℂ) from y).isPrime a).symm`. Establish `hx : v.base ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x) ∈ U` using `hv (Set.mem_univ x)`.

Rewrite `hx` using `[e]`. Conclude with `hx`.
-/
theorem top_le_iff_dual {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
  constructor
  · intro hv x _
    exact hv (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))
  · intro hv y _
    let x : ↥(Sp ℂ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have e : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x = y := by
      apply PrimeSpectrum.ext
      ext a
      exact (mem_prime_dualNumber_iff_fst_eq_zero _ (PrimeSpectrum.isPrime _) a).trans
        (mem_prime_dualNumber_iff_fst_eq_zero _ (show PrimeSpectrum (DualNumber ℂ) from y).isPrime a).symm
    have hx : v.base ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x) ∈ U := hv (Set.mem_univ x)
    rw [e] at hx
    exact hx

/- English proof (translation)
Introduce `_ _` and use `trivial`.
-/
private theorem top_le_preimage_top' {X Y : Scheme.{0}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

/- English proof (translation)
Establish `hD : ∀ c : ℂ, dval (v ≫ p) ⊤ (top_le_preimage_top' _) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c) = algebraMap ℂ (DualNumber ℂ) c`. Introduce `c`. Apply `TrivSqZeroExt.ext` to reduce the goal to its premises. Rewrite using `[fst_dval, h1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, show (𝟙 (Sp ℂ)) = spMap (RingHom.id ℂ) by simp [spMap], valAt', dif_pos (top_le_preimage_top' _), valAt]`. Conclude with `(ΓSpecIso_appLE_spMap_top (RingHom.id ℂ) _ _).trans (by simp)`.

Rewrite using `[dval_comp v p ⊤ (top_le_preimage_top' _) ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _)]`. Use `(h2 c).trans ?_` and prove the remaining obligations. Rewrite using `[TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]`. Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv, ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]`.

Use `CommRingCat.hom_ext (RingHom.ext fun c => ?_)` and prove the remaining obligations. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Use `(hD c).trans ?_` and prove the remaining obligations. Establish `k` using `ΓSpecIso_appLE_spMap_top (algebraMap ℂ (DualNumber ℂ)) (top_le_preimage_top' _) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)`. Rewrite `k` using `[Iso.inv_hom_id_apply]`.

Conclude with `k.symm`.
-/
theorem comp_eq_spMap {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (v : Sp (DualNumber ℂ) ⟶ X)
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ p = 𝟙 _)
    (h2 : ∀ a, (dval v ⊤ le_top (constFn p ⊤ a)).snd = 0) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) := by
  have hD : ∀ c : ℂ, dval (v ≫ p) ⊤ (top_le_preimage_top' _) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c) =
      algebraMap ℂ (DualNumber ℂ) c := by
    intro c
    apply TrivSqZeroExt.ext
    · rw [fst_dval, h1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
        show (𝟙 (Sp ℂ)) = spMap (RingHom.id ℂ) by simp [spMap],
        valAt', dif_pos (top_le_preimage_top' _), valAt]
      exact (ΓSpecIso_appLE_spMap_top (RingHom.id ℂ) _ _).trans (by simp)
    · rw [dval_comp v p ⊤ (top_le_preimage_top' _) ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _)]
      refine (h2 c).trans ?_
      rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv,
    ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  refine (hD c).trans ?_
  have k := ΓSpecIso_appLE_spMap_top (algebraMap ℂ (DualNumber ℂ)) (top_le_preimage_top' _)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)
  rw [Iso.inv_hom_id_apply] at k
  exact k.symm

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

def tr (a : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex a) * 𝟙 A

/- English proof (translation)
Rewrite using `[tr, comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit B), Category.comp_id]`.
-/
theorem comp_tr {B : Over (Sp ℂ)} (x : B ⟶ A) (a : Fin g → ℂ) : x ≫ tr u a = (toUnit B ≫ u.ex a) * x := by
  rw [tr, comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit B), Category.comp_id]

/- English proof (translation)
Rewrite using `[comp_tr, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, u.ex_add]`.
-/
theorem ex_tr (a z : Fin g → ℂ) : u.ex z ≫ tr u a = u.ex (a + z) := by
  rw [comp_tr, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, u.ex_add]

/- English proof (translation)
Establish `h` using `u.ex_add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `_root_.mul_eq_left.mp h.symm`.
-/
theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact _root_.mul_eq_left.mp h.symm

/- English proof (translation)
Rewrite using `[comp_tr, tr, ← _root_.mul_assoc, ← comp_mul, ← u.ex_add, add_neg_cancel, ex_zero, comp_one, _root_.one_mul]`.
-/
theorem tr_neg_tr (a : Fin g → ℂ) : tr u (-a) ≫ tr u a = 𝟙 A := by
  rw [comp_tr, tr, ← _root_.mul_assoc, ← comp_mul, ← u.ex_add, add_neg_cancel, ex_zero, comp_one, _root_.one_mul]

def DiffAt (v : Sp (DualNumber ℂ) ⟶ A.left) (z w : Fin g → ℂ) : Prop :=
  ∀ (U : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(A.left, U)),
    (dval v U h f).snd = fderiv ℂ (fun z' => valAt' (u.ex z').left U f) z w

/- English proof (translation)
Establish `nat : ∀ {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)), valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f`. Introduce `X Y x φ U V e hx f`. Establish `hxφ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U` using `fun y hy => e (hx hy)`. Rewrite using `[valAt', dif_pos hx, valAt', dif_pos hxφ, valAt, valAt, ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ e hx, CommRingCat.hom_comp, RingHom.comp_apply]`. Introduce `U h' f`.

Establish `hV : ⊤ ≤ v ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U)` using `h'`. Rewrite using `[dval_comp v (TangentAt.tr u a).left U h' _ le_rfl hV f, h]`. Establish `hfun : (fun z' => valAt' (u.ex z').left ((TangentAt.tr u a).left ⁻¹ᵁ U) (((TangentAt.tr u a).left.appLE U _ le_rfl).hom f)) = fun z' => valAt' (u.ex (a + z')).left U f`. Use function extensionality and compare the values at `z'`. Distinguish the cases in `hz : ⊤ ≤ (u.ex z').left ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U)`.

Rewrite using `[nat _ _ _ _ _ hz, ← Over.comp_left, ex_tr]`. Establish `hz' : ¬ ⊤ ≤ (u.ex (a + z')).left ⁻¹ᵁ U`. Rewrite using `[← ex_tr, Over.comp_left]`. Conclude with `hz`. Rewrite using `[valAt', dif_neg hz, valAt', dif_neg hz']`.

Rewrite using `[hfun]`. Conclude with `congrArg (fun L => L w) (fderiv_comp_add_left (𝕜 := ℂ) (f := fun y => valAt' (u.ex y).left U f) a)`.
-/
theorem DiffAt.tr {v : Sp (DualNumber ℂ) ⟶ A.left} {z w : Fin g → ℂ} (h : DiffAt u v z w) (a : Fin g → ℂ) :
    DiffAt u (v ≫ (tr u a).left) (a + z) w := by
  have nat : ∀ {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
      (e : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)),
      valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by
    intro X Y x φ U V e hx f
    have hxφ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := fun y hy => e (hx hy)
    rw [valAt', dif_pos hx, valAt', dif_pos hxφ, valAt, valAt, ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ e hx,
      CommRingCat.hom_comp, RingHom.comp_apply]
  intro U h' f
  have hV : ⊤ ≤ v ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U) := h'
  rw [dval_comp v (TangentAt.tr u a).left U h' _ le_rfl hV f, h]
  have hfun : (fun z' => valAt' (u.ex z').left ((TangentAt.tr u a).left ⁻¹ᵁ U) (((TangentAt.tr u a).left.appLE U _ le_rfl).hom f)) =
      fun z' => valAt' (u.ex (a + z')).left U f := by
    funext z'
    by_cases hz : ⊤ ≤ (u.ex z').left ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U)
    · rw [nat _ _ _ _ _ hz, ← Over.comp_left, ex_tr]
    · have hz' : ¬ ⊤ ≤ (u.ex (a + z')).left ⁻¹ᵁ U := by
        rw [← ex_tr, Over.comp_left]
        exact hz
      rw [valAt', dif_neg hz, valAt', dif_neg hz']
  rw [hfun]
  exact congrArg (fun L => L w) (fderiv_comp_add_left (𝕜 := ℂ) (f := fun y => valAt' (u.ex y).left U f) a)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `DiffAt.tr u h (-z)`. Rewrite `h'` using `[neg_add_cancel]`. Then use the resulting hypothesis. Introduce `h`.

Establish `h'` using `DiffAt.tr u h z`. Rewrite `h'` using `[add_zero, Category.assoc, ← Over.comp_left, tr_neg_tr, Over.id_left, Category.comp_id]`. Then use the resulting hypothesis.
-/
theorem diffAt_iff (v : Sp (DualNumber ℂ) ⟶ A.left) (z w : Fin g → ℂ) :
    DiffAt u v z w ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w := by
  constructor
  · intro h
    have h' := DiffAt.tr u h (-z)
    rwa [neg_add_cancel] at h'
  · intro h
    have h' := DiffAt.tr u h z
    rwa [add_zero, Category.assoc, ← Over.comp_left, tr_neg_tr, Over.id_left, Category.comp_id] at h'

/- English proof (translation)
Take `⟨v, ⟨hv0, hvd⟩, -⟩` from `PtDual.existsUnique_point hδ`. Establish `hv0' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (u.ex z).left` using `hv0`. Establish `hvd' : ∀ (W : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(A.left, W)), (dval v W h f).snd = δ W f` using `hvd`. Establish `hone : (u.ex 0).left = (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left`. Rewrite using `[ex_zero]`.

Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Establish `h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ (tr u (-z)).left = (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left`. Rewrite using `[← Category.assoc, hv0', ← Over.comp_left, ex_tr, neg_add_cancel, hone]`. Establish `h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v ≫ (tr u (-z)).left) ≫ A.hom = 𝟙 _`. Rewrite using `[← Category.assoc, h0]`.

Conclude with `Over.w _`. Establish `hc' : ∀ a, (dval (v ≫ (tr u (-z)).left) ⊤ (top_le_preimage_top' _) (constFn A.hom ⊤ a)).snd = 0`. Introduce `a`. Rewrite using `[dval_comp v (tr u (-z)).left ⊤ _ ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _), hvd']`. Establish `e3` using `congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) (Scheme.Hom.appLE_comp_appLE (tr u (-z)).left A.hom ⊤ ⊤ ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _))`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e3`. Establish `key : ∀ (k : A.left ⟶ Sp ℂ) (_ : k = A.hom) (e : ⊤ ≤ k ⁻¹ᵁ ⊤), (k.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = constFn A.hom ⊤ a`. Introduce and unpack `_ rfl e`. Both sides reduce to the same expression. Establish `e4 : ((tr u (-z)).left.appLE ⊤ ⊤ (top_le_preimage_top' _)).hom (constFn A.hom ⊤ a) = constFn A.hom ⊤ a` using `e3.trans (key _ (Over.w _) _)`.

Rewrite using `[e4]`. Conclude with `hc a`. Set `v'' : epsR ℂ ⟶ A` to `Over.homMk (v ≫ (tr u (-z)).left) (comp_eq_spMap A.hom _ h1 hc')`. Establish `htv : IsTangent v''` using `h0`. Take `⟨w, hw, huniq⟩` from `htan v'' htv`.

Establish `hdiff : ∀ w', u.IsDiff w' v'' ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w'` using `fun _ => Iff.rfl`. Use `⟨w, ?_, ?_⟩` and prove the remaining obligations. Introduce `O f hO`. Establish `hv : ⊤ ≤ v ⁻¹ᵁ O` using `(top_le_iff_dual v O).2 (by rw [hv0']; exact hO)`. Rewrite using `[← hvd' O hv f]`.

Conclude with `((diffAt_iff u v z w).2 ((hdiff w).1 hw)) O hv f`. Introduce `w' hw'`. Apply `huniq` to reduce the goal to its premises. Rewrite using `[hdiff, ← diffAt_iff]`. Introduce `U h f`.

Rewrite using `[hvd' U h f]`. Conclude with `hw' U f (by rw [← hv0']; exact (top_le_iff_dual v U).1 h)`.
-/
theorem existsUnique_vector (htan : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (z : Fin g → ℂ)
    (δ : ∀ W : A.left.Opens, Γ(A.left, W) → ℂ) (hδ : PtDer (u.ex z).left δ)
    (hc : ∀ a, δ ⊤ (constFn A.hom ⊤ a) = 0) :
    ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  obtain ⟨v, ⟨hv0, hvd⟩, -⟩ := PtDual.existsUnique_point hδ
  have hv0' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (u.ex z).left := hv0
  have hvd' : ∀ (W : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(A.left, W)), (dval v W h f).snd = δ W f := hvd
  have hone : (u.ex 0).left = (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left := by
    rw [ex_zero]
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ (tr u (-z)).left =
      (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left := by
    rw [← Category.assoc, hv0', ← Over.comp_left, ex_tr, neg_add_cancel, hone]
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v ≫ (tr u (-z)).left) ≫ A.hom = 𝟙 _ := by
    rw [← Category.assoc, h0]
    exact Over.w _
  have hc' : ∀ a, (dval (v ≫ (tr u (-z)).left) ⊤ (top_le_preimage_top' _) (constFn A.hom ⊤ a)).snd = 0 := by
    intro a
    rw [dval_comp v (tr u (-z)).left ⊤ _ ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _), hvd']
    have e3 := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE (tr u (-z)).left A.hom ⊤ ⊤ ⊤ (top_le_preimage_top' _)
        (top_le_preimage_top' _))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
    have key : ∀ (k : A.left ⟶ Sp ℂ) (_ : k = A.hom) (e : ⊤ ≤ k ⁻¹ᵁ ⊤),
        (k.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = constFn A.hom ⊤ a := by
      rintro _ rfl e
      rfl
    have e4 : ((tr u (-z)).left.appLE ⊤ ⊤ (top_le_preimage_top' _)).hom (constFn A.hom ⊤ a) =
        constFn A.hom ⊤ a := e3.trans (key _ (Over.w _) _)
    rw [e4]
    exact hc a
  let v'' : epsR ℂ ⟶ A := Over.homMk (v ≫ (tr u (-z)).left) (comp_eq_spMap A.hom _ h1 hc')
  have htv : IsTangent v'' := h0
  obtain ⟨w, hw, huniq⟩ := htan v'' htv
  have hdiff : ∀ w', u.IsDiff w' v'' ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w' := fun _ => Iff.rfl
  refine ⟨w, ?_, ?_⟩
  · intro O f hO
    have hv : ⊤ ≤ v ⁻¹ᵁ O := (top_le_iff_dual v O).2 (by rw [hv0']; exact hO)
    rw [← hvd' O hv f]
    exact ((diffAt_iff u v z w).2 ((hdiff w).1 hw)) O hv f
  · intro w' hw'
    apply huniq
    rw [hdiff, ← diffAt_iff]
    intro U h f
    rw [hvd' U h f]
    exact hw' U f (by rw [← hv0']; exact (top_le_iff_dual v U).1 h)

/- English proof (translation)
Introduce `P₀ u Hm χ hG z δ hδ hc`. Take `⟨-, htan, -, -, -⟩` from `hG`. Conclude with `existsUnique_vector u htan z δ hδ hc`.
-/
theorem tangent_at_point : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ z δ, PtDer (u.ex z).left δ → (∀ a, δ ⊤ (constFn P₀.A.hom ⊤ a) = 0) → ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  intro P₀ u Hm χ hG z δ hδ hc
  obtain ⟨-, htan, -, -, -⟩ := hG
  exact existsUnique_vector u htan z δ hδ hc

end GlobalTheory.KS.TangentAt

end
