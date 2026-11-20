import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClosedTriv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionCubeLBIsoPolarisationTranslateStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPicardGroup
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.BundleForm

section
variable {Pic : Scheme.{0} → Type 1} [∀ X, CommGroup (Pic X)]
  (pl : ∀ {X Y : Scheme.{0}}, (Y ⟶ X) → (Pic X →* Pic Y))
  {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def lam (c : Pic A.left) {T : Over S} (a b : T ⟶ A) : Pic T.left :=
  pl (a * b).left c * pl (1 : T ⟶ A).left c / (pl a.left c * pl b.left c)

/- English proof (translation)
Simplify using `[lam, _root_.mul_comm]`.
-/
theorem lam_one_left (c : Pic A.left) {T : Over S} (b : T ⟶ A) : lam @pl c 1 b = 1 := by
  simp [lam, _root_.mul_comm]

/- English proof (translation)
Simplify using `[lam]`.
-/
theorem lam_one_right (c : Pic A.left) {T : Over S} (a : T ⟶ A) : lam @pl c a 1 = 1 := by
  simp [lam]

/- English proof (translation)
Unfold `lam`. Rewrite using `[_root_.mul_comm a b, _root_.mul_comm (pl a.left c)]`.
-/
theorem lam_comm (c : Pic A.left) {T : Over S} (a b : T ⟶ A) : lam @pl c a b = lam @pl c b a := by
  unfold lam
  rw [_root_.mul_comm a b, _root_.mul_comm (pl a.left c)]

/- English proof (translation)
Unfold `lam`. Rewrite using `[map_div, map_mul, map_mul, ← hc, ← hc, ← hc, ← hc, ← MonObj.comp_mul, ← MonObj.comp_one u]`. Both sides reduce to the same expression.
-/
theorem pl_lam (hc : ∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c))
    (c : Pic A.left) {T T' : Over S} (u : T' ⟶ T) (a b : T ⟶ A) :
    pl u.left (lam @pl c a b) = lam @pl c (u ≫ a) (u ≫ b) := by
  unfold lam
  rw [map_div, map_mul, map_mul, ← hc, ← hc, ← hc, ← hc, ← MonObj.comp_mul, ← MonObj.comp_one u]
  rfl

/- English proof (translation)
Unfold `cubeLB`. Rewrite using `[(hl _ _ L hL _ _ _).2, ← Equiv.ulift.symm.prod_comp]`. Establish `e : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}}` using `by decide`. Rewrite using `[e, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]`. Establish `e0 : psum A ![a, b] ∅ = 1` using `rfl`.

Establish `e1 : psum A ![a, b] {0} = a` using `_root_.mul_one a`. Establish `e2 : psum A ![a, b] {1} = b` using `_root_.mul_one b`. Establish `e3 : psum A ![a, b] {0, 1} = a * b` using `congrArg (a * ·) (_root_.mul_one b)`. Simplify using `only [Equiv.ulift_symm_down, e0, e1, e2, e3, lam]`. Simplify using `[div_eq_mul_inv, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc]`.
-/
theorem cl_cube (cl : ∀ {X : Scheme.{0}}, LB X → Pic X)
    (hl : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ),
      (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k)
    {L : LB A.left} (hL : L.IsLB) {T : Over S} (a b : T ⟶ A) :
    cl (cubeLB A ![a, b] L) = lam @pl (cl L) a b := by
  unfold cubeLB
  rw [(hl _ _ L hL _ _ _).2, ← Equiv.ulift.symm.prod_comp]
  have e : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [e, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have e0 : psum A ![a, b] ∅ = 1 := rfl
  have e1 : psum A ![a, b] {0} = a := _root_.mul_one a
  have e2 : psum A ![a, b] {1} = b := _root_.mul_one b
  have e3 : psum A ![a, b] {0, 1} = a * b := congrArg (a * ·) (_root_.mul_one b)
  simp only [Equiv.ulift_symm_down, e0, e1, e2, e3, lam]
  simp [div_eq_mul_inv, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc]

/- English proof (translation)
Set `τ : T ⊗ A ⟶ T ⊗ A` to `lift (fst T A) ((fst T A ≫ y')⁻¹ * snd T A)`. Establish `h'` using `congrArg (pl τ.left) h`. Rewrite `h'` using `[pl_lam @pl hc, pl_lam @pl hc, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd]`. Establish `et : Out.translPt A (y * y'⁻¹) = (fst T A ≫ y) * ((fst T A ≫ y')⁻¹ * snd T A)`. Express the relevant statement in the definitionally equal form `(fst T A ≫ (y * y'⁻¹)) * snd T A = _`.

Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]`. Unfold `lam at h'`. Rewrite `h'` using `[← et, mul_inv_cancel_left]`. Establish `H : KerPow.HasGen L (K` using `Fin 4) ![(Out.translPt A (y * y'⁻¹)).left, (snd T A).left, (fst T A).left ≫ y.left, (fst T A).left ≫ y'.left] ![1, -1, -1, 1] := by`. Use `(h1 _ _ (hl _ _ L hL _ _ _).1).1 ?_` and prove the remaining obligations.

Rewrite using `[(hl _ _ L hL _ _ _).2, Fin.prod_univ_four]`. Establish `aux : ∀ a b c d e f : Pic (T ⊗ A).left, a * e / (c * f) = b * e / (d * f) → a ^ (1 : ℤ) * b ^ (-1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) = 1` using `fun a b c d e f k => by`. Establish `k'` using `congrArg Additive.ofMul k`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div, ofMul_zpow, ofMul_one] at k' ⊢`.

Take the linear combination `(norm := module) k'`. Conclude with `aux _ _ _ _ _ _ h'`. Establish `H' : KerPow.LocGen L (K` using `Fin 4) (fst T A).left ![(Out.translPt A (y * y'⁻¹)).left, (snd T A).left, (fst T A).left ≫ y.left, (fst T A).left ≫ y'.left] ![1, -1, -1, 1] := fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩`. Establish `B` using `BoxKernel.locGen_base hL (fst T A).left (K := Fin 2) ![y.left, y'.left] ![-1, 1]`. Use `mul_inv_eq_one.1 (KerPow.eq_one_of_locGen hK _ (H'.comb hL B fun U _ g => ?_))` and prove the remaining obligations.

Simplify using `[Fin.prod_univ_four, Fin.prod_univ_two]`.
-/
theorem eq_of_lam_eq (cl : ∀ {X : Scheme.{0}}, LB X → Pic X)
    (h1 : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → (cl L = 1 ↔ ∃ t : LB.Gen L, t.IsGen))
    (hc : ∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c))
    (hl : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ),
      (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k)
    {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (y y' : T ⟶ A)
    (h : lam @pl (cl L) (fst T A ≫ y) (snd T A) = lam @pl (cl L) (fst T A ≫ y') (snd T A)) : y = y' := by
  let τ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((fst T A ≫ y')⁻¹ * snd T A)
  have h' := congrArg (pl τ.left) h
  rw [pl_lam @pl hc, pl_lam @pl hc, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd] at h'
  have et : Out.translPt A (y * y'⁻¹) = (fst T A ≫ y) * ((fst T A ≫ y')⁻¹ * snd T A) := by
    change (fst T A ≫ (y * y'⁻¹)) * snd T A = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
  unfold lam at h'
  rw [← et, mul_inv_cancel_left] at h'
  have H : KerPow.HasGen L (K := Fin 4) ![(Out.translPt A (y * y'⁻¹)).left, (snd T A).left,
      (fst T A).left ≫ y.left, (fst T A).left ≫ y'.left] ![1, -1, -1, 1] := by
    refine (h1 _ _ (hl _ _ L hL _ _ _).1).1 ?_
    rw [(hl _ _ L hL _ _ _).2, Fin.prod_univ_four]
    have aux : ∀ a b c d e f : Pic (T ⊗ A).left, a * e / (c * f) = b * e / (d * f) →
        a ^ (1 : ℤ) * b ^ (-1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) = 1 := fun a b c d e f k => by
      have k' := congrArg Additive.ofMul k
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_zpow, ofMul_one] at k' ⊢
      linear_combination (norm := module) k'
    exact aux _ _ _ _ _ _ h'
  have H' : KerPow.LocGen L (K := Fin 4) (fst T A).left ![(Out.translPt A (y * y'⁻¹)).left, (snd T A).left,
      (fst T A).left ≫ y.left, (fst T A).left ≫ y'.left] ![1, -1, -1, 1] :=
    fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have B := BoxKernel.locGen_base hL (fst T A).left (K := Fin 2) ![y.left, y'.left] ![-1, 1]
  refine mul_inv_eq_one.1 (KerPow.eq_one_of_locGen hK _ (H'.comb hL B fun U _ g => ?_))
  simp [Fin.prod_univ_four, Fin.prod_univ_two]

end

/- English proof (translation)
Introduce `hA hB K _ _ P M hM`. Take `⟨Pic, _, cl, pl, hiso, h1, -, hc, hl, hd⟩` from `GlobalTheory.CechPicMul.exists_picardGroup`. Establish `cc` using `fun {L : LB P.A.left} (hL : L.IsLB) {T : Over (Sp K)} (a b : T ⟶ P.A) => cl_cube @pl @cl hl hL a b`. Establish `ci : ∀ {L : LB P.A.left} (_ : L.IsLB) {T : Over (Sp K)} (a b : T ⟶ P.A), (cubeLB P.A ![a, b] L).IsLB` using `fun hL _ a b => (hl _ _ _ hL _ _ _).1`. Establish `cp : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) (f : Y ⟶ X), (∃ t : (L.pull f).Gen, t.IsGen) ↔ pl f (cl L) = 1` using `fun hL f => by`.

Rewrite using `[← h1 _ _ (hl _ _ _ hL _ _ _).1, (hl _ _ _ hL _ _ _).2, Fintype.prod_unique, zpow_one]`. Take `⟨hN, eN⟩` from `hd _ _ _ (ci P.isLB (fst (P.A ⊗ P.A) P.A ≫ snd _ _) (snd _ _)) (ci hM (fst (P.A ⊗ P.A) P.A ≫ fst _ _) (snd _ _))`. Rewrite `eN` using `[cc hM, cc P.isLB]`. Take `⟨Z, i, hi, hZ⟩` from `GlobalTheory.SeesawGlobal.exists_closed_triv hA hB K P (P.A ⊗ P.A) _ hN (by`. Rewrite using `[cp hN, eN, map_div, pl_lam @pl hc, pl_lam @pl hc, lift_snd, lam_one_right, lam_one_right, div_one])`.

Establish `hR : ∀ (T : Over (Sp K)) (h : T ⟶ P.A ⊗ P.A), lam @pl (cl M) (fst T P.A ≫ h ≫ fst _ _) (snd T P.A) = lam @pl (cl P.L) (fst T P.A ≫ h ≫ snd _ _) (snd T P.A) ↔ ∃ u : T.left ⟶ Z, u ≫ i = h.left` using `fun T h => by`. Rewrite using `[← hZ, cp hN, eN, map_div, pl_lam @pl hc, pl_lam @pl hc, div_eq_one, whiskerRight_snd, whiskerRight_fst_assoc, whiskerRight_fst_assoc]`. Establish `uniq` using `fun {T : Over (Sp K)} (y y' : T ⟶ P.A) => eq_of_lam_eq @pl @cl h1 hc hl P.isLB P.ktriv y y'`. Set `q : Z ⟶ P.A.left` to `i ≫ (fst P.A P.A).left`. Establish `w1 : (fst P.A P.A).left ≫ P.A.hom = (P.A ⊗ P.A).hom` using `Over.w _`.

Establish `hmono : Mono q` using `⟨fun {W} u v e => by`. Set `T : Over (Sp K)` to `Over.mk (u ≫ i ≫ (P.A ⊗ P.A).hom)`. Set `a : T ⟶ P.A ⊗ P.A` to `Over.homMk (u ≫ i) (Category.assoc _ _ _)`. Set `b : T ⟶ P.A ⊗ P.A` to `Over.homMk (v ≫ i) (by`. Use `congrArg (· ≫ P.A.hom) e` as an intermediate fact.

Simplify using `only [q, Category.assoc, w1] at this`. Conclude with `(Category.assoc _ _ _).trans this.symm)`. Establish `e1 : a ≫ fst _ _ = b ≫ fst _ _` using `Over.OverMorphism.ext (by`. Simplify `e)` using `only [q, a, b, Over.comp_left, Over.homMk_left, Category.assoc]`. Establish `e2 : a ≫ snd _ _ = b ≫ snd _ _` using `uniq _ _ (by`.

Rewrite using `[← (hR T a).2 ⟨u, rfl⟩, ← (hR T b).2 ⟨v, rfl⟩, e1])`. Establish `e3 : a = b` using `CartesianMonoidalCategory.hom_ext _ _ e1 e2`. Conclude with `(cancel_mono i).1 (congrArg (fun z => z.left) e3)⟩`. Use `P.isAb.proper` as an intermediate fact. Establish `: IsProper (fst P.A P.A).left` using `inferInstanceAs (IsProper (pullback.fst P.A.hom P.A.hom))`.

Establish `hq : IsClosedImmersion q` using `(IsClosedImmersion.iff_isProper_and_mono q).2 ⟨inferInstance, hmono⟩`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl1, hl2⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by`. Distinguish the cases in `h2 : ((2 : ℕ) : K) = 0`. Use `⟨3, Nat.prime_three, fun h3 => one_ne_zero (α := K) ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at h2 h3`.

Take the linear combination `h3 - h2`. Conclude with `⟨2, Nat.prime_two, h2⟩`. Establish `hsurj : Surjective q` using `⟨by`. Rewrite using `[← Set.range_eq_univ, ← q.isClosedEmbedding.isClosed_range.closure_eq]`. Use `((GlobalTheory.PrimePowerTorsion.dense_torsion_and_eq_one hA hB K P l hl1 hl2).1.mono ?_).closure_eq` and prove the remaining obligations.

Use `Set.iUnion₂_subset fun x ⟨j, hj⟩ => ?_` and prove the remaining obligations. Take `⟨y, -, hy⟩` from `GlobalTheory.T.exists_torsion_cubeLB_iso_polarisation_translate hA hB K P M (l ^ j) x hM (by push_cast; exact pow_ne_zero _ hl2) hj`. Rewrite `hy` using `[← hiso _ _ _ (ci hM _ _) (ci P.isLB _ _), cc hM, cc P.isLB]`. Establish `hy'` using `congrArg (pl (snd (𝟙_ (Over (Sp K))) P.A).left) hy`. Rewrite `hy'` using `[pl_lam @pl hc, pl_lam @pl hc, Category.comp_id, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ _) (fst _ _)]`.

Take `⟨u, hu⟩` from `(hR _ (lift x y)).1 (by rw [lift_fst, lift_snd]; exact hy')`. Establish `e : u ≫ q = x.left`. Rewrite using `[← Category.assoc, hu, ← Over.comp_left, lift_fst]`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `⟨u z, by rw [← e]; rfl⟩⟩`.

Use `polAV_isIntegral_of_isAlgClosed K P` as an intermediate fact. Establish `: IsIso q` using `isIso_of_isClosedImmersion_of_surjective q`. Set `h : P.A ⟶ P.A ⊗ P.A` to `Over.homMk (inv q ≫ i) (by`. Rewrite using `[← w1, Category.assoc, ← Category.assoc i, IsIso.inv_hom_id_assoc])`. Establish `h₁ : h ≫ fst _ _ = 𝟙 _` using `Over.OverMorphism.ext (by`.

Express the relevant statement in the definitionally equal form `(inv q ≫ i) ≫ _ = 𝟙 _`. Rewrite using `[Category.assoc, IsIso.inv_hom_id])`. Establish `key` using `(hR _ h).2 ⟨inv q, rfl⟩`. Rewrite `key` using `[h₁, Category.comp_id]`. Use `⟨h ≫ snd _ _, hA.rigidity _ _ _ P.isAb P.isAb _ ?_, ?_⟩` and prove the remaining obligations.

Establish `e1 : (1 : 𝟙_ (Over (Sp K)) ⟶ P.A) = η[P.A]` using `by rw [Hom.one_def]; simp`. Rewrite using `[← e1]`. Use `uniq _ _ ?_` and prove the remaining obligations. Establish `k` using `congrArg (pl ((1 : 𝟙_ (Over (Sp K)) ⟶ P.A) ▷ P.A).left) key`. Rewrite `k` using `[pl_lam @pl hc, pl_lam @pl hc, whiskerRight_snd, whiskerRight_fst_assoc, whiskerRight_fst, MonObj.comp_one, lam_one_left]`.

Rewrite using `[← k, MonObj.comp_one, lam_one_left]`. Express the relevant statement in the definitionally equal form `LBIso (cubeLB P.A ![fst _ _, snd _ _] M) _`. Rewrite using `[← hiso _ _ _ (ci hM _ _) (ci P.isLB _ _), cc hM, cc P.isLB]`. Establish `k` using `congrArg (pl (lift (snd P.A P.A) (fst P.A P.A)).left) key`. Rewrite `k` using `[pl_lam @pl hc, pl_lam @pl hc, lift_fst_assoc, lift_fst, lift_snd]`.

Rewrite using `[lam_comm, k, lam_comm]`.
-/
theorem exists_formIs : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → ∃ s : P.A ⟶ P.A, FormIs P M s := by
  intro hA hB K _ _ P M hM
  obtain ⟨Pic, _, cl, pl, hiso, h1, -, hc, hl, hd⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  have cc := fun {L : LB P.A.left} (hL : L.IsLB) {T : Over (Sp K)} (a b : T ⟶ P.A) => cl_cube @pl @cl hl hL a b
  have ci : ∀ {L : LB P.A.left} (_ : L.IsLB) {T : Over (Sp K)} (a b : T ⟶ P.A), (cubeLB P.A ![a, b] L).IsLB :=
    fun hL _ a b => (hl _ _ _ hL _ _ _).1
  have cp : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) (f : Y ⟶ X),
      (∃ t : (L.pull f).Gen, t.IsGen) ↔ pl f (cl L) = 1 := fun hL f => by
    rw [← h1 _ _ (hl _ _ _ hL _ _ _).1, (hl _ _ _ hL _ _ _).2, Fintype.prod_unique, zpow_one]
  obtain ⟨hN, eN⟩ := hd _ _ _ (ci P.isLB (fst (P.A ⊗ P.A) P.A ≫ snd _ _) (snd _ _))
    (ci hM (fst (P.A ⊗ P.A) P.A ≫ fst _ _) (snd _ _))
  rw [cc hM, cc P.isLB] at eN
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.SeesawGlobal.exists_closed_triv hA hB K P (P.A ⊗ P.A) _ hN (by
    rw [cp hN, eN, map_div, pl_lam @pl hc, pl_lam @pl hc, lift_snd, lam_one_right, lam_one_right, div_one])

  have hR : ∀ (T : Over (Sp K)) (h : T ⟶ P.A ⊗ P.A),
      lam @pl (cl M) (fst T P.A ≫ h ≫ fst _ _) (snd T P.A) = lam @pl (cl P.L) (fst T P.A ≫ h ≫ snd _ _) (snd T P.A) ↔
        ∃ u : T.left ⟶ Z, u ≫ i = h.left := fun T h => by
    rw [← hZ, cp hN, eN, map_div, pl_lam @pl hc, pl_lam @pl hc, div_eq_one, whiskerRight_snd,
      whiskerRight_fst_assoc, whiskerRight_fst_assoc]
  have uniq := fun {T : Over (Sp K)} (y y' : T ⟶ P.A) => eq_of_lam_eq @pl @cl h1 hc hl P.isLB P.ktriv y y'
  let q : Z ⟶ P.A.left := i ≫ (fst P.A P.A).left
  have w1 : (fst P.A P.A).left ≫ P.A.hom = (P.A ⊗ P.A).hom := Over.w _
  have hmono : Mono q := ⟨fun {W} u v e => by
    let T : Over (Sp K) := Over.mk (u ≫ i ≫ (P.A ⊗ P.A).hom)
    let a : T ⟶ P.A ⊗ P.A := Over.homMk (u ≫ i) (Category.assoc _ _ _)
    let b : T ⟶ P.A ⊗ P.A := Over.homMk (v ≫ i) (by
      have := congrArg (· ≫ P.A.hom) e
      simp only [q, Category.assoc, w1] at this
      exact (Category.assoc _ _ _).trans this.symm)
    have e1 : a ≫ fst _ _ = b ≫ fst _ _ := Over.OverMorphism.ext (by
      simpa only [q, a, b, Over.comp_left, Over.homMk_left, Category.assoc] using e)
    have e2 : a ≫ snd _ _ = b ≫ snd _ _ := uniq _ _ (by
      rw [← (hR T a).2 ⟨u, rfl⟩, ← (hR T b).2 ⟨v, rfl⟩, e1])
    have e3 : a = b := CartesianMonoidalCategory.hom_ext _ _ e1 e2
    exact (cancel_mono i).1 (congrArg (fun z => z.left) e3)⟩
  have := P.isAb.proper
  have : IsProper (fst P.A P.A).left := inferInstanceAs (IsProper (pullback.fst P.A.hom P.A.hom))
  have hq : IsClosedImmersion q := (IsClosedImmersion.iff_isProper_and_mono q).2 ⟨inferInstance, hmono⟩
  obtain ⟨l, hl1, hl2⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
    by_cases h2 : ((2 : ℕ) : K) = 0
    · refine ⟨3, Nat.prime_three, fun h3 => one_ne_zero (α := K) ?_⟩
      push_cast at h2 h3
      linear_combination h3 - h2
    · exact ⟨2, Nat.prime_two, h2⟩
  have hsurj : Surjective q := ⟨by
    rw [← Set.range_eq_univ, ← q.isClosedEmbedding.isClosed_range.closure_eq]
    refine ((GlobalTheory.PrimePowerTorsion.dense_torsion_and_eq_one hA hB K P l hl1 hl2).1.mono ?_).closure_eq
    refine Set.iUnion₂_subset fun x ⟨j, hj⟩ => ?_
    obtain ⟨y, -, hy⟩ := GlobalTheory.T.exists_torsion_cubeLB_iso_polarisation_translate hA hB K P M (l ^ j) x hM (by push_cast; exact pow_ne_zero _ hl2) hj
    rw [← hiso _ _ _ (ci hM _ _) (ci P.isLB _ _), cc hM, cc P.isLB] at hy
    have hy' := congrArg (pl (snd (𝟙_ (Over (Sp K))) P.A).left) hy
    rw [pl_lam @pl hc, pl_lam @pl hc, Category.comp_id, ← Category.assoc, ← Category.assoc,
      toUnit_unique (_ ≫ _) (fst _ _)] at hy'
    obtain ⟨u, hu⟩ := (hR _ (lift x y)).1 (by rw [lift_fst, lift_snd]; exact hy')
    have e : u ≫ q = x.left := by
      rw [← Category.assoc, hu, ← Over.comp_left, lift_fst]
    rintro _ ⟨z, rfl⟩
    exact ⟨u z, by rw [← e]; rfl⟩⟩
  have := polAV_isIntegral_of_isAlgClosed K P
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  let h : P.A ⟶ P.A ⊗ P.A := Over.homMk (inv q ≫ i) (by
    rw [← w1, Category.assoc, ← Category.assoc i, IsIso.inv_hom_id_assoc])
  have h₁ : h ≫ fst _ _ = 𝟙 _ := Over.OverMorphism.ext (by
    change (inv q ≫ i) ≫ _ = 𝟙 _
    rw [Category.assoc, IsIso.inv_hom_id])
  have key := (hR _ h).2 ⟨inv q, rfl⟩
  rw [h₁, Category.comp_id] at key
  refine ⟨h ≫ snd _ _, hA.rigidity _ _ _ P.isAb P.isAb _ ?_, ?_⟩
  · have e1 : (1 : 𝟙_ (Over (Sp K)) ⟶ P.A) = η[P.A] := by rw [Hom.one_def]; simp
    rw [← e1]
    refine uniq _ _ ?_
    have k := congrArg (pl ((1 : 𝟙_ (Over (Sp K)) ⟶ P.A) ▷ P.A).left) key
    rw [pl_lam @pl hc, pl_lam @pl hc, whiskerRight_snd, whiskerRight_fst_assoc, whiskerRight_fst,
      MonObj.comp_one, lam_one_left] at k
    rw [← k, MonObj.comp_one, lam_one_left]
  · change LBIso (cubeLB P.A ![fst _ _, snd _ _] M) _
    rw [← hiso _ _ _ (ci hM _ _) (ci P.isLB _ _), cc hM, cc P.isLB]
    have k := congrArg (pl (lift (snd P.A P.A) (fst P.A P.A)).left) key
    rw [pl_lam @pl hc, pl_lam @pl hc, lift_fst_assoc, lift_fst, lift_snd] at k
    rw [lam_comm, k, lam_comm]

end GlobalTheory.BundleForm
end
