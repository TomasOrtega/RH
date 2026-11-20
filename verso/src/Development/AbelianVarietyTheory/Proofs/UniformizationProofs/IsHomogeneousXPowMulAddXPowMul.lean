import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjQuot

open MvPolynomial GlobalTheory.ProjSpace GlobalTheory.ThickeningDetermines

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {R A σ : Type} [CommRing R] [CommRing A] [Algebra R A] {r : σ → A} {i : σ}

/- English proof (translation)
Rewrite using `[map_mul, map_pow, aeval_X, hi, one_pow, _root_.one_mul]`.
-/
theorem aeval_X_pow_mul (hi : r i = 1) (k : ℕ) (F : MvPolynomial σ R) :
    aeval r (X i ^ k * F) = aeval r F := by
  rw [map_mul, map_pow, aeval_X, hi, one_pow, _root_.one_mul]

/- English proof (translation)
Establish `h₁ : (X i ^ m * F).IsHomogeneous (m + n)` using `(isHomogeneous_X_pow i m).mul hF`. Establish `h₂ : (X i ^ n * G).IsHomogeneous (m + n)`. Simplify `(isHomogeneous_X_pow i n).mul hG` using `only [Nat.add_comm n m]`. Conclude with `h₁.add h₂`.
-/
theorem isHomogeneous_X_pow_mul_add_X_pow_mul (i : σ) {n m : ℕ} {F G : MvPolynomial σ R} (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) : (X i ^ m * F + X i ^ n * G).IsHomogeneous (m + n) := by
  have h₁ : (X i ^ m * F).IsHomogeneous (m + n) := (isHomogeneous_X_pow i m).mul hF
  have h₂ : (X i ^ n * G).IsHomogeneous (m + n) := by
    simpa only [Nat.add_comm n m] using (isHomogeneous_X_pow i n).mul hG
  exact h₁.add h₂

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨0, C a, isHomogeneous_C _ a, rfl⟩`. Consider the case `add p q hp hq`. Take `⟨a, F, hF, eF⟩` from `hp`. Take `⟨b, G, hG, eG⟩` from `hq`.

Use `⟨b + a, X i ^ b * F + X i ^ a * G, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, aeval_X_pow_mul hi, aeval_X_pow_mul hi, eF, eG, map_add]`. Consider the case `mul_X p j hp`. Take `⟨a, F, hF, eF⟩` from `hp`. Conclude with `⟨a + 1, F * X j, hF.mul (isHomogeneous_X R j), by rw [map_mul, map_mul, eF]⟩`.
-/
theorem exists_isHomogeneous_aeval_eq (hi : r i = 1) (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ aeval r G = aeval r p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isHomogeneous_C _ a, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, F, hF, eF⟩ := hp
    obtain ⟨b, G, hG, eG⟩ := hq
    refine ⟨b + a, X i ^ b * F + X i ^ a * G, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG, ?_⟩
    rw [map_add, aeval_X_pow_mul hi, aeval_X_pow_mul hi, eF, eG, map_add]
  | mul_X p j hp =>
    obtain ⟨a, F, hF, eF⟩ := hp
    exact ⟨a + 1, F * X j, hF.mul (isHomogeneous_X R j), by rw [map_mul, map_mul, eF]⟩

def valueIdeal (hi : r i = 1) (hr : Function.Surjective (aeval (R := R) r))
    (J : Ideal (MvPolynomial σ R)) : Ideal A where
  carrier := {a | ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ G ∈ J ∧ aeval r G = a}
  zero_mem' := ⟨0, 0, isHomogeneous_zero _ R 0, J.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, F, hF, jF, rfl⟩ ⟨m, G, hG, jG, rfl⟩
    refine ⟨_, _, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG,
      J.add_mem (J.mul_mem_left _ jF) (J.mul_mem_left _ jG), ?_⟩
    rw [map_add, aeval_X_pow_mul hi, aeval_X_pow_mul hi]
  smul_mem' := by
    rintro c _ ⟨m, G, hG, jG, rfl⟩
    obtain ⟨p, rfl⟩ := hr c
    obtain ⟨n, F, hF, eF⟩ := exists_isHomogeneous_aeval_eq hi p
    exact ⟨_, _, hF.mul hG, J.mul_mem_left _ jG, by rw [map_mul, eF, smul_eq_mul]⟩

end Algebra

variable {R : Type} [CommRing R] {n : ℕ}

def formIdeal (J : Ideal (MvPolynomial (Fin (n + 1)) R)) : (PSpace R n).IdealSheafData :=
  ⨆ p : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J},
    secIdeal (On_isLB R n p.1.1) (formSec p.1.1 p.1.2 p.2.1)

/- English proof (translation)
Establish `hle : chart R n i ≤ (On R n (d : ℤ)).U (fun _ => i)` using `(On_U R n d (fun _ => i)).ge`. Rewrite using `[GlobalTheory.ThickeningDetermines.secIdeal]`. Use `(GlobalTheory.EffCartierData.ideal_locIdeal _ _ _ _ _ (fun _ => i) hle).trans ?_` and prove the remaining obligations. Rewrite using `[formSec_f, resG_formOn, formOn_eq_aeval]`.
-/
theorem ideal_secIdeal_formSec (i : Fin (n + 1)) (d : ℕ) (G : MvPolynomial (Fin (n + 1)) R)
    (hG : G.IsHomogeneous d) :
    (secIdeal (On_isLB R n d) (formSec d G hG)).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ =
      Ideal.span {aeval (ratio R n i) G} := by
  have hle : chart R n i ≤ (On R n (d : ℤ)).U (fun _ => i) := (On_U R n d (fun _ => i)).ge
  rw [GlobalTheory.ThickeningDetermines.secIdeal]
  refine (GlobalTheory.EffCartierData.ideal_locIdeal _ _ _ _ _ (fun _ => i) hle).trans ?_
  rw [formSec_f, resG_formOn, formOn_eq_aeval]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_valueIdeal_of_eq_one {S A σ : Type} [CommRing S] [CommRing A] [Algebra S A] {r : σ → A}
    {i : σ} (hi : r i = 1) (hr : Function.Surjective (aeval (R := S) r)) (J : Ideal (MvPolynomial σ S))
    (a : A) : a ∈ valueIdeal hi hr J ↔
      ∃ (m : ℕ) (G : MvPolynomial σ S), G.IsHomogeneous m ∧ G ∈ J ∧ aeval r G = a :=
  Iff.rfl

/- English proof (translation)
Establish `hone : ratio R n i i = 1` using `ratioOn_self`. Establish `hsurj` using `aeval_ratio_surjective R n i`. Establish `key : (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ = valueIdeal hone hsurj J`. Rewrite using `[formIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply]`. Simplify using `only [ideal_secIdeal_formSec]`.

Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun p => ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_valueIdeal_of_eq_one]`. Conclude with `⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩`. Introduce `a ha`.

Take `⟨m, G, hG, jG, rfl⟩` from `(mem_valueIdeal_of_eq_one hone hsurj J a).1 ha`. Use `Ideal.mem_iSup_of_mem (⟨(m, G), hG, jG⟩ : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J}) ?_` and prove the remaining obligations. Conclude with `Ideal.subset_span (Set.mem_singleton _)`. Rewrite using `[key, mem_valueIdeal_of_eq_one]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, G, hG, jG, e⟩`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `h₁ : (X i ^ m * F).IsHomogeneous (m + t)` using `(isHomogeneous_X_pow i m).mul hF`. Establish `h₂ : (X i ^ t * G).IsHomogeneous (m + t)`. Simplify `(isHomogeneous_X_pow i t).mul hG` using `only [Nat.add_comm t m]`.

Establish `hEq : X i ^ m * F = X i ^ t * G`. Rewrite using `[← formOn_chart_inj R n i h₁ h₂, formOn_eq_aeval, formOn_eq_aeval]`. Express the relevant statement in the definitionally equal form `aeval (ratio R n i) (X i ^ m * F) = aeval (ratio R n i) (X i ^ t * G)`. Rewrite using `[aeval_X_pow_mul hone, aeval_X_pow_mul hone, e]`. Rewrite using `[hEq]`.

Conclude with `J.mul_mem_left _ jG`. Introduce and unpack `⟨k, hk⟩`. Conclude with `⟨k + t, X i ^ k * F, (isHomogeneous_X_pow i k).mul hF, hk, aeval_X_pow_mul hone k F⟩`.
-/
theorem aeval_mem_formIdeal_iff (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin (n + 1))
    {t : ℕ} {F : MvPolynomial (Fin (n + 1)) R} (hF : F.IsHomogeneous t) :
    aeval (ratio R n i) F ∈ (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ ↔
      ∃ k : ℕ, X i ^ k * F ∈ J := by
  have hone : ratio R n i i = 1 := ratioOn_self
  have hsurj := aeval_ratio_surjective R n i
  have key : (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ = valueIdeal hone hsurj J := by
    rw [formIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    simp only [ideal_secIdeal_formSec]
    apply le_antisymm
    · refine iSup_le fun p => ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_valueIdeal_of_eq_one]
      exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
    · intro a ha
      obtain ⟨m, G, hG, jG, rfl⟩ := (mem_valueIdeal_of_eq_one hone hsurj J a).1 ha
      refine Ideal.mem_iSup_of_mem
        (⟨(m, G), hG, jG⟩ : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J}) ?_
      exact Ideal.subset_span (Set.mem_singleton _)
  rw [key, mem_valueIdeal_of_eq_one]
  constructor
  · rintro ⟨m, G, hG, jG, e⟩
    refine ⟨m, ?_⟩
    have h₁ : (X i ^ m * F).IsHomogeneous (m + t) := (isHomogeneous_X_pow i m).mul hF
    have h₂ : (X i ^ t * G).IsHomogeneous (m + t) := by
      simpa only [Nat.add_comm t m] using (isHomogeneous_X_pow i t).mul hG
    have hEq : X i ^ m * F = X i ^ t * G := by
      rw [← formOn_chart_inj R n i h₁ h₂, formOn_eq_aeval, formOn_eq_aeval]
      change aeval (ratio R n i) (X i ^ m * F) = aeval (ratio R n i) (X i ^ t * G)
      rw [aeval_X_pow_mul hone, aeval_X_pow_mul hone, e]
    rw [hEq]
    exact J.mul_mem_left _ jG
  · rintro ⟨k, hk⟩
    exact ⟨k + t, X i ^ k * F, (isHomogeneous_X_pow i k).mul hF, hk, aeval_X_pow_mul hone k F⟩

/- English proof (translation)
Establish `e : homOfLE h = 𝟙 U` using `Subsingleton.elim _ _`. Rewrite using `[resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]`.
-/
private theorem resG_refl' {Y : Scheme.{0}} {U : Y.Opens} (h : U ≤ U) (a : Γ(Y, U)) :
    resG Y h a = a := by
  have e : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]

/- English proof (translation)
Rewrite using `[Scheme.Hom.appLE, CommRingCat.comp_apply]`.
-/
private theorem appLE_congr_of_eq' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (a : Γ(Z, U)) : (φ.appLE U V e).hom a = resG Y e ((φ.app U).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]

/- English proof (translation)
Rewrite using `[← appLE_congr_of_eq', ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr_of_eq']`. Both sides reduce to the same expression.
-/
private theorem cst_comp_eq_resG_app {Y Z : Scheme.{0}} {S : Type} [CommRing S] (φ : Y ⟶ Z)
    (g : Z ⟶ Spec (CommRingCat.of S)) (U : Z.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (h : U ≤ g ⁻¹ᵁ ⊤) (a : S) :
    GlobalTheory.AbLaw.cst (φ ≫ g) V a = resG Y e ((φ.app U).hom ((g.appLE ⊤ U h).hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a))) := by
  rw [← appLE_congr_of_eq', ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr_of_eq']
  rfl

/- English proof (translation)
Establish `hle` using `(Cartier.pull_U (O1 R n) φ k).le`. Establish `key : (eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k)) fun j => (Cartier.secPull (coord R n j) φ).f k) = (resG Y hle).comp ((φ.app (chart R n (k ⟨⟩))).hom.comp (aeval (ratio R n (k ⟨⟩))).toRingHom)`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)` and prove the remaining obligations. Use `show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (C a)))`. Rewrite using `[eval₂Hom_C, aeval_C, algebraMap_sections_eq, CommRingCat.comp_apply]`.

Conclude with `cst_comp_eq_resG_app φ (PSpace.str R n) _ _ hle le_top a`. Use `show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (X j)))`. Rewrite using `[eval₂Hom_X', aeval_X, ← resG_refl' (le_refl (((O1 R n).pull φ).U k)) ((Cartier.secPull (coord R n j) φ).f k), resG_secPull_coord φ j k (le_refl _), pullRatio, appLE_congr_of_eq']`. Both sides reduce to the same expression. Conclude with `RingHom.congr_fun key F`.
-/
theorem eval₂Hom_secPull_coord {Y : Scheme.{0}} (φ : Y ⟶ PSpace R n) (k : PUnit → Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) :
    eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k))
        (fun j => (Cartier.secPull (coord R n j) φ).f k) F =
      resG Y (Cartier.pull_U (O1 R n) φ k).le
        ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) F)) := by
  have hle := (Cartier.pull_U (O1 R n) φ k).le
  have key : (eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k))
      fun j => (Cartier.secPull (coord R n j) φ).f k) =
      (resG Y hle).comp ((φ.app (chart R n (k ⟨⟩))).hom.comp (aeval (ratio R n (k ⟨⟩))).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (C a)))
      rw [eval₂Hom_C, aeval_C, algebraMap_sections_eq, CommRingCat.comp_apply]
      exact cst_comp_eq_resG_app φ (PSpace.str R n) _ _ hle le_top a
    · show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (X j)))
      rw [eval₂Hom_X', aeval_X, ← resG_refl' (le_refl (((O1 R n).pull φ).U k)) ((Cartier.secPull (coord R n j) φ).f k),
        resG_secPull_coord φ j k (le_refl _), pullRatio, appLE_congr_of_eq']
      rfl
  exact RingHom.congr_fun key F

/- English proof (translation)
Substitute `hUV` using the available equality. Establish `e : homOfLE h = 𝟙 V` using `Subsingleton.elim _ _`. Rewrite `ha` using `[resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]`. Then use the resulting hypothesis.
-/
private theorem eq_zero_of_resG_eq_zero_of_eq {Y : Scheme.{0}} {U V : Y.Opens} (hUV : V = U) {h : V ≤ U}
    {a : Γ(Y, U)} (ha : resG Y h a = 0) : a = 0 := by
  subst hUV
  have e : homOfLE h = 𝟙 V := Subsingleton.elim _ _
  rwa [resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] at ha

/- English proof (translation)
Introduce `R _ n J _`. Use `⟨(formIdeal J).subscheme, (formIdeal J).subschemeι ≫ PSpace.str R n, (O1 R n).pull (formIdeal J).subschemeι, fun j => Cartier.secPull (coord R n j) (formIdeal J).subschemeι, pull_isLB (O1_isLB R n) _, veryAmpleBy_secPull_coord _, fun t F hF => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Rewrite using `[← aeval_mem_formIdeal_iff J i hF, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker]`.

Conclude with `eq_zero_of_resG_eq_zero_of_eq (Cartier.pull_U (O1 R n) _ (fun _ => i)) ((eval₂Hom_secPull_coord _ (fun _ => i) F).symm.trans (h (fun _ => i)))`. Introduce `h k`. Take `⟨m, hm⟩` from `h (k ⟨⟩)`. Establish `hz` using `(aeval_mem_formIdeal_iff J (k ⟨⟩) hF).2 ⟨m, hm⟩`. Rewrite `hz` using `[← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker]`.

Conclude with `((eval₂Hom_secPull_coord _ k F).trans (congrArg _ hz)).trans (map_zero _)`.
-/
theorem exists_veryAmpleBy_of_ideal : ∀ (R : Type) [CommRing R] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ F ∈ J, ∀ t, MvPolynomial.homogeneousComponent t F ∈ J) → ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → ((∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F) = 0) ↔ ∀ i, ∃ k : ℕ, MvPolynomial.X i ^ k * F ∈ J) := by
  intro R _ n J _
  refine ⟨(formIdeal J).subscheme, (formIdeal J).subschemeι ≫ PSpace.str R n,
    (O1 R n).pull (formIdeal J).subschemeι,
    fun j => Cartier.secPull (coord R n j) (formIdeal J).subschemeι,
    pull_isLB (O1_isLB R n) _, veryAmpleBy_secPull_coord _, fun t F hF => ?_⟩
  constructor
  · intro h i
    rw [← aeval_mem_formIdeal_iff J i hF, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker]
    exact eq_zero_of_resG_eq_zero_of_eq (Cartier.pull_U (O1 R n) _ (fun _ => i))
      ((eval₂Hom_secPull_coord _ (fun _ => i) F).symm.trans (h (fun _ => i)))
  · intro h k
    obtain ⟨m, hm⟩ := h (k ⟨⟩)
    have hz := (aeval_mem_formIdeal_iff J (k ⟨⟩) hF).2 ⟨m, hm⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker] at hz
    exact ((eval₂Hom_secPull_coord _ k F).trans (congrArg _ hz)).trans (map_zero _)

end GlobalTheory.ProjQuot
