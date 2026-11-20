import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueWeightDecompositionRaynaudAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionOfBasicOpensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPartStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtSub

/- English proof (translation)
Establish `h' : ⊤ ≤ x ⁻¹ᵁ U` using `h.trans (x.preimage_mono e)`. Simplify using `only [valR, dif_pos h, dif_pos h']`. Use `congr 1`. Express the relevant statement in the definitionally equal form `(X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f = _`. Rewrite using `[Scheme.Hom.map_appLE]`.
-/
theorem valR_resG' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  simp only [valR, dif_pos h, dif_pos h']
  congr 1
  change (X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f = _
  rw [Scheme.Hom.map_appLE]

/- English proof (translation)
Simplify using `only [valR, dif_pos h, map_one]`.
-/
theorem valR_one' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valR x U (1 : Γ(X, U)) = 1 := by
  simp only [valR, dif_pos h, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom f = _`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (f : Γ(X, U)) :
    resG X h2 (resG X h1 f) = resG X (h2.trans h1) f := by
  change (X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom f = _
  rw [← Functor.map_comp]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(X.presheaf.map (homOfLE h).op).hom f = f`. Rewrite using `[show homOfLE h = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression.
-/
theorem resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (f : Γ(X, U)) : resG X h f = f := by
  change (X.presheaf.map (homOfLE h).op).hom f = f
  rw [show homOfLE h = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

/- English proof (translation)
Introduce `S _ φ x x' c a a' ha ha' hV hV' hq hc`. Establish `hU : ⊤ ≤ a ⁻¹ᵁ U` using `hV.trans (a.preimage_mono e)`. Establish `hU' : ⊤ ≤ a' ⁻¹ᵁ U` using `hV'.trans (a'.preimage_mono e)`. Rewrite using `[valR_resG' a' e hV', valR_resG' a e hV]`. Conclude with `hf S φ x x' c a a' ha ha' hU hU' hq hc`.
-/
theorem isWt_res {α : Q.X} {U V : Y.H.left.Opens} (e : V ≤ U) {f : Γ(Y.H.left, U)} (hf : IsWt Y α U f) :
    IsWt Y α V (resG Y.H.left e f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have hU : ⊤ ≤ a ⁻¹ᵁ U := hV.trans (a.preimage_mono e)
  have hU' : ⊤ ≤ a' ⁻¹ᵁ U := hV'.trans (a'.preimage_mono e)
  rw [valR_resG' a' e hV', valR_resG' a e hV]
  exact hf S φ x x' c a a' ha ha' hU hU' hq hc

/- English proof (translation)
Introduce `S _ φ x x' c a a' ha ha' hV hV' hq hc`. Establish `hc0 : c 0 = 1` using `WtAlg.c_zero x x' c hc`. Establish `e1` using `hu S φ x x' c a a' ha ha' hV hV' hq hc`. Rewrite `e1` using `[hc0, Units.val_one, _root_.one_mul]`. Rewrite using `[hc0, Units.val_one, _root_.one_mul]`.

Establish `m : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V → valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR b V u.val = 1`. Introduce `b hb`. Rewrite using `[← WtAlg.valR_mul'' b V hb, Units.inv_mul, valR_one' b V hb]`. Establish `m' : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V → valR b V u.val * valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val = 1`. Introduce `b hb`.

Rewrite using `[← WtAlg.valR_mul'' b V hb, Units.mul_inv, valR_one' b V hb]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isWt_inv {V : Y.H.left.Opens} (u : Γ(Y.H.left, V)ˣ) (hu : IsWt Y 0 V u.val) :
    IsWt Y 0 V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have hc0 : c 0 = 1 := WtAlg.c_zero x x' c hc
  have e1 := hu S φ x x' c a a' ha ha' hV hV' hq hc
  rw [hc0, Units.val_one, _root_.one_mul] at e1
  rw [hc0, Units.val_one, _root_.one_mul]
  have m : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V →
      valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR b V u.val = 1 := by
    intro b hb
    rw [← WtAlg.valR_mul'' b V hb, Units.inv_mul, valR_one' b V hb]
  have m' : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V →
      valR b V u.val * valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val = 1 := by
    intro b hb
    rw [← WtAlg.valR_mul'' b V hb, Units.mul_inv, valR_one' b V hb]
  calc valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val
        = valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val *
            (valR a V u.val * valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val) := by rw [m' a hV, _root_.mul_one]
    _ = (valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR a' V u.val) *
            valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by rw [e1, _root_.mul_assoc]
    _ = valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by rw [m a' hV', _root_.one_mul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero]`. Establish `h1` using `WtAlg.isWt_natCast (Y := Y) V 1`. Rewrite `h1` using `[Nat.cast_one]`. Then use the resulting hypothesis.

Consider the case `succ n ih`. Rewrite using `[pow_succ']`. Conclude with `WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hg ih`.
-/
theorem isRaynaudTorusWeightFunction_zero_pow {V : Y.H.left.Opens} {g : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (n : ℕ) : IsWt Y 0 V (g ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have h1 := WtAlg.isWt_natCast (Y := Y) V 1
    rwa [Nat.cast_one] at h1
  | succ n ih =>
    rw [pow_succ']
    exact WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hg ih

end GlobalTheory.Heat.WtSub

namespace GlobalTheory.Heat.WtSub

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

/- English proof (translation)
Establish `hle : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g ≤ Y.q.left ⁻¹ᵁ V.1` using `Y.q.left.preimage_mono (Q.P.A.left.basicOpen_le g)`. Use `set G : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) := (Y.q.left.app V.1).hom g with hGdef`. Establish `hG0 : IsWt Y 0 _ G` using `AbConst.isWt_app Y V.1 g`. Establish `heq : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g = Y.H.left.basicOpen G` using `Scheme.preimage_basicOpen Y.q.left g`. Set `_ : Algebra Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g)` to `(Y.H.left.presheaf.map (homOfLE hle).op).hom.toAlgebra`.

Establish `: IsLocalization.Away G Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g)` using `hP.isLocalization_of_eq_basicOpen G (homOfLE hle) heq`. Establish `halg : ∀ t, algebraMap Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) t = resG Y.H.left hle t` using `fun _ => rfl`. Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj G f`. Rewrite `ha` using `[← map_pow, halg, halg]`. Establish `hunit : IsUnit (resG Y.H.left hle (G ^ n))`.

Rewrite using `[← halg, map_pow]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit G).pow n`. Establish `hGn0 : IsWt Y 0 _ (resG Y.H.left hle (G ^ n))` using `isWt_res hle (isRaynaudTorusWeightFunction_zero_pow hG0 n)`. Take `⟨F, ⟨hFw, hFa⟩, -⟩` from `hdec V.1 V.2 a`. Take `⟨F0, -, huniq⟩` from `hdec (Q.P.A.left.basicOpen g) (V.2.basicOpen g) (f * resG Y.H.left hle (G ^ n))`.

Establish `hA : Finsupp.mapRange (resG Y.H.left hle) (map_zero _) F = F0`. Use `huniq _ ⟨fun χ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mapRange_apply]`. Conclude with `isWt_res hle (hFw χ)`. Rewrite using `[Finsupp.sum_mapRange_index (fun _ => rfl), ha, hFa, map_finsuppSum]`.

Establish `hB : Finsupp.single α (f * resG Y.H.left hle (G ^ n)) = F0`. Use `huniq _ ⟨fun χ => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hχ : α = χ`. Substitute `hχ` using the available equality. Rewrite using `[Finsupp.single_eq_same, _root_.mul_comm]`.

Conclude with `WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hGn0 hf`. Rewrite using `[Finsupp.single_eq_of_ne' hχ]`. Conclude with `WtAlg.isWt_zero _ _`. Rewrite using `[Finsupp.sum_single_index rfl]`. Establish `hα : resG Y.H.left hle (F α) = f * resG Y.H.left hle (G ^ n)`.

Establish `h1` using `DFunLike.congr_fun (hA.trans hB.symm) α`. Rewrite `h1` using `[Finsupp.mapRange_apply, Finsupp.single_eq_same]`. Then use the resulting hypothesis. Take `⟨-, hmul, hres⟩` from `hd`. Establish `hdfG : IsWt Y α _ (d _ (f * resG Y.H.left hle (G ^ n)))`. Rewrite using `[← hα, hres _ _ hle le_rfl]`.

Conclude with `isWt_res hle (hpres α (F α) (hFw α))`. Establish `hdG : IsWt Y 0 _ (d _ (resG Y.H.left hle (G ^ n)))`. Rewrite using `[hres _ _ hle le_rfl]`. Conclude with `isWt_res hle (hpres 0 (G ^ n) (isRaynaudTorusWeightFunction_zero_pow hG0 n))`. Establish `hGdf : IsWt Y α _ (resG Y.H.left hle (G ^ n) * d _ f)`.

Establish `e2 : resG Y.H.left hle (G ^ n) * d _ f = d _ (f * resG Y.H.left hle (G ^ n)) - f * d _ (resG Y.H.left hle (G ^ n))`. Rewrite using `[hmul _ hle]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, _root_.mul_comm f (d _ (resG Y.H.left hle (G ^ n)))]`. Conclude with `WtAlg.isWt_sub hdfG (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hdG hf)`.

Take `⟨u, hu⟩` from `hunit`. Establish `hu0 : IsWt Y 0 _ (u⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g)ˣ).val`. Use `isWt_inv u ?_` and prove the remaining obligations. Rewrite using `[hu]`. Conclude with `hGn0`.

Establish `h2` using `WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hu0 hGdf`. Rewrite `h2` using `[← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]`. Then use the resulting hypothesis.
-/
theorem isWt_basicOpen (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left)
    (hd : IsField (Y.q.left ⁻¹ᵁ V.1) d)
    (hpres : ∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f))
    (hdec : ∀ (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W),
      ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t))
    (hP : IsAffineOpen (Y.q.left ⁻¹ᵁ V.1))
    (g : Γ(Q.P.A.left, V.1)) (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g))
    (hf : IsWt Y α _ f) : IsWt Y α _ (d _ f) := by
  have hle : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g ≤ Y.q.left ⁻¹ᵁ V.1 :=
    Y.q.left.preimage_mono (Q.P.A.left.basicOpen_le g)
  set G : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) := (Y.q.left.app V.1).hom g with hGdef
  have hG0 : IsWt Y 0 _ G := AbConst.isWt_app Y V.1 g
  have heq : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g = Y.H.left.basicOpen G :=
    Scheme.preimage_basicOpen Y.q.left g
  let _ : Algebra Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    (Y.H.left.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : IsLocalization.Away G Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    hP.isLocalization_of_eq_basicOpen G (homOfLE hle) heq
  have halg : ∀ t, algebraMap Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)
      Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) t = resG Y.H.left hle t := fun _ => rfl
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj G f
  rw [← map_pow, halg, halg] at ha
  have hunit : IsUnit (resG Y.H.left hle (G ^ n)) := by
    rw [← halg, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit G).pow n
  have hGn0 : IsWt Y 0 _ (resG Y.H.left hle (G ^ n)) := isWt_res hle (isRaynaudTorusWeightFunction_zero_pow hG0 n)
  obtain ⟨F, ⟨hFw, hFa⟩, -⟩ := hdec V.1 V.2 a
  obtain ⟨F0, -, huniq⟩ := hdec (Q.P.A.left.basicOpen g) (V.2.basicOpen g) (f * resG Y.H.left hle (G ^ n))
  have hA : Finsupp.mapRange (resG Y.H.left hle) (map_zero _) F = F0 := by
    refine huniq _ ⟨fun χ => ?_, ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact isWt_res hle (hFw χ)
    · rw [Finsupp.sum_mapRange_index (fun _ => rfl), ha, hFa, map_finsuppSum]
  have hB : Finsupp.single α (f * resG Y.H.left hle (G ^ n)) = F0 := by
    refine huniq _ ⟨fun χ => ?_, ?_⟩
    · by_cases hχ : α = χ
      · subst hχ
        rw [Finsupp.single_eq_same, _root_.mul_comm]
        exact WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hGn0 hf
      · rw [Finsupp.single_eq_of_ne' hχ]
        exact WtAlg.isWt_zero _ _
    · rw [Finsupp.sum_single_index rfl]
  have hα : resG Y.H.left hle (F α) = f * resG Y.H.left hle (G ^ n) := by
    have h1 := DFunLike.congr_fun (hA.trans hB.symm) α
    rwa [Finsupp.mapRange_apply, Finsupp.single_eq_same] at h1
  obtain ⟨-, hmul, hres⟩ := hd
  have hdfG : IsWt Y α _ (d _ (f * resG Y.H.left hle (G ^ n))) := by
    rw [← hα, hres _ _ hle le_rfl]
    exact isWt_res hle (hpres α (F α) (hFw α))
  have hdG : IsWt Y 0 _ (d _ (resG Y.H.left hle (G ^ n))) := by
    rw [hres _ _ hle le_rfl]
    exact isWt_res hle (hpres 0 (G ^ n) (isRaynaudTorusWeightFunction_zero_pow hG0 n))
  have hGdf : IsWt Y α _ (resG Y.H.left hle (G ^ n) * d _ f) := by
    have e2 : resG Y.H.left hle (G ^ n) * d _ f =
        d _ (f * resG Y.H.left hle (G ^ n)) - f * d _ (resG Y.H.left hle (G ^ n)) := by
      rw [hmul _ hle]
      ring
    rw [e2, _root_.mul_comm f (d _ (resG Y.H.left hle (G ^ n)))]
    exact WtAlg.isWt_sub hdfG (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hdG hf)
  obtain ⟨u, hu⟩ := hunit
  have hu0 : IsWt Y 0 _ (u⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g)ˣ).val := by
    refine isWt_inv u ?_
    rw [hu]
    exact hGn0
  have h2 := WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hu0 hGdf
  rwa [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul] at h2

end GlobalTheory.Heat.WtSub

namespace GlobalTheory.Heat.WtSub

/- English proof (translation)
Introduce `R _ _ Q O _ _ _ oa Y V d hd hpres α V' hV' f hf`. Apply `GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens R Q O oa Y V V' hV' α (d _ f)` to reduce the goal to its premises. Introduce `g hg`. Establish `hle : Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V.1` using `Y.q.left.preimage_mono hV'`. Take `⟨hadd, hmul, hres⟩` from `hd`.

Rewrite using `[← hres _ _ (Y.q.left.preimage_mono hg) hle f]`. Conclude with `isWt_basicOpen Y V d ⟨hadd, hmul, hres⟩ hpres (fun W hW => GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y W hW) (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) g α _ (isWt_res _ hf)`.
-/
theorem isWt_field_of_le : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V.1) d → (∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f)) → ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V d hd hpres α V' hV' f hf
  apply GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens R Q O oa Y V V' hV' α (d _ f)
  intro g hg
  have hle : Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V.1 := Y.q.left.preimage_mono hV'
  obtain ⟨hadd, hmul, hres⟩ := hd
  rw [← hres _ _ (Y.q.left.preimage_mono hg) hle f]
  exact isWt_basicOpen Y V d ⟨hadd, hmul, hres⟩ hpres (fun W hW => GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y W hW)
    (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) g α _ (isWt_res _ hf)

end GlobalTheory.Heat.WtSub
