import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfFreeStalksStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM germ_resM)

namespace GlobalTheory.VB

variable {X : Scheme.{0}} [IsIntegral X] {F : X.Modules}

/- English proof (translation)
Use `Module.IsTorsionFree.of_smul_eq_zero fun a t hat => ?_` and prove the remaining obligations. Take `⟨V, hV, a, rfl⟩` from `X.presheaf.exists_germ_eq a`. Take `⟨T, hT, hxT, t, rfl⟩` from `Twist.exists_germ_eq_of_mem hV t`. Rewrite `hat`, the goal using `[← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hT) x hxT a]`. Generalize the expression as in `X.presheaf.map (homOfLE hT).op a = b at hat ⊢`.

Distinguish the cases in `hb : b = 0`. Conclude with `Or.inl (by rw [hb, map_zero])`. Use `right`. Rewrite `hat` using `[← QCoh.germ_smul, ← map_zero (ConcreteCategory.hom (F.presheaf.germ T x hxT))]`. Take `⟨W, hxW, i₁, i₂, e⟩` from `F.presheaf.germ_eq x hxT hxT _ _ hat`.

Rewrite `e` using `[map_zero, Scheme.Modules.map_smul]`. Establish `: Nonempty W` using `⟨⟨x, hxW⟩⟩`. Establish `hb' : X.presheaf.map i₁.op b ≠ 0` using `fun h0 => hb (map_injective_of_isIntegral X i₁ (h0.trans (map_zero _).symm))`. Use `h.eq_zero_of_smul hb' e` as an intermediate fact. Rewrite using `[← TopCat.Presheaf.germ_res_apply F.presheaf i₁ x hxW t, this, map_zero]`.
-/
theorem IsTorsionFree.isTorsionFree_stalk (h : IsTorsionFree F) (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x) (F.presheaf.stalk x :) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a t hat => ?_
  obtain ⟨V, hV, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨T, hT, hxT, t, rfl⟩ := Twist.exists_germ_eq_of_mem hV t
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hT) x hxT a] at hat ⊢
  generalize X.presheaf.map (homOfLE hT).op a = b at hat ⊢
  by_cases hb : b = 0
  · exact Or.inl (by rw [hb, map_zero])
  · right
    rw [← QCoh.germ_smul, ← map_zero (ConcreteCategory.hom (F.presheaf.germ T x hxT))] at hat
    obtain ⟨W, hxW, i₁, i₂, e⟩ := F.presheaf.germ_eq x hxT hxT _ _ hat
    rw [map_zero, Scheme.Modules.map_smul] at e
    have : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hb' : X.presheaf.map i₁.op b ≠ 0 := fun h0 =>
      hb (map_injective_of_isIntegral X i₁ (h0.trans (map_zero _).symm))
    have := h.eq_zero_of_smul hb' e
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf i₁ x hxW t, this, map_zero]

/- English proof (translation)
Take `⟨U, hU, hx⟩` from `QCoh.exists_affine_mem x`. Establish `: Nonempty U` using `⟨⟨x, hx⟩⟩`. Establish `key (y : U) : Module.finrank (X.presheaf.stalk (y : X)) (F.presheaf.stalk (y : X) :) = Module.finrank Γ(X, U) Γ(F, U)`. Use `hU.isLocalization_stalk y` as an intermediate fact. Use `QCoh.isLocalizedModule_germLinear F hU y` as an intermediate fact.

Establish `hp` using `(hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors`. Rewrite using `[IsLocalization.finrank_eq _ _ hp, IsLocalizedModule.finrank_eq _ (QCoh.germLinear F y) hp]`. Conclude with `(key ⟨x, hx⟩).trans (key ⟨_, genericPoint_mem hx⟩).symm`.
-/
theorem finrank_stalk_eq_genRank [F.IsQuasicoherent] (x : X) :
    Module.finrank (X.presheaf.stalk x) (F.presheaf.stalk x :) = genRank F := by
  obtain ⟨U, hU, hx⟩ := QCoh.exists_affine_mem x
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have key (y : U) : Module.finrank (X.presheaf.stalk (y : X)) (F.presheaf.stalk (y : X) :) =
      Module.finrank Γ(X, U) Γ(F, U) := by
    have := hU.isLocalization_stalk y
    have := QCoh.isLocalizedModule_germLinear F hU y
    have hp := (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
    rw [IsLocalization.finrank_eq _ _ hp, IsLocalizedModule.finrank_eq _ (QCoh.germLinear F y) hp]
  exact (key ⟨x, hx⟩).trans (key ⟨_, genericPoint_mem hx⟩).symm

/- English proof (translation)
Use `hC.smooth` as an intermediate fact. Use `hC.toIsProjCurve.isNoetherian` as an intermediate fact. Establish `hn` using `(forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strHom k X) (fun y => by`. Establish `hf : IsField ((Sp k).presheaf.stalk y)`. Establish `: Ring.KrullDimLE 0 ((Sp k).presheaf.stalk y)` using `krullDimLE_of_coheight_le (by`.

Establish `: Subsingleton (Sp k)` using `inferInstanceAs (Subsingleton (PrimeSpectrum k))`. Conclude with `(Order.coheight_eq_zero.2 (fun b _ => (Subsingleton.elim b y).le)).le)`. Establish `: IsIntegral (Sp k)` using `inferInstanceAs (IsIntegral (Spec (.of k)))`. Conclude with `Ring.KrullDimLE.isField_of_isDomain`. Use `letI := hf.toField`.

Conclude with `⟨inferInstance, inferInstance⟩) x).2`. Establish `h1 : Ring.KrullDimLE 1 (X.presheaf.stalk x)`. Use `krullDimLE_of_coheight_le ?_` and prove the remaining obligations. Establish `e : topologicalKrullDim X = Order.krullDim X` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))`. Use `Order.coheight_le_krullDim x` as an intermediate fact.

Rewrite `this` using `[← e, hC.dim_eq]`. Conclude with `this` after adjusting the coercions. Establish `h3 : IsIntegrallyClosed (X.presheaf.stalk x) ∧ ∀ P : Ideal (X.presheaf.stalk x), P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _` using `⟨hn, fun P h0 hP => IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h0 hP)⟩`. Conclude with `((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 0 3).mpr h3`.
-/
theorem IsSmoothProjCurve.isPrincipalIdealRing_stalk {k : Type} [Field k] [Algebra k Γ(X, ⊤)]
    (hC : IsSmoothProjCurve k X) (x : X) : IsPrincipalIdealRing (X.presheaf.stalk x) := by
  have := hC.smooth
  have := hC.toIsProjCurve.isNoetherian
  have hn := (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strHom k X) (fun y => by
    have hf : IsField ((Sp k).presheaf.stalk y) := by
      have : Ring.KrullDimLE 0 ((Sp k).presheaf.stalk y) :=
        krullDimLE_of_coheight_le (by
          have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
          exact (Order.coheight_eq_zero.2 (fun b _ => (Subsingleton.elim b y).le)).le)
      have : IsIntegral (Sp k) := inferInstanceAs (IsIntegral (Spec (.of k)))
      exact Ring.KrullDimLE.isField_of_isDomain
    letI := hf.toField
    exact ⟨inferInstance, inferInstance⟩) x).2
  have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
    refine krullDimLE_of_coheight_le ?_
    have e : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have := Order.coheight_le_krullDim x
    rw [← e, hC.dim_eq] at this
    exact_mod_cast this
  have h3 : IsIntegrallyClosed (X.presheaf.stalk x) ∧ ∀ P : Ideal (X.presheaf.stalk x),
      P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _ :=
    ⟨hn, fun P h0 hP => IsLocalRing.eq_maximalIdeal
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h0 hP)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 0 3).mpr h3

/- English proof (translation)
Introduce `k _ C _ _ hC`. Use `hC.toIsProjCurve.isNoetherian` as an intermediate fact. Establish `H : ∀ (F : C.Modules) [GlobalTheory.QCoh.IsFiniteQC F], IsTorsionFree F → IsVB F (genRank F)`. Introduce `F _ hF`. Use `GlobalTheory.T.vector_bundle_of_free_stalks C F _ fun x => ?_` and prove the remaining obligations.

Use `hC.isPrincipalIdealRing_stalk x` as an intermediate fact. Use `hF.isTorsionFree_stalk x` as an intermediate fact. Conclude with `⟨Module.finBasisOfFinrankEq _ _ (finrank_stalk_eq_genRank x)⟩`. Conclude with `⟨H, fun F G i _ => ⟨inferInstance, _, H _ (isSaturated_satι i)⟩⟩`.
-/
theorem isVB_of_isTorsionFree_and_isSubbundle_satι : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C → (∀ (F : C.Modules) [GlobalTheory.QCoh.IsFiniteQC F], IsTorsionFree F → IsVB F (genRank F)) ∧ ∀ (F G : C.Modules) (i : G ⟶ F) [GlobalTheory.QCoh.IsFiniteQC F], IsSubbundle (satι i) := by
  intro k _ C _ _ hC
  have := hC.toIsProjCurve.isNoetherian
  have H : ∀ (F : C.Modules) [GlobalTheory.QCoh.IsFiniteQC F], IsTorsionFree F → IsVB F (genRank F) := by
    intro F _ hF
    refine GlobalTheory.T.vector_bundle_of_free_stalks C F _ fun x => ?_
    have := hC.isPrincipalIdealRing_stalk x
    have := hF.isTorsionFree_stalk x
    exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_stalk_eq_genRank x)⟩
  exact ⟨H, fun F G i _ => ⟨inferInstance, _, H _ (isSaturated_satι i)⟩⟩

end GlobalTheory.VB
