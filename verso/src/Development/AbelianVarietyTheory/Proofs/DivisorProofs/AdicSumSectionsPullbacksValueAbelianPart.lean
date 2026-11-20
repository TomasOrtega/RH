import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.SecAdicSumAny

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.SecAdicSum

/- English proof (translation)
Introduce `R _ _ _ I hR D F _ _ _ X N hL K _ φ ε Ix n n₀ hS b τ _ x x₀ hx`. Use `hR.1` as an intermediate fact. Use `D.toPre.P.isAb.smooth` as an intermediate fact. Take `⟨P⟩` from `GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)`. Use `choose v hv hv' using fun i => exists_vec P (n i)`.

Take `⟨v₀, hv₀, hv₀'⟩` from `exists_vec P n₀`. Take `⟨z⟩` from `CoefBasic.exists_pt (R := R) (F := F)`. Take `⟨J, hJ⟩` from `CoefBasic.exists_good' hL z`. Take `⟨i₀, hi₀⟩` from `exists_mem P (b.left z)`. Set `t` to `trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J`.

Use `choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)`. Use `letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))`. Set `ev : (Fin P.a → R) →ₗ[R] F` to `Fintype.linearCombination R y`. Establish `key : ∀ (s : LB.Sec (LB.LinComb N φ ε)) (w : Fin P.a → R) (c : F), (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) → sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w` using `fun s w c h₁ h₂ => by`. Establish `e` using `gs_loc₀ P h₁ b.left z hi₀ hJ`.

Rewrite `e` using `[h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq]`. Use `CoefBasic.cstH_inj (R := R) z ?_` and prove the remaining obligations. Establish `e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val` using `(Units.eq_mul_inv_iff_mul_eq t).2 e.symm`. Establish `hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k)` using `fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]`. Rewrite using `[e', loc₀, hs, Finset.sum_mul]`.

Use `Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm` and prove the remaining obligations. Rewrite using `[gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]`. Both sides reduce to the same expression. Take `rfl : x = fun i => ev (v i)` from `funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)`. Take `rfl : x₀ = ev v₀` from `key _ _ _ hv₀' (hx z J hJ).2`.

Use `sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_` and prove the remaining obligations. Take `⟨S, hS⟩` from `hS e`. Use `⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]`. Take `⟨J', hJ'⟩` from `CoefBasic.exists_good' hL p`.

Take `⟨h₁, h₂⟩` from `hS _ (𝟙 _) p J' hJ'`. Rewrite `h₁`, `h₂` using `[Category.id_comp]`. Establish `h₃` using `h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)`. Establish `e₀` using `gs_loc₀ P hv₀' _ p hp hJ'`. Establish `e₁` using `fun j => gs_loc₀ P (hv' j) _ p hp hJ'`.

Rewrite `e₀` using `[gs_eq _ p _ hp]`. Simplify using `only [gs_eq _ p _ hp] at e₁`. Rewrite using `[loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j, ← Finset.mul_sum]`. Conclude with `sub_eq_zero.2 (congrArg _ h₃)`.
-/
theorem sumF_of_sum_on_thickenings_any : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ X)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb N φ ε)) (n₀ : LB.Sec (LB.LinComb N φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good N z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb N (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good N z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro R _ _ _ I hR D F _ _ _ X N hL K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb N φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁
    rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
      ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSumAny
