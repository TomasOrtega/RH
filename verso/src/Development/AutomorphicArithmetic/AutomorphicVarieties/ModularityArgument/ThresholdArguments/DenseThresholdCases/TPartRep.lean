import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PartRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
/- English proof (translation)
Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace T b F).1 hg`. Establish `hp : ∀ k : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ k) F = (a - b) ^ k • F`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]`. Rewrite `hk` using `[hp k]`. Break down `smul_eq_zero.1 hk with h1 | h1` into its components or cases. Conclude with `sub_eq_zero.1 (by_contra fun h2 => pow_ne_zero k h2 h1)`.

Conclude with `absurd h1 h0`.
-/
private theorem val_eq {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {F : M} (h0 : F ≠ 0) {a b : ℂ}
    (h : T F = a • F) (hg : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hg
  have hp : ∀ k : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ k) F = (a - b) ^ k • F := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, LinearMap.smul_apply,
        Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]
  rw [hp k] at hk
  rcases smul_eq_zero.1 hk with h1 | h1
  · exact sub_eq_zero.1 (by_contra fun h2 => pow_ne_zero k h2 h1)
  · exact absurd h1 h0
/- English proof (translation)
Use `letI : Algebra R (Polynomial S) := ((algebraMap S (Polynomial S)).comp f).toAlgebra`. Set `φ : Polynomial R →ₐ[R] Polynomial S` to `{ Polynomial.mapRingHom f with commutes' := fun b => Polynomial.map_C f }`. Use `Eq.trans ?_ (D.nat (Polynomial R) (Polynomial S) φ (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)`. Use `congr 1`.

Simplify using `[map_sub, MonoidAlgebra.mapRingHom_single]`.
-/
private theorem chi_map {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (D : W.GDet n R G) (f : R →+* S) (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra R (Polynomial S) := ((algebraMap S (Polynomial S)).comp f).toAlgebra
  let φ : Polynomial R →ₐ[R] Polynomial S :=
    { Polynomial.mapRingHom f with commutes' := fun b => Polynomial.map_C f }
  refine Eq.trans ?_ (D.nat (Polynomial R) (Polynomial S) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)))
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]
/- English proof (translation)
Unfold `Hi.heckePol`. Rewrite using `[Polynomial.map_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]`. Simplify using the standard rewrite rules.
-/
private theorem pol_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n q : ℕ) (a : ℕ → R) (b : ℕ → S)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp
/- English proof (translation)
Introduce `M hM` and use `by rcases h.2.2 M le_top hM with rfl | rfl · exact ⟨⊤, h.2.1, isCompl_bot_top⟩ · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩ rw [(Submodule.mem_bot k).1 hv] simp`.
-/
private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp
/- English proof (translation)
Introduce `L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι x lam d ξ c0 sp _ K a _ _ _ z _ I D ψ hU ρ hρ hirr hD Y hY`. Take `⟨F, hF, hF0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hY`. Establish `hgen : ∀ i, F ∈ (H.opC ι lam d i).maxGenEigenspace (ι (z (H.gen θ a K i)))` using `fun i => (Submodule.mem_iInf _).1 hF.2.2 i`. Establish `hval : ∀ (w : H.Wp) (j : ℕ), j ≤ n → ι (z (H.genW θ a K w j)) = Y.a w j`. Introduce `w j hj`.

Unfold `HSet.genW`. Use `split_ifs with h`. Establish `e` using `Y.sph w (j - 1 + 1) F hF.1`. Rewrite `e` using `[show j - 1 + 1 = j by omega]`. Establish `e' : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = Y.a w j • F`.

Establish `e2 : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = sphOp (H.atW ι d w.1) (j - 1 + 1) F` using `rfl`. Rewrite using `[e2, show j - 1 + 1 = j by omega, e]`. Conclude with `(val_eq _ hF0 e' (hgen _)).symm`. Rewrite using `[show j = 0 by omega, Y.a_zero, map_one, map_one]`. Establish `e : W.GDet.ofRep (W.mat Y.r) = W.GDet.ofRep (W.mat ρ)`.

Use `AlgebraTools.Det.extDense _ _ _ hH.dense (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp Y.cont) i) (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hρ) i) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, B, σ, hB, hσ, rfl⟩`. Rewrite using `[← hD, chi_map, hU.frob ⟨w, hw⟩ B σ hB hσ, (AlgebraTools.Det.repApi _).2.1]`. Use `Polynomial.map_injective ι.toRingHom ι.injective ?_` and prove the remaining obligations. Use `(Y.frob ⟨w, hw⟩ B σ hB hσ).trans ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.map_map]`. Conclude with `(pol_map _ n _ _ _ fun j hj => hval ⟨w, hw⟩ j hj).symm`. Take `⟨P, hP⟩` from `AlgebraTools.Det.bnRep (W.mat Y.r) (W.mat ρ) Y.ss (ss_irr hirr) fun g => by`. Rewrite using `[← (AlgebraTools.Det.repApi (W.mat Y.r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g, e]`. Use `⟨P, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_mul_inv_iff_mul_eq]`. Conclude with `Units.ext (hP g).symm`.
-/
theorem partRep_s : _root_.UpperTheory.V.Z.J.D.PartRepAlt := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι x lam d ξ c0 sp _ K a _ _ _ z _ I D ψ hU ρ hρ hirr hD Y hY
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  have hgen : ∀ i, F ∈ (H.opC ι lam d i).maxGenEigenspace (ι (z (H.gen θ a K i))) := fun i =>
    (Submodule.mem_iInf _).1 hF.2.2 i
  have hval : ∀ (w : H.Wp) (j : ℕ), j ≤ n → ι (z (H.genW θ a K w j)) = Y.a w j := by
    intro w j hj
    unfold HSet.genW
    split_ifs with h
    · have e := Y.sph w (j - 1 + 1) F hF.1
      rw [show j - 1 + 1 = j by omega] at e
      have e' : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = Y.a w j • F := by
        have e2 : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = sphOp (H.atW ι d w.1) (j - 1 + 1) F := rfl
        rw [e2, show j - 1 + 1 = j by omega, e]
      exact (val_eq _ hF0 e' (hgen _)).symm
    · rw [show j = 0 by omega, Y.a_zero, map_one, map_one]
  have e : W.GDet.ofRep (W.mat Y.r) = W.GDet.ofRep (W.mat ρ) := by
    refine AlgebraTools.Det.extDense _ _ _ hH.dense (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp Y.cont) i)
      (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hρ) i) ?_
    rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [← hD, chi_map, hU.frob ⟨w, hw⟩ B σ hB hσ, (AlgebraTools.Det.repApi _).2.1]
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    refine (Y.frob ⟨w, hw⟩ B σ hB hσ).trans ?_
    rw [Polynomial.map_map]
    exact (pol_map _ n _ _ _ fun j hj => hval ⟨w, hw⟩ j hj).symm
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat Y.r) (W.mat ρ) Y.ss (ss_irr hirr) fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat Y.r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm
end UpperTheory.V.Z.J.D
end
end
