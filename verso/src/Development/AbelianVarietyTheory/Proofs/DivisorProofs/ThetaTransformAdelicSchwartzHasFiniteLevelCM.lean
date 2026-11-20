import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformFixedBySmallFiniteHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaLevelF

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[TensorProduct.smul_tmul']`. Rewrite using `[Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]`.

Use `congr 1`. Conclude with `Prod.ext (one_mul _) (zero_mul _)`. Consider the case `add z z' hz hz'`. Rewrite using `[smul_add (pairA F 1 0) z z', hz, hz', map_add (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) z z', map_add]`.
-/
theorem infIdem_smul (z : AF F ⊗[F] E) :
    pairA F 1 0 • z = TensorProduct.map (GlobalTheory.ThetaLevel.infIncl F) LinearMap.id
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (one_mul _) (zero_mul _)
  | add z z' hz hz' =>
    rw [smul_add (pairA F 1 0) z z', hz, hz', map_add (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) z z',
      map_add]

/- English proof (translation)
Establish `h1 : pairA F 0 1 + pairA F 1 0 = 1` using `Prod.ext (zero_add 1) (add_zero 1)`. Establish `h2` using `infIdem_smul z`. Rewrite `h2` using `[show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = 0 from hz, map_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finIdem_smul (z : AF F ⊗[F] E) (hz : infPartF F E z = 0) : pairA F 0 1 • z = z := by
  have h1 : pairA F 0 1 + pairA F 1 0 = 1 := Prod.ext (zero_add 1) (add_zero 1)
  have h2 := infIdem_smul z
  rw [show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = 0 from hz, map_zero] at h2
  calc pairA F 0 1 • z = pairA F 0 1 • z + pairA F 1 0 • z := by rw [h2, add_zero]
    _ = z := by rw [← add_smul, h1, one_smul]

/- English proof (translation)
Establish `hu' : pairA F 0 1 • u = u`. Use extensionality with `a b`. Conclude with `finIdem_smul (u a b) (congrFun (congrFun hu a) b)`. Establish `h2` using `congrArg co.e hu'`. Rewrite `h2` using `[LinearEquiv.map_smul]`.

Use `conv_lhs => rw [← h2]`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Conclude with `Prod.ext (zero_mul _) (one_mul _)`. Conclude with `Prod.ext (zero_mul _) (one_mul _)`.
-/
theorem e_eq_fin {nS nT : ℕ} {B : WOF F E nS nT → WOF F E nS nT → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (u : WOF F E nS nT)
    (hu : u.map (infPartF F E) = 0) :
    co.e u = ((fun i => pairA F 0 ((co.e u).1 i).2), (fun i => pairA F 0 ((co.e u).2 i).2)) := by
  have hu' : pairA F 0 1 • u = u := by
    ext a b
    exact finIdem_smul (u a b) (congrFun (congrFun hu a) b)
  have h2 := congrArg co.e hu'
  rw [LinearEquiv.map_smul] at h2
  conv_lhs => rw [← h2]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact Prod.ext (zero_mul _) (one_mul _)
  · exact Prod.ext (zero_mul _) (one_mul _)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co _ Φ hΦ`. Use `haveI : IsModuleTopology (AF F) (WOF F E nS nT) := inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))`. Take `⟨K, hK⟩` from `GlobalTheory.ThetaLevel.schr_fin_fix F B.ψ hψ.1.1 Φ hΦ`. Establish `hcont : Continuous co.e` using `IsModuleTopology.continuous_of_linearMap co.e.toLinearMap`. Set `f1 : WOF F E nS nT →+ (κ → Af F)` to `AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add]; rfl)`.

Set `f2 : WOF F E nS nT →+ (κ → Af F)` to `AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add]; rfl)`. Establish `hf1 : Continuous f1` using `continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))`. Establish `hf2 : Continuous f2` using `continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))`. Set `U : OpenAddSubgroup (WOF F E nS nT)` to `K.comap f1 hf1 ⊓ K.comap f2 hf2`. Use `⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩` and prove the remaining obligations.

Establish `hfix : GlobalTheory.WeilM.schr B.ψ (co.e u) Φ = Φ`. Rewrite using `[e_eq_fin co u hinf]`. Conclude with `hK _ hu.1 _ hu.2`. Use `show B.ψ (symplOHF σ JS JT ξ₀ w u) * GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e (w + u)) Φ) = GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e w) Φ)`. Rewrite using `[map_add]`.

Establish `h1 : GlobalTheory.WeilM.schr B.ψ (co.e w + co.e u) Φ = fun x => B.ψ (-(⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) * GlobalTheory.WeilM.schr B.ψ (co.e w) (GlobalTheory.WeilM.schr B.ψ (co.e u) Φ) x`. Use function extensionality and compare the values at `(GlobalTheory.ThetaLevel.schr_add B.ψ _ _ Φ)`. Rewrite using `[h1, hfix]`. Simplify using `only [GlobalTheory.WeilM.thetaSum]`. Rewrite using `[tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]`.

Establish `h2 : symplOHF σ JS JT ξ₀ w u = ⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2)`. Rewrite using `[symplOHF, GlobalTheory.TransportF.symplOF_eq_symp hA hB, co.form]`. Use `congr 1`. Use `(invOf_eq_right_inv ?_).symm` and prove the remaining obligations. Rewrite using `[← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]`.

Evaluate the numerical expressions. Rewrite using `[h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]`.
-/
theorem thetaTr_levelF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  obtain ⟨K, hK⟩ := GlobalTheory.ThetaLevel.schr_fin_fix F B.ψ hψ.1.1 Φ hΦ
  have hcont : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  let f1 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add]; rfl)
  let f2 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add]; rfl)
  have hf1 : Continuous f1 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))
  have hf2 : Continuous f2 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))
  let U : OpenAddSubgroup (WOF F E nS nT) := K.comap f1 hf1 ⊓ K.comap f2 hf2
  refine ⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩
  have hfix : GlobalTheory.WeilM.schr B.ψ (co.e u) Φ = Φ := by
    rw [e_eq_fin co u hinf]
    exact hK _ hu.1 _ hu.2
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e (w + u)) Φ) =
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e w) Φ)
  rw [map_add]
  have h1 : GlobalTheory.WeilM.schr B.ψ (co.e w + co.e u) Φ = fun x =>
      B.ψ (-(⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) *
        GlobalTheory.WeilM.schr B.ψ (co.e w) (GlobalTheory.WeilM.schr B.ψ (co.e u) Φ) x :=
    funext (GlobalTheory.ThetaLevel.schr_add B.ψ _ _ Φ)
  rw [h1, hfix]
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have h2 : symplOHF σ JS JT ξ₀ w u =
      ⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2) := by
    rw [symplOHF, GlobalTheory.TransportF.symplOF_eq_symp hA hB, co.form]
    congr 1
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaLevelF

end
