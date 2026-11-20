import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaQuasiRat

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]`. Use `congr 2`. Establish `h : ⅟(2 : R) * 2 = 1` using `invOf_mul_self 2`. Take the linear combination `(-(w.1 ⬝ᵥ w'.2)) * h`.
-/
theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' φ) =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • GlobalTheory.WeilM.schr ψ (w + w') φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]`.
-/
theorem thetaSum_smul' (F : Type) [Field F] [NumberField F] {κ : Type} (c : ℂ) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (c • φ) = c * GlobalTheory.WeilM.thetaSum F φ := by
  simp only [GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

/- English proof (translation)
Establish `h2 : ⅟(2 : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) (1 / 2)`. Apply `invOf_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← map_ofNat (algebraMap F (AdeleRing (𝓞 F) F)) 2, ← map_mul]`. Evaluate the numerical expressions. Establish `key : ∀ ξ : κ → F, ψ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) + ⅟(2 : AdeleRing (𝓞 F) F) * ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)))) = 1`.

Introduce `ξ`. Establish `e : (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) + ⅟(2 : AdeleRing (𝓞 F) F) * ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i))) = algebraMap F (AdeleRing (𝓞 F) F) (ξ ⬝ …`. Simplify using `only [dotProduct, map_add, map_mul, map_sum, h2]`. Rewrite using `[e]`. Conclude with `hψ _`.

Unfold `GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr`. Simplify using `only [key, one_mul]`. Rewrite using `[← (Equiv.addRight y).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))]`. Use `congr 1`. Use function extensionality and compare the values at `ξ`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem thetaSum_schr_rat (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1)
    {κ : Type} [Fintype κ] (y z : κ → F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) φ) =
      GlobalTheory.WeilM.thetaSum F φ := by
  have h2 : ⅟(2 : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AdeleRing (𝓞 F) F)) 2, ← map_mul]
    norm_num
  have key : ∀ ξ : κ → F, ψ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) + ⅟(2 : AdeleRing (𝓞 F) F) *
      ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)))) = 1 := by
    intro ξ
    have e : (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) +
        ⅟(2 : AdeleRing (𝓞 F) F) * ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i))) =
        algebraMap F (AdeleRing (𝓞 F) F) (ξ ⬝ᵥ z + 1 / 2 * (y ⬝ᵥ z)) := by
      simp only [dotProduct, map_add, map_mul, map_sum, h2]
    rw [e]
    exact hψ _
  unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
  simp only [key, one_mul]
  rw [← (Equiv.addRight y).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))]
  congr 1
  funext ξ
  congr 1
  funext i
  simp

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => rfl`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem cA_apply (D : D7) (a : AF D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig a = cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Unfold `GlobalTheory.WeilM.symp Formalism.IndefR.Datum.symplO`. Use `congr 1`. Establish `hb : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l)` using `fun j l => by`. Use `congrFun (congrFun hB j) l` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at this`.

Rewrite using `[this]`. Simplify using `[incM, Matrix.map_apply, Matrix.smul_apply, map_mul]`. Establish `e : ∀ i j k l, ξ * (x i j * incM D.host.F JA i k * incM D.host.F JB j l * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (y k l)) = incA D D.host.xi0 * (incA D (S.gram⁻¹ j l) * cA D (y k l) * incA D (T.gram k i) * x i j)` using `fun i j k l => by`. Establish `h1 : incM D.host.F JA i k = incA D (T.gram k i)`. Substitute `hA` using the available equality.

Both sides reduce to the same expression. Rewrite using `[cA_apply, h1]`. Take the linear combination `(x i j * incA D (T.gram k i) * cA D (y k l)) * hb j l`. Unfold `GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.hO`. Simplify using `only [Finset.mul_sum, e]`.

Use `symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem symp_eq_symplO (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (x y : Formalism.IndefR.Datum.WO S T) :
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
      Formalism.IndefR.Datum.symplO S T x y := by
  unfold GlobalTheory.WeilM.symp Formalism.IndefR.Datum.symplO
  congr 1
  have hb : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := fun j l => by
    have := congrFun (congrFun hB j) l
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [this]
    simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]
  have e : ∀ i j k l, ξ * (x i j * incM D.host.F JA i k * incM D.host.F JB j l * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (y k l)) =
      incA D D.host.xi0 * (incA D (S.gram⁻¹ j l) * cA D (y k l) * incA D (T.gram k i) * x i j) := fun i j k l => by
    have h1 : incM D.host.F JA i k = incA D (T.gram k i) := by
      subst hA; rfl
    rw [cA_apply, h1]
    linear_combination (x i j * incA D (T.gram k i) * cA D (y k l)) * hb j l
  unfold GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.hO
  simp only [Finset.mul_sum, e]
  symm
  calc _ = ∑ a, ∑ b, ∑ d, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

/- English proof (translation)
Introduce `D ψ hψ S T JA JB ξ hA hB κ _ co hrat Φ _ γ w`. Take `⟨y, z, hyz⟩` from `hrat γ`. Establish `hγ : ratW T S γ = incM D.host.F γ` using `rfl`. Establish `hform` using `co.form (incM D.host.F γ) w`. Rewrite `hform` using `[symp_eq_symplO D S T JA JB ξ hA hB, hyz]`.

Unfold `GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho`. Rewrite using `[map_add, hγ, hyz]`. Use `set u : (κ → AF D.host.F) × (κ → AF D.host.F) := (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) with hu`. Use `set v := co.e w`. Establish `law` using `schr_schr ψ u v Φ`.

Establish `hinv : ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) * ψ (⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1`. Rewrite using `[← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`. Establish `hsum : GlobalTheory.WeilM.schr ψ (u + v) Φ = ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.schr ψ v Φ)`. Rewrite using `[law, smul_smul, hinv, one_smul]`. Establish `h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2)`.

Apply `invOf_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]`. Evaluate the numerical expressions. Rewrite using `[hsum, thetaSum_smul', hu, thetaSum_schr_rat D.host.F ψ hψ.1.2.2.1 y z, ← hu, Formalism.IndefR.Datum.symplOH, hform, h2]`.
-/
theorem thetaTr_ratW_add : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratW T S γ = incM D.host.F γ := rfl
  have hform := co.form (incM D.host.F γ) w
  rw [symp_eq_symplO D S T JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add, hγ, hyz]
  set u : (κ → AF D.host.F) × (κ → AF D.host.F) :=
    (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) with hu
  set v := co.e w
  have law := schr_schr ψ u v Φ
  have hinv : ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      ψ (⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr ψ (u + v) Φ =
      ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.schr ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [hsum, thetaSum_smul', hu, thetaSum_schr_rat D.host.F ψ hψ.1.2.2.1 y z, ← hu,
    Formalism.IndefR.Datum.symplOH, hform, h2]

end GlobalTheory.ThetaQuasiRat
