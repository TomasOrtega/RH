import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFinStab

variable {D : D7}

/- English proof (translation)
Unfold `symplOH`. Rewrite using `[← add_mul, ← map_add]`. Evaluate the numerical expressions.
-/
theorem symplO_eq_two (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add]
  norm_num

/- English proof (translation)
Rewrite using `[GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.symplOH_skew S T a b, add_comm b a]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem heisO_comm_of (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {a b : WO S T} (g : WO S T → ℂ)
    (h : ψ (symplOH S T a b + symplOH S T a b) = 1) :
    heisO ψ S T a (heisO ψ S T b g) = heisO ψ S T b (heisO ψ S T a g) := by
  rw [GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.symplOH_skew S T a b, add_comm b a]
  congr 1
  calc ψ (symplOH S T a b) = ψ ((symplOH S T a b + symplOH S T a b) + -symplOH S T a b) := by congr 1; ring
    _ = ψ (-symplOH S T a b) := by rw [AddChar.map_add_eq_mul, h, one_mul]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [heisO, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisO_smul'' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (c • g) = c • heisO ψ S T w g := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.zero_apply]`. Conclude with `RingHom.mem_ker.1 (Ideal.mem_inf.1 (h i j)).1`.
-/
theorem fin_of_mxAt {m n : ℕ} {a : Mx D m n} (h : MxAt (fun _ => True) a) : a.map (infPart D) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (h i j)).1

/- English proof (translation)
Rewrite using `[Matrix.map_mul, hu, Matrix.mul_zero]`.
-/
theorem fin_mul_left {k m n : ℕ} (M : Mx D k m) {u : Mx D m n} (hu : u.map (infPart D) = 0) :
    (M * u).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hu, Matrix.mul_zero]

/- English proof (translation)
Rewrite using `[Matrix.map_mul, hu, Matrix.zero_mul]`.
-/
theorem fin_mul_right {k m n : ℕ} {u : Mx D k m} (hu : u.map (infPart D) = 0) (M : Mx D m n) :
    (u * M).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, hu l j]`.
-/
theorem isHalf_mul_left {e : AE D} {k m n : ℕ} (M : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (M * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hu l j]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, hu i l]`.
-/
theorem isHalf_mul_right {e : AE D} {k m n : ℕ} {u : Mx D k m} (hu : IsHalf e u) (M : Mx D m n) : IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hu i l]

end GlobalTheory.AscFinStab

namespace GlobalTheory.AscFinStab

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ}

def Comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : WO S T) : Prop :=
  ∀ g : WO S T → ℂ, heisO ψ S T a (heisO ψ S T b g) = heisO ψ S T b (heisO ψ S T a g)

/- English proof (translation)
Simplify using `only [cls, Set.mem_setOf_eq] at hΦ ⊢`. Take `⟨_, hA₁, hA₂, hB₁, hB₂, hL⟩` from `hΦ`. Use `⟨hθ, fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_, fun η hη => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h₁ a ha, hA₁ a ha]`. Rewrite using `[h₂ a ha, hA₂ a ha, heisO_smul'']`.

Rewrite using `[h₃ ξ hξ, hB₁ ξ hξ, heisO_smul'']`. Rewrite using `[h₄ η hη, hB₂ η hη]`. Unfold `IsLatVac`. Use `⟨fun u hu => ?_, fun e he u hu hh => ?_⟩` and prove the remaining obligations. Take `⟨u₀, hu₀, rfl⟩` from `AddSubgroup.mem_map.1 hu`.

Establish `e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ` using `hL.1 (dV.ext0 W (dW.inc0 V₀ u₀)) hu`. Use `show heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ`. Rewrite using `[h₅ u₀ hu₀, e1]`. Take `⟨u₀, hu₀, rfl⟩` from `AddSubgroup.mem_map.1 hu`. Establish `e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ` using `hL.2 e he (dV.ext0 W (dW.inc0 V₀ u₀)) hu hh`.

Use `show heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ`. Rewrite using `[h₆ e he u₀ hu₀ hh, e1]`.
-/
theorem mem_cls_of_comm (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ)
    (y : Mx D V₀.rank σ) {Φ : WO V W → ℂ} (hΦ : Φ ∈ cls dV dW p x y ψ) (c : WO V W)
    (hθ : IsThetaFunO ψ V W (heisO ψ V W c Φ))
    (h₁ : ∀ a ∈ p.A₁, Comm ψ V W (dV.extX W a) c) (h₂ : ∀ a ∈ p.A₂, Comm ψ V W (dV.extY W a) c)
    (h₃ : ∀ ξ ∈ p.B₁, Comm ψ V W (dV.ext0 W (dW.incX V₀ ξ)) c)
    (h₄ : ∀ η ∈ p.B₂, Comm ψ V W (dV.ext0 W (dW.incY V₀ η)) c)
    (h₅ : ∀ u ∈ p.Γ₀, Comm ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) c)
    (h₆ : ∀ e, IsSplitIdem D e → ∀ u ∈ p.Γ₀, IsHalf e (dV.ext0 W (dW.inc0 V₀ u)) → Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) c) :
    heisO ψ V W c Φ ∈ cls dV dW p x y ψ := by
  simp only [cls, Set.mem_setOf_eq] at hΦ ⊢
  obtain ⟨_, hA₁, hA₂, hB₁, hB₂, hL⟩ := hΦ
  refine ⟨hθ, fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_, fun η hη => ?_, ?_⟩
  · rw [h₁ a ha, hA₁ a ha]
  · rw [h₂ a ha, hA₂ a ha, heisO_smul'']
  · rw [h₃ ξ hξ, hB₁ ξ hξ, heisO_smul'']
  · rw [h₄ η hη, hB₂ η hη]
  · unfold IsLatVac
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · obtain ⟨u₀, hu₀, rfl⟩ := AddSubgroup.mem_map.1 hu
      have e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ := hL.1 (dV.ext0 W (dW.inc0 V₀ u₀)) hu
      show heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ
      rw [h₅ u₀ hu₀, e1]
    · obtain ⟨u₀, hu₀, rfl⟩ := AddSubgroup.mem_map.1 hu
      have e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ := hL.2 e he (dV.ext0 W (dW.inc0 V₀ u₀)) hu hh
      show heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ
      rw [h₆ e he u₀ hu₀ hh, e1]

end GlobalTheory.AscFinStab

namespace GlobalTheory.AscFinStab

/- English proof (translation)
Introduce `D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hlin p hp Φ hΦ`. Establish `hstd : IsStdChar D ψ (-1)` using `s.weil.std`. Establish `hΦ'` using `hΦ`. Simplify using `only [cls, Set.mem_setOf_eq] at hΦ'`. Take `⟨hθ, -, -, -, -, hL⟩` from `hΦ'`.

Establish `hJ : ∀ a b : WO V₀ W₀, symplOH V W (dV.ext0 W (dW.inc0 V₀ a)) (dV.ext0 W (dW.inc0 V₀ b)) = symplOH V₀ W₀ a b`. Introduce `a b`. Rewrite using `[dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclAnisotropic_inclAnisotropic V₀]`. Establish `hfin0 : ∀ u ∈ p.Γ₀, (dV.ext0 W (dW.inc0 V₀ u)).map (infPart D) = 0` using `fun u hu => fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.fin₀ u hu))) _`. Establish `comm0 : ∀ {a b : WO V W}, symplOH V W a b = 0 → Comm ψ V W a b` using `fun h g => heisO_comm_of ψ g (by rw [h, add_zero, AddChar.map_zero_eq_one])`.

Use `⟨fun w hw => ?_, fun w hw => ?_, ?_⟩` and prove the remaining obligations. Establish `cr : ∀ {a : WO V W}, a.map (infPart D) = 0 → Comm ψ V W a w` using `fun ha => comm0 (GlobalTheory.FinTranslate.symplOH_fin_real ha hw)`. Conclude with `mem_cls_of_comm dV dW p _ y hΦ w (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ w) (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₁.fin a ha)) _)) (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₂.fin a ha)) _)) (fun ξ hξ => cr (fin_mul_right (fin_mul_left _ (fin_of_m …`. Rewrite using `[← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]`. Conclude with `hfin0 _ (nsmul_mem hu 2)))`.

Use the proof step `(fun e _ u hu _ => cr (hfin0 u hu))`. Take `⟨hw1, hw2⟩` from `hw`. Establish `hc : ∀ u : WO V₀ W₀, ψ (symplO V₀ W₀ w u) = 1 → Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) (dV.ext0 W (dW.inc0 V₀ w))`. Introduce `u hu g`. Use `heisO_comm_of ψ g ?_` and prove the remaining obligations.

Rewrite using `[hJ, GlobalTheory.FinTranslate.symplOH_skew V₀ W₀ w u, ← neg_add, AddChar.map_neg_eq_inv, ← symplO_eq_two, hu, inv_one]`. Conclude with `mem_cls_of_comm dV dW p _ y hΦ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ _) (fun a _ => comm0 (dV.wittDecomp_sympl_extIsotropic_extAnisotropic W a _)) (fun a _ => comm0 (dV.wittDecomp_sympl_extDual_extAnisotropic W a _)) (fun ξ _ => comm0 (by rw [dV.wittDecomp_sym …`. Rewrite using `[← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]`. Conclude with `hc _ (hw1 u hu))`. Use the proof step `(fun e he u hu hh => hc u (hw2 e he u hu (by`.

Establish `h'` using `isHalf_mul_right (isHalf_mul_left dW.p0 hh) dV.j0`. Establish `eq : dW.p0 * (dV.ext0 W (dW.inc0 V₀ u)) * dV.j0 = u`. Rewrite using `[dV.matrixExtendByZero_apply, dW.wittDecomp_inclAnisotropicHom_apply]`. Simplify using `only [← Matrix.mul_assoc, dW.p0_j0, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, dV.p0_j0, Matrix.mul_one]`.

Rewrite using `[eq] at h')))` and apply the resulting hypothesis. Establish `hfl` using `GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU (rat x₀) y Φ hθ`. Unfold `VacG IsLatVac`. Use `⟨(GlobalTheory.Unf.Flat.flatLaw D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU x₀ hlin y Φ hθ).2, fun u hu => ?_, fun e he u hu hh => ?_⟩` and prove the remaining obligations. Establish `e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ` using `hL.1 _ (AddSubgroup.mem_map_of_mem _ hu) show heisO ψ V₀ W₀ (2 • u) (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) = flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ`.

Rewrite using `[← hfl.2.1, map_nsmul (dW.inc0 V₀), map_nsmul (dV.ext0 W), e1]`. Establish `e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ` using `hL.2 e he _ (AddSubgroup.mem_map_of_mem _ hu) (isHalf_mul_right (isHalf_mul_left _ hh) _) show heisO ψ V₀ W₀ u (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) = flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ`. Rewrite using `[← hfl.2.1, e1]`.
-/
theorem cls_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, (∀ w : WO V W, w.map (finPart D) = 0 → heisO ψ V W w Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ (∀ w ∈ Ann ψ V₀ W₀ p.Γ₀, heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ VacG ψ V₀ W₀ p.Γ₀ (flatS dV dW s (rat x₀) y Φ) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hlin p hp Φ hΦ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hΦ' := hΦ
  simp only [cls, Set.mem_setOf_eq] at hΦ'
  obtain ⟨hθ, -, -, -, -, hL⟩ := hΦ'
  have hJ : ∀ a b : WO V₀ W₀,
      symplOH V W (dV.ext0 W (dW.inc0 V₀ a)) (dV.ext0 W (dW.inc0 V₀ b)) = symplOH V₀ W₀ a b := by
    intro a b
    rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclAnisotropic_inclAnisotropic V₀]
  have hfin0 : ∀ u ∈ p.Γ₀, (dV.ext0 W (dW.inc0 V₀ u)).map (infPart D) = 0 := fun u hu =>
    fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.fin₀ u hu))) _
  have comm0 : ∀ {a b : WO V W}, symplOH V W a b = 0 → Comm ψ V W a b := fun h g =>
    heisO_comm_of ψ g (by rw [h, add_zero, AddChar.map_zero_eq_one])
  refine ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩
  · have cr : ∀ {a : WO V W}, a.map (infPart D) = 0 → Comm ψ V W a w := fun ha =>
      comm0 (GlobalTheory.FinTranslate.symplOH_fin_real ha hw)
    exact mem_cls_of_comm dV dW p _ y hΦ w (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ w)
      (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₁.fin a ha)) _))
      (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₂.fin a ha)) _))
      (fun ξ hξ => cr (fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.b₁.fin ξ hξ))) _))
      (fun η hη => cr (fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.b₂.fin η hη))) _))
      (fun u hu => cr (by
        rw [← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]
        exact hfin0 _ (nsmul_mem hu 2)))
      (fun e _ u hu _ => cr (hfin0 u hu))
  · obtain ⟨hw1, hw2⟩ := hw
    have hc : ∀ u : WO V₀ W₀, ψ (symplO V₀ W₀ w u) = 1 →
        Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) (dV.ext0 W (dW.inc0 V₀ w)) := by
      intro u hu g
      refine heisO_comm_of ψ g ?_
      rw [hJ, GlobalTheory.FinTranslate.symplOH_skew V₀ W₀ w u, ← neg_add, AddChar.map_neg_eq_inv, ← symplO_eq_two, hu, inv_one]
    exact mem_cls_of_comm dV dW p _ y hΦ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ _)
      (fun a _ => comm0 (dV.wittDecomp_sympl_extIsotropic_extAnisotropic W a _))
      (fun a _ => comm0 (dV.wittDecomp_sympl_extDual_extAnisotropic W a _))
      (fun ξ _ => comm0 (by rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclIsotropic_inclAnisotropic V₀]))
      (fun η _ => comm0 (by rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclDual_inclAnisotropic V₀]))
      (fun u hu => by
        rw [← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]
        exact hc _ (hw1 u hu))
      (fun e he u hu hh => hc u (hw2 e he u hu (by
        have h' := isHalf_mul_right (isHalf_mul_left dW.p0 hh) dV.j0
        have eq : dW.p0 * (dV.ext0 W (dW.inc0 V₀ u)) * dV.j0 = u := by
          rw [dV.matrixExtendByZero_apply, dW.wittDecomp_inclAnisotropicHom_apply]
          simp only [← Matrix.mul_assoc, dW.p0_j0, Matrix.one_mul]
          rw [Matrix.mul_assoc, dV.p0_j0, Matrix.mul_one]
        rwa [eq] at h')))
  · have hfl := GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU (rat x₀) y Φ hθ
    unfold VacG IsLatVac
    refine ⟨(GlobalTheory.Unf.Flat.flatLaw D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU x₀ hlin y Φ hθ).2,
      fun u hu => ?_, fun e he u hu hh => ?_⟩
    · have e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ :=
        hL.1 _ (AddSubgroup.mem_map_of_mem _ hu)
      show heisO ψ V₀ W₀ (2 • u) (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) =
        flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ
      rw [← hfl.2.1, map_nsmul (dW.inc0 V₀), map_nsmul (dV.ext0 W), e1]
    · have e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ :=
        hL.2 e he _ (AddSubgroup.mem_map_of_mem _ hu) (isHalf_mul_right (isHalf_mul_left _ hh) _)
      show heisO ψ V₀ W₀ u (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) =
        flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ
      rw [← hfl.2.1, e1]

end GlobalTheory.AscFinStab

end
