import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardAddCharSymplecticLocalLatticeEqOne

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.VacCocycle
open _root_.GlobalTheory

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/- English proof (translation)
Establish `h` using `Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun (p q : α × β) => f p.1 p.2 q.1 q.2)`. Simplify `h` using `only [Fintype.sum_prod_type]`.
-/
theorem sum_four_comm (f : α → β → α → β → A) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  have h := Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun (p q : α × β) => f p.1 p.2 q.1 q.2)
  simpa only [Fintype.sum_prod_type] using h

/- English proof (translation)
Unfold `GlobalTheory.WeilM.hTens`. Simplify using `only [map_sum, map_mul, hc, hA, hB, ← Finset.sum_neg_distrib]`. Rewrite using `[sum_four_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_hTens (hc : ∀ z, c (c z) = z) {JA : Matrix α α A} {JB : Matrix β β A}
    (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j) (x y : Matrix α β A) :
    c (GlobalTheory.WeilM.hTens c JA JB y x) = -GlobalTheory.WeilM.hTens c JA JB x y := by
  unfold GlobalTheory.WeilM.hTens
  simp only [map_sum, map_mul, hc, hA, hB, ← Finset.sum_neg_distrib]
  rw [sum_four_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
The claim follows from `Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z`.
-/
theorem trace_conj (hc : ∀ z, c (c z) = z) (z : A) : Algebra.trace R A (c z) = Algebra.trace R A z :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z

/- English proof (translation)
Unfold `GlobalTheory.WeilM.symp`. Rewrite using `[← trace_conj c hc, map_mul, conj_hTens c hc hA hB, ← map_add]`. Use `congr 1`. Take the linear combination `(-GlobalTheory.WeilM.hTens c JA JB x y) * hξ`.
-/
theorem symp_swap (hc : ∀ z, c (c z) = z) {JA : Matrix α α A} {JB : Matrix β β A}
    (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j) {ξ : A} (hξ : ξ + c ξ = 1)
    (x y : Matrix α β A) :
    GlobalTheory.WeilM.symp (R := R) c ξ JA JB y x =
      GlobalTheory.WeilM.symp (R := R) c ξ JA JB x y + GlobalTheory.WeilM.symp (R := R) c (-1) JA JB x y := by
  unfold GlobalTheory.WeilM.symp
  rw [← trace_conj c hc, map_mul, conj_hTens c hc hA hB, ← map_add]
  congr 1
  linear_combination (-GlobalTheory.WeilM.hTens c JA JB x y) * hξ

end General

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'`. Establish `hσ : ∀ x : E, σ (σ x) = x` using `fun x => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hB.cm.2.2.2, hB.cm.2.2.2, star_star]`.

Establish `hc : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hi : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F` using `F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl`. Establish `hsw` using `symp_swap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hc (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (fun i j => by simp only [GlobalTheory.IndefiniteRo …`. Establish `h1` using `Tw.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 1 (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'`. Establish `h2` using `Tw.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v (-1) 1 (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'`. Establish `hm : inclR (F` using `F) (AF F) ((-1 : 𝓞 E) : E) = -1 := by`.

Rewrite using `[show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one]`. Rewrite `h2` using `[hm]`. Rewrite using `[Tw.LatVacArith.symp_add_left, Tw.LatVacArith.symp_add_right, Tw.LatVacArith.symp_add_right, hsw, ← mul_one (_ * _ * _), ← h1, ← mul_one (_ * _ * _ * _), ← h2]`. Simplify using `only [← AddChar.map_add_eq_mul]`. Use `congr 1`.

Establish `h : (⅟(2 : AF F)) * 2 = 1` using `invOf_mul_self _`. Generalize the expression as in `(⅟(2 : AF F)) = t at h ⊢`. Take the linear combination `(GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' + …`.
-/
theorem psi_half_symp_add : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have hsw := symp_swap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hc (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)
    (fun i j => by simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hX.herm])
    (fun i j => by simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hY.skew, map_neg])
    (ξ := inclR (F := F) (AF F) (θ : E)) (by rw [hi, ← map_add, hθ, map_one]) γ γ'
  have h1 := Tw.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have h2 := Tw.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v (-1) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have hm : inclR (F := F) (AF F) ((-1 : 𝓞 E) : E) = -1 := by
    rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one]
  rw [hm] at h2
  rw [Tw.LatVacArith.symp_add_left, Tw.LatVacArith.symp_add_right, Tw.LatVacArith.symp_add_right, hsw,
    ← mul_one (_ * _ * _), ← h1, ← mul_one (_ * _ * _ * _), ← h2]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  have h : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
  generalize (⅟(2 : AF F)) = t at h ⊢
  linear_combination (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') * h

end Tw.VacCocycle

end
