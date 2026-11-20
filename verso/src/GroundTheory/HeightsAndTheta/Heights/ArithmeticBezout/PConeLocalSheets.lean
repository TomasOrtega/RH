import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeLocalSheets
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsQuasiFiniteSheets
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix

namespace ConeLocalSheets

variable {n e : ℕ}

def homogenize (c : MvPolynomial (Fin e) ℂ) : MvPolynomial (Fin (e + 1)) ℂ :=
  ∑ m ∈ c.support, C (coeff m c) * (X 0 ^ (c.totalDegree - m.degree) * rename Fin.succ (monomial m 1))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem homogenize_isHomogeneous (c : MvPolynomial (Fin e) ℂ) :
    (homogenize c).IsHomogeneous c.totalDegree := by
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  have hle : m.degree ≤ c.totalDegree := le_totalDegree hm
  have h := (isHomogeneous_X_pow (R := ℂ) (0 : Fin (e + 1)) (c.totalDegree - m.degree)).mul
    ((isHomogeneous_monomial (σ := Fin e) (R := ℂ) (d := m) 1 rfl).rename_isHomogeneous (f := Fin.succ))
  rw [Nat.sub_add_cancel hle] at h
  exact h.C_mul _

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eval_homogenize (c : MvPolynomial (Fin e) ℂ) (x : Fin e → ℂ) :
    eval (Fin.cons 1 x : Fin (e + 1) → ℂ) (homogenize c) = eval x c := by
  have hcs : (Fin.cons 1 x : Fin (e + 1) → ℂ) ∘ Fin.succ = x := funext fun i => Fin.cons_succ _ _ _
  conv_rhs => rw [c.as_sum]
  simp only [homogenize, map_sum, map_mul, eval_C, map_pow, eval_X, Fin.cons_zero, one_pow, one_mul,
    eval_rename, hcs, eval_monomial]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem homogenize_ne_zero {c : MvPolynomial (Fin e) ℂ} (hc : c ≠ 0) : homogenize c ≠ 0 := by
  intro h
  apply hc
  apply MvPolynomial.funext
  intro x
  have := congrArg (eval (Fin.cons 1 x : Fin (e + 1) → ℂ)) h
  rw [eval_homogenize, map_zero] at this
  simpa using this

def lift (z : Fin n → ℂ) : (Σ k, PBlk n k) → ℂ := fun p => z p.2

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem lift_injective : Function.Injective (lift : (Fin n → ℂ) → (Σ k, PBlk n k) → ℂ) :=
  fun _ _ h => funext fun i => congrFun h ⟨(), i⟩

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem segre_lift (z : Fin n → ℂ) : segre (lift z) = fun i => z (i ()) := by
  funext i
  simp [segre, lift]

def lin (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
  Ψ ∘ₗ LinearMap.funLeft ℂ ℂ (fun i : Unit → Fin n => i ())

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem mat_mulVec (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (z : Fin n → ℂ) :
    LinearMap.toMatrix' (lin Ψ) *ᵥ z = Ψ (segre (lift z)) := by
  rw [LinearMap.toMatrix'_mulVec, segre_lift]
  rfl

def chartIdeal (P : Ideal (MRing (PBlk n))) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.map ((rename (fun p : Σ k, PBlk n k => p.2)).toRingHom.comp (map (Int.castRingHom ℂ))) P ⊔
    Ideal.span {∑ j, C (LinearMap.toMatrix' (lin Ψ) 0 j) * X j - 1}

def tailMat (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Matrix (Fin e) (Fin n) ℂ :=
  (LinearMap.toMatrix' (lin Ψ)).submatrix Fin.succ id

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem mem_zeroSet_chartIdeal {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {z : Fin n → ℂ} :
    z ∈ ComplexSets.zeroSet (chartIdeal P Ψ) ↔
      (∀ f ∈ P, eval (lift z) (map (Int.castRingHom ℂ) f) = 0) ∧ Ψ (segre (lift z)) 0 = 1 := by
  have key : ∀ J : Ideal (MvPolynomial (Fin n) ℂ),
      z ∈ ComplexSets.zeroSet J ↔ J ≤ RingHom.ker (eval z) := fun J => by
    simp [ComplexSets.zeroSet, SetLike.le_def, RingHom.mem_ker]
  rw [key, chartIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff,
    ← mat_mulVec]
  refine and_congr ?_ ?_
  · simp only [SetLike.le_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]
    rfl
  · simp [RingHom.mem_ker, Matrix.mulVec, dotProduct, sub_eq_zero]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem eq_cons {v : Fin (e + 1) → ℂ} {y : Fin e → ℂ} (h0 : v 0 = 1) (hs : ∀ i, v i.succ = y i) :
    v = Fin.cons 1 y := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [h0]
  · simp [hs]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem tailMat_mulVec (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (z : Fin n → ℂ)
    (i : Fin e) : (tailMat Ψ *ᵥ z) i = Ψ (segre (lift z)) i.succ := by
  rw [← mat_mulVec]
  simp [tailMat, Matrix.mulVec, dotProduct]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem of_mem_fibre {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {z : Fin n → ℂ}
    (hz : z ∈ ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y) :
    lift z ∈ mcPts P ∧ Ψ (segre (lift z)) = Fin.cons 1 y := by
  obtain ⟨hZ, hA⟩ := hz
  obtain ⟨hP, h0⟩ := mem_zeroSet_chartIdeal.mp hZ
  refine ⟨⟨fun k => ?_, hP⟩, eq_cons h0 fun i => by rw [← tailMat_mulVec, hA]⟩
  by_contra hne
  push Not at hne
  have hz0 : z = 0 := funext fun i => hne i
  rw [hz0, ← mat_mulVec, Matrix.mulVec_zero] at h0
  exact zero_ne_one h0

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Both sides reduce to the same expression.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem to_mem_fibre {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : Unit) → PBlk n k) → ℂ} (hw : w ∈ fibre P Ψ y) :
    ∃ z ∈ ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y, segre (lift z) = w := by
  obtain ⟨z, hz, rfl, hΨ⟩ := hw
  have hl : lift (fun i => z ⟨(), i⟩) = z := by
    funext p
    obtain ⟨u, i⟩ := p
    rfl
  refine ⟨fun i => z ⟨(), i⟩, ⟨mem_zeroSet_chartIdeal.mpr ⟨?_, ?_⟩, ?_⟩, by rw [hl]⟩
  · rw [hl]
    exact hz.2
  · rw [hl, hΨ]
    rfl
  · funext i
    rw [tailMat_mulVec, hl, hΨ]
    rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem fibre_finite {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hP : IsArithVar P (e + 1))
    (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y).Finite := by
  have hinj : Function.Injective fun z : Fin n → ℂ => segre (lift z) := by
    intro a b h
    funext i
    simpa [segre_lift] using congrFun h (fun _ => i)
  refine ((ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite Unit (PBlk n) P e Ψ hP hΨ y).preimage hinj.injOn).subset ?_
  intro z hz
  have h := of_mem_fibre hz
  exact ⟨lift z, h.1, rfl, h.2⟩

end ConeLocalSheets

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem ConeLocalSheets.proof (hQ : QuasiFiniteSheets.Statement) : ConeLocalSheets.Statement := by
  intro n e P Ψ hP hΨ
  obtain ⟨c, hc0, hc⟩ := hQ n e (ConeLocalSheets.chartIdeal P Ψ) (ConeLocalSheets.tailMat Ψ)
    (ConeLocalSheets.fibre_finite hP hΨ)
  refine ⟨ConeLocalSheets.homogenize c, c.totalDegree, ConeLocalSheets.homogenize_ne_zero hc0,
    ConeLocalSheets.homogenize_isHomogeneous c, fun x hx => ?_⟩
  rw [ConeLocalSheets.eval_homogenize] at hx
  obtain ⟨U, N, s, hU, hxU, hs, hsy⟩ := hc x hx
  refine ⟨U, N, fun j y => ConeLocalSheets.lift (s j y), hU, hxU, fun j => ?_, fun y hy => ?_⟩
  · rw [differentiableOn_pi]
    intro p
    exact differentiableOn_pi.mp (hs j) p.2
  · obtain ⟨hval, hinj, hfib⟩ := hsy y hy
    refine ⟨fun j => ConeLocalSheets.of_mem_fibre (hval j),
      fun j k h => hinj (ConeLocalSheets.lift_injective h), ?_⟩
    intro w hw
    obtain ⟨z, hz, rfl⟩ := ConeLocalSheets.to_mem_fibre hw
    obtain ⟨j, hj⟩ := hfib hz
    exact ⟨j, by simp only [hj]⟩

end GroundTheory.Heights₂.Heights
