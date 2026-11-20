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
Use `IsHomogeneous.sum _ _ _ fun m hm => ?_` and prove the remaining obligations. Establish `hle : m.degree ≤ c.totalDegree` using `le_totalDegree hm`. Establish `h` using `(isHomogeneous_X_pow (R := ℂ) (0 : Fin (e + 1)) (c.totalDegree - m.degree)).mul ((isHomogeneous_monomial (σ := Fin e) (R := ℂ) (d := m) 1 rfl).rename_isHomogeneous (f := Fin.succ))`. Rewrite `h` using `[Nat.sub_add_cancel hle]`. Conclude with `h.C_mul _`.
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
Establish `hcs : (Fin.cons 1 x : Fin (e + 1) → ℂ) ∘ Fin.succ = x` using `funext fun i => Fin.cons_succ _ _ _`. Use `conv_rhs => rw [c.as_sum]`. Simplify using `only [homogenize, map_sum, map_mul, eval_C, map_pow, eval_X, Fin.cons_zero, one_pow, one_mul, eval_rename, hcs, eval_monomial]`.
-/
theorem eval_homogenize (c : MvPolynomial (Fin e) ℂ) (x : Fin e → ℂ) :
    eval (Fin.cons 1 x : Fin (e + 1) → ℂ) (homogenize c) = eval x c := by
  have hcs : (Fin.cons 1 x : Fin (e + 1) → ℂ) ∘ Fin.succ = x := funext fun i => Fin.cons_succ _ _ _
  conv_rhs => rw [c.as_sum]
  simp only [homogenize, map_sum, map_mul, eval_C, map_pow, eval_X, Fin.cons_zero, one_pow, one_mul,
    eval_rename, hcs, eval_monomial]

/- English proof (translation)
Introduce `h`. Apply `hc` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Use `congrArg (eval (Fin.cons 1 x : Fin (e + 1) → ℂ)) h` as an intermediate fact.

Rewrite `this` using `[eval_homogenize, map_zero]`. Simplify using `using this`.
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
Introduce `_ _ h` and use `funext fun i => congrFun h ⟨(), i⟩`.
-/
theorem lift_injective : Function.Injective (lift : (Fin n → ℂ) → (Σ k, PBlk n k) → ℂ) :=
  fun _ _ h => funext fun i => congrFun h ⟨(), i⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[segre, lift]`.
-/
theorem segre_lift (z : Fin n → ℂ) : segre (lift z) = fun i => z (i ()) := by
  funext i
  simp [segre, lift]

def lin (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
  Ψ ∘ₗ LinearMap.funLeft ℂ ℂ (fun i : Unit → Fin n => i ())

/- English proof (translation)
Rewrite using `[LinearMap.toMatrix'_mulVec, segre_lift]`. Both sides reduce to the same expression.
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
Establish `key : ∀ J : Ideal (MvPolynomial (Fin n) ℂ), z ∈ ComplexSets.zeroSet J ↔ J ≤ RingHom.ker (eval z)` using `fun J => by`. Simplify using `[ComplexSets.zeroSet, SetLike.le_def, RingHom.mem_ker]`. Rewrite using `[key, chartIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff, ← mat_mulVec]`. Use `and_congr ?_ ?_` and prove the remaining obligations. Simplify using `only [SetLike.le_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]`.

Both sides reduce to the same expression. Simplify using `[RingHom.mem_ker, Matrix.mulVec, dotProduct, sub_eq_zero]`.
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
Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[h0]`. Simplify using `[hs]`.
-/
theorem eq_cons {v : Fin (e + 1) → ℂ} {y : Fin e → ℂ} (h0 : v 0 = 1) (hs : ∀ i, v i.succ = y i) :
    v = Fin.cons 1 y := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [h0]
  · simp [hs]

/- English proof (translation)
Rewrite using `[← mat_mulVec]`. Simplify using `[tailMat, Matrix.mulVec, dotProduct]`.
-/
theorem tailMat_mulVec (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (z : Fin n → ℂ)
    (i : Fin e) : (tailMat Ψ *ᵥ z) i = Ψ (segre (lift z)) i.succ := by
  rw [← mat_mulVec]
  simp [tailMat, Matrix.mulVec, dotProduct]

/- English proof (translation)
Take `⟨hZ, hA⟩` from `hz`. Take `⟨hP, h0⟩` from `mem_zeroSet_chartIdeal.mp hZ`. Use `⟨⟨fun k => ?_, hP⟩, eq_cons h0 fun i => by rw [← tailMat_mulVec, hA]⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Establish `hz0 : z = 0` using `funext fun i => hne i`. Rewrite `h0` using `[hz0, ← mat_mulVec, Matrix.mulVec_zero]`. Conclude with `zero_ne_one h0`.
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
Take `⟨z, hz, rfl, hΨ⟩` from `hw`. Establish `hl : lift (fun i => z ⟨(), i⟩) = z`. Use function extensionality and compare the values at `p`. Take `⟨u, i⟩` from `p`. Both sides reduce to the same expression.

Use `⟨fun i => z ⟨(), i⟩, ⟨mem_zeroSet_chartIdeal.mpr ⟨?_, ?_⟩, ?_⟩, by rw [hl]⟩` and prove the remaining obligations. Rewrite using `[hl]`. Conclude with `hz.2`. Rewrite using `[hl, hΨ]`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `i`. Rewrite using `[tailMat_mulVec, hl, hΨ]`. Both sides reduce to the same expression.
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
Establish `hinj : Function.Injective fun z : Fin n → ℂ => segre (lift z)`. Introduce `a b h`. Use function extensionality and compare the values at `i`. Simplify `congrFun h (fun _ => i)` using `[segre_lift]`. Use `((ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite Unit (PBlk n) P e Ψ hP hΨ y).preimage hinj.injOn).subset ?_` and prove the remaining obligations.

Introduce `z hz`. Establish `h` using `of_mem_fibre hz`. Conclude with `⟨lift z, h.1, rfl, h.2⟩`.
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
Introduce `n e P Ψ hP hΨ`. Take `⟨c, hc0, hc⟩` from `hQ n e (ConeLocalSheets.chartIdeal P Ψ) (ConeLocalSheets.tailMat Ψ) (ConeLocalSheets.fibre_finite hP hΨ)`. Use `⟨ConeLocalSheets.homogenize c, c.totalDegree, ConeLocalSheets.homogenize_ne_zero hc0, ConeLocalSheets.homogenize_isHomogeneous c, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[ConeLocalSheets.eval_homogenize]`. Take `⟨U, N, s, hU, hxU, hs, hsy⟩` from `hc x hx`.

Use `⟨U, N, fun j y => ConeLocalSheets.lift (s j y), hU, hxU, fun j => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[differentiableOn_pi]`. Introduce `p`. Conclude with `differentiableOn_pi.mp (hs j) p.2`. Take `⟨hval, hinj, hfib⟩` from `hsy y hy`.

Use `⟨fun j => ConeLocalSheets.of_mem_fibre (hval j), fun j k h => hinj (ConeLocalSheets.lift_injective h), ?_⟩` and prove the remaining obligations. Introduce `w hw`. Take `⟨z, hz, rfl⟩` from `ConeLocalSheets.to_mem_fibre hw`. Take `⟨j, hj⟩` from `hfib hz`. Conclude with `⟨j, by simp only [hj]⟩`.
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
