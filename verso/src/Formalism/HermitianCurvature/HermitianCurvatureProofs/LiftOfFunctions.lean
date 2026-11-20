import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftZeroOrder
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

namespace Formalism.FourierDecayAlt.P.TLB

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section mulAt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

def MulAt (x : (Fin r → ℂ) × Q.Mx k r) (T : Module.End ℂ (Q.RadSp k r z z' π π')) (s : ℂ) : Prop :=
  ∀ Φ : Q.RadSp k r z z' π π', (T Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = s • (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

/- English proof (translation)
Introduce `Φ`. Simplify using the standard rewrite rules.
-/
theorem mulAt_one (x : (Fin r → ℂ) × Q.Mx k r) : MulAt (z := z) (z' := z') (π := π) (π' := π') x 1 1 := by
  intro Φ; simp

/- English proof (translation)
Introduce `Φ`. Rewrite using `[Module.End.mul_apply, h₁, h₂, smul_smul]`.
-/
theorem mulAt_mul {x : (Fin r → ℂ) × Q.Mx k r} {T₁ T₂ : Module.End ℂ (Q.RadSp k r z z' π π')} {s₁ s₂ : ℂ}
    (h₁ : MulAt x T₁ s₁) (h₂ : MulAt x T₂ s₂) : MulAt x (T₁ * T₂) (s₁ * s₂) := by
  intro Φ
  rw [Module.End.mul_apply, h₁, h₂, smul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_mul_fst (a b : Q.Pr (Q.RadSp k r z z' π π')) : (a * b).1 = a.1 * b.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_one_fst : (1 : Q.Pr (Q.RadSp k r z z' π π')).1 = 1 := rfl

/- English proof (translation)
The claim follows from `| 0, T, s, _ => by simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty, pr_one_fst] exact mulAt_one x | n + 1, T, s, h => by rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, pr_mul_fst] exact mulAt_mul (h 0) (mulAt_ofFn (fun i => T i.succ) (fu …`.
-/
theorem mulAt_ofFn {x : (Fin r → ℂ) × Q.Mx k r} :
    ∀ {n : ℕ} (T : Fin n → Q.Pr (Q.RadSp k r z z' π π')) (s : Fin n → ℂ), (∀ i, MulAt x (T i).1 (s i)) →
      MulAt x (List.ofFn T).prod.1 (∏ i, s i)
  | 0, T, s, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty, pr_one_fst]
    exact mulAt_one x
  | n + 1, T, s, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, pr_mul_fst]
    exact mulAt_mul (h 0) (mulAt_ofFn (fun i => T i.succ) (fun i => s i.succ) fun i => h i.succ)

end mulAt

section fns

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Use `⟨fun g _ => ⟨Set.univ, fun _ => 1, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, fun ε _ i => ⟨‖(1 : C6.EndH Wp Wq)‖, fun u v _ g hg _ => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fibBound_one {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) : C6.FibBound D (fun _ => (1 : C6.EndH Wp Wq)) := by
  refine ⟨fun g _ => ⟨Set.univ, fun _ => 1, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    fun ε _ i => ⟨‖(1 : C6.EndH Wp Wq)‖, fun u v _ g hg _ => ?_⟩⟩
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
  calc ‖Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw (Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) (fun _ => (1 : C6.EndH Wp Wq)) g‖
      ≤ ‖(1 : C6.EndH Wp Wq)‖ := JCx2.pd_Dw_const _ _ _
    _ ≤ ‖(1 : C6.EndH Wp Wq)‖ * B.gN g ^ (3 * (r + 1) * i) :=
      le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg))

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.lift_zero_order Wp Wq Pa Bs κ i j c Pol (fun _ => 1) a hP (fibBound_one Bs) ?_ ?_` and prove the remaining obligations. Introduce `p hp g _ J`. Simplify using `only [_root_.smul_apply, one_apply_eq_self]`. Rewrite using `[hinv p hp g, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]`. Introduce `Φ x hx`.

Rewrite using `[hrad x hx Φ]`. Simplify using the standard rewrite rules.
-/
theorem liftScalar (Pa : M.Par) (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) (κ i j c : ℕ) (Pol : B.Mat Pa.k Pa.r → ℂ)
    (a : Q.Pr (Q.RadSp Pa.k Pa.r Bs.z Bs.z' Bs.π Bs.π')) (hP : U.IsPolyDeg κ Pol)
    (hinv : ∀ p, Bs.inSS p → ∀ g, Pol (B.sgs p g) = Pol g)
    (hrad : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x a.1
      (Pol (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) *
        (Dmin Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) (Fin.last _))⁻¹ ^ i *
        (star (Dmin Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) (Fin.last _)))⁻¹ ^ j *
        ((Gf Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) : ℝ) : ℂ)⁻¹ ^ c)) :
    TL.Lifts Pa Bs 0 κ a := by
  refine Formalism.FourierDecayAlt.P.lift_zero_order Wp Wq Pa Bs κ i j c Pol (fun _ => 1) a hP (fibBound_one Bs) ?_ ?_
  · intro p hp g _ J
    simp only [_root_.smul_apply, one_apply_eq_self]
    rw [hinv p hp g, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx
    rw [hrad x hx Φ]
    simp

end fns

section acts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {k r : ℕ}
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  (X : Q.ActualOps k r z z' π π') (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r)

/- English proof (translation)
Introduce `Φ`. Rewrite using `[hL.2.2.1 l]`. Use `show (X.op l 1 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _`. Rewrite using `[X.op_apply]`. Both sides reduce to the same expression.
-/
theorem act_c (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.c l).1 (x.1 l) := by
  intro Φ
  rw [hL.2.2.1 l]
  show (X.op l 1 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

/- English proof (translation)
Introduce `Φ`. Rewrite using `[hL.2.2.2.1 l]`. Use `show (X.op l 2 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _`. Rewrite using `[X.op_apply]`. Both sides reduce to the same expression.
-/
theorem act_ci (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.ci l).1 (x.1 l)⁻¹ := by
  intro Φ
  rw [hL.2.2.2.1 l]
  show (X.op l 2 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

/- English proof (translation)
Introduce `Φ`. Rewrite using `[hL.2.2.2.2.1 l]`. Use `show (X.op l 4 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _`. Rewrite using `[X.op_apply]`. Both sides reduce to the same expression.
-/
theorem act_cb (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.cb l).1 (star (x.1 l)) := by
  intro Φ
  rw [hL.2.2.2.2.1 l]
  show (X.op l 4 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

/- English proof (translation)
Introduce `Φ`. Rewrite using `[hL.2.2.2.2.2.1 l]`. Use `show (X.op l 5 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _`. Rewrite using `[X.op_apply]`. Both sides reduce to the same expression.
-/
theorem act_cbi (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.cbi l).1 (star (x.1 l))⁻¹ := by
  intro Φ
  rw [hL.2.2.2.2.2.1 l]
  show (X.op l 5 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

/- English proof (translation)
Introduce `Φ` and use `X.fn_apply j Φ x hx`.
-/
theorem act_fn (x : (Fin r → ℂ) × Q.Mx k r) (hx : x ∈ Q.DomR k r z z') (j : Fin 6) :
    MulAt x (X.fn j) (Q.fnVal k r z z' j x.2) := fun Φ => X.fn_apply j Φ x hx

end acts

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.TLB
open scoped ComplexConjugate

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ Pa Bs X L hL`. Establish `hcell` using `big_cell_values Pa.k Pa.r Wp Wq Bs`. Establish `hpd1 : U.IsPolyDeg 0 (fun _ : B.Mat Pa.k Pa.r => (1 : ℂ))` using `⟨MvPolynomial.C 1, by simp, fun g => by simp⟩`. Establish `hDr : ∀ x, MulAt x L.Dr.1 (∏ a, x.1 a)` using `fun x => mulAt_ofFn L.c _ fun l => act_c X L hL x l`. Establish `hDri : ∀ x, MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹)` using `fun x => mulAt_ofFn L.ci _ fun l => act_ci X L hL x l`.

Establish `hDrb : ∀ x, MulAt x L.Drb.1 (∏ a, star (x.1 a))` using `fun x => mulAt_ofFn L.cb _ fun l => act_cb X L hL x l`. Establish `hDrbi : ∀ x, MulAt x L.Drbi.1 (∏ a, (star (x.1 a))⁻¹)` using `fun x => mulAt_ofFn L.cbi _ fun l => act_cbi X L hL x l`. Establish `hz : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζ.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)`. Introduce `x hx`. Rewrite using `[hL.2.2.2.2.2.2.1]`.

Conclude with `act_fn X x hx 0`. Establish `hzi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζi.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹`. Introduce `x hx`. Rewrite using `[hL.2.2.2.2.2.2.2.1]`. Conclude with `act_fn X x hx 1`.

Establish `hzb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζb.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))`. Introduce `x hx`. Rewrite using `[hL.2.2.2.2.2.2.2.2.1]`. Conclude with `act_fn X x hx 2`. Establish `hzbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζbi.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹`.

Introduce `x hx`. Rewrite using `[hL.2.2.2.2.2.2.2.2.2.1]`. Conclude with `act_fn X x hx 3`. Establish `hGGi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.GGi.1 ((Q.GGl Pa.k Pa.r Bs.z Bs.z' x.2 : ℂ))⁻¹`. Introduce `x hx`.

Rewrite using `[hL.2.2.2.2.2.2.2.2.2.2.2.1]`. Conclude with `act_fn X x hx 5`. Establish `inv_last : ∀ p, Bs.inSS p → ∀ g, Dmin Pa.k Pa.r Bs.z Bs.z' (B.sgs p g) (Fin.last _) = Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _)` using `fun p hp g => Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _`. Establish `inv_r : ∀ p, Bs.inSS p → ∀ g, Dmin Pa.k Pa.r Bs.z Bs.z' (B.sgs p g) ⟨Pa.r, by omega⟩ = Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩` using `fun p hp g => Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `liftScalar Pa Bs 0 0 0 0 (fun _ => 1) 1 hpd1 (fun _ _ _ => rfl) fun x _ => ?_` and prove the remaining obligations. Simplify using `only [pow_zero, mul_one]`. Conclude with `mulAt_one x`. Use `liftScalar Pa Bs (Pa.r + 1) 0 0 0 (fun g => Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _)) L.D (by simpa using minor_polynomial_property Pa.k Pa.r Bs.z Bs.z' (Fin.last _)) inv_last fun x hx => ?_` and prove the remaining obligations. Simplify using `only [pow_zero, mul_one]`.

Rewrite using `[(hcell x hx).2.2.1]`. Conclude with `mulAt_mul (hDr x) (hz x hx)`. Use `liftScalar Pa Bs (Pa.r + 1) 0 0 0 (fun g => star (Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _))) L.Db (by simpa using dmin_star_pd Pa.k Pa.r Bs.z Bs.z' (Fin.last _)) (fun p hp g => by rw [inv_last p hp g]) fun x hx => ?_` and prove the remaining obligations. Simplify using `only [pow_zero, mul_one]`. Rewrite using `[(hcell x hx).2.2.1, star_mul', star_prod]`.

Conclude with `mulAt_mul (hDrb x) (hzb x hx)`. Use `liftScalar Pa Bs Pa.r 0 0 0 (fun g => Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩) L.Dr (by simpa using minor_polynomial_property Pa.k Pa.r Bs.z Bs.z' ⟨Pa.r, by omega⟩) inv_r fun x hx => ?_` and prove the remaining obligations. Simplify using `only [pow_zero, mul_one]`. Rewrite using `[(hcell x hx).2.1]`. Conclude with `hDr x`.

Use `liftScalar Pa Bs Pa.r 0 0 0 (fun g => star (Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩)) L.Drb (by simpa using dmin_star_pd Pa.k Pa.r Bs.z Bs.z' ⟨Pa.r, by omega⟩) (fun p hp g => by rw [inv_r p hp g]) fun x hx => ?_` and prove the remaining obligations. Simplify using `only [pow_zero, mul_one]`. Rewrite using `[(hcell x hx).2.1, star_prod]`. Conclude with `hDrb x`. Use `liftScalar Pa Bs 0 1 0 0 (fun _ => 1) L.Di hpd1 (fun _ _ _ => rfl) fun x hx => ?_` and prove the remaining obligations.

Simplify using `only [pow_zero, pow_one, mul_one, one_mul]`. Rewrite using `[(hcell x hx).2.2.1, mul_inv, ← Finset.prod_inv_distrib, mul_comm]`. Conclude with `mulAt_mul (hzi x hx) (hDri x)`. Use `liftScalar Pa Bs 0 0 1 0 (fun _ => 1) L.Dbi hpd1 (fun _ _ _ => rfl) fun x hx => ?_` and prove the remaining obligations. Simplify using `only [pow_zero, pow_one, mul_one, one_mul]`.

Rewrite using `[(hcell x hx).2.2.1, star_mul', star_prod, mul_inv, ← Finset.prod_inv_distrib, mul_comm]`. Conclude with `mulAt_mul (hzbi x hx) (hDrbi x)`. Use `liftScalar Pa Bs 0 0 0 1 (fun _ => 1) (TL.gI L) hpd1 (fun _ _ _ => rfl) fun x hx => ?_` and prove the remaining obligations. Simplify using `only [pow_zero, pow_one, mul_one, one_mul]`. Rewrite using `[(hcell x hx).2.2.2, Complex.ofReal_mul, ← Complex.mul_conj, mul_inv, mul_inv, ← Finset.prod_inv_distrib, map_prod, ← Finset.prod_inv_distrib]`.

Conclude with `mulAt_mul (mulAt_mul (hDri x) (hDrbi x)) (hGGi x hx)`.
-/
theorem lift_of_functions : TL.LiftFns := by
  intro Wp Wq _ _ _ _ _ _ Pa Bs X L hL
  have hcell := big_cell_values Pa.k Pa.r Wp Wq Bs
  have hpd1 : U.IsPolyDeg 0 (fun _ : B.Mat Pa.k Pa.r => (1 : ℂ)) := ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
  have hDr : ∀ x, MulAt x L.Dr.1 (∏ a, x.1 a) := fun x =>
    mulAt_ofFn L.c _ fun l => act_c X L hL x l
  have hDri : ∀ x, MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹) := fun x =>
    mulAt_ofFn L.ci _ fun l => act_ci X L hL x l
  have hDrb : ∀ x, MulAt x L.Drb.1 (∏ a, star (x.1 a)) := fun x =>
    mulAt_ofFn L.cb _ fun l => act_cb X L hL x l
  have hDrbi : ∀ x, MulAt x L.Drbi.1 (∏ a, (star (x.1 a))⁻¹) := fun x =>
    mulAt_ofFn L.cbi _ fun l => act_cbi X L hL x l
  have hz : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζ.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) := by
    intro x hx; rw [hL.2.2.2.2.2.2.1]; exact act_fn X x hx 0
  have hzi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζi.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.1]; exact act_fn X x hx 1
  have hzb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζb.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 2
  have hzbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζbi.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 3
  have hGGi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.GGi.1 ((Q.GGl Pa.k Pa.r Bs.z Bs.z' x.2 : ℂ))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 5
  have inv_last : ∀ p, Bs.inSS p → ∀ g, Dmin Pa.k Pa.r Bs.z Bs.z' (B.sgs p g) (Fin.last _) =
      Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _) := fun p hp g => Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _
  have inv_r : ∀ p, Bs.inSS p → ∀ g, Dmin Pa.k Pa.r Bs.z Bs.z' (B.sgs p g) ⟨Pa.r, by omega⟩ =
      Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩ := fun p hp g => Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine liftScalar Pa Bs 0 0 0 0 (fun _ => 1) 1 hpd1 (fun _ _ _ => rfl) fun x _ => ?_
    simp only [pow_zero, mul_one]
    exact mulAt_one x
  · refine liftScalar Pa Bs (Pa.r + 1) 0 0 0 (fun g => Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _)) L.D
      (by simpa using minor_polynomial_property Pa.k Pa.r Bs.z Bs.z' (Fin.last _)) inv_last fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.2.1]
    exact mulAt_mul (hDr x) (hz x hx)
  · refine liftScalar Pa Bs (Pa.r + 1) 0 0 0 (fun g => star (Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _))) L.Db
      (by simpa using dmin_star_pd Pa.k Pa.r Bs.z Bs.z' (Fin.last _)) (fun p hp g => by rw [inv_last p hp g])
      fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.2.1, star_mul', star_prod]
    exact mulAt_mul (hDrb x) (hzb x hx)
  · refine liftScalar Pa Bs Pa.r 0 0 0 (fun g => Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩) L.Dr
      (by simpa using minor_polynomial_property Pa.k Pa.r Bs.z Bs.z' ⟨Pa.r, by omega⟩) inv_r fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.1]
    exact hDr x
  · refine liftScalar Pa Bs Pa.r 0 0 0 (fun g => star (Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩)) L.Drb
      (by simpa using dmin_star_pd Pa.k Pa.r Bs.z Bs.z' ⟨Pa.r, by omega⟩) (fun p hp g => by rw [inv_r p hp g])
      fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.1, star_prod]
    exact hDrb x
  · refine liftScalar Pa Bs 0 1 0 0 (fun _ => 1) L.Di hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.1, mul_inv, ← Finset.prod_inv_distrib, mul_comm]
    exact mulAt_mul (hzi x hx) (hDri x)
  · refine liftScalar Pa Bs 0 0 1 0 (fun _ => 1) L.Dbi hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.1, star_mul', star_prod, mul_inv, ← Finset.prod_inv_distrib, mul_comm]
    exact mulAt_mul (hzbi x hx) (hDrbi x)
  · refine liftScalar Pa Bs 0 0 0 1 (fun _ => 1) (TL.gI L) hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.2, Complex.ofReal_mul, ← Complex.mul_conj, mul_inv, mul_inv, ← Finset.prod_inv_distrib,
      map_prod, ← Finset.prod_inv_distrib]
    exact mulAt_mul (mulAt_mul (hDri x) (hDrbi x)) (hGGi x hx)
