import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocSymp

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] (σL : L →+* L) {α β : Type} [Fintype α] [Fintype β]
    (X Y : Matrix α β L) (A : Matrix α α L) (B : Matrix β β L) :
    (∑ i, ∑ j, ∑ k, ∑ l, X i j * A i k * B j l * σL (Y k l)) =
      Matrix.trace (A * Y.map σL * Bᵀ * Xᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]`. Rewrite using `[Matrix.trace_mul_comm PVᵀ]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem trace_coords {L : Type} [CommRing L] (σL : L →+* L) {n d : ℕ}
    (PV A : Matrix (Fin n) (Fin n) L) (PW B : Matrix (Fin d) (Fin d) L) (x y : Matrix (Fin d) (Fin n) L) :
    Matrix.trace (A * (PV * yᵀ * PWᵀ).map σL * Bᵀ * (PV * xᵀ * PWᵀ)ᵀ) =
      Matrix.trace ((PVᵀ * A * PV.map σL) * (y.map σL)ᵀ * (PWᵀ * B * PW.map σL)ᵀ * x) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm PVᵀ]
  simp only [Matrix.mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hat : ∃ z, ι z = ι 1 * inclR (F` using `F) (AF F) e := by`. Use `(hAt _).1 fun u hu => ?_` and prove the remaining obligations. Establish `h1 : u • ι 1 = 0` using `(hAt (ι 1)).2 ⟨1, rfl⟩ u hu`. Rewrite using `[← smul_mul_assoc, h1, zero_mul]`. Rewrite using `[hmul, GlobalTheory.InertLocFrame.pre_spec ι hat, ← mul_assoc, ← hmul, mul_one]`.
-/
theorem mul_inclR {L : Type} [Field L] (ι : L →+ AE F E) (v : Pl F)
    (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y) (a : L) (e : E) :
    ι a * inclR (F := F) (AF F) e = ι (a * GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e)) := by
  have hat : ∃ z, ι z = ι 1 * inclR (F := F) (AF F) e := by
    refine (hAt _).1 fun u hu => ?_
    have h1 : u • ι 1 = 0 := (hAt (ι 1)).2 ⟨1, rfl⟩ u hu
    rw [← smul_mul_assoc, h1, zero_mul]
  rw [hmul, GlobalTheory.InertLocFrame.pre_spec ι hat, ← mul_assoc, ← hmul, mul_one]

end GlobalTheory.InertLocSymp

open GlobalTheory.InertLocSymp in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B v n d X W L _ _ ϖ σL q δ ψL ι _ hδ hinj hAt hmul hσ hψ PV JS PW JT hGV hGW x y`. Establish `hδ0 : δ ≠ 0`. Introduce `h`. Rewrite `hδ` using `[h, map_zero]`. Conclude with `zero_ne_one hδ.1`.

Establish `hT : hTens (cA σ) (incM F X.J) (incM F W.J) (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) = ι (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j * GlobalTheory.InertLocFrame.tJ ι X.J i k * Globa …`. Simplify using `only [hTens, map_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.InertLocFrame.xm_apply, incM, Matrix.map_apply, ← hσ]`. Rewrite using `[mul_inclR ι v hAt hmul, mul_inclR ι v hAt hmul, ← hmul]`.

Both sides reduce to the same expression. Establish `hS : (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j * GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l * σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) = -Glo …`. Rewrite using `[quadruple_sum_eq_trace_transpose_mul, trace_coords]`. Establish `e1 : (PV : Matrix (Fin n) (Fin n) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι X.J * (PV : Matrix (Fin n) (Fin n) L).map σL = ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)` using `hGV.symm`. Establish `e2 : ((PW : Matrix (Fin d) (Fin d) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι W.J * (PW : Matrix (Fin d) (Fin d) L).map σL)ᵀ = -δ • (JT : Matrix (Fin d) (Fin d) L)`.

Rewrite using `[hGW, smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ0, one_smul]`. Both sides reduce to the same expression. Rewrite using `[e1, e2, GlobalTheory.Hk3.locH, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm _ x]`. Simplify using `only [Matrix.mul_assoc]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : (2 : L) ≠ 0`. Introduce `h`. Establish `h1 : (2 : AF F) • ι 1 = 0`. Rewrite using `[two_smul, ← map_add, one_add_one_eq_two, h, map_zero]`. Establish `: ι 1 = 0`.

Rewrite using `[← one_smul (AF F) (ι 1), ← invOf_mul_self (2 : AF F), mul_smul, h1, smul_zero]`. Conclude with `one_ne_zero (hinj (this.trans (map_zero ι).symm))`. Use `haveI : NeZero (2 : L) := ⟨h2⟩`. Use `set z := GlobalTheory.Hk3.locH σL δ JS JT x y`. Establish `hhalf : ⅟(2 : AF F) • ι z = ι (z / 2)`.

Establish `: ι z = (2 : AF F) • ι (z / 2)`. Rewrite using `[two_smul, ← map_add, add_halves]`. Rewrite using `[this, smul_smul, invOf_mul_self, one_smul]`. Establish `hsymp : ⅟(2 : AF F) * symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) = Algebra.trace (AF F) (AE F E) (ι (z / 2)) := by`. Rewrite using `[symp, hT, hS, map_neg, neg_one_mul, neg_neg, ← smul_eq_mul, ← LinearMap.map_smul, hhalf]`.

Rewrite using `[hsymp, hψ, map_div₀, map_ofNat, add_div]`.
-/
theorem GlobalTheory.InertLocSymp.psi_symp_eq :
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (v : Pl F) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) →
      ∀ (PV JS : GL (Fin n) L) (PW JT : GL (Fin d) L),
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι PV X.J →
        (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι PW W.J)ᵀ →
        ∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) := by
  intro F E _ _ _ _ _ σ B v n d X W L _ _ ϖ σL q δ ψL ι _ hδ hinj hAt hmul hσ hψ PV JS PW JT hGV hGW x y
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, map_zero] at hδ; exact zero_ne_one hδ.1

  have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) =
      ι (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j *
        GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l *
        σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) := by
    simp only [hTens, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [GlobalTheory.InertLocFrame.xm_apply, incM, Matrix.map_apply, ← hσ]
    rw [mul_inclR ι v hAt hmul, mul_inclR ι v hAt hmul, ← hmul]
    rfl

  have hS : (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j *
        GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l *
        σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) =
      -GlobalTheory.Hk3.locH σL δ JS JT x y := by
    rw [quadruple_sum_eq_trace_transpose_mul, trace_coords]
    have e1 : (PV : Matrix (Fin n) (Fin n) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι X.J * (PV : Matrix (Fin n) (Fin n) L).map σL =
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := hGV.symm
    have e2 : ((PW : Matrix (Fin d) (Fin d) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι W.J * (PW : Matrix (Fin d) (Fin d) L).map σL)ᵀ =
        -δ • (JT : Matrix (Fin d) (Fin d) L) := by
      rw [hGW, smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ0, one_smul]; rfl
    rw [e1, e2, GlobalTheory.Hk3.locH, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm _ x]
    simp only [Matrix.mul_assoc]; ring
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have h1 : (2 : AF F) • ι 1 = 0 := by
      rw [two_smul, ← map_add, one_add_one_eq_two, h, map_zero]
    have : ι 1 = 0 := by
      rw [← one_smul (AF F) (ι 1), ← invOf_mul_self (2 : AF F), mul_smul, h1, smul_zero]
    exact one_ne_zero (hinj (this.trans (map_zero ι).symm))
  haveI : NeZero (2 : L) := ⟨h2⟩
  set z := GlobalTheory.Hk3.locH σL δ JS JT x y
  have hhalf : ⅟(2 : AF F) • ι z = ι (z / 2) := by
    have : ι z = (2 : AF F) • ι (z / 2) := by
      rw [two_smul, ← map_add, add_halves]
    rw [this, smul_smul, invOf_mul_self, one_smul]
  have hsymp : ⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) =
      Algebra.trace (AF F) (AE F E) (ι (z / 2)) := by
    rw [symp, hT, hS, map_neg, neg_one_mul, neg_neg, ← smul_eq_mul, ← LinearMap.map_smul, hhalf]
  rw [hsymp, hψ, map_div₀, map_ofNat, add_div]
