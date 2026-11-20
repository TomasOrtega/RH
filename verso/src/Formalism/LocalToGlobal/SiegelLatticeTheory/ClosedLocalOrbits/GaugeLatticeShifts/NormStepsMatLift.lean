import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviElt

noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Matrix Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace MatLiftPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

/- English proof (translation)
Establish `h : ∀ i j, ∃ t : ↥(IntAf X.B.I.F X.B.I.E), X.ew * ((P - 1) i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t`. Introduce `i j`. Establish `h0 : ∀ v, TR.res v ((P - 1) i j) = 0` using `fun v => by`. Use `congrFun (congrFun (hP v) i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`.

Rewrite using `[Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Take `⟨t, ht, e⟩` from `(TR.res_ker _).1 h0`. Conclude with `⟨⟨t, ht⟩, e⟩`. Use `choose T hT using h`.

Use `⟨Matrix.of T, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `e` using `hT i j`. Simplify using `only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply] at e ⊢`. Generalize the expression as in `((1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) i j) = o at e ⊢`.

Move the coercions through the operations in `at e ⊢`. Take the linear combination `(ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e - ((P i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - (o : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * hew`.
-/
theorem near_one (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (P : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hP : ∀ v, P.map (TR.res v) = 1) :
    ∃ T : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • P = ηO • (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) := by
  have h : ∀ i j, ∃ t : ↥(IntAf X.B.I.F X.B.I.E), X.ew * ((P - 1) i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
    intro i j
    have h0 : ∀ v, TR.res v ((P - 1) i j) = 0 := fun v => by
      have := congrFun (congrFun (hP v) i) j
      simp only [Matrix.map_apply] at this
      rw [Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨t, ht, e⟩ := (TR.res_ker _).1 h0
    exact ⟨⟨t, ht⟩, e⟩
  choose T hT using h
  refine ⟨Matrix.of T, ?_⟩
  ext i j
  have e := hT i j
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply] at e ⊢
  generalize ((1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) i j) = o at e ⊢
  push_cast at e ⊢
  linear_combination (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e -
    ((P i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - (o : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * hew

/- English proof (translation)
Use `set J := Ideal.span {((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E))}`. Establish `hm : (Ideal.Quotient.mk J).mapMatrix (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) = 1`. Establish `hg : Ideal.Quotient.mk J ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`. Use extensionality with `i j`. Apply the tactic sequence `rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.add_apply, *]`.

Establish `h1 : Ideal.Quotient.mk J ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det) = 1`. Rewrite using `[RingHom.map_det, hm, Matrix.det_one]`. Establish `h2 : (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det - 1 ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 h2`.

Conclude with `⟨a, by rw [mul_comm, ha]; ring⟩`.
-/
theorem det_near (T : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) :
    ∃ s0 : ↥(IntAf X.B.I.F X.B.I.E), (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det = 1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0 := by
  set J := Ideal.span {((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E))}
  have hm : (Ideal.Quotient.mk J).mapMatrix (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) = 1 := by
    have hg : Ideal.Quotient.mk J ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    ext i j
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.add_apply, *]
  have h1 : Ideal.Quotient.mk J ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det) = 1 := by
    rw [RingHom.map_det, hm, Matrix.det_one]
  have h2 : (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
  exact ⟨a, by rw [mul_comm, ha]; ring⟩

/- English proof (translation)
Take `⟨T, hT⟩` from `near_one TR ηO hew (A * B) hAB`. Take `⟨s0, hs0⟩` from `det_near (X := X) T`. Take `⟨s', hs', e⟩` from `hj s0 s0.2`. Establish `e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO` using `Subtype.ext (by simpa using e)`. Use `⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate), ?_⟩` and prove the remaining obligations.

Establish `e0 : A * ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate)) = (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (A * B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate)`. Rewrite using `[Matrix.mul_smul, Matrix.mul_assoc]`. Rewrite using `[e0, smul_comm, ← Matrix.smul_mul, hT, Matrix.smul_mul, Matrix.mul_adjugate, hs0, smul_smul, smul_smul]`. Use `congr 1`. Take the linear combination `e'`.
-/
theorem right_inv (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (hj : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ηO)
    (A B : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hAB : ∀ v, (A * B).map (TR.res v) = 1) :
    ∃ B' : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • (A * B') = ηO • 1 := by
  obtain ⟨T, hT⟩ := near_one TR ηO hew (A * B) hAB
  obtain ⟨s0, hs0⟩ := det_near (X := X) T
  obtain ⟨s', hs', e⟩ := hj s0 s0.2
  have e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO := Subtype.ext (by simpa using e)
  refine ⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate), ?_⟩
  have e0 : A * ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate)) =
      (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (A * B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate) := by
    rw [Matrix.mul_smul, Matrix.mul_assoc]
  rw [e0, smul_comm, ← Matrix.smul_mul, hT, Matrix.smul_mul, Matrix.mul_adjugate, hs0, smul_smul, smul_smul]
  congr 1
  linear_combination e'

/- English proof (translation)
Take `⟨T, hT⟩` from `near_one TR ηO hew (B * A) hAB`. Take `⟨s0, hs0⟩` from `det_near (X := X) T`. Take `⟨s', hs', e⟩` from `hj s0 s0.2`. Establish `e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO` using `Subtype.ext (by simpa using e)`. Use `⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B), ?_⟩` and prove the remaining obligations.

Establish `e0 : ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B)) * A = (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * (B * A))`. Rewrite using `[Matrix.smul_mul, Matrix.mul_assoc]`. Rewrite using `[e0, smul_comm, ← Matrix.mul_smul, hT, Matrix.mul_smul, Matrix.adjugate_mul, hs0, smul_smul, smul_smul]`. Use `congr 1`. Take the linear combination `e'`.
-/
theorem left_inv (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (hj : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ηO)
    (A B : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hAB : ∀ v, (B * A).map (TR.res v) = 1) :
    ∃ B' : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • (B' * A) = ηO • 1 := by
  obtain ⟨T, hT⟩ := near_one TR ηO hew (B * A) hAB
  obtain ⟨s0, hs0⟩ := det_near (X := X) T
  obtain ⟨s', hs', e⟩ := hj s0 s0.2
  have e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO := Subtype.ext (by simpa using e)
  refine ⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B), ?_⟩
  have e0 : ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B)) * A =
      (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * (B * A)) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc]
  rw [e0, smul_comm, ← Matrix.mul_smul, hT, Matrix.mul_smul, Matrix.adjugate_mul, hs0, smul_smul, smul_smul]
  congr 1
  linear_combination e'

/- English proof (translation)
Use extensionality with `i j`. Use `congrArg (fun M : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E) => ((M i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) h` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Subring.coe_mul, Matrix.map_apply, Matrix.one_apply] at this ⊢`. Move the coercions through the operations in `at this`. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa using this`.
-/
theorem coe_eq (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (P Q : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (h : ηO • (P * Q) = ηO • 1) :
    (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P.map Subtype.val * Q.map Subtype.val) =
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (1 : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by
  ext i j
  have := congrArg (fun M : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E) => ((M i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) h
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Subring.coe_mul, Matrix.map_apply,
    Matrix.one_apply] at this ⊢
  push_cast at this
  split_ifs at this ⊢ <;> simpa using this

/- English proof (translation)
Introduce `η hη _ hew _ hj s`. Use `set ηO : ↥(IntAf X.B.I.F X.B.I.E) := ⟨η, hη⟩`. Establish `hs : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v, TR.res v c = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j` using `fun i j => by`. Take `⟨c, hc⟩` from `TR.res_joint (fun v => (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)`. Conclude with `⟨c, fun v => congrFun hc v⟩`.

Establish `hs' : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v, TR.res v c = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j` using `fun i j => by`. Take `⟨c, hc⟩` from `TR.res_joint (fun v => (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)`. Conclude with `⟨c, fun v => congrFun hc v⟩`. Use `choose A hA using hs`. Use `choose B hB using hs'`.

Establish `hAm : ∀ v, (Matrix.of A).map (TR.res v) = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v))` using `fun v => by`. Use extensionality with `i j`. Simplify using `[hA]`. Establish `hBm : ∀ v, (Matrix.of B).map (TR.res v) = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v))` using `fun v => by ext i j; simp [hB]`. Establish `hAB : ∀ v, (Matrix.of A * Matrix.of B).map (TR.res v) = 1` using `fun v => by`.

Rewrite using `[Matrix.map_mul, hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hBA : ∀ v, (Matrix.of B * Matrix.of A).map (TR.res v) = 1` using `fun v => by`. Rewrite using `[Matrix.map_mul, hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Take `⟨R', hR'⟩` from `right_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hAB`. Take `⟨L', hL'⟩` from `left_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hBA`.

Establish `e1 : ηO • L' = ηO • R'`. Combine the equalities or inequalities in the displayed calculation. Use `⟨(Matrix.of A).map Subtype.val, R'.map Subtype.val, fun i j => ⟨(A i j).2, (R' i j).2⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `coe_eq ηO _ _ hR'`. Use `coe_eq ηO _ _ ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Introduce `v`. Use extensionality with `i j`. Use `show resT TR v ((A i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j`. Rewrite using `[LeviEltPf.resT_of_mem TR v (A i j).2]`.

Conclude with `hA i j v`.
-/
theorem integral_matrix_lift_exists : MatLift TR := by
  intro η hη _ hew _ hj s
  set ηO : ↥(IntAf X.B.I.F X.B.I.E) := ⟨η, hη⟩
  have hs : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v, TR.res v c = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j :=
    fun i j => by
      obtain ⟨c, hc⟩ := TR.res_joint (fun v => (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
      exact ⟨c, fun v => congrFun hc v⟩
  have hs' : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v,
      TR.res v c = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j :=
    fun i j => by
      obtain ⟨c, hc⟩ := TR.res_joint (fun v => (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
      exact ⟨c, fun v => congrFun hc v⟩
  choose A hA using hs
  choose B hB using hs'
  have hAm : ∀ v, (Matrix.of A).map (TR.res v) = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := fun v => by
    ext i j; simp [hA]
  have hBm : ∀ v, (Matrix.of B).map (TR.res v) = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) :=
    fun v => by ext i j; simp [hB]
  have hAB : ∀ v, (Matrix.of A * Matrix.of B).map (TR.res v) = 1 := fun v => by
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : ∀ v, (Matrix.of B * Matrix.of A).map (TR.res v) = 1 := fun v => by
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨R', hR'⟩ := right_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hAB
  obtain ⟨L', hL'⟩ := left_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hBA
  have e1 : ηO • L' = ηO • R' := by
    calc ηO • L' = L' * (ηO • (1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E))) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = L' * (ηO • (Matrix.of A * R')) := by rw [hR']
      _ = (ηO • (L' * Matrix.of A)) * R' := by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = ηO • R' := by rw [hL', Matrix.smul_mul, Matrix.one_mul]
  refine ⟨(Matrix.of A).map Subtype.val, R'.map Subtype.val, fun i j => ⟨(A i j).2, (R' i j).2⟩, ?_, ?_, ?_⟩
  · exact coe_eq ηO _ _ hR'
  · refine coe_eq ηO _ _ ?_
    calc ηO • (R' * Matrix.of A) = (ηO • R') * Matrix.of A := by rw [Matrix.smul_mul]
      _ = (ηO • L') * Matrix.of A := by rw [e1]
      _ = ηO • 1 := by rw [Matrix.smul_mul, hL']
  · intro v
    ext i j
    show resT TR v ((A i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j
    rw [LeviEltPf.resT_of_mem TR v (A i j).2]
    exact hA i j v

end MatLiftPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
