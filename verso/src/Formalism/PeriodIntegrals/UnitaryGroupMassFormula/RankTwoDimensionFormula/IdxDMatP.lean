import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h1 : E * (1 - E) = 0` using `by rw [mul_sub, mul_one, hE, sub_self]`. Establish `h2 : (1 - E) * E = 0` using `by rw [sub_mul, one_mul, hE, sub_self]`. Establish `h3 : (1 - E) * (1 - E) = 1 - E` using `by rw [sub_mul, one_mul, h1, sub_zero]`. Establish `e1 : E * a * (E * b) = E * (a * b)`. Rewrite using `[mul_assoc, ← mul_assoc a E b, ← hc a, ← mul_assoc, ← mul_assoc, hE, mul_assoc]`.

Establish `e2 : E * a * (1 - E) = 0`. Establish `: a * (1 - E) = (1 - E) * a` using `by rw [mul_sub, sub_mul, mul_one, one_mul, hc a]`. Rewrite using `[mul_assoc, this, ← mul_assoc, h1, zero_mul]`. Establish `e3 : (1 - E) * (E * b) = 0` using `by rw [← mul_assoc, h2, zero_mul]`. Rewrite using `[add_mul, mul_add, mul_add, e1, e2, e3, h3, add_zero, zero_add]`.
-/
theorem mat_idem_mul {Rg : Type} [Ring Rg] (E a b : Rg) (hE : E * E = E) (hc : ∀ x : Rg, E * x = x * E) :
    (E * a + (1 - E)) * (E * b + (1 - E)) = E * (a * b) + (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : E * a * (E * b) = E * (a * b) := by
    rw [mul_assoc, ← mul_assoc a E b, ← hc a, ← mul_assoc, ← mul_assoc, hE, mul_assoc]
  have e2 : E * a * (1 - E) = 0 := by
    have : a * (1 - E) = (1 - E) * a := by rw [mul_sub, sub_mul, mul_one, one_mul, hc a]
    rw [mul_assoc, this, ← mul_assoc, h1, zero_mul]
  have e3 : (1 - E) * (E * b) = 0 := by rw [← mul_assoc, h2, zero_mul]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, h3, add_zero, zero_add]

/- English proof (translation)
Use `set Q : Matrix (Fin k) (Fin k) O := 1 + gO • tt with hQdef`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : O, Q.det = 1 + gO * m := by`. Establish `hQ : (Ideal.Quotient.mk (Ideal.span {gO})).mapMatrix Q = 1`. Establish `hπg : Ideal.Quotient.mk (Ideal.span {gO}) gO = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Rewrite using `[hQdef, map_add, map_one]`.

Use extensionality with `i j`. Simplify using `[hπg]`. Establish `h1 : Ideal.Quotient.mk (Ideal.span {gO}) (Q.det - 1) = 0`. Rewrite using `[map_sub, RingHom.map_det, hQ, det_one, map_one, sub_self]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, ha]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨yO, hey0⟩` from `hJ m`. Establish `hey : eO * Q.det * yO = eO` using `by rw [hm]; exact hey0`.

Use `set εO := eO * wO with hεdef`. Use `set E : Matrix (Fin k) (Fin k) O := εO • 1 with hEdef`. Establish `hEc : ∀ x : Matrix (Fin k) (Fin k) O, E * x = x * E`. Introduce `x`. Simplify using `[hEdef]`.

Establish `hε2 : εO * εO = εO`. Combine the equalities or inequalities in the displayed calculation. Establish `hE2 : E * E = E` using `by simp [hEdef, smul_smul, hε2]`. Establish `hEQ : E * (No * Mo) = E * Q`. Use extensionality with `i j`.

Simplify using `only [hEdef, Matrix.smul_mul, one_mul, Matrix.smul_apply, smul_eq_mul, hQdef, Matrix.add_apply]`. Establish `h1 : (No * Mo) i j = (No * Mo - 1) i j + (1 : Matrix (Fin k) (Fin k) O) i j`. Rewrite using `[Matrix.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : wO * (gO * tt i j) = gO * tt i j`.

Rewrite using `[← htt i j, ← mul_assoc, hw2]`. Establish `key : εO * (No * Mo - 1) i j = εO * (gO • tt) i j`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, mul_add, mul_add, key, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `set P : Matrix (Fin k) (Fin k) O := yO • Q.adjugate with hPdef`. Establish `hEPQ : E * (P * Q) = E`. Establish `: P * Q = (yO * Q.det) • (1 : Matrix (Fin k) (Fin k) O)`. Rewrite using `[hPdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]`. Rewrite using `[this, hEdef, smul_mul_smul, one_mul]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Use `⟨E * Mo + (1 - E), E * (P * No) + (1 - E), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mat_idem_mul E _ _ hE2 hEc]`. Establish `: E * (P * No * Mo) = E`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc E, hEc P, Matrix.mul_assoc, hEQ, ← Matrix.mul_assoc, ← hEc P, Matrix.mul_assoc, hEPQ]`. Rewrite using `[this, add_sub_cancel]`. Introduce `i j`. Establish `hEC : E * (E * Mo + (1 - E)) = E * Mo`. Rewrite using `[Matrix.mul_add, ← Matrix.mul_assoc, hE2, Matrix.mul_sub, Matrix.mul_one, hE2, sub_self, add_zero]`.

Use `congrFun (congrFun hEC i) j` as an intermediate fact. Simplify `this` using `[hEdef, Matrix.smul_mul]`.
-/
theorem mat_lift_core {O : Type} [CommRing O] {k : ℕ} (gO eO wO : O) (he2 : eO * eO = eO) (hw2 : wO * wO = wO)
    (Mo No tt : Matrix (Fin k) (Fin k) O) (htt : ∀ i j, wO * (No * Mo - 1) i j = gO * tt i j)
    (hJ : ∀ m : O, ∃ y : O, eO * (1 + gO * m) * y = eO) :
    ∃ C C' : Matrix (Fin k) (Fin k) O, C' * C = 1 ∧ ∀ i j, (eO * wO) * C i j = (eO * wO) * Mo i j := by
  set Q : Matrix (Fin k) (Fin k) O := 1 + gO • tt with hQdef
  obtain ⟨m, hm⟩ : ∃ m : O, Q.det = 1 + gO * m := by
    have hQ : (Ideal.Quotient.mk (Ideal.span {gO})).mapMatrix Q = 1 := by
      have hπg : Ideal.Quotient.mk (Ideal.span {gO}) gO = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [hQdef, map_add, map_one]
      ext i j
      simp [hπg]
    have h1 : Ideal.Quotient.mk (Ideal.span {gO}) (Q.det - 1) = 0 := by
      rw [map_sub, RingHom.map_det, hQ, det_one, map_one, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    refine ⟨a, ?_⟩
    rw [mul_comm, ha]; ring
  obtain ⟨yO, hey0⟩ := hJ m
  have hey : eO * Q.det * yO = eO := by rw [hm]; exact hey0
  set εO := eO * wO with hεdef
  set E : Matrix (Fin k) (Fin k) O := εO • 1 with hEdef
  have hEc : ∀ x : Matrix (Fin k) (Fin k) O, E * x = x * E := by
    intro x; simp [hEdef]
  have hε2 : εO * εO = εO := by
    calc εO * εO = (eO * eO) * (wO * wO) := by rw [hεdef]; ring
      _ = εO := by rw [he2, hw2]
  have hE2 : E * E = E := by simp [hEdef, smul_smul, hε2]
  have hEQ : E * (No * Mo) = E * Q := by
    ext i j
    simp only [hEdef, Matrix.smul_mul, one_mul, Matrix.smul_apply, smul_eq_mul, hQdef, Matrix.add_apply]
    have h1 : (No * Mo) i j = (No * Mo - 1) i j + (1 : Matrix (Fin k) (Fin k) O) i j := by
      rw [Matrix.sub_apply]; ring
    have h2 : wO * (gO * tt i j) = gO * tt i j := by
      rw [← htt i j, ← mul_assoc, hw2]
    have key : εO * (No * Mo - 1) i j = εO * (gO • tt) i j := by
     calc εO * (No * Mo - 1) i j = eO * (wO * (No * Mo - 1) i j) := by rw [hεdef]; ring
      _ = eO * (wO * (gO * tt i j)) := by rw [htt i j, h2]
      _ = εO * (gO * tt i j) := by rw [hεdef]; ring
      _ = εO * (gO • tt) i j := by rw [Matrix.smul_apply, smul_eq_mul]
    rw [h1, mul_add, mul_add, key, Matrix.smul_apply, smul_eq_mul]; ring
  set P : Matrix (Fin k) (Fin k) O := yO • Q.adjugate with hPdef
  have hEPQ : E * (P * Q) = E := by
    have : P * Q = (yO * Q.det) • (1 : Matrix (Fin k) (Fin k) O) := by
      rw [hPdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    rw [this, hEdef, smul_mul_smul, one_mul]
    congr 1
    calc εO * (yO * Q.det) = wO * (eO * Q.det * yO) := by rw [hεdef]; ring
      _ = εO := by rw [hey, hεdef, mul_comm]
  refine ⟨E * Mo + (1 - E), E * (P * No) + (1 - E), ?_, ?_⟩
  · rw [mat_idem_mul E _ _ hE2 hEc]
    have : E * (P * No * Mo) = E := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEc P, Matrix.mul_assoc, hEQ, ← Matrix.mul_assoc, ← hEc P,
        Matrix.mul_assoc, hEPQ]
    rw [this, add_sub_cancel]
  · intro i j
    have hEC : E * (E * Mo + (1 - E)) = E * Mo := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hE2, Matrix.mul_sub, Matrix.mul_one, hE2, sub_self, add_zero]
    have := congrFun (congrFun hEC i) j
    simpa [hEdef, Matrix.smul_mul] using this

/- English proof (translation)
Introduce `D X TR e he A`. Establish `heO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E` using `Subring.subset_closure (Set.mem_union_right _ ⟨⟨e, he.1⟩, rfl⟩)`. Take `⟨t, ht, het⟩` from `he.2.2.1`. Establish `htO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) ∈ IntAf X.B.I.F X.B.I.E` using `Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)`. Set `eO : IntAf X.B.I.F X.B.I.E` to `⟨_, heO⟩`.

Set `wO : IntAf X.B.I.F X.B.I.E` to `⟨X.ew, X.ew_int⟩`. Set `tO : IntAf X.B.I.F X.B.I.E` to `⟨_, htO⟩`. Set `gO : IntAf X.B.I.F X.B.I.E` to `X.B.g`. Establish `hgO : ((gO : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)`. Simplify using `[gO]`.

Establish `kerZ : ∀ x : IntAf X.B.I.F X.B.I.E, (∀ v, TR.res v x = 0) → ∃ t : IntAf X.B.I.F X.B.I.E, wO * x = gO * t`. Introduce `x hx`. Take `⟨t, ht, he'⟩` from `(TR.res_ker x).1 hx`. Use `⟨⟨t, ht⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `X.ew * (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t`.

Rewrite using `[hgO]`. Conclude with `he'`. Establish `resG : ∀ v, TR.res v gO = 0`. Use `(TR.res_ker gO).2 ⟨X.ew, X.ew_int, ?_⟩` and prove the remaining obligations. Rewrite using `[hgO, mul_comm]`.

Establish `heq : eO = 1 - gO * tO`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(1 : X.B.I.E) ⊗ₜ[X.B.I.F] e = 1 - (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t)`. Rewrite using `[hgO]`. Establish `h1 : e = 1 - (X.B.g : Af X.B.I.F) * t` using `by rw [← het]; ring`.

Rewrite using `[h1, TensorProduct.tmul_sub]`. Use `congr 1`. Rewrite using `[← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E) (B := Af X.B.I.F)) X.B.g]`. Rewrite using `[Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Establish `resE : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * x) = TR.res v x`.

Introduce `v x`. Rewrite using `[heq, sub_mul, one_mul, map_sub, mul_assoc, map_mul, resG, zero_mul, sub_zero]`. Establish `resEps : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * wO * x) = TR.res v x`. Introduce `v x`. Rewrite using `[mul_assoc, resE]`.

Conclude with `TR.res_ew v x`. Use `choose a0 ha0 using fun i j => TR.res_joint (fun v => (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)`. Use `choose b0 hb0 using fun i j => TR.res_joint (fun v => ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) i j)`. Set `Mo : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E)` to `Matrix.of a0`. Set `No : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E)` to `Matrix.of b0`.

Establish `hNM : ∀ v i j, TR.res v ((No * Mo - 1) i j) = 0`. Introduce `v i j`. Establish `hM : (TR.res v).mapMatrix Mo = (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v))`. Use extensionality with `i j`. Conclude with `congrFun (ha0 i j) v`.

Establish `hN : (TR.res v).mapMatrix No = ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v))`. Use extensionality with `i j`. Conclude with `congrFun (hb0 i j) v`. Establish `: (TR.res v).mapMatrix (No * Mo - 1) = 0`. Rewrite using `[map_sub, map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one, sub_self]`.

Conclude with `congrFun (congrFun this i) j`. Use `choose tt htt using fun i j => kerZ _ (fun v => hNM v i j)`. Establish `hw2 : wO * wO = wO` using `Subtype.ext X.ew_idem`. Establish `he2 : eO * eO = eO` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.2.1])`. Establish `hJO : ∀ m : IntAf X.B.I.F X.B.I.E, ∃ y : IntAf X.B.I.F X.B.I.E, eO * (1 + gO * m) * y = eO`. Introduce `m`. Take `⟨y, hy, hyeq⟩` from `hJ X.B.I.F X.B.I.E X.B.g e he (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) m.2`. Use `⟨⟨y, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (1 + (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) * y = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e`. Rewrite using `[hgO]`. Conclude with `hyeq`. Take `⟨CO, C'O, hCC, hent⟩` from `mat_lift_core gO eO wO he2 hw2 Mo No (Matrix.of tt) (fun i j => htt i j) hJO`. Use `⟨CO.map (IntAf X.B.I.F X.B.I.E).subtype, C'O.map (IntAf X.B.I.F X.B.I.E).subtype, ?_, fun i j => ⟨(CO i j).2, (C'O i j).2⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.map_mul, hCC, Matrix.map_one _ (map_zero _) (map_one _)]`. Introduce `v i j`. Establish `hmem : epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j ∈ IntAf X.B.I.F X.B.I.E` using `(eO * wO * CO i j).2`. Unfold `resT`. Rewrite using `[dif_pos hmem]`.

Establish `: (⟨epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j, hmem⟩ : IntAf X.B.I.F X.B.I.E) = eO * wO * Mo i j`. Rewrite using `[← hent i j]`. Both sides reduce to the same expression. Rewrite using `[this, resEps]`. Conclude with `congrFun (ha0 i j) v`.
-/
theorem idxDMat_of (hJ : IdxDJacE) : IdxDMat := by
  intro D X TR e he A
  have heO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨e, he.1⟩, rfl⟩)
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have htO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)
  let eO : IntAf X.B.I.F X.B.I.E := ⟨_, heO⟩
  let wO : IntAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  let tO : IntAf X.B.I.F X.B.I.E := ⟨_, htO⟩
  let gO : IntAf X.B.I.F X.B.I.E := X.B.g
  have hgO : ((gO : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    simp [gO]
  have kerZ : ∀ x : IntAf X.B.I.F X.B.I.E, (∀ v, TR.res v x = 0) →
      ∃ t : IntAf X.B.I.F X.B.I.E, wO * x = gO * t := by
    intro x hx
    obtain ⟨t, ht, he'⟩ := (TR.res_ker x).1 hx
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change X.ew * (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t
    rw [hgO]; exact he'
  have resG : ∀ v, TR.res v gO = 0 := by
    refine (TR.res_ker gO).2 ⟨X.ew, X.ew_int, ?_⟩
    rw [hgO, mul_comm]
  have heq : eO = 1 - gO * tO := by
    apply Subtype.ext
    change (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e = 1 - (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t)
    rw [hgO]
    have h1 : e = 1 - (X.B.g : Af X.B.I.F) * t := by rw [← het]; ring
    rw [h1, TensorProduct.tmul_sub]
    congr 1
    rw [← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E) (B := Af X.B.I.F)) X.B.g]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have resE : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * x) = TR.res v x := by
    intro v x
    rw [heq, sub_mul, one_mul, map_sub, mul_assoc, map_mul, resG, zero_mul, sub_zero]
  have resEps : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * wO * x) = TR.res v x := by
    intro v x
    rw [mul_assoc, resE]
    exact TR.res_ew v x
  choose a0 ha0 using fun i j => TR.res_joint (fun v => (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
  choose b0 hb0 using fun i j => TR.res_joint
    (fun v => ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) i j)
  let Mo : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of a0
  let No : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of b0
  have hNM : ∀ v i j, TR.res v ((No * Mo - 1) i j) = 0 := by
    intro v i j
    have hM : (TR.res v).mapMatrix Mo = (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (ha0 i j) v
    have hN : (TR.res v).mapMatrix No = ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (hb0 i j) v
    have : (TR.res v).mapMatrix (No * Mo - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one, sub_self]
    exact congrFun (congrFun this i) j
  choose tt htt using fun i j => kerZ _ (fun v => hNM v i j)
  have hw2 : wO * wO = wO := Subtype.ext X.ew_idem
  have he2 : eO * eO = eO := Subtype.ext (by
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.2.1])
  have hJO : ∀ m : IntAf X.B.I.F X.B.I.E, ∃ y : IntAf X.B.I.F X.B.I.E, eO * (1 + gO * m) * y = eO := by
    intro m
    obtain ⟨y, hy, hyeq⟩ := hJ X.B.I.F X.B.I.E X.B.g e he (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) m.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (1 + (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) * y =
      (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [hgO]; exact hyeq
  obtain ⟨CO, C'O, hCC, hent⟩ := mat_lift_core gO eO wO he2 hw2 Mo No (Matrix.of tt) (fun i j => htt i j) hJO
  refine ⟨CO.map (IntAf X.B.I.F X.B.I.E).subtype, C'O.map (IntAf X.B.I.F X.B.I.E).subtype, ?_,
    fun i j => ⟨(CO i j).2, (C'O i j).2⟩, ?_⟩
  · rw [← Matrix.map_mul, hCC, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro v i j
    have hmem : epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j ∈ IntAf X.B.I.F X.B.I.E :=
      (eO * wO * CO i j).2
    unfold resT
    rw [dif_pos hmem]
    have : (⟨epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j, hmem⟩ : IntAf X.B.I.F X.B.I.E) =
        eO * wO * Mo i j := by
      rw [← hent i j]; rfl
    rw [this, resEps]
    exact congrFun (ha0 i j) v

end PI.UnitaryDimensionFormula
