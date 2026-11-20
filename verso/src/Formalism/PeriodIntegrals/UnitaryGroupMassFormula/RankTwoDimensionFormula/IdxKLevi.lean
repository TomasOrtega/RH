import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DualBetaReferenceCongruence

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section AlgL

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

/- English proof (translation)
Simplify using `only [dotProduct, hrow, Formalism.UG.hform, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem hrow_dot (x y : Fin n → A) : hrow σ J x ⬝ᵥ y = Formalism.UG.hform σ J x y := by
  simp only [dotProduct, hrow, Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `q`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun r _ => by ring`.
-/
private lemma vecMulVec_mulVec_rank_two_dimension_formula (u v y : Fin n → A) : Matrix.vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  ext q
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

/- English proof (translation)
Rewrite using `[sMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sum_mulVec]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_rank_two_dimension_formula, vecMulVec_mulVec_rank_two_dimension_formula, hrow_dot, hrow_dot, smul_smul, smul_smul]`.
-/
theorem sMat_mulVec (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A) :
    sMat σ J b bs C D *ᵥ y = y + ∑ i, ∑ j, (((C - 1) i j * Formalism.UG.hform σ J (bs j) y) • b i +
      ((D - 1) i j * Formalism.UG.hform σ J (b j) y) • bs i) := by
  rw [sMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_rank_two_dimension_formula,
    vecMulVec_mulVec_rank_two_dimension_formula, hrow_dot, hrow_dot, smul_smul, smul_smul]

end AlgL

section Main

variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr ⟨⟨e, he⟩, rfl⟩)`.
-/
theorem tmul_one_mem {e : Af X.B.I.F} (he : e ∈ Formalism.UG.intAd X.B.I.F) :
    ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Or.inr ⟨⟨e, he⟩, rfl⟩)

/- English proof (translation)
Take `⟨t, ht, hxy⟩` from `hZ`. Establish `hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E` using `natCast_mem _ _`. Establish `hgt : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t ∈ IntAf X.B.I.F X.B.I.E` using `(IntAf X.B.I.F X.B.I.E).mul_mem hg ht`. Establish `hx : x = y + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t` using `sub_eq_iff_eq_add'.1 hxy`. Establish `hxm : x ∈ IntAf X.B.I.F X.B.I.E` using `hx ▸ (IntAf X.B.I.F X.B.I.E).add_mem hy hgt`.

Establish `h0 : TR.res v ⟨_, hgt⟩ = 0`. Use `(TR.res_ker ⟨_, hgt⟩).2 ?_ v` and prove the remaining obligations. Conclude with `⟨X.ew * t, (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int ht, mul_left_comm _ _ _⟩`. Establish `hsplit : (⟨x, hxm⟩ : IntAf X.B.I.F X.B.I.E) = ⟨y, hy⟩ + ⟨_, hgt⟩` using `Subtype.ext hx`. Simplify using `only [resT, dif_pos hxm, dif_pos hy]`.

Rewrite using `[hsplit, map_add, h0, add_zero]`.
-/
theorem resT_congr (TR : TypedRed X) (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) (hZ : ZMod' X.B.I X.B.g (x - y)) : resT TR v x = resT TR v y := by
  obtain ⟨t, ht, hxy⟩ := hZ
  have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E :=
    natCast_mem _ _
  have hgt : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t ∈ IntAf X.B.I.F X.B.I.E :=
    (IntAf X.B.I.F X.B.I.E).mul_mem hg ht
  have hx : x = y + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := sub_eq_iff_eq_add'.1 hxy
  have hxm : x ∈ IntAf X.B.I.F X.B.I.E := hx ▸ (IntAf X.B.I.F X.B.I.E).add_mem hy hgt
  have h0 : TR.res v ⟨_, hgt⟩ = 0 := by
    refine (TR.res_ker ⟨_, hgt⟩).2 ?_ v
    exact ⟨X.ew * t, (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int ht, mul_left_comm _ _ _⟩
  have hsplit : (⟨x, hxm⟩ : IntAf X.B.I.F X.B.I.E) = ⟨y, hy⟩ + ⟨_, hgt⟩ := Subtype.ext hx
  simp only [resT, dif_pos hxm, dif_pos hy]
  rw [hsplit, map_add, h0, add_zero]

/- English proof (translation)
Introduce `D X TR e he b bs hF hL hC C C' _ hCint v i j`. Establish `hew` using `X.ew_int`. Establish `hbwd : ∀ l, X.bwd l ∈ X.B.I.Lf` using `fun l => (X.vectorsInLattice.2.2 l).2`. Establish `he1 : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E` using `tmul_one_mem he.1`. Establish `hεint : epsX X e * C i j ∈ IntAf X.B.I.F X.B.I.E` using `mul_mem (mul_mem he1 hew) (hCint i j).1`.

Apply `resT_congr TR v hεint` to reduce the goal to its premises. Establish `hh : ∀ x y : VA X.B.I, Formalism.UG.hform (sigA X.B.I) (JA X.B.I) x y = hA X.B.I x y` using `fun _ _ => rfl`. Establish `hsig1 : sigA X.B.I ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e`. Rewrite using `[unitaryCongruence.sigA_tmul, star_one]`. Establish `hzero : ∀ q, hA X.B.I (b q) (X.bw j) = 0`.

Introduce `q`. Rewrite using `[hF.2.2.1 q, X.bw_w j, unitaryCongruence.hA_smul_left, unitaryCongruence.hA_smul_right]`. Unfold `epsX`. Rewrite using `[map_mul, hsig1]`. Use `X.ew_orth` as an intermediate fact.

Take the linear combination `((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * hA X.B.I (b q) (X.bw j) * this`. Establish `hexp : hA X.B.I (X.bwd i) (sMat (sigA X.B.I) (JA X.B.I) b bs C (C'.map (sigA X.B.I))ᵀ *ᵥ X.bw j) = hA X.B.I (X.bwd i) (X.bw j) + ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p)`. Rewrite using `[sMat_mulVec]`. Simplify using `only [hh]`. Rewrite using `[← unitaryCongruence.hL_apply]`.

Simplify using `only [map_add, map_sum, map_smul, unitaryCongruence.hL_apply, smul_eq_mul, hzero, mul_zero, zero_mul, add_zero]`. Rewrite using `[hexp]`. Establish `hCm : ∀ p q, (C - 1) p q ∈ IntAf X.B.I.F X.B.I.E`. Introduce `p q`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply]`.

Use `sub_mem (hCint p q).1 ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `set S1 := ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) with hS1`.

Use `set S2 := ∑ p, ∑ q, (C - 1) p q * ((if q = j then X.ew else 0) * (if i = p then X.ew else 0)) with hS2`. Establish `key1 : ZMod' X.B.I X.B.g (S1 - S2)`. Establish `eq : S1 - S2 = ∑ p, ∑ q, (C - 1) p q * (hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) - (if q = j then X.ew else 0) * (if i = p then X.ew else 0))`. Rewrite using `[hS1, hS2]`. Simplify using `only [← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq]`. Use `unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun p _ => unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun q _ => ?_` and prove the remaining obligations. Use `unitaryCongruence.Z_smul X.B.I X.B.g (hCm p q) ?_` and prove the remaining obligations.

Establish `eq2 : hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) - (if q = j then X.ew else 0) * (if i = p then X.ew else 0) = hA X.B.I (X.bwd i) (b p) * (hA X.B.I (bs q) (X.bw j) - if q = j then X.ew else 0) + (if q = j then X.ew else 0) * (hA X.B.I (X.bwd i) (b p) - if i = p then X.ew …` using `by ring`. Rewrite using `[eq2]`. Use `unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g (unitaryCongruence.hA_int X.B.I (hbwd i) (hL p).1) (hC q j).1) (unitaryCongruence.Z_smul X.B.I X.B.g ?_ (hC i p).2)` and prove the remaining obligations. Use `split_ifs`. Conclude with `hew`.

Conclude with `zero_mem _`. Establish `hsum : S2 = (C - 1) i j * X.ew`. Rewrite using `[hS2]`. Simplify using `[mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', X.ew_idem]`. Take `⟨t, ht, het⟩` from `he.2.2.1`.

Establish `hlast : ZMod' X.B.I X.B.g ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j)`. Use `⟨((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) * X.ew * C i j, mul_mem (mul_mem (tmul_one_mem ht) hew) (hCint i j).1, ?_⟩` and prove the remaining obligations. Establish `hg : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] ((X.B.g : Af X.B.I.F)) = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)`. Rewrite using `[← Algebra.TensorProduct.includeRight_apply (R := X.B.I.F) (A := X.B.I.E), map_natCast]`. Establish `h1 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t)`.

Rewrite using `[het, ← hg, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Establish `h2 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) = 1 - (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e`. Rewrite using `[TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]`. Establish `h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e = 1 - (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t)`. Rewrite using `[← h1, h2]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `epsX`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply, h3]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `eqF : hA X.B.I (X.bwd i) (X.bw j) + S1 - epsX X e * C i j = (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (S1 - S2) + (S2 - (C - 1) i j * X.ew) + ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j)` using `by ring`.

Establish `h0 : S2 - (C - 1) i j * X.ew = 0` using `by rw [hsum, sub_self]`. Rewrite using `[eqF, h0, add_zero]`. Conclude with `unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g (X.bw_dual i j) key1) hlast`.
-/
theorem idxDLevi : IdxDLevi := by
  intro D X TR e he b bs hF hL hC C C' _ hCint v i j
  have hew := X.ew_int
  have hbwd : ∀ l, X.bwd l ∈ X.B.I.Lf := fun l => (X.vectorsInLattice.2.2 l).2
  have he1 : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E := tmul_one_mem he.1
  have hεint : epsX X e * C i j ∈ IntAf X.B.I.F X.B.I.E := mul_mem (mul_mem he1 hew) (hCint i j).1
  apply resT_congr TR v hεint
  have hh : ∀ x y : VA X.B.I, Formalism.UG.hform (sigA X.B.I) (JA X.B.I) x y = hA X.B.I x y := fun _ _ => rfl
  have hsig1 : sigA X.B.I ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e := by
    rw [unitaryCongruence.sigA_tmul, star_one]
  have hzero : ∀ q, hA X.B.I (b q) (X.bw j) = 0 := by
    intro q
    rw [hF.2.2.1 q, X.bw_w j, unitaryCongruence.hA_smul_left, unitaryCongruence.hA_smul_right]
    unfold epsX
    rw [map_mul, hsig1]
    have := X.ew_orth
    linear_combination ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * hA X.B.I (b q) (X.bw j) * this
  have hexp : hA X.B.I (X.bwd i) (sMat (sigA X.B.I) (JA X.B.I) b bs C (C'.map (sigA X.B.I))ᵀ *ᵥ X.bw j) =
      hA X.B.I (X.bwd i) (X.bw j) +
        ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) := by
    rw [sMat_mulVec]
    simp only [hh]
    rw [← unitaryCongruence.hL_apply]
    simp only [map_add, map_sum, map_smul, unitaryCongruence.hL_apply, smul_eq_mul, hzero, mul_zero, zero_mul,
      add_zero]
  rw [hexp]
  have hCm : ∀ p q, (C - 1) p q ∈ IntAf X.B.I.F X.B.I.E := by
    intro p q
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine sub_mem (hCint p q).1 ?_
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  set S1 := ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) with hS1
  set S2 := ∑ p, ∑ q, (C - 1) p q * ((if q = j then X.ew else 0) * (if i = p then X.ew else 0)) with hS2
  have key1 : ZMod' X.B.I X.B.g (S1 - S2) := by
    have eq : S1 - S2 = ∑ p, ∑ q, (C - 1) p q * (hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) -
        (if q = j then X.ew else 0) * (if i = p then X.ew else 0)) := by
      rw [hS1, hS2]
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [eq]
    refine unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun p _ => unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun q _ => ?_
    refine unitaryCongruence.Z_smul X.B.I X.B.g (hCm p q) ?_
    have eq2 : hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) -
        (if q = j then X.ew else 0) * (if i = p then X.ew else 0) =
        hA X.B.I (X.bwd i) (b p) * (hA X.B.I (bs q) (X.bw j) - if q = j then X.ew else 0) +
        (if q = j then X.ew else 0) * (hA X.B.I (X.bwd i) (b p) - if i = p then X.ew else 0) := by ring
    rw [eq2]
    refine unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g
      (unitaryCongruence.hA_int X.B.I (hbwd i) (hL p).1) (hC q j).1) (unitaryCongruence.Z_smul X.B.I X.B.g ?_ (hC i p).2)
    split_ifs
    · exact hew
    · exact zero_mem _
  have hsum : S2 = (C - 1) i j * X.ew := by
    rw [hS2]
    simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', X.ew_idem]
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have hlast : ZMod' X.B.I X.B.g ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j) := by
    refine ⟨((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) * X.ew * C i j,
      mul_mem (mul_mem (tmul_one_mem ht) hew) (hCint i j).1, ?_⟩
    have hg : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] ((X.B.g : Af X.B.I.F)) = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      rw [← Algebra.TensorProduct.includeRight_apply (R := X.B.I.F) (A := X.B.I.E), map_natCast]
    have h1 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
      rw [het, ← hg, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) = 1 - (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e := by
      rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]
    have h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e =
        1 - (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
      rw [← h1, h2]; ring
    unfold epsX
    rw [Matrix.sub_apply, Matrix.one_apply, h3]
    split_ifs <;> ring
  have eqF : hA X.B.I (X.bwd i) (X.bw j) + S1 - epsX X e * C i j =
      (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (S1 - S2) + (S2 - (C - 1) i j * X.ew) +
        ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j) := by ring
  have h0 : S2 - (C - 1) i j * X.ew = 0 := by rw [hsum, sub_self]
  rw [eqF, h0, add_zero]
  exact unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g (X.bw_dual i j) key1) hlast

end Main

end PI.UnitaryDimensionFormula
