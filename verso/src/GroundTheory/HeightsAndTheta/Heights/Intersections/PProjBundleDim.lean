import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagArith
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsIntDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Establish `hinj : LinearMap.ker B.transpose.mulVecLin = ⊥`. Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `v w h`. Establish `h' : B.transpose.mulVec v = B.transpose.mulVec w` using `h`. Rewrite `h'` using `[Matrix.mulVec_transpose, Matrix.mulVec_transpose]`.

Conclude with `Matrix.vecMul_injective_iff.2 hB h'`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hinj`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Establish `hl : Matrix.toLin' B.transpose = B.transpose.mulVecLin` using `rfl`. Rewrite using `[← LinearMap.toMatrix'_toLin' B.transpose, ← LinearMap.toMatrix'_comp, hl, hg, LinearMap.toMatrix'_id]`.
-/
theorem exists_mul_transpose_eq_one {F : Type} [Field F] {n N : ℕ} (B : Matrix (Fin n) (Fin N) F)
    (hB : LinearIndependent F B) : ∃ D : Matrix (Fin n) (Fin N) F, D * B.transpose = 1 := by
  have hinj : LinearMap.ker B.transpose.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro v w h
    have h' : B.transpose.mulVec v = B.transpose.mulVec w := h
    rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose] at h'
    exact Matrix.vecMul_injective_iff.2 hB h'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hl : Matrix.toLin' B.transpose = B.transpose.mulVecLin := rfl
  rw [← LinearMap.toMatrix'_toLin' B.transpose, ← LinearMap.toMatrix'_comp, hl, hg, LinearMap.toMatrix'_id]

section Bundle

variable {K : Type} {ι : K → Type}

/- English proof (translation)
Establish `key : (projBundleMap P B).comp (rename (inlV (ι₂` using `fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom = (C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) := by`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)` and prove the remaining obligations. Establish `hC` using `RingHom.ext_int (((projBundleMap P B).comp (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom).comp C) (((C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P))).comp C)`. Conclude with `RingHom.congr_fun hC r`. Take `⟨k, i⟩` from `p`.

Simplify using `[projBundleMap, inlV, genPt]`. Conclude with `RingHom.congr_fun key g`.
-/
theorem projBundleMap_rename_inlV (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (g : MRing ι) :
    projBundleMap P B (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) g) =
      C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P g)) := by
  have key : (projBundleMap P B).comp
      (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom =
      (C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
        ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · have hC := RingHom.ext_int
        (((projBundleMap P B).comp
          (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom).comp C)
        (((C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
          ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P))).comp C)
      exact RingHom.congr_fun hC r
    · obtain ⟨k, i⟩ := p
      simp [projBundleMap, inlV, genPt]
  exact RingHom.congr_fun key g

def projBundleAlgHom (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    MRing (PBlk ι N1) →ₐ[ℤ] MvPolynomial (Fin n) (FnField P) :=
  ⟨projBundleMap P B, fun r => by simp⟩

/- English proof (translation)
Use `set F := projBundleAlgHom P B`. Establish `hker : RingHom.ker F = projBundleIdeal P B` using `rfl`. Set `e : (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) ≃ₐ[ℤ] F.range` to `AlgEquiv.ofRingEquiv (f := ((Ideal.quotientEquivAlgOfEq ℤ hker.symm).trans (Ideal.quotientKerEquivRange F)).toRingEquiv) fun x => Subtype.ext (by simp)`. Rewrite using `[AlgEquiv.trdeg_eq (R := ℤ) (A := MRing (PBlk ι N1) ⧸ projBundleIdeal P B) (A' := F.range) e]`. Use `set S := F.range`.

Establish `hmemS : ∀ g : MRing ι, (C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P g)) : MvPolynomial (Fin n) (FnField P)) ∈ S` using `fun g => ⟨rename (inlV (ι₂ := fun _ : Unit => Fin N1)) g, projBundleMap_rename_inlV P B g⟩`. Establish `hlin : ∀ j, (∑ a, C (B a j) * X a : MvPolynomial (Fin n) (FnField P)) ∈ S` using `fun j => ⟨X ⟨Sum.inr (), j⟩, projBundleMap_X_inr P B () j⟩`. Establish `halgS : ∀ x ∈ S, IsAlgebraic S x` using `fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : S)`. Establish `halgC : ∀ φ : FnField P, IsAlgebraic S (C φ : MvPolynomial (Fin n) (FnField P))`. Introduce `φ`.

Take `⟨a, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := MRing ι ⧸ P) φ`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective s`. Establish `hs0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FnField P) hs`. Establish `hC0 : (C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P s)) : MvPolynomial (Fin n) (FnField P)) ≠ 0`.

Rewrite using `[Ne, C_eq_zero]`. Conclude with `hs0`. Use `IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hC0) (halgS _ (hmemS s)) ?_` and prove the remaining obligations. Rewrite using `[← C_mul, mul_div_cancel₀ _ hs0]`. Conclude with `halgS _ (hmemS a)`.

Take `⟨D, hD⟩` from `exists_mul_transpose_eq_one B hB`. Establish `halgX : ∀ b, IsAlgebraic S (X b : MvPolynomial (Fin n) (FnField P))`. Introduce `b`. Establish `h1 : ∀ a, ∑ j, D b j * B a j = if b = a then 1 else 0` using `fun a => by`. Use `congrFun (congrFun hD b) a` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hX : (X b : MvPolynomial (Fin n) (FnField P)) = ∑ j, C (D b j) * ∑ a, C (B a j) * X a`. Repeatedly rewrite using `[Finset.mul_sum, ← mul_assoc, ← C_mul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_mul, ← map_sum, h1]`.

Simplify using the standard rewrite rules. Rewrite using `[hX]`. Conclude with `(Subalgebra.mem_algebraicClosure S _).1 (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ((Subalgebra.mem_algebraicClosure S _).2 (halgC _)) ((Subalgebra.mem_algebraicClosure S _).2 (halgS _ (hlin j))))`. Establish `hall : ∀ p : MvPolynomial (Fin n) (FnField P), p ∈ Subalgebra.algebraicClosure S _` using `fun p => MvPolynomial.induction_on p (fun φ => halgC φ) (fun _ _ hp hq => Subalgebra.add_mem _ hp hq) (fun _ b hp => Subalgebra.mul_mem _ hp (halgX b))`. Establish `hAlg : Algebra.IsAlgebraic S (MvPolynomial (Fin n) (FnField P))` using `⟨fun p => hall p⟩`.

Establish `hA : Function.Injective (algebraMap ℤ (MRing ι ⧸ P))` using `algebraMap_int_injective P hPz`. Establish `hΦ : Function.Injective (algebraMap ℤ (FnField P))`. Rewrite using `[show algebraMap ℤ (FnField P) = (algebraMap (MRing ι ⧸ P) (FnField P)).comp (algebraMap ℤ _) from RingHom.ext_int _ _]`. Conclude with `(IsFractionRing.injective (MRing ι ⧸ P) (FnField P)).comp hA`. Establish `hM : Function.Injective (algebraMap ℤ (MvPolynomial (Fin n) (FnField P)))`.

Rewrite using `[show algebraMap ℤ (MvPolynomial (Fin n) (FnField P)) = (C : FnField P →+* _).comp (algebraMap ℤ _) from RingHom.ext_int _ _]`. Conclude with `(C_injective _ _).comp hΦ`. Use `(faithfulSMul_iff_algebraMap_injective ℤ (MRing ι ⧸ P)).2 hA` as an intermediate fact. Use `(faithfulSMul_iff_algebraMap_injective (MRing ι ⧸ P) (FnField P)).2 (IsFractionRing.injective (MRing ι ⧸ P) (FnField P))` as an intermediate fact. Use `(faithfulSMul_iff_algebraMap_injective ℤ (FnField P)).2 hΦ` as an intermediate fact.

Use `(faithfulSMul_iff_algebraMap_injective (FnField P) (MvPolynomial (Fin n) (FnField P))).2 (C_injective _ _)` as an intermediate fact. Use `(faithfulSMul_iff_algebraMap_injective S (MvPolynomial (Fin n) (FnField P))).2 Subtype.val_injective` as an intermediate fact. Use `(faithfulSMul_iff_algebraMap_injective ℤ S).2 fun a b h => hM (by` as an intermediate fact. Rewrite using `[IsScalarTower.algebraMap_apply ℤ S (MvPolynomial (Fin n) (FnField P)) a, IsScalarTower.algebraMap_apply ℤ S (MvPolynomial (Fin n) (FnField P)) b, h])`. Establish `: Algebra.IsAlgebraic (MRing ι ⧸ P) (FnField P)` using `IsLocalization.isAlgebraic _ (nonZeroDivisors _)`.

Establish `e1` using `trdeg_add_eq ℤ S (A := MvPolynomial (Fin n) (FnField P))`. Establish `e2` using `trdeg_add_eq ℤ (FnField P) (A := MvPolynomial (Fin n) (FnField P))`. Establish `e3` using `trdeg_add_eq ℤ (MRing ι ⧸ P) (A := FnField P)`. Rewrite `e1` using `[trdeg_eq_zero (R := S) (A := MvPolynomial (Fin n) (FnField P)), add_zero]`. Rewrite `e3` using `[trdeg_eq_zero (R := MRing ι ⧸ P) (A := FnField P), add_zero]`.

Rewrite `e2` using `[MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin]`. Rewrite using `[e1, ← e2, e3]`.
-/
theorem trdeg_projBundle (P : Ideal (MRing ι)) [P.IsPrime] (hPz : IsHorizontal P) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hB : LinearIndependent (FnField P) B) :
    Algebra.trdeg ℤ (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) =
      Algebra.trdeg ℤ (MRing ι ⧸ P) + n := by
  classical
  set F := projBundleAlgHom P B
  have hker : RingHom.ker F = projBundleIdeal P B := rfl
  let e : (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) ≃ₐ[ℤ] F.range :=
    AlgEquiv.ofRingEquiv (f := ((Ideal.quotientEquivAlgOfEq ℤ hker.symm).trans
      (Ideal.quotientKerEquivRange F)).toRingEquiv) fun x => Subtype.ext (by simp)
  rw [AlgEquiv.trdeg_eq (R := ℤ) (A := MRing (PBlk ι N1) ⧸ projBundleIdeal P B) (A' := F.range) e]
  set S := F.range
  have hmemS : ∀ g : MRing ι,
      (C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P g)) : MvPolynomial (Fin n) (FnField P)) ∈ S :=
    fun g => ⟨rename (inlV (ι₂ := fun _ : Unit => Fin N1)) g, projBundleMap_rename_inlV P B g⟩
  have hlin : ∀ j, (∑ a, C (B a j) * X a : MvPolynomial (Fin n) (FnField P)) ∈ S :=
    fun j => ⟨X ⟨Sum.inr (), j⟩, projBundleMap_X_inr P B () j⟩
  have halgS : ∀ x ∈ S, IsAlgebraic S x := fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : S)
  have halgC : ∀ φ : FnField P, IsAlgebraic S (C φ : MvPolynomial (Fin n) (FnField P)) := by
    intro φ
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ P) φ
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hs0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FnField P) hs
    have hC0 : (C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P s)) :
        MvPolynomial (Fin n) (FnField P)) ≠ 0 := by
      rw [Ne, C_eq_zero]
      exact hs0
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hC0) (halgS _ (hmemS s)) ?_
    rw [← C_mul, mul_div_cancel₀ _ hs0]
    exact halgS _ (hmemS a)
  obtain ⟨D, hD⟩ := exists_mul_transpose_eq_one B hB
  have halgX : ∀ b, IsAlgebraic S (X b : MvPolynomial (Fin n) (FnField P)) := by
    intro b
    have h1 : ∀ a, ∑ j, D b j * B a j = if b = a then 1 else 0 := fun a => by
      have := congrFun (congrFun hD b) a
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    have hX : (X b : MvPolynomial (Fin n) (FnField P)) = ∑ j, C (D b j) * ∑ a, C (B a j) * X a := by
      simp_rw [Finset.mul_sum, ← mul_assoc, ← C_mul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, ← map_sum, h1]
      simp
    rw [hX]
    exact (Subalgebra.mem_algebraicClosure S _).1 (Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ ((Subalgebra.mem_algebraicClosure S _).2 (halgC _))
        ((Subalgebra.mem_algebraicClosure S _).2 (halgS _ (hlin j))))
  have hall : ∀ p : MvPolynomial (Fin n) (FnField P), p ∈ Subalgebra.algebraicClosure S _ := fun p =>
    MvPolynomial.induction_on p (fun φ => halgC φ) (fun _ _ hp hq => Subalgebra.add_mem _ hp hq)
      (fun _ b hp => Subalgebra.mul_mem _ hp (halgX b))
  have hAlg : Algebra.IsAlgebraic S (MvPolynomial (Fin n) (FnField P)) := ⟨fun p => hall p⟩

  have hA : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := algebraMap_int_injective P hPz
  have hΦ : Function.Injective (algebraMap ℤ (FnField P)) := by
    rw [show algebraMap ℤ (FnField P) = (algebraMap (MRing ι ⧸ P) (FnField P)).comp (algebraMap ℤ _) from
      RingHom.ext_int _ _]
    exact (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)).comp hA
  have hM : Function.Injective (algebraMap ℤ (MvPolynomial (Fin n) (FnField P))) := by
    rw [show algebraMap ℤ (MvPolynomial (Fin n) (FnField P)) = (C : FnField P →+* _).comp (algebraMap ℤ _) from
      RingHom.ext_int _ _]
    exact (C_injective _ _).comp hΦ
  have := (faithfulSMul_iff_algebraMap_injective ℤ (MRing ι ⧸ P)).2 hA
  have := (faithfulSMul_iff_algebraMap_injective (MRing ι ⧸ P) (FnField P)).2
    (IsFractionRing.injective (MRing ι ⧸ P) (FnField P))
  have := (faithfulSMul_iff_algebraMap_injective ℤ (FnField P)).2 hΦ
  have := (faithfulSMul_iff_algebraMap_injective (FnField P) (MvPolynomial (Fin n) (FnField P))).2
    (C_injective _ _)
  have := (faithfulSMul_iff_algebraMap_injective S (MvPolynomial (Fin n) (FnField P))).2 Subtype.val_injective
  have := (faithfulSMul_iff_algebraMap_injective ℤ S).2 fun a b h => hM (by
    rw [IsScalarTower.algebraMap_apply ℤ S (MvPolynomial (Fin n) (FnField P)) a,
      IsScalarTower.algebraMap_apply ℤ S (MvPolynomial (Fin n) (FnField P)) b, h])
  have : Algebra.IsAlgebraic (MRing ι ⧸ P) (FnField P) := IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have e1 := trdeg_add_eq ℤ S (A := MvPolynomial (Fin n) (FnField P))
  have e2 := trdeg_add_eq ℤ (FnField P) (A := MvPolynomial (Fin n) (FnField P))
  have e3 := trdeg_add_eq ℤ (MRing ι ⧸ P) (A := FnField P)
  rw [trdeg_eq_zero (R := S) (A := MvPolynomial (Fin n) (FnField P)), add_zero] at e1
  rw [trdeg_eq_zero (R := MRing ι ⧸ P) (A := FnField P), add_zero] at e3
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at e2
  rw [e1, ← e2, e3]

end Bundle

/- English proof (translation)
Introduce `K _ ι _ N1 n P d B hP hB`. Take `⟨-, ⟨hPr, -, -⟩, hPz, -⟩` from `hP`. Establish `hHor : IsHorizontal (projBundleIdeal P B)`. Use extensionality with `z`. Rewrite using `[Ideal.mem_comap, Ideal.mem_bot]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2 : (C z : MRing ι) ∈ P` using `(rename_inlV_mem_projBundleIdeal_iff P B (C z)).1 (by simpa using h)`. Establish `h3 : z ∈ P.comap (C : ℤ →+* MRing ι)` using `h2`. Rewrite `h3` using `[hPz]`.

Conclude with `h3`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Establish `hprime : (projBundleIdeal P B).IsPrime` using `RingHom.ker_isPrime _`. Rewrite using `[hInt _ (algebraMap_int_injective _ hHor), hInt _ (algebraMap_int_injective P hPz), trdeg_projBundle P hPz B hB, map_add, map_natCast]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ProjBundleDim.proof (hInt : IntDomainDim.Statement) : ProjBundleDim.Statement := by
  intro K _ ι _ N1 n P d B hP hB
  obtain ⟨-, ⟨hPr, -, -⟩, hPz, -⟩ := hP
  have hHor : IsHorizontal (projBundleIdeal P B) := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h
      have h2 : (C z : MRing ι) ∈ P := (rename_inlV_mem_projBundleIdeal_iff P B (C z)).1 (by simpa using h)
      have h3 : z ∈ P.comap (C : ℤ →+* MRing ι) := h2
      rw [hPz] at h3
      exact h3
    · rintro rfl
      simp
  have hprime : (projBundleIdeal P B).IsPrime := RingHom.ker_isPrime _
  rw [hInt _ (algebraMap_int_injective _ hHor), hInt _ (algebraMap_int_injective P hPz),
    trdeg_projBundle P hPz B hB, map_add, map_natCast]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
